{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NoStarIsType #-}
module PMap where
import PCore
import POrd
import Data.Type.Equality
import GHC.TypeNats
import GHC.TypeLits hiding (natVal,natVal')

type family InsertWithKey (f :: k ~> a ~> a ~> a) (x :: k) (y :: a) (kvs :: [(k, a)]) :: [(k, a)] where
  InsertWithKey _ k a '[] = '[ '(k, a) ]
  InsertWithKey f k a ( '(k1, a1) ': kvs ) = If (k==k1) ('(k, f @@ k @@ a @@ a1) ': kvs) ('(k1, a1) ': InsertWithKey f k a kvs)

type family InsertWith (f :: a ~> a ~> a) (x :: k) (y :: a) (kvs :: [(k, a)]) :: [(k, a)] where
  InsertWith f k a kvs = InsertWithKey (KSym1 f) k a kvs

type family Insert (x :: k) (y :: a) (kvs :: [(k, a)]) :: [(k, a)] where
  Insert k a kvs = InsertWithKey (KSym1 (KSym1 (KSym1 a))) k a kvs

type family Lookup (x :: k) (kvs :: [(k, a)]) :: Maybe a where
  Lookup _ '[] = 'Nothing
  Lookup k ('(k1,a) : kvs) = If (k==k1) ('Just a) (Lookup k kvs)

type family Delete (x :: k) (kvs :: [(k, a)]) :: [(k, a)] where
  Delete k '[] = TypeError ('Text "Delete: could not find key k=" ':<>: 'ShowType k)
  Delete k ('(k1, a) : kvs) = If (k==k1) kvs ('(k1, a) ': Delete k kvs)

-- this is a strict version of FindAt
type family ElemAtMap (i :: Nat) (kvs :: [(k, a)]) :: a where
  ElemAtMap i kvs = Snd (FindAt' i kvs)

type family Keys (kvs :: [(k, a)]) :: [k] where
  Keys kvs = Map FstSym0 kvs

type family Elems (kvs :: [(k, a)]) :: [a] where
  Elems kvs = Map SndSym0 kvs

type family Singleton (x :: k) (y :: a) :: [(k, a)] where
  Singleton k a = '[ '(k, a) ]

type family UpdateWithKeys (f :: k ~> a ~> Maybe a) (x :: k) (kvs :: [(k, a)]) :: [(k, a)] where
  UpdateWithKeys _ _ '[] = '[]
  UpdateWithKeys f k ( '(k1,a) ': kvs) =
     If (k==k1)
         ( '(k1,a) ': UpdateWithKeys f k kvs)
         (Maybe' kvs (FlipSym2 ConsSym0 kvs :.: PairSym1 k) (f @@ k @@ a))

type family UpdateWith (f :: a ~> Maybe a) (x :: k) (kvs :: [(k, a)]) :: [(k, a)] where
  UpdateWith f k kvs = UpdateWithKeys (KSym1 f) k kvs

-- quadratic! cos Eq not Ord
type family UnionWith (f :: a ~> a ~> a) (m1 :: [(k, a)]) (m2 :: [(k, a)]) :: [(k, a)] where
  UnionWith _ '[] m2 = m2
  UnionWith f ('(k, a) ': kvs) m2 =
     Maybe'
       ('(k, a) ': UnionWith f kvs m2)
       (FlipSym2 ConsSym0 (UnionWith f kvs (Delete k m2)) :.: PairSym1 k :.: (f @@ a))
       (Lookup k m2)

data UnionWithSym0 :: (a ~> a ~> a) ~> [(k, a)] ~> [(k, a)] ~> [(k, a)]
type instance Apply UnionWithSym0 x = UnionWithSym1 x

data UnionWithSym1 :: (a ~> a ~> a) -> [(k, a)] ~> [(k, a)] ~> [(k, a)]
type instance Apply (UnionWithSym1 x) y = UnionWithSym2 x y

data UnionWithSym2 :: (a ~> a ~> a) -> [(k, a)] -> [(k, a)] ~> [(k, a)]
type instance Apply (UnionWithSym2 x y) z = UnionWith x y z


type family Union (m1 :: [(k, a)]) (m2 :: [(k, a)]) :: [(k, a)] where
  Union m1 m2 = UnionWith KSym0 m1 m2

type family UnionsWith (f :: a ~> a ~> a) (ms :: [[(k, a)]]) :: [(k, a)] where
  UnionsWith f ms = Foldr (UnionWithSym1 f) '[] ms


type family FilterWithKey (f :: k ~> a ~> Bool) (m :: [(k, a)]) :: [(k, a)] where
  FilterWithKey _ '[] = '[]
  FilterWithKey f ('(k, a) ': kvs) =
     If
        (f @@ k @@ a)
        ('(k, a) ': FilterWithKey f kvs)
        (FilterWithKey f kvs)

type family FilterWith (f :: a ~> Bool) (m :: [(k, a)]) :: [(k, a)] where
  FilterWith f kvs = FilterWithKey (KSym1 f) kvs

type family MergeSort (as :: [k]) where
  MergeSort as = MergeSortOn LESym0 as
-- Lessthanorequalto function (stable sort if you use <=)
type family MergeSortOn' (f :: a ~> a ~> Bool) (as :: [a]) (bs :: [a]) :: [a] where
  MergeSortOn' _ '[] bs = bs
  MergeSortOn' _ as '[] = as
  MergeSortOn' f (a ': as) (b ': bs) =
     If (f @@ a @@ b)
        (a ': MergeSortOn' f as (b ': bs))
        (b ': MergeSortOn' f (a ': as) bs)

type family MergeSortOn (f :: a ~> a ~> Bool) (as :: [a]) :: [a] where
  MergeSortOn _ '[] = '[]
  MergeSortOn _ '[a] = '[a]
  MergeSortOn f (a ': a1 ': as) = MergeSortOn'' f (SplitAt (Div (Len as+2) 2) (a ': a1 ': as))

type family MergeSortOn'' (f :: a ~> a ~> Bool) (tps :: ([a], [a])) :: [a] where
  MergeSortOn'' f '(as, bs) = MergeSortOn' f (MergeSortOn f as) (MergeSortOn f bs)

type family QuickSort as where
  QuickSort as = QuickSortOn LESym0 as

type family QuickSortOn f as where
  QuickSortOn _ '[] = '[]
  QuickSortOn f (a ': as) = QuickSortOn f (Filter (NotSym0 :.: (f @@ a)) as) ++ '[a] ++ QuickSortOn f (Filter (f @@ a) as)

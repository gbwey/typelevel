-- use IToList' instead of FWI version in lens using IToList
-- the FWI version will mess things up! might have partly cos my signatures were not accurate when call IxListSym1 cos not taking FWI into account from IToList
{-# OPTIONS -Wall #-}
-- {-# OPTIONS -Wall -Wcompat -Wincomplete-record-updates -Wincomplete-uni-patterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ConstraintKinds #-}
module PChar where
import GHC.TypeNats
import GHC.TypeLits hiding (natVal,natVal')
import PBounded
import PEq
import POrd
import PCore
import Data.Type.Equality
import PEnum
import PMonoid
import PSemigroup
import PFoldable
-- need to make this explicit else way too slow!
type CharSetLower = ["a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t","u","v","w","x","y","z"]
type CharSetUpper = ["A","B","C","D","E","F","G","H","I","J","K","L","M","N","O","P","Q","R","S","T","U","V","W","X","Y","Z"]
type CharSetDigit = ["0","1","2","3","4","5","6","7","8","9"]
type CharSetPunctuation = '["!","\"","#","%","&","'","(",")","*",",","-",".","/",":",";","?","@","[","\\","]","_","{","}"]

type family UnChar1 (arg :: Char1) :: Symbol where
  UnChar1 ('Char1 c) = c

data UnChar1Sym0 :: Char1 ~> Symbol
type instance Apply UnChar1Sym0 x = UnChar1 x

newtype Char1 = Char1 { unChar1 :: Symbol }

instance PBounded Char1 where
  type MinBound = 'Char1 (Hd CharSetLower)
  type MaxBound = 'Char1 (Lst CharSetLower)

instance PEq Char1 where
  type 'Char1 c === 'Char1 c1 = c == c1

instance POrd Char1 where
  type LessThanOrEqual ('Char1 c) ('Char1 c1) = LessThanOrEqual c c1

-- problem with expansion because i was using Lenses
-- replaced (CharSet ^? IxListSym1 n) with (FindAt n CharSet) and it expanded fine using kind!
instance PEnum Char1 where
  type ToEnum n =
           Maybe' (TypeError ('Text "ToEnum: out of range n=" ':<>: 'ShowType n))
                  (TyCon1Sym1 'Char1)
                  (FindAt n CharSetLower)
  type FromEnum ('Char1 c) =
           Maybe' (TypeError ('Text "FromEnum: oops not a valid Symbol c=" ':<>: 'ShowType c))
                  Id
                  (FindIndex c CharSetLower)
  type ESucc c =
        FailWhen (FromEnum c + 1 == Length CharSetLower)
           ('Text "ESucc: end of the road c=" ':<>: 'ShowType c)
           (ToEnum (FromEnum c + 1))

  type EPred c =
        FailWhen (FromEnum c == 0)
           ('Text "EPred: already at the beginning c=" ':<>: 'ShowType c)
           (ToEnum (FromEnum c - 1))

type family NatToString (n :: Nat) :: Symbol where
  NatToString n = If (n == 0) "0"
    (Mconcat
      (Reverse
        (Unfoldr
          (WhenSym3 (EqSym1 0)
            (KSym1 'Nothing)
            (TyCon1Sym1 'Just :.: NatToString'Sym0 :.: FlipSym2 DivModSym0 10)
           ) n
         )
       ))

type family NatToString' (n :: (Nat, Nat)) :: (Symbol, Nat) where
  NatToString' '(a, b) = '(FindAt' b CharSetDigit, a)

data NatToString'Sym0 :: (Nat, Nat) ~> (Symbol, Nat)
type instance Apply NatToString'Sym0 x = NatToString' x

type family Unique (xs :: [Symbol]) :: [Symbol] where
  Unique xs = Foldl UniqueImplSym0 '[] xs

data UniqueImplSym0 :: [a] ~> a ~> [a]
type instance Apply UniqueImplSym0 x = UniqueImplSym1 x

data UniqueImplSym1 :: [a] -> a ~> [a]
type instance Apply (UniqueImplSym1 xs) x = xs `SnocSym2` UniqueImpl 1 x "" xs

type family UniqueImpl (n :: Nat) (x :: Symbol) (suffix :: Symbol) (xs :: [Symbol]) :: Symbol where
  UniqueImpl 11 x suffix xs = TypeError ('Text "UniqueImpl: only max of 10 duplicates allowed") -- only need it so the FindAt' doesnt fail
  UniqueImpl n x suffix xs = UniqueImpl_ (ElemList (x <> suffix) xs) n x suffix xs

type family UniqueImpl_ b n x suffix xs where
  UniqueImpl_ 'True n x suffix xs = UniqueImpl (n+1) x ("_" <> FindAt' n CharSetDigit) xs
  UniqueImpl_ 'False n x suffix xs = x <> suffix



type family UniquePair (xs :: [(Symbol, k)]) :: [(Symbol,k)] where
  UniquePair xs = Foldl UniquePairImplSym0 '[] xs

data UniquePairImplSym0 :: [(Symbol, k)] ~> (Symbol, k) ~> [(Symbol, k)]
type instance Apply UniquePairImplSym0 x = UniquePairImplSym1 x

data UniquePairImplSym1 :: [(Symbol, k)] -> (Symbol, k) ~> [(Symbol, k)]
type instance Apply (UniquePairImplSym1 xs) x = xs `SnocSym2` UniquePairImpl 1 x "" (Map FstSym0 xs)

type family UniquePairImpl (n :: Nat) (x :: (Symbol, k)) (suffix :: Symbol) (xs :: [Symbol]) :: (Symbol, k) where
  UniquePairImpl 11 x suffix xs = TypeError ('Text "UniquePairImpl: only max of 10 duplicates allowed") -- only need it so the FindAt' doesnt fail
  UniquePairImpl n '(x,t) suffix xs = '(UniqueImpl_ (ElemList (x <> suffix) xs) n x suffix xs, t)


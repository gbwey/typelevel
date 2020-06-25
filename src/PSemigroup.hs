{-# OPTIONS -Wall -Wcompat -Wincomplete-record-updates -Wincomplete-uni-patterns -Wno-redundant-constraints #-}
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
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
module PSemigroup where
import GHC.TypeNats
import GHC.TypeLits hiding (natVal,natVal')
import Data.Kind (Type)
import Data.Constraint
import qualified Data.Monoid as MM
import qualified Data.Semigroup as SG
import Data.List.NonEmpty (NonEmpty(..))
import Data.These
import Data.Void
import PCore
import PNum
import Data.Functor.Const
import Data.Functor.Identity
import Data.Type.Equality
import Data.Ord
import Data.Tagged
import Data.Proxy
import Control.Applicative

data SAppSym0 :: a ~> a ~> a
type instance Apply SAppSym0 x = SAppSym1 x

data SAppSym1 :: a -> a ~> a
type instance Apply (SAppSym1 x) y = x <> y

data SconcatSym0 :: NonEmpty a ~> a
type instance Apply SconcatSym0 x = Sconcat x

data StimesSym0 :: Nat ~> a ~> a
type instance Apply StimesSym0 x = StimesSym1 x

data StimesSym1 :: Nat -> a ~> a
type instance Apply (StimesSym1 x) y = Stimes x y

class PSemigroup (a :: Type) where
  type family (arg :: a) <> (arg1 :: a) :: a
--  type x <> y = TypeError ('Text "PSemigroup (<>) is undefined x=" ':<>: 'ShowType x ':<>: 'Text " y=" ':<>: 'ShowType y)

  infixr 6 <>

  type family Sconcat (arg :: NonEmpty a) :: a
  type Sconcat ne = FoldrNE SAppSym0 ne

  type family Stimes (n :: Nat) (arg :: a) :: a
  type Stimes n a = If (n==0) (TypeError ('Text "Stimes not defined for 0 " ':<>: 'ShowType a)) (Foldr1 SAppSym0 (Replicate n a))
--  type Stimes n ne = Sconcat (Replicate n ne)

  type family SUnWrap (arg :: a) :: k1
--  type SUnWrap a = a  -- cant use this as a default cos we are now saying that a == b

{- ghc 8.10.1
src\PSemigroup.hs:70:3: error:
    • Type indexes must match class instance head
      Expected: (<>) @Constraint _ _
        Actual: (<>) @* c c1
    • In the type instance declaration for ‘<>’
      In the instance declaration for ‘PSemigroup Constraint’
   |
70 |   type c <> c1 = (c, c1)
   |   ^^^^^^^^^^^^^^^^^^^^^^
-}

-- type family == type within class instance
-- ok this is seriously cool!
instance PSemigroup Constraint where
  type (c :: Constraint) <> (c1 :: Constraint) = ((c, c1) :: Constraint)
  type SUnWrap me = me

{-
>:kind! Mconcat '[KnownNat 4, KnownNat 5]
Mconcat '[KnownNat 4, KnownNat 5] :: Constraint
= (KnownNat 4, (KnownNat 5, () :: Constraint))
-}

-- ARGGHHHHH! keep screwing up:dont use 'a' in the type cos appears in the head
instance PNum a => PSemigroup (SG.Sum a) where
  type 'SG.Sum x <> 'SG.Sum y = 'SG.Sum (PAdd x y)
  type SUnWrap ('SG.Sum x) = x
  --type Sconcat ne = FoldrNE MSumSym0 ne

{- if you see this then dont use 'a'!!!!
C:\haskell\vectorn.hs:4448:8: error:
    * Expected kind `SG.Sum a', but ` 'SG.Sum a' has kind `SG.Sum *'
    * In the first argument of `(<>)', namely ` 'SG.Sum a'
      In the type instance declaration for `<>'
      In the instance declaration for `PSemigroup (SG.Sum a)'
     |
4448 |   type 'SG.Sum a <> 'SG.Sum y = 'SG.Sum (PAdd a y)
     |        ^^^^^^^^^
-}

--  type Mappend ('SG.Sum a) ('SG.Sum b) = 'SG.Sum (a+b)
--  type Mconcat sms = Foldr MSumSym0 Mempty sms

--data MSumSym0 :: SG.Sum Nat ~> SG.Sum Nat ~> SG.Sum Nat
--type instance Apply MSumSym0 x = MSumSym1 x

--data MSumSym1 :: SG.Sum Nat -> SG.Sum Nat ~> SG.Sum Nat
--type instance Apply (MSumSym1 x) y = MSum x y

--type family MSum x y where
--  MSum ('SG.Sum x) ('SG.Sum y) = 'SG.Sum (x + y)


instance PNum a => PSemigroup (SG.Product a) where
  type 'SG.Product x <> 'SG.Product y = 'SG.Product (PMult x y)
  type SUnWrap ('SG.Product x) = x

-- it makes no diff if explicit specifying each case or handling this way ie x -- just have to handle all the cases!
instance PSemigroup a => PSemigroup (SG.Option a) where
  type 'SG.Option 'Nothing <> x = x
  type x <> 'SG.Option 'Nothing = x
  type 'SG.Option ('Just x) <> 'SG.Option ('Just y) = 'SG.Option ('Just (x <> y))
  type SUnWrap ('SG.Option ('Just x)) = 'Just (SUnWrap x)
  type SUnWrap ('SG.Option 'Nothing) = 'Nothing -- ('Nothing :: Maybe a)

instance PSemigroup a => PSemigroup (Maybe a) where
  type 'Nothing <> y = y
  type x <> 'Nothing = x
  type 'Just x <> 'Just y = 'Just (x <> y)
  type SUnWrap 'Nothing = 'Nothing
  type SUnWrap ('Just x) = 'Just (SUnWrap x)

instance PSemigroup (SG.First a) where
  type x <> y = x
  type SUnWrap ('SG.First x) = x

-- remember the semigroup and monoid types for First and Last are different
-- ie Monoid has Maybe inside
instance PSemigroup (MM.First a) where
  type 'MM.First 'Nothing <> y = y
  type 'MM.First ('Just x) <> y = 'MM.First ('Just x)
  type SUnWrap ('MM.First x) = x


instance PSemigroup (SG.Last a) where
  type x <> y = y
  type SUnWrap ('SG.Last x) = x

-- remember the semigroup and monoid types for Last and Last are different
-- ie Monoid has Maybe inside
-- remember First is sticky and Last always wants to change
instance PSemigroup (MM.Last a) where
  type 'MM.Last 'Nothing <> y = y
  type x <> 'MM.Last ('Just y) = 'MM.Last ('Just y)
  type x <> 'MM.Last 'Nothing = x
  type SUnWrap ('MM.Last x) = x



-- cant have overlaps hence it is explicit
instance PSemigroup Ordering where
  type 'EQ <> y = y
  type 'LT <> y = 'LT
  type 'GT <> y = 'GT
  type SUnWrap me = me

-- Max has lower bound of 0 cos Natural numbers
instance PNum a => PSemigroup (SG.Max a) where
  type 'SG.Max x <> 'SG.Max y = 'SG.Max $$ If (ToInteger x <=? ToInteger y) y x
  type SUnWrap ('SG.Max x) = x

-- unbounded so no Monoid instance
instance PNum a => PSemigroup (SG.Min a) where
  type 'SG.Min x <> 'SG.Min y = 'SG.Min $$ If (ToInteger x <=? ToInteger y) x y
  type SUnWrap ('SG.Min x) = x


-- tricky: we only care that Apply works so create the Apply instance
-- todo: how to unwrap using type family
-- no matter how i do it i end up with "Illegal type synonym ..."
instance PSemigroup b => PSemigroup (a ~> b) where
  type x <> y = ABSym0 x y
  type SUnWrap me = me
--  type SUnWrap me = UnWrapArrowSym1 me
--  type SUnWrap me = Fmap SUnWrapSym0 ('R me)

-- stuck
--type family UnWrapArrow (ab :: (a :: k1) ~> (b :: k2)) :: ((a :: k1) ~> (SUnWrap (b :: k2)) where
--  UnWrapArrow x = Undefined


--data UnWrapArrowSym0 :: (a ~> b) ~> a ~> SUnWrap b
--type instance Apply UnWrapArrowSym0 ab = UnWrapArrowSym1 ab

--data UnWrapArrowSym1 :: (a ~> b) -> a ~> SUnWrap b
--type instance Apply (UnWrapArrowSym1 ab) a = SUnWrap (ab @@ a)
{-
C:\haskell\typelevel\src\PSemigroup.hs:195:15-19: error:
    * Illegal type synonym family application in instance: SUnWrap a2
    * In the type instance declaration for `Apply'
    |
195 | type instance Apply (UnWrapArrowSym1 ab) a = SUnWrap (ab @@ a)
    |               ^^^^^
-}


data ABSym0 :: (a ~> b) -> (a ~> b) -> a ~> b
type instance Apply (ABSym0 f g) a = f @@ a <> g @@ a


--data XABSym0 :: (a ~> b) -> (a ~> SUnWrap b)
--type instance Apply (XABSym0 ab) a = SUnWrap (ab @@ a)
{-
D:\haskell\vectorn.hs:4751:15-19: error:
    * Illegal type synonym family application in instance: SUnWrap a2
    * In the type instance declaration for `Apply'
     |
4751 | type instance Apply (XABSym0 ab) a = SUnWrap (ab @@ a)
     |               ^^^^^
-}


-- need our own version of Endo cos can partially apply types!
newtype EndoX a = EndoX (a ~> a)
--data EndoSym0 :: a ~> a
--type instance Apply EndoSym0 x = EndoX x

instance PSemigroup (EndoX a) where
  type 'EndoX x <> 'EndoX y = 'EndoX (x :.: y)
  type SUnWrap ('EndoX x) = x

instance PSemigroup [a] where
  type '[] <> ys = ys
  type (x ': xs) <> ys = x ': (xs <> ys)
  type SUnWrap me = me

instance PSemigroup (NonEmpty a) where
  type (x ':| xs) <> (y ':| ys) = x ':| (xs <> (y ': ys))
  type SUnWrap me = me
--  type SUnWrap (x ':| xs) = x ': xs

-- had a bug where i didnt handle False False: no errors but type checker just gets stuck
instance PSemigroup SG.All where
--  type 'SG.All x <> 'SG.All y = 'SG.All (x && y)
  type 'SG.All 'True <> x = x
  type 'SG.All 'False <> x = 'SG.All 'False
  type SUnWrap ('SG.All x) = x


-- had a bug where i didnt handle True True
instance PSemigroup SG.Any where
--  type 'SG.Any x <> 'SG.Any y = 'SG.Any (x || y)
  type 'SG.Any 'False <> x = x
  type 'SG.Any 'True <> x = 'SG.Any 'True
  type SUnWrap ('SG.Any x) = x


instance (PSemigroup a, PSemigroup b) => PSemigroup (a,b) where
  type '(x, y) <> '(x1, y1) = '(x <> x1, y <> y1)
  type SUnWrap '(x, y) = '(SUnWrap x, SUnWrap y)


instance (PSemigroup a, PSemigroup b, PSemigroup c) => PSemigroup (a, b, c) where
  type '(x, y, z) <> '(x1, y1, z1) = '(x <> x1, y <> y1, z <> z1)
  type SUnWrap '(x, y, z) = '(SUnWrap x, SUnWrap y, SUnWrap z)


instance (PSemigroup a, PSemigroup b, PSemigroup c, PSemigroup d) => PSemigroup (a, b, c, d) where
  type '(x, y, z, w) <> '(x1, y1, z1, w1) = '(x <> x1, y <> y1, z <> z1, w <> w1)
  type SUnWrap '(x, y, z, w) = '(SUnWrap x, SUnWrap y, SUnWrap z, SUnWrap w)

instance PSemigroup a => PSemigroup (SG.Dual a) where
  type 'SG.Dual x <> 'SG.Dual y = 'SG.Dual (y <> x)
  type SUnWrap ('SG.Dual x) = SUnWrap x


data SMinSym0 :: a ~> SG.Min a
type instance Apply SMinSym0 x = 'SG.Min x

data SMaxSym0 :: a ~> SG.Max a
type instance Apply SMaxSym0 x = 'SG.Max x

data SOptionSym0 :: a ~> SG.Option a
type instance Apply SOptionSym0 x = 'SG.Option ('Just x)

data SFirstSym0 :: a ~> SG.First a
type instance Apply SFirstSym0 x = 'SG.First x

data SLastSym0 :: a ~> SG.Last a
type instance Apply SLastSym0 x = 'SG.Last x

data SDualSym0 :: a ~> SG.Dual a
type instance Apply SDualSym0 x = 'SG.Dual x

data SSumSym0 :: a ~> SG.Sum a
type instance Apply SSumSym0 x = 'SG.Sum x

data SProductSym0 :: a ~> SG.Product a
type instance Apply SProductSym0 x = 'SG.Product x

data SAllSym0 :: Bool ~> SG.All
type instance Apply SAllSym0 x = 'SG.All x

data SAnySym0 :: Bool ~> SG.Any
type instance Apply SAnySym0 x = 'SG.Any x

-- AGAIN make sure you dont use x y else you get weird errors: use a a1 b etc [ie dont use vars from the instance head]
-- no monoid instance for These and ZipList
instance (PSemigroup x, PSemigroup y) => PSemigroup (These x y) where
  type 'This a <> 'This a1 = 'This a
  type 'This a <> 'That b = 'These a b
  type 'This a <> 'These a1 b = 'These (a <> a1) b

  type 'That b <> 'This a = 'These a b
  type 'That b <> 'That b1 = 'That (b <> b1)
  type 'That b <> 'These a b1 = 'These a (b <> b1)

  type 'These a b <> 'This a1 = 'These (a <> a1) b
  type 'These a b <> 'That b1 = 'These a (b <> b1)
  type 'These a b <> 'These a1 b1 = 'These (a <> a1) (b <> b1)
  -- make sure to deeply unwrap! ie ...
  type SUnWrap ('This a) = 'This (SUnWrap a)
  type SUnWrap ('That b) = 'That (SUnWrap b)
  type SUnWrap ('These a b) = 'These (SUnWrap a) (SUnWrap b)

instance PSemigroup (Either x y) where
  type 'Left a <> 'Left a1 = 'Left a1
  type 'Left a <> 'Right b = 'Right b
  type 'Right b <> 'Left a1 = 'Right b
  type 'Right a <> 'Right a1 = 'Right a1
  type SUnWrap me = me  -- dont use x or y cos mentioned on the head cos will cause problems

{-
-- this fails: have to be explicit
instance PSemigroup (Either x y) where
  type 'Left a <> b = b
  type 'Right a <> x = 'Right a
  type SUnWrap me = me  -- dont use x or y cos mentioned on the head and will cause problems
-}
{-
D:\haskell\typelevel\src\PSemigroup.hs:323:20: error:
    * Expected kind `Either x y', but `x' has kind `*'
    * In the second argument of `(<>)', namely `x'
      In the type instance declaration for `<>'
      In the instance declaration for `PSemigroup (Either x y)'
    |
323 |   type 'Right a <> x = 'Right a
-}

instance PSemigroup () where
  type '() <> '() = '()
  type SUnWrap me = me

instance PSemigroup Symbol where
  type s <> s1 = AppendSymbol s s1
  type SUnWrap me = me

instance PSemigroup Void where
  type x <> x = x
  type SUnWrap me = '()

instance PSemigroup (Proxy z) where
  type 'Proxy <> 'Proxy = 'Proxy
  type SUnWrap me = '()

instance PSemigroup s => PSemigroup (Tagged s a) where
  type 'Tagged a1 <> 'Tagged a2 = 'Tagged (a1 <> a2)
  type SUnWrap ('Tagged a1) = a1

-- there is no instance for monoid or semigroup
--instance PSemigroup (ZipList a) where
--  type 'ZipList as <> 'ZipList bs = 'ZipList (as <> bs)
--  type SUnWrap ('ZipList me) = me

-- there is no semigroup/monoid instance for ziplist but we are creating one
-- which is different cos it accesses an inner semigroup which makes it useful
-- from a simple list: a<>b for each element in the zip
instance PSemigroup z => PSemigroup (ZipList z) where
   type 'ZipList as <> 'ZipList bs = 'ZipList (ZipListAppend as bs)
   type SUnWrap ('ZipList '[]) = '[]
   type SUnWrap ('ZipList (a ': as)) = SUnWrap a ': SUnWrap ('ZipList as)

type family ZipListAppend as bs where
  ZipListAppend '[] bs = bs
  ZipListAppend as '[] = as
  ZipListAppend (a ': as) (b ': bs) = (a <> b) ': ZipListAppend as bs

instance PSemigroup z => PSemigroup (Const z z1) where
  type 'Const a <> 'Const b = 'Const (a <> b)
  type SUnWrap ('Const a) = SUnWrap a

instance PSemigroup z => PSemigroup (Identity z) where
  type 'Identity a <> 'Identity b = 'Identity (a <> b)
  type SUnWrap ('Identity a) = a

instance PSemigroup z => PSemigroup (Down z) where
  type 'Down a <> 'Down a1 = 'Down (a <> a1)
  type SUnWrap ('Down e) = e

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE NoStarIsType #-}
module PCore where
import Data.Type.Equality ( type (==) ) -- only using it for Nat ==. use PEq for all other uses!
import Data.Constraint ( Constraint )
import GHC.Natural ( Natural )
import GHC.TypeNats (KnownNat,Nat,type (<=?),CmpNat,Div,Mod,Log2,natVal,type (-), type(+), type(*), type(^))
import GHC.TypeLits (KnownSymbol,Symbol,TypeError,AppendSymbol,ErrorMessage(Text, (:<>:), ShowType),symbolVal)
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty(..))
import Data.These ( These(..) )
import Data.Proxy ( Proxy(..) )
import Data.Tagged ( Tagged )
import qualified Data.Semigroup as SG
import qualified Data.Monoid as MM
import qualified Data.Symbol.Ascii as S
import Data.Functor.Identity ( Identity(Identity) )
import Data.Functor.Compose ( Compose(Compose) )
import Data.Functor.Const ( Const(Const) )
import Data.Void ( Void )
import Control.Applicative (ZipList)

-- Deep equals: required when looking at kinds
-- Nat DTE.== Nat  is 'True but Nat PEq.== Nat is stuck
-- cant handle it cos not a type but a kind! so we cant have as an instance of PEq class
-- 4 == 4 does work though

type family (/=) (x :: a) (y :: a) :: Bool where
  x /= y = Not (x == y)

infix 4 /=

data EqSym0 :: k ~> k ~> Bool
type instance Apply EqSym0 x = EqSym1 x

data EqSym1 :: k -> k ~> Bool
type instance Apply (EqSym1 x) y = x == y

data NeSym0 :: k ~> k ~> Bool
type instance Apply NeSym0 x = NeSym1 x

data NeSym1 :: k -> k ~> Bool
type instance Apply (NeSym1 x) y = Not (x == y)


data SListSym0 :: Symbol ~> [Symbol]
type instance Apply SListSym0 x = S.ToList x

data SHeadSym0 :: Symbol ~> Symbol
type instance Apply SHeadSym0 x = S.Head x

-- not so great cos it either works or gets stuck: see PParser for a better approach using IntP or IntP' (signed)
data SReadNatSym0 :: Symbol ~> Nat
type instance Apply SReadNatSym0 x = S.ReadNat x

data TyFun a b
type a ~> b = TyFun a b -> Type
infixr 0 ~>

type family Apply (f :: a ~> b) (x :: a) :: b

--type f @@ a = Apply f a
type family f @@ a where
  f @@ a = Apply f a

infixl 9 @@

{- not sure how to write the signature here? let ghc figure it out
type family S (eab :: a1 ~> (a ~> k)) (ea :: a1 ~> a) (e :: a1) :: k
-- (eab :: (e :: k) ~> (a :: k1) ~> (b :: k2)) (ea :: e ~> a) (arg :: e) :: k2
-}
type family S eab ea e where
  S eab ea e = eab @@ e @@ (ea @@ e)

data SSym0 :: (e ~> a ~> b) ~> (e ~> a) ~> e ~> b
type instance Apply SSym0 eab = SSym1 eab

data SSym1 :: (e ~> a ~> b) -> (e ~> a) ~> e ~> b
type instance Apply (SSym1 eab) ea = SSym2 eab ea

data SSym2 :: (e ~> a ~> b) -> (e ~> a) -> e ~> b
type instance Apply (SSym2 eab ea) e = S eab ea e


type family K (x :: k) (y :: k1) :: k where
  K x _ = x

data KSym0 :: a ~> b ~> a
type instance Apply KSym0 x = KSym1 x

data KSym1 :: a -> b ~> a
type instance Apply (KSym1 x) y = K x y


type family KK (x :: k) (y :: k) :: k where
  KK x _ = x

data KKSym0 :: a ~> a ~> a
type instance Apply KKSym0 x = KKSym1 x

data KKSym1 :: a -> a ~> a
type instance Apply (KKSym1 x) y = KK x y

type family I (x :: k) :: k where
  I x = x

data ISym0 :: a ~> a
type instance Apply ISym0 x = I x

data FlipSym0 :: (a ~> b ~> c) ~> b ~> a ~> c
type instance Apply FlipSym0 x = FlipSym1 x

data FlipSym1 :: (a ~> b ~> c) -> b ~> a ~> c
type instance Apply (FlipSym1 x) y = FlipSym2 x y

data FlipSym2 :: (a ~> b ~> c) -> b -> a ~> c
type instance Apply (FlipSym2 x y) z = x @@ z @@ y

type family Flip x y z where Flip x y z = x @@ z @@ y


data AppSym0 :: (a ~> b) ~> a ~> b
type instance Apply AppSym0 x = AppSym1 x

data AppSym1 :: (a ~> b) -> a ~> b
type instance Apply (AppSym1 x) y =  x @@ y

-- this is (.)
type family Dot f g a where
  Dot f g a = f $ g @@ a

data DotSym0 :: (b ~> c) ~> (a ~> b) ~> a ~> c
type instance Apply DotSym0 x = DotSym1 x

data DotSym1 :: (b ~> c) -> (a ~> b) ~> a ~> c
type instance Apply (DotSym1 x) y = x :.: y

data (:.:) :: (b ~> c) -> (a ~> b) -> a ~> c
type instance Apply (x :.: y) z = Dot x y z
infixr 9 :.:

-- keep for consistency
data DotSym2 :: (b ~> c) -> (a ~> b) -> a ~> c
type instance Apply (DotSym2 x y) z = Dot x y z

-- >:t ((.).(.))
-- ((.).(.)) :: (b -> c) -> (a1 -> a2 -> b) -> a1 -> a2 -> c

data TwoSym0 :: (b ~> c) ~> (a1 ~> a2 ~> b) ~> a1 ~> a2 ~> c
type instance Apply TwoSym0 x =  TwoSym1 x

data TwoSym1 :: (b ~> c) -> (a1 ~> a2 ~> b) ~> a1 ~> a2 ~> c
type instance Apply (TwoSym1 x) y =  TwoSym2 x y

data (:..:) :: (b ~> c) -> (a1 ~> a2 ~> b) -> a1 ~> a2 ~> c
type instance Apply (x :..: y) z =  TwoSym3 x y z

infixr 9 :..:

data TwoSym2 :: (b ~> c) -> (a1 ~> a2 ~> b) -> a1 ~> a2 ~> c
type instance Apply (TwoSym2 x y) z =  TwoSym3 x y z

data TwoSym3 :: (b ~> c) -> (a1 ~> a2 ~> b) -> a1 -> a2 ~> c
type instance Apply (TwoSym3 x y z) w =  TwoSym4 x y z w

type family TwoSym4 x y z w where
  TwoSym4 x y z w = x $ y @@ z @@ w

data ThreeSym0 :: (b ~> c) ~> (a1 ~> a2 ~> a3 ~> b) ~> a1 ~> a2 ~> a3 ~> c
type instance Apply ThreeSym0 x =  ThreeSym1 x

data ThreeSym1 :: (b ~> c) -> (a1 ~> a2 ~> a3 ~> b) ~> a1 ~> a2 ~> a3 ~> c
type instance Apply (ThreeSym1 x) y =  ThreeSym2 x y

data ThreeSym2 :: (b ~> c) -> (a1 ~> a2 ~> a3 ~> b) -> a1 ~> a2 ~> a3 ~> c
type instance Apply (ThreeSym2 x y) z =  ThreeSym3 x y z

data ThreeSym3 :: (b ~> c) -> (a1 ~> a2 ~> a3 ~> b) -> a1 -> a2 ~> a3 ~> c
type instance Apply (ThreeSym3 x y z) w =  ThreeSym4 x y z w

data ThreeSym4 :: (b ~> c) -> (a1 ~> a2 ~> a3 ~> b) -> a1 -> a2 -> a3 ~> c
type instance Apply (ThreeSym4 x y z w) w1 =  ThreeSym5 x y z w w1

type family ThreeSym5 x y z w w1 where
  ThreeSym5 x y z w w1 = x $ y @@ z @@ w @@ w1

type family (:...:) x y where (:...:) x y = ThreeSym2 x y
infixr 9 :...:

type family ($) (a :: k ~> k1) (b :: k) :: k1 where
  ($) a b = a @@ b
infixr 0 $

type family (&) (a :: k) (b :: k ~> k1) :: k1 where
  (&) a b = b @@ a
infixl 1 &

-- this doesnt work cos of partial application: works in ghci :kind! but not in signatures
-- doesnt work cos of partial application works from ghci :kind! but not in signatures
-- not useful cos no partial evaluation for type synonyms or families

-- this works fine in type family definitions and :kind! just not elsewhere
-- also used for Constraints ie k -> Constraint but if you need unsaturated then use TyCon1Sym0 or TyCon1Sym1 or just apply direct eg Show Int
type family ($$) (a :: k -> k1) (b :: k) :: k1 where
  ($$) a b = a b
infixr 0 $$

{-
-- same as TyCon1Sym0
data DollarSym0 :: (a -> b) ~> a ~> b
type instance Apply DollarSym0 x = DollarSym1 x

-- same as TyCon1Sym1
data DollarSym1 :: (a -> b) -> a ~> b
type instance Apply (DollarSym1 x) y = x y
-}

-- clashes with And so have to use a different operator
type family (&$) (b :: k) (a :: k -> k1) :: k1 where
  (&$) a b = b a
infixl 1 &$

data SMaybeSym0 :: (a ~> a ~> a) ~> Maybe a ~> Maybe a ~> Maybe a
type instance Apply SMaybeSym0 x = SMaybeSym1 x

data SMaybeSym1 :: (a ~> a ~> a) -> Maybe a ~> Maybe a ~> Maybe a
type instance Apply (SMaybeSym1 x) y = SMaybeSym2 x y

data SMaybeSym2 :: (a ~> a ~> a) -> Maybe a -> Maybe a ~> Maybe a
type instance Apply (SMaybeSym2 x y) z = SMaybe x y z

type family SMaybe (f :: a ~> a ~> a) (x :: Maybe a) (y :: Maybe a) :: Maybe a where
  SMaybe _ a 'Nothing = a
  SMaybe _ 'Nothing b = b
  SMaybe f ('Just a) ('Just b) = 'Just (f @@ a @@ b)


type family Foldr (f :: j ~> k ~> k) (z :: k) (xs :: [j]) :: k where
  Foldr _ z '[]       = z
  Foldr f z (x ': xs) = f @@ x $ Foldr f z xs

data FoldrSym0 :: (j ~> k ~> k) ~> k ~> [j] ~> k
type instance Apply FoldrSym0 x = FoldrSym1 x

data FoldrSym1 :: (j ~> k ~> k) -> k ~> [j] ~> k
type instance Apply (FoldrSym1 x) y = FoldrSym2 x y

data FoldrSym2 :: (j ~> k ~> k) -> k -> [j] ~> k
type instance Apply (FoldrSym2 x y) z = Foldr x y z


type family Foldr1 (f :: k ~> k ~> k) (xs :: [k]) :: k where
  Foldr1 _ '[] = TypeError ('Text "Foldr1: empty list")
  Foldr1 _ '[x] = x
  Foldr1 f (x ': xs) = f @@ x $ Foldr1 f xs

data Foldr1Sym0 :: (k ~> k ~> k) ~> [k] ~> k
type instance Apply Foldr1Sym0 x = Foldr1Sym1 x

data Foldr1Sym1 :: (k ~> k ~> k) -> [k] ~> k
type instance Apply (Foldr1Sym1 x) y = Foldr1 x y

type family FoldrNE (f :: k ~> k ~> k) (xs :: NonEmpty k) :: k where
  FoldrNE _ (x ':| '[]) = x
  FoldrNE f (x ':| (x1 ': xs)) = f @@ x $ FoldrNE f (x1 ':| xs)

data FoldrNESym0 :: (k ~> k ~> k) ~> (NonEmpty k ~> k)
type instance Apply FoldrNESym0 x = FoldrNESym1 x

data FoldrNESym1 :: (k ~> k ~> k) -> (NonEmpty k ~> k)
type instance Apply (FoldrNESym1 x) y = FoldrNE x y

-- oops found a mistake where (f @@ x) @@ z    should be (f @@ z) @@ x
-- only way i found it was to write the exact xlation at the value level: ie foldlTest
type family Foldl (f :: k ~> j ~> k) (z :: k) (xs :: [j]) :: k where
  Foldl _ z '[]       = z
  Foldl f z (x ': xs) = Foldl f (f @@ z @@ x) xs

data FoldlSym0 :: (k ~> j ~> k) ~> k ~> [j] ~> k
type instance Apply FoldlSym0 x = FoldlSym1 x

data FoldlSym1 :: (k ~> j ~> k) -> k ~> [j] ~> k
type instance Apply (FoldlSym1 x) y = FoldlSym2 x y

data FoldlSym2 :: (k ~> j ~> k) -> k -> [j] ~> k
type instance Apply (FoldlSym2 x y) z = Foldl x y z

type family UnfoldNat (f :: Nat ~> b ~> b) (x :: b) (n :: Nat) :: b where
  UnfoldNat _ b 0 = b
  UnfoldNat f b n = UnfoldNat f (f @@ n @@ b) (n - 1)

data UnfoldNatSym0 :: (Nat ~> b ~> b) ~> b ~> Nat ~> b
type instance Apply UnfoldNatSym0 x = UnfoldNatSym1 x

data UnfoldNatSym1 :: (Nat ~> b ~> b) -> b ~> Nat ~> b
type instance Apply (UnfoldNatSym1 x) y = UnfoldNatSym2 x y

data UnfoldNatSym2 :: (Nat ~> b ~> b) -> b -> Nat ~> b
type instance Apply (UnfoldNatSym2 x y) z = UnfoldNat x y z

type family UnfoldNat2 (f :: s ~> (a,s)) (n :: Nat) (x :: s) :: [a] where
  UnfoldNat2 _ 0 _ = '[]
  UnfoldNat2 f n s = UnCurry ConsSym0 (Second (UnfoldNat2Sym2 f (n - 1)) (f @@ s))

data UnfoldNat2Sym0 :: (s ~> (a,s)) ~> Nat ~> s ~> [a]
type instance Apply UnfoldNat2Sym0 x = UnfoldNat2Sym1 x

data UnfoldNat2Sym1 :: (s ~> (a,s)) -> Nat ~> s ~> [a]
type instance Apply (UnfoldNat2Sym1 x) y = UnfoldNat2Sym2 x y

data UnfoldNat2Sym2 :: (s ~> (a,s)) -> Nat -> s ~> [a]
type instance Apply (UnfoldNat2Sym2 x y) z = UnfoldNat2 x y z


type family FromMaybe (arg :: a) (arg1 :: Maybe a) :: a where
  FromMaybe a ma = Maybe' a Id ma


type family Maybe' (b :: k) (f :: a ~> k) (d :: Maybe a) :: k where
  Maybe' b _ 'Nothing = b
  Maybe' _ f ('Just a) = f @@ a

data Maybe'Sym0 :: b ~> (a ~> b) ~> Maybe a ~> b
type instance Apply Maybe'Sym0 x = Maybe'Sym1 x

data Maybe'Sym1 :: b -> (a ~> b) ~> Maybe a ~> b
type instance Apply (Maybe'Sym1 x) y = Maybe'Sym2 x y

data Maybe'Sym2 :: b -> (a ~> b) -> Maybe a ~> b
type instance Apply (Maybe'Sym2 x y) z = Maybe' x y z



type family Either' (f :: a ~> k) (g :: a ~> k) (d :: Either a b) :: k where
  Either' f _ ('Left a) = f @@ a
  Either' _ g ('Right b) = g @@ b

data Either'Sym0 :: (a ~> c) ~> (b ~> c) ~> Either a b ~> c
type instance Apply Either'Sym0 x = Either'Sym1 x

data Either'Sym1 :: (a ~> c) -> (b ~> c) ~> Either a b ~> c
type instance Apply (Either'Sym1 x) y = Either'Sym2 x y

data Either'Sym2 :: (a ~> c) -> (b ~> c) -> Either a b ~> c
type instance Apply (Either'Sym2 x y) z = Either' x y z

type family Unfoldr1 (f :: s ~> (a, Maybe s)) (x :: s) :: [a] where
  Unfoldr1 f s = UnCurry ConsSym0 (Second (Maybe'Sym2 '[] (Unfoldr1Sym1 f)) (f @@ s))

data Unfoldr1Sym0 :: (s ~> (a, Maybe s)) ~> s ~> [a]
type instance Apply Unfoldr1Sym0 x = Unfoldr1Sym1 x

data Unfoldr1Sym1 :: (s ~> (a, Maybe s)) -> s ~> [a]
type instance Apply (Unfoldr1Sym1 x) y = Unfoldr1 x y

-- calls Unfoldr1Sym1 ie leverages [a] version cos NonEmpty doesnt compose properly
-- eg a :| NonEmpty a doesnt exist
--  a :| [a]!!
type family Unfoldr1' (f :: s ~> (a, Maybe s)) (x :: s) :: NonEmpty a where
  Unfoldr1' f s = UnCurry Cons1Sym0 (Second (Maybe'Sym2 '[] (Unfoldr1Sym1 f)) (f @@ s))

data Unfoldr1'Sym0 :: (s ~> (a, Maybe s)) ~> (s ~> NonEmpty a)
type instance Apply Unfoldr1'Sym0 x = Unfoldr1'Sym1 x

data Unfoldr1'Sym1 :: (s ~> (a, Maybe s)) -> (s ~> NonEmpty a)
type instance Apply (Unfoldr1'Sym1 x) y = Unfoldr1' x y


-- trick is to use DotSym2 for dot composition not Apply which is $ function application
type family Unfoldr (f :: s ~> Maybe (a,s)) (x :: s) :: [a] where
  Unfoldr f s = Maybe' '[] (UnCurrySym1 ConsSym0 :.: SecondSym1 (UnfoldrSym1 f)) (f @@ s)

data UnfoldrSym0 :: (s ~> Maybe (a,s)) ~> s ~> [a]
type instance Apply UnfoldrSym0 x = UnfoldrSym1 x

data UnfoldrSym1 :: (s ~> Maybe (a,s)) -> s ~> [a]
type instance Apply (UnfoldrSym1 x) y = Unfoldr x y

data AmpSym0 :: (a ~> k) ~> ((a ~> k1) ~> a ~> (k,k1))
type instance Apply AmpSym0 x = AmpSym1 x

data AmpSym1 :: (a ~> k) -> ((a ~> k1) ~> a ~> (k,k1))
type instance Apply (AmpSym1 x) y = AmpSym2 x y

data AmpSym2 :: (a ~> k) -> ((a ~> k1) -> a ~> (k,k1))
type instance Apply (AmpSym2 x y) z = (&&&) x y z

type family DupSym0 where DupSym0 = AmpSym2 Id Id
type family DupSym1 s where DupSym1 s = (***) Id Id s

data StarSym0 :: (a ~> k) ~> (b ~> k1) ~> (a,b) ~> (k,k1)
type instance Apply StarSym0 x = StarSym1 x

data StarSym1 :: (a ~> k) -> (b ~> k1) ~> (a,b) ~> (k,k1)
type instance Apply (StarSym1 x) y = StarSym2 x y

data StarSym2 :: (a ~> k) -> (b ~> k1) -> (a,b) ~> (k,k1)
type instance Apply (StarSym2 x y) z = (***) x y z

type family FirstSym0 where FirstSym0 = FlipSym2 StarSym0 Id
type family FirstSym1 f where FirstSym1 f = StarSym2 f Id

type family First f a where First f a = (***) f Id a

type family SecondSym0 where SecondSym0 = StarSym1 Id
type family SecondSym1 f where SecondSym1 f = StarSym2 Id f

type family Second g a where Second g a = (***) Id g a


type family ZipN (n :: Nat) (xs :: [a]) :: [(Nat,a)] where
  ZipN _ '[] = '[]
  ZipN n (a ': as) = '(n,a) ': ZipN (n + 1) as

data ZipNSym0 :: Nat ~> [a] ~> [(Nat,a)]
type instance Apply ZipNSym0 x = ZipNSym1 x

data ZipNSym1 :: Nat -> [a] ~> [(Nat,a)]
type instance Apply (ZipNSym1 x) y = ZipN x y

type family Cons1 (x :: a) (ne :: NonEmpty a) :: NonEmpty a where
  Cons1 x (x1 ':| xs) = x ':| (x1 ': xs)

type family (***) (f :: a ~> b) (g :: c ~> d) (ac :: (a, c)) where
  (***) f g '(a,c) = '(f @@ a, g @@ c)

type family (&&&) (f :: a ~> k) (g :: a ~> k1) (a1 :: a) :: (k, k1) where
--type family (&&&) f g a where  -- ghc often does a better job!
  (&&&) f g a = '(f @@ a, g @@ a)

type family UnZip (xs :: [(a,b)]) :: ([a],[b]) where
  UnZip ( '(a,b) ': abs ) = (***) (ConsSym1 a) (ConsSym1 b) (UnZip abs)
  UnZip '[] = '( '[], '[] )

-- alternatively
type family UnZip' (kvs :: [(k, a)]) :: ([k], [a]) where
  UnZip' kvs = (MapSym1 FstSym0 &&& MapSym1 SndSym0) kvs

-- 2 parameters hence more complex
data ConsSym0 :: k ~> [k] ~> [k]
type instance Apply ConsSym0 x = ConsSym1 x

data ConsSym1 :: k -> [k] ~> [k]
type instance Apply (ConsSym1 x) y = ConsSym2 x y

type family ConsSym2 x y where
  ConsSym2 x y = x ': y

-- just to be parallel with Snoc'
type family Cons' x y where
  Cons' x y = x ': y

-- synonyms -- '(:) and (:) work the same without warning messages
type family ConsSym0' where ConsSym0' = TyCon2Sym1 '(:)
type family ConsSym1' a where ConsSym1' a = TyCon2Sym2 (:) a
--type family ConsSym2' where ConsSym2' a as = a ': as

data Cons1Sym0 :: k ~> ([k] ~> NonEmpty k)
type instance Apply Cons1Sym0 x = Cons1Sym1 x

data Cons1Sym1 :: k -> ([k] ~> NonEmpty k)
type instance Apply (Cons1Sym1 x) y = Cons1Sym2 x y

type family Cons1Sym2 (x :: k) (y :: [k]) :: NonEmpty k where
  Cons1Sym2 x ys = x ':| ys


data ConsNESym0 :: k ~> (NonEmpty k ~> NonEmpty k)
type instance Apply ConsNESym0 x = ConsNESym1 x

data ConsNESym1 :: k -> (NonEmpty k ~> NonEmpty k)
type instance Apply (ConsNESym1 x) y = ConsNESym2 x y

type family ConsNESym2 (x :: k) (y :: NonEmpty k) :: NonEmpty k where
  ConsNESym2 x (x1 ':| ys) = x ':| x1 ': ys


type family Snoc' xs x where
  Snoc' xs x = xs ++ '[x]

data SnocSym0 :: [k] ~> k ~> [k]
type instance Apply SnocSym0 x = SnocSym1 x

data SnocSym1 :: [k] -> k ~> [k]
type instance Apply (SnocSym1 x) y = SnocSym2 x y

type family SnocSym2 xs x where
  SnocSym2 xs x = Snoc' xs x

type family UnCurry (f :: a ~> b ~> c) (ab :: (a,b)) :: c where
  UnCurry f '(a,b) = f @@ a @@ b

data UnCurrySym0 :: (a ~> b ~> c) ~> (a,b) ~> c
type instance Apply UnCurrySym0 x = UnCurrySym1 x

data UnCurrySym1 :: (a ~> b ~> c) -> (a,b) ~> c
type instance Apply (UnCurrySym1 x) y = UnCurry x y


type family Curry (f :: (a,b) ~> c) (x :: a) (y :: b) :: c where
  Curry f a b = f @@ '(a,b)

data CurrySym0 :: ((a,b) ~> c) ~> a ~> b ~> c
type instance Apply CurrySym0 x = CurrySym1 x

data CurrySym1 :: ((a,b) ~> c) -> a ~> b ~> c
type instance Apply (CurrySym1 x) y = CurrySym2 x y

data CurrySym2 :: ((a,b) ~> c) -> a -> b ~> c
type instance Apply (CurrySym2 x y) z = Curry x y z

data Id :: a ~> a
type instance Apply Id x = x

type family Not a = r | r -> a where
  Not 'True = 'False
  Not 'False = 'True

data NotSym0 :: Bool ~> Bool
type instance Apply NotSym0 a = Not a

{-
-- these 4 are exactly the same
-- data NotSym0 :: Bool ~> Bool
data NotSym0' (f :: TyFun Bool Bool) :: Type
data NotSym0'' :: TyFun Bool Bool -> Type
data NotSym0''' (f :: TyFun Bool Bool)
type instance Apply NotSym0' a = Not a
-}

data TyCon1Sym0 :: (k1 -> k2) ~> k1 ~> k2
type instance Apply TyCon1Sym0 t = TyCon1Sym1 t

data TyCon1Sym1 :: (k1 -> k2) -> k1 ~> k2
type instance Apply (TyCon1Sym1 t) a = t a

data TyCon2Sym0 :: (k1 -> k2 -> k3) ~> k1 ~> k2 ~> k3
type instance Apply TyCon2Sym0 t = TyCon2Sym1 t

data TyCon2Sym1 :: (k1 -> k2 -> k3) -> k1 ~> k2 ~> k3
type instance Apply (TyCon2Sym1 t) a = TyCon2Sym2 t a

data TyCon2Sym2 :: (k1 -> k2 -> k3) -> k1 -> k2 ~> k3
type instance Apply (TyCon2Sym2 t a) b = t a b


data TyCon3Sym0 :: (k1 -> k2 -> k3 -> k4) ~> k1 ~> k2 ~> k3 ~> k4
type instance Apply TyCon3Sym0 t = TyCon3Sym1 t

data TyCon3Sym1 :: (k1 -> k2 -> k3 -> k4) -> k1 ~> k2 ~> k3 ~> k4
type instance Apply (TyCon3Sym1 t) a = TyCon3Sym2 t a

data TyCon3Sym2 :: (k1 -> k2 -> k3 -> k4) -> k1 -> k2 ~> k3 ~> k4
type instance Apply (TyCon3Sym2 t a) b = TyCon3Sym3 t a b

data TyCon3Sym3 :: (k1 -> k2 -> k3 -> k4) -> k1 -> k2 -> k3 ~> k4
type instance Apply (TyCon3Sym3 t a b) c = t a b c

-- | And
type family (&&) (x :: Bool) (y :: Bool) :: Bool where
    'False && _ = 'False
    'True && x = x
    _ && 'False = 'False
    x && 'True = x
    x && x = x

infixr 3 &&

data AndSym0 :: Bool ~> Bool ~> Bool
type instance Apply AndSym0 x = AndSym1 x

data AndSym1 :: Bool -> Bool ~> Bool
type instance Apply (AndSym1 x) y = x && y


type family (||) (x :: Bool) (y :: Bool) :: Bool where
    'True || _ = 'True
    'False || x = x
    _ || 'True = 'True
    x || 'False = x
    x || x = x

infixr 2 ||

data OrSym0 :: Bool ~> Bool ~> Bool
type instance Apply OrSym0 x = OrSym1 x

data OrSym1 :: Bool -> Bool ~> Bool
type instance Apply (OrSym1 x) y = x || y


type family Impl (a :: Bool) (b :: Bool) :: Bool where
  Impl 'True x = x
  Impl 'False _ = 'True
  Impl x 'True = x
  Impl _ 'False = 'True

data ImplSym0 :: Bool ~> Bool ~> Bool
type instance Apply ImplSym0 x = ImplSym1 x

data ImplSym1 :: Bool -> Bool ~> Bool
type instance Apply (ImplSym1 x) y = Impl x y

-- not lazy -- careful using this!
type family If (b :: Bool) (t :: k) (f :: k) :: k where
    If 'False _ f = f
    If 'True  t _ = t

data IfSym0 :: Bool ~> k ~> k ~> k
type instance Apply IfSym0 x = IfSym1 x

data IfSym1 :: Bool -> k ~> k ~> k
type instance Apply (IfSym1 x) y = IfSym2 x y

data IfSym2 :: Bool -> k -> k ~> k
type instance Apply (IfSym2 x y) z = If x y z

--type family When (ff :: a ~> Bool) (t :: a ~> k) (f :: a ~> k) (z :: a) :: k where
type family When ff t f z where
  When ff t f z = If (ff @@ z) (t @@ z) (f @@ z)

data WhenSym0 :: (k ~> Bool) ~> (k ~> a) ~> (k ~> a) ~> k ~> a
type instance Apply WhenSym0 x = WhenSym1 x

data WhenSym1 :: (k ~> Bool) -> (k ~> a) ~> (k ~> a) ~> k ~> a
type instance Apply (WhenSym1 x) y = WhenSym2 x y

data WhenSym2 :: (k ~> Bool) -> (k ~> a) -> (k ~> a) ~> k ~> a
type instance Apply (WhenSym2 x y) z = WhenSym3 x y z

data WhenSym3 :: (k ~> Bool) -> (k ~> a) -> (k ~> a) -> k ~> a
type instance Apply (WhenSym3 x y z) w = When x y z w


data StringSym0 :: Symbol ~> Symbol ~> Symbol
type instance Apply StringSym0 x = StringSym1 x

data StringSym1 :: Symbol -> Symbol ~> Symbol
type instance Apply (StringSym1 x) y = AppendSymbol x y


data SumSym0 :: Nat ~> Nat ~> Nat
type instance Apply SumSym0 x = SumSym1 x

data SumSym1 :: Nat -> Nat ~> Nat
type instance Apply (SumSym1 x) y = x + y

data ProductSym0 :: Nat ~> Nat ~> Nat
type instance Apply ProductSym0 x = ProductSym1 x

data ProductSym1 :: Nat -> Nat ~> Nat
type instance Apply (ProductSym1 x) y = x * y

type family Subtract x y where
  Subtract x y =
    If (CmpNat x y == 'LT)
       (TypeError ('Text "SubtractSym3: " ':<>: 'ShowType x ':<>: 'Text " < " ':<>: 'ShowType y))
       (x - y)

data SubtractSym0 :: Nat ~> Nat ~> Nat
type instance Apply SubtractSym0 x = SubtractSym1 x

data SubtractSym1 :: Nat -> Nat ~> Nat
type instance Apply (SubtractSym1 x) y = Subtract x y

type family SuccSym0 where SuccSym0 = SumSym1 1
type family SuccSym1 x where SuccSym1 x = 1 + x
type family Succ x where Succ x = 1 + x

type family PredSym0 where PredSym0 = FlipSym2 SubtractSym0 1
type family PredSym1 x where PredSym1 x = Pred x
type family Pred x where Pred x = Subtract x 1

data ModSym0 :: Nat ~> Nat ~> Nat
type instance Apply ModSym0 x = ModSym1 x

data ModSym1 :: Nat -> Nat ~> Nat
type instance Apply (ModSym1 x) y = x `Mod` y

type family ModSym2 x y where
  ModSym2 x y = FailWhen (CmpNat y 0 == 'EQ) ('Text "ModSym2: denominator is zero x=" ':<>: 'ShowType x) (Mod x y)

data DivSym0 :: Nat ~> Nat ~> Nat
type instance Apply DivSym0 x = DivSym1 x

data DivSym1 :: Nat -> Nat ~> Nat
type instance Apply (DivSym1 x) y = DivSym2 x y

type family DivSym2 x y where
  DivSym2 x y = FailWhen (CmpNat y 0 == 'EQ) ('Text "DivSym2: denominator is zero x=" ':<>: 'ShowType x) (Div x y)

type family DivMod x y where
  DivMod x y = '(DivSym2 x y, ModSym2 x y)

data DivModSym0 :: Nat ~> Nat ~> (Nat, Nat)
type instance Apply DivModSym0 x = DivModSym1 x

data DivModSym1 :: Nat -> Nat ~> (Nat, Nat)
type instance Apply (DivModSym1 x) y = DivMod x y


data PowerSym0 :: Nat ~> Nat ~> Nat
type instance Apply PowerSym0 x = PowerSym1 x

data PowerSym1 :: Nat -> Nat ~> Nat
type instance Apply (PowerSym1 x) y = x ^ y


data Log2Sym0 :: Nat ~> Nat
type instance Apply Log2Sym0 x = Log2Sym1 x

type family Log2Sym1 x where Log2Sym1 x = Log2 x

type family SingSym0 where SingSym0 = FlipSym2 ConsSym0 '[]
type family Sing1Sym0 where Sing1Sym0 = FlipSym2 Cons1Sym0 '[]

data LenSym0 :: [a]  ~> Nat
type instance Apply LenSym0 as = Len as

type family Len (as :: [k]) :: Nat where
  Len '[] = 0
  Len (_ ': as) = 1 + Len as

data CmpNatSym0 :: Nat ~> Nat ~> Ordering
type instance Apply CmpNatSym0 x = CmpNatSym1 x

data CmpNatSym1 :: Nat -> Nat ~> Ordering
type instance Apply (CmpNatSym1 x) y = CmpNat x y


data FstSym0 :: (,) a b ~> a
type instance Apply FstSym0 ab = Fst ab

data SndSym0 :: (,) a b ~> b
type instance Apply SndSym0 ab = Snd ab

data SwapSym0 :: (,) a b ~> (,) b a
type instance Apply SwapSym0 ab = Swap ab

data LstSym0 :: [k] ~> k
type instance Apply LstSym0 xs = Lst xs

data HdSym0 :: [k] ~> k
type instance Apply HdSym0 xs = Hd xs

data TlSym0 :: [k] ~> [k]
type instance Apply TlSym0 xs = Tl xs


type family Lst (xs :: [k]) :: k where
  Lst (_ ': x1 ': xs) = Lst (x1 ': xs)
  Lst '[x] = x

type family Hd (xs :: [k]) :: k where
  Hd (x ': _) = x

type family Tl (xs :: [k]) :: [k] where
  Tl (_ ': xs) = xs

type family Swap (xs :: (a, b)) :: (b, a) where
  Swap '(a,b) = '(b,a)

type family Fst (xs :: (a, b)) :: a where
  Fst '(a,_) = a

type family Snd (xs :: (a, b)) :: b where
  Snd '(_,b) = b


data PairSym0 :: a ~> b ~> (a,b)
type instance Apply PairSym0 x = PairSym1 x

data PairSym1 :: a -> b ~> (a,b)
type instance Apply (PairSym1 x) y = '(x, y) -- if we call PairSym2 it doesnt get fully evaluated

type family PairSym0' where PairSym0' = TyCon2Sym1 '(,)
type family PairSym1' a where PairSym1' a = TyCon2Sym2 '(,) a
type family Pair a b where Pair a b = '(,) a b

type family Take (n :: Nat) (xs :: [a]) :: [a] where
  Take 0 _ = '[]
  Take n (a ': as) = a ': Take (PredSym1 n) as
  Take n '[] = TypeError ('Text "Take: no more data left n=" ':<>: 'ShowType n)

data TakeSym0 :: Nat ~> [k] ~> [k]
type instance Apply TakeSym0 x = TakeSym1 x

data TakeSym1 :: Nat -> [k] ~> [k]
type instance Apply (TakeSym1 x) y = Take x y


type family DropUnsafe (n :: Nat) (xs :: [a]) :: [a] where
  DropUnsafe 0 xs = xs
  DropUnsafe n (_ ': as) = DropUnsafe (PredSym1 n) as
  DropUnsafe _ '[] = '[]

type family Drop (n :: Nat) (xs :: [a]) :: [a] where
  Drop 0 xs = xs
  Drop n (_ ': as) = Drop (PredSym1 n) as
  Drop n '[] = TypeError ('Text "Drop: no more data left n=" ':<>: 'ShowType n)

data DropSym0 :: Nat ~> [k] ~> [k]
type instance Apply DropSym0 x = DropSym1 x

data DropSym1 :: Nat -> [k] ~> [k]
type instance Apply (DropSym1 x) y = Drop x y

-- stops as soon as one is empty
type family ZipWithMin (f :: a ~> b ~> c) (as :: [a]) (bs :: [b]) :: [c] where
   ZipWithMin _ _ '[] = '[]
   ZipWithMin _ '[] _ = '[]
   ZipWithMin f (a ': as) (b ': bs) = f @@ a @@ b ': ZipWithMin f as bs


type family ZipThese (as :: [a]) (bs :: [b]) :: [These a b] where
   ZipThese as '[] = Map ThisSym0 as
   ZipThese '[] bs = Map ThatSym0 bs
   ZipThese (a ': as) (b ': bs) = 'These a b ': ZipThese as bs

data ThisSym0 :: a ~> These a b
type instance Apply ThisSym0 a = 'This a

data ThatSym0 :: b ~> These a b
type instance Apply ThatSym0 b = 'That b

data TheseSym0 :: a ~> b ~> These a b
type instance Apply TheseSym0 a = TheseSym1 a

data TheseSym1 :: a -> b ~> These a b
type instance Apply (TheseSym1 a) b = 'These a b

type family These' (f :: a ~> c) (g :: b ~> c) (h :: a ~> b ~> c) (th :: These a b) :: c where
  These' f _ _ ('This a) = f @@ a
  These' _ g _ ('That b) = g @@ b
  These' _ _ h ('These a b) = h @@ a @@ b

data These'Sym0 :: (a ~> c) ~> (b ~> c) ~> (a ~> b ~> c) ~> These a b ~> c
type instance Apply These'Sym0 x = These'Sym1 x

data These'Sym1 :: (a ~> c) -> (b ~> c) ~> (a ~> b ~> c) ~> These a b ~> c
type instance Apply (These'Sym1 x) y = These'Sym2 x y

data These'Sym2 :: (a ~> c) -> (b ~> c) -> (a ~> b ~> c) ~> These a b ~> c
type instance Apply (These'Sym2 x y) z = These'Sym3 x y z

data These'Sym3 :: (a ~> c) -> (b ~> c) -> (a ~> b ~> c) -> These a b ~> c
type instance Apply (These'Sym3 x y z) w  = These' x y z w

type family Map1 (f :: j ~> k) (xs :: NonEmpty j) :: NonEmpty k where
  Map1 f (x ':| '[]) = f @@ x ':| '[]
  Map1 f (x ':| (x1 ': xs)) = Cons1 (f @@ x) (Map1 f (x1 ':| xs))

data Map1Sym0 :: (j ~> k) ~> (NonEmpty j ~> NonEmpty k)
type instance Apply Map1Sym0 x = Map1Sym1 x

data Map1Sym1 :: (j ~> k) -> (NonEmpty j ~> NonEmpty k)
type instance Apply (Map1Sym1 x) y = Map1 x y

type family Map (f :: j ~> k) (xs :: [j]) :: [k] where
  Map _ '[] = '[]
  Map f (x ': xs) = f @@ x ': Map f xs

data MapSym0 :: (j ~> k) ~> [j] ~> [k]
type instance Apply MapSym0 x = MapSym1 x

data MapSym1 :: (j ~> k) -> [j] ~> [k]
type instance Apply (MapSym1 x) y = Map x y


-- these are exactly the same
type family AA (aa :: k) (bb :: k1) :: k2
type family AA1 (aa :: k) :: k1 -> k2
type family AA2 :: k -> k1 -> k2

type family IterateNat (n :: Nat) (f :: k ~> k) (s :: k) :: [k] where
--  IterateNat' f s n = UnfoldNat (f :..: FlipSym1 KSym0) s n -- 'True
  IterateNat 0 _ _ = '[]
  IterateNat n f s = s ': IterateNat (n - 1) f (f @@ s)

type family IterateNat' (n :: Nat) (f :: k ~> k) (s :: k) :: k where
--  IterateNat' f s n = UnfoldNat (f :..: FlipSym1 KSym0) s n -- 'True
  IterateNat' 0 _ s = s
  IterateNat' n f s = IterateNat' (n - 1) f (f @@ s)

data IterateNatSym0 :: Nat ~> (a ~> a) ~> a ~> a
type instance Apply IterateNatSym0 x = IterateNatSym1 x

data IterateNatSym1 :: Nat -> (a ~> a) ~> a ~> a
type instance Apply (IterateNatSym1 x) y = IterateNatSym2 x y

data IterateNatSym2 :: Nat -> (a ~> a) -> a ~> a
type instance Apply (IterateNatSym2 x y) z = IterateNat' x y z

type family Replicate n a where
  Replicate n a = Iterate n Id a

type family Iterate (n :: Nat) (f :: a ~> a) (s :: a) :: [a] where
  Iterate 0 _ _ = '[]
  Iterate n f a = a ': Iterate (PredSym1 n) f (f @@ a)

data IterateSym0 :: Nat ~> (a ~> a) ~> a ~> [a]
type instance Apply IterateSym0 x = IterateSym1 x

data IterateSym1 :: Nat -> (a ~> a) ~> a ~> [a]
type instance Apply (IterateSym1 x) y = IterateSym2 x y

data IterateSym2 :: Nat -> (a ~> a) -> a ~> [a]
type instance Apply (IterateSym2 x y) z = Iterate x y z


type family Filter (p :: a ~> Bool) (xs :: [a]) :: [a] where
  Filter p as = Fst (Partition p as)

data FilterSym0 :: (a ~> Bool) ~> [a] ~> [a]
type instance Apply FilterSym0 x = FilterSym1 x

data FilterSym1 :: (a ~> Bool) -> [a] ~> [a]
type instance Apply (FilterSym1 x) y = Filter x y

type family Append (as :: [a]) (bs :: [a]) :: [a] where
  Append as bs = Foldr ConsSym0 bs as

data AppendSym0 :: [a] ~> [a] ~> [a]
type instance Apply AppendSym0 x = AppendSym1 x

data AppendSym1 :: [a] -> [a] ~> [a]
type instance Apply (AppendSym1 x) y = Append x y

type family (++) (as :: [a]) (bs :: [a]) :: [a] where
  as ++ bs = Append as bs

type family SplitAt (i :: Nat) (as :: [a]) :: ([a], [a]) where
  SplitAt i as =
     FailWhen (Len as + 1 <=? i)
              ('Text "SplitAt: out of range i=" ':<>: 'ShowType i)
             '(Take i as, Drop i as)

type family Break (p :: a ~> Bool) (as :: [a]) :: ([a], [a]) where
  Break _ '[] = '( '[], '[] )
  Break p (a ': as) =
    If
      (p @@ a)
      '( '[], a ': as)
      (First (ConsSym1 a) (Break p as))

type family Span (p :: a ~> Bool) (as :: [a]) :: ([a], [a]) where
  Span p as = Break (NotSym0 :.: p) as

type family Partition (p :: a ~> Bool) (xs :: [a]) :: ([a], [a]) where
  Partition _ '[] = '( '[], '[] )
  Partition p (a ': as) = If (p @@ a) (FirstSym1 (ConsSym1 a)) (SecondSym1 (ConsSym1 a)) @@ Partition p as

type family TakeWhile (p :: a ~> Bool) (xs :: [a]) :: [a] where
  TakeWhile _ '[] = '[]
  TakeWhile p (a ': as) = If (p @@ a) (a ': TakeWhile p as) '[]

type family DropWhile (p :: a ~> Bool) (xs :: [a]) :: [a] where
  DropWhile _ '[] = '[]
  DropWhile p (a ': as) = If (p @@ a) (DropWhile p as) (a ': as)

--type family MapMaybe (p :: a ~> Maybe b) (xs :: [a]) :: [b] where
type family MapMaybe p xs where
  MapMaybe _ '[] = '[]
  MapMaybe p (a ': as) = Maybe' (MapMaybe p as) (FlipSym2 ConsSym0 (MapMaybe p as)) (p @@ a)

class GetBool (a :: Bool) where
  getBool :: Bool
instance GetBool 'True where
  getBool = True
instance GetBool 'False where
  getBool = False

class GetStrings a where
  getStrings :: [String]

  getStringsP :: p a -> [String]
  getStringsP _ = getStrings @a

instance GetStrings '[] where
  getStrings = []

instance (GetStrings ss, KnownSymbol s) => GetStrings (s ': ss) where
  getStrings = symbolVal (Proxy @s) : getStrings @ss

class GetNats a where
  getNats :: [Natural]

  getNatsP :: p a -> [Natural]
  getNatsP _ = getNats @a

instance GetNats '[] where
  getNats = []

instance (GetNats ns, KnownNat n) => GetNats (n ': ns) where
  getNats = natVal (Proxy @n) : getNats @ns

instance (GetNats ns, KnownNat (Len (S.ToList n))) => GetNats (n ': ns) where
  getNats = natVal (Proxy @(Len (S.ToList n))) : getNats @ns


class GetNat a where
  getNat :: Natural
  getNatP :: Proxy a -> Natural

instance KnownNat n => GetNat n where
  getNat = natVal (Proxy @n)
  getNatP _ = getNat @n

instance KnownNat (Len (S.ToList n)) => GetNat n where
  getNat = natVal (Proxy @(Len (S.ToList n)))
  getNatP _ = getNat @n
{-
>getNats @'[ "adf","dd" ]
[3,2]
it :: [GHC.Natural.Natural]
-}

{- needs work
-- make c apply to the whole list
class ApplyList (rs :: [k]) c where
  applyList :: (forall w r . w ~ c r => ret) -> [ret]

instance ApplyList '[] c where
  applyList _ = []

instance (ApplyList rs c, c r) => ApplyList (r ': rs) c where
  applyList f = f @(c r) @r : applyList @rs @c f

-- applyList @'[1,2,3] @KnownNat getNatP

>:t applyList @'[1,2,3] @KnownNat getNat

<interactive>:1:31: error:
    * Could not deduce (GetNat a0) arising from a use of `getNat'
      from the context: w ~ KnownNat r
        bound by a type expected by the context:
                   forall (w :: Constraint) (r :: Nat). (w ~ KnownNat r) => Natural
        at <interactive>:1:1-36
      The type variable `a0' is ambiguous
-}

type family Loop (x :: ()) :: () where
  Loop n = Loop n

data LoopSym0 :: () ~> ()
type instance Apply LoopSym0 x = Loop x

type family Err (s :: Symbol) :: b where
  Err s = TypeError ('Text "Err thrown: " ':<>: 'ShowType s)

type family FailWhen (b :: Bool) (err :: ErrorMessage) (x :: r) :: r where
  FailWhen 'True err _ = TypeError ('Text "FailWhen: " ':<>: err)
  FailWhen 'False _ z = z

type family FailUnless (b :: Bool) (err :: ErrorMessage) (x :: r) :: r where
  FailUnless 'False err _ = TypeError ('Text "FailUnless: " ':<>: err)
  FailUnless 'True _ z = z

-- these can all be handled by existing combinators
--type On c f g a b = c (f a) (g b)  -- curry (uncurry c . (f *** g))
--type Again c f g a = c (f a) (g a)  --  uncurry c . (f &&& g)
--type Again2 c f g a b = c (f a b) (g a b)  -- (uncurry c .) . (uncurry f &&& uncurry g)
--type Again2C c f g a b = c (f '(a, b)) (g '(a, b)) -- (uncurry c .) . (f &&& g)

type family On' c f g a b where
  On' c f g a b = c @@ (f @@ a) @@ (g @@ b)

data On'Sym0 :: (a1 ~> (b1 ~> c)) ~> (a2 ~> a1) ~> (b2 ~> b1) ~> a2 ~> b2 ~> c
type instance Apply On'Sym0 x = On'Sym1 x

data On'Sym1 :: (a1 ~> (b1 ~> c)) -> (a2 ~> a1) ~> (b2 ~> b1) ~> a2 ~> b2 ~> c
type instance Apply (On'Sym1 x) y = On'Sym2 x y

data On'Sym2 :: (a1 ~> (b1 ~> c)) -> (a2 ~> a1) -> (b2 ~> b1) ~> a2 ~> b2 ~> c
type instance Apply (On'Sym2 x y) z = On'Sym3 x y z

data On'Sym3 :: (a1 ~> (b1 ~> c)) -> (a2 ~> a1) -> (b2 ~> b1) -> a2 ~> b2 ~> c
type instance Apply (On'Sym3 x y z) w = On'Sym4 x y z w

data On'Sym4 :: (a1 ~> (b1 ~> c)) -> (a2 ~> a1) -> (b2 ~> b1) -> a2 -> b2 ~> c
type instance Apply (On'Sym4 x y z w) w1 = On' x y z w w1

-- curry the last bit to make it easier -- could just leverage On' and just curry c
type family On'' c f g a b where
  On'' c f g a b = c @@ '(f @@ a, g @@ b)

data On''Sym0 :: ((a1,b1) ~> c) ~> (a2 ~> a1) ~> (b2 ~> b1) ~> a2 ~> b2 ~> c
type instance Apply On''Sym0 x = On''Sym1 x

data On''Sym1 :: ((a1,b1) ~> c) -> (a2 ~> a1) ~> (b2 ~> b1) ~> a2 ~> b2 ~> c
type instance Apply (On''Sym1 x) y = On''Sym2 x y

data On''Sym2 :: ((a1,b1) ~> c) -> (a2 ~> a1) -> (b2 ~> b1) ~> a2 ~> b2 ~> c
type instance Apply (On''Sym2 x y) z = On''Sym3 x y z

data On''Sym3 :: ((a1,b1) ~> c) -> (a2 ~> a1) -> (b2 ~> b1) -> a2 ~> b2 ~> c
type instance Apply (On''Sym3 x y z) w = On''Sym4 x y z w

data On''Sym4 :: ((a1,b1) ~> c) -> (a2 ~> a1) -> (b2 ~> b1) -> a2 -> b2 ~> c
type instance Apply (On''Sym4 x y z w) w1 = On'' x y z w w1


-- traditional form of 'on'
data OnSym0 :: (b ~> (b ~> c)) ~> (a ~> b) ~> a ~> a ~> c
type instance Apply OnSym0 x = OnSym1 x

data OnSym1 :: (b ~> (b ~> c)) -> (a ~> b) ~> a ~> a ~> c
type instance Apply (OnSym1 x) y = OnSym2 x y

data OnSym2 :: (b ~> (b ~> c)) -> (a ~> b) -> a ~> a ~> c
type instance Apply (OnSym2 x y) z = OnSym3 x y z

data OnSym3 :: (b ~> (b ~> c)) -> (a ~> b) -> a -> a ~> c
type instance Apply (OnSym3 x y z) w = On x y z w

type family On c f a b where
  On c f a b = c @@ (f @@ a) @@ (f @@ b)

data AgainSym0 :: (k2 ~> k3 ~> k4) ~> (k ~> k2) ~> (k ~> k3) ~> k ~> k4
type instance Apply AgainSym0 x = AgainSym1 x

type family AgainSym1 c where
  AgainSym1 c = UnCurrySym1 c :...: AmpSym0
type family AgainSym2 c f where
  AgainSym2 c f = UnCurrySym1 c :..: AmpSym1 f
type family AgainSym3 c f g where
  AgainSym3 c f g = UnCurrySym1 c :.: AmpSym2 f g
type family Again c f g a where
  Again c f g a = UnCurrySym1 c @@ (&&&) f g a

type family Again2Sym3 c f g where
  Again2Sym3 c f g = UnCurrySym1 c :..: CurrySym1 (AmpSym2 (UnCurrySym1 f) (UnCurrySym1 g))

type family Again2CSym3 c f g where
  Again2CSym3 c f g = UnCurrySym1 c :..: CurrySym1 (AmpSym2 f g)



data ArgSym0 :: e ~> a ~> SG.Arg e a
type instance Apply ArgSym0 x = ArgSym1 x

data ArgSym1 :: e -> a ~> SG.Arg e a
type instance Apply (ArgSym1 x) y = 'SG.Arg x y

data KnownNatSym0 :: Nat ~> Constraint
type instance Apply KnownNatSym0 a = KnownNat a

data KnownSymbolSym0 :: Symbol ~> Constraint
type instance Apply KnownSymbolSym0 a = KnownSymbol a

type family UnIdentity (x :: Identity a) where
  UnIdentity ('Identity a) = a

type family UnConst (x :: Const a b) where
  UnConst ('Const a) = a

type family UnCompose (x :: Compose f g a) where
  UnCompose ('Compose fga) = fga

type family UnFirstM (x :: MM.First a) where
  UnFirstM ('MM.First a) = a

type family UnLastM (x :: MM.Last a) where
  UnLastM ('MM.Last a) = a

type family UnFirst (x :: SG.First a) where
  UnFirst ('SG.First a) = a

type family UnSum (x :: SG.Sum a) where
  UnSum ('SG.Sum a) = a

type family UnMin (x :: SG.Min a) where
  UnMin ('SG.Min a) = a

type family UnMax (x :: SG.Max a) where
  UnMax ('SG.Max a) = a

type family UnLast (x :: SG.Last a) where
  UnLast ('SG.Last a) = a

type family UnProduct (x :: SG.Product a) where
  UnProduct ('SG.Product a) = a

type family UnAny (x :: SG.Any) where
  UnAny ('SG.Any a) = a

type family UnAll (x :: SG.All) where
  UnAll ('SG.All a) = a


type family IToList' i as where
  IToList' _ '[] = '[]
  IToList' i (a ': as) = '(i, a) ': IToList' (i + 1) as

type family SwapLR lr where
  SwapLR ('Left e) = 'Right e
  SwapLR ('Right a) = 'Left a

data SwapLRSym0 :: Either e a ~> Either a e
type instance Apply SwapLRSym0 x = SwapLR x

type family SingletonList (arg :: a) :: [a] where
  SingletonList a = '[a]

data SingletonListSym0 :: a ~> [a]
type instance Apply SingletonListSym0 x = SingletonList x

type family SingletonNE (arg :: a) :: NonEmpty a where
  SingletonNE a = a ':| '[]

data SingletonNESym0 :: a ~> NonEmpty a
type instance Apply SingletonNESym0 x = SingletonNE x

-- this is a cool trick but kind! doesnt work so well in ghci
-- to avoid this use IToList' instead of the indexed lens version IToList that uses FWI
type family FWI (arg :: Type) :: Type
type instance FWI [_] = Nat
type instance FWI (NonEmpty _) = Nat
type instance FWI (Maybe _) = ()
type instance FWI (Identity _) = ()
type instance FWI (ZipList _) = Nat
type instance FWI (Proxy _) = Void
type instance FWI (Tagged _ _) = ()
type instance FWI (Compose f g a) = (FWI (f (g a)), FWI (g a))
type instance FWI (e,_) = e

type family Undefined where Undefined = TypeError ('Text "Undefined called")

type family UnOption (arg :: SG.Option a) :: Maybe a where
  UnOption ('SG.Option x) = x

type family FromJust (arg :: Maybe a) :: a where
  FromJust ('Just a) = a
  FromJust 'Nothing = TypeError ('Text "FromJust Nothing found")

type family FromLeft (arg :: Either l r) :: l where
  FromLeft ('Left l) = l
  FromLeft ('Right r) = TypeError ('Text "FromLeft Right found r=" ':<>: 'ShowType r)

type family FromRight (arg :: Either l r) :: r where
  FromRight ('Left l) = TypeError ('Text "FromRight Left found l=" ':<>: 'ShowType l)
  FromRight ('Right r) = r

type family CatMaybes (arg :: [Maybe a]) :: [a] where
  CatMaybes '[] = '[]
  CatMaybes ('Just a ': as) = a ': CatMaybes as
  CatMaybes ('Nothing ': as) = CatMaybes as

-- find first match
-- this is strict: it will run every one!!
type family Case (x :: a) (fs :: [(a, b)]) (y :: b) :: b where
  Case _ '[] b0 = b0
  Case a ('(a,b) ': _) _ = b
  Case a0 ('(_,_) ': fs) b0 = Case a0 fs b0

type family Case' (x :: a) (fs :: [(a, b)]) :: b where
  Case' a fs = Case a fs (TypeError ('Text "Case': no match ie missing a case!"))


type family CaseAll (fs :: [(a ~> Bool, Bool ~> b)]) (y :: b) (x :: a) :: b where
  CaseAll '[] b0 _ = b0
  CaseAll ('(p, f) ': fs) b0 a = CaseAll' (p @@ a) a f fs b0

type family CaseAll' b a f fs b0 where
  CaseAll' 'True _ f _ _ = f @@ 'True
  CaseAll' 'False a _ fs b0 = CaseAll fs b0 a


-- version with 'a' at the end so you can compose it
type family CaseWhen (fs :: [(a ~> Bool, a ~> b)]) (y :: b) (x :: a) :: b where
  CaseWhen '[] b0 _ = b0
  CaseWhen ('(p, f) ': fs) b0 a = CaseWhen' (p @@ a) a f fs b0

type family CaseWhen' b a f fs b0 where
  CaseWhen' 'True a f _ _ = f @@ a
  CaseWhen' 'False a _ fs b0 = CaseWhen fs b0 a


data CaseWhenSym0 :: [(a ~> Bool, a ~> b)] ~> b ~> a ~> b
type instance Apply CaseWhenSym0 x = CaseWhenSym1 x

data CaseWhenSym1 :: [(a ~> Bool, a ~> b)] -> b ~> a ~> b
type instance Apply (CaseWhenSym1 x) y = CaseWhenSym2 x y

data CaseWhenSym2 :: [(a ~> Bool, a ~> b)] -> b -> a ~> b
type instance Apply (CaseWhenSym2 x y) z = CaseWhen x y z

-- version with 'a' at the end so you can compose it
type family CaseFlip (fs :: [(a, b)]) (y :: b) (x :: a) :: b where
  CaseFlip '[] b0 _ = b0
  CaseFlip ('(a,b) ': _) _ a = b
  CaseFlip ('(_,_) ': fs) b0 a0 = CaseFlip fs b0 a0


data CaseFlipSym0 :: [(a,b)] ~> b ~> a ~> b
type instance Apply CaseFlipSym0 x = CaseFlipSym1 x

data CaseFlipSym1 :: [(a,b)] -> b ~> a ~> b
type instance Apply (CaseFlipSym1 x) y = CaseFlipSym2 x y

data CaseFlipSym2 :: [(a,b)] -> b -> a ~> b
type instance Apply (CaseFlipSym2 x y) z = CaseFlip x y z


type family UnOrdering (o :: Ordering) (arg :: x) (arg1 :: x) (arg2 :: x) :: x where
  UnOrdering 'LT x _ _ = x
  UnOrdering 'EQ _ y _ = y
  UnOrdering 'GT _ _ z = z

type family Absurd (arg :: Void) :: a where
  Absurd _ = Undefined

data AbsurdSym0 :: Void ~> a
type instance Apply AbsurdSym0 x = Absurd x

type family FindIndex (arg :: a) (args :: [a]) :: Maybe Nat where
  FindIndex a0 as = FindIndexImpl 0 a0 as

type family FindIndexImpl (n :: Nat) (arg :: a) (args :: [a]) :: Maybe Nat where
  FindIndexImpl _ _ '[] = 'Nothing
  FindIndexImpl n a (a ': _) = 'Just n
  FindIndexImpl n a0 (_ ': as) = FindIndexImpl (n + 1) a0 as

type family FindAt (n :: Nat) (args :: [a]) :: Maybe a where
  FindAt n as = FindAtImpl 0 n as

type family FindAtImpl (n :: Nat) (arg :: Nat) (args :: [a]) :: Maybe a where
  FindAtImpl _ _ '[] = 'Nothing
  FindAtImpl i i (a ': _) = 'Just a
  FindAtImpl i n (_ ': as) = FindAtImpl (i + 1) n as

data FindAtSym0 :: Nat ~> [a] ~> Maybe a
type instance Apply FindAtSym0 x = FindAtSym1 x

data FindAtSym1 :: Nat -> [a] ~> Maybe a
type instance Apply (FindAtSym1 x) y = FindAt x y


type family FindAt' (n :: Nat) (args :: [a]) :: a where
  FindAt' n as =
    Maybe' (TypeError ('Text "FindAt': index out of range :left n=" ':<>: 'ShowType n))
           Id
           (FindAt n as)

data FindAt'Sym0 :: Nat ~> [a] ~> a
type instance Apply FindAt'Sym0 x = FindAt'Sym1 x

data FindAt'Sym1 :: Nat -> [a] ~> a
type instance Apply (FindAt'Sym1 x) y = FindAt' x y




type family Subset (as :: [k]) (bs :: [k]) :: Bool where
  Subset '[] _ = 'True
  Subset (a ': as) bs = Subset' as (Break (EqSym1 a) bs)

type family Subset' (as :: [k]) (tps :: ([k], [k])) :: Bool where
  Subset' _ '(_, '[]) = 'False
  Subset' as '(bs, _ ': bs1) = Subset as (bs ++ bs1)

type family DupsBy (f :: a ~> a ~> Bool) (as :: [a]) :: [a] where
  DupsBy _ '[] = '[]
  DupsBy f (a ': as) = DupsBy' f (Partition (f @@ a) (a ': as))

type family DupsBy' (f :: a ~> a ~> Bool) (tps :: ([a], [a])) :: [a] where
  DupsBy' f '(bs,cs) = If (Len bs == 1) '[] bs ++ DupsBy f cs

type family Dups (as :: [a]) :: [a] where
  Dups as = DupsBy EqSym0 as

-- more direct version without using Again2C
type family Scanr (f :: k ~> k1 ~> k1) (b :: k1) (as :: [k]) :: [k1] where
  Scanr f b as =
    UnCurry
      (FlipSym1 ConsSym0)
      (Foldr
         (CurrySym1
           (AmpSym2
             (UnCurrySym1 ConsSym0 :.: SwapSym0 :.: SndSym0)
             (UnCurrySym1 f :.: SecondSym1 SndSym0)
           )
          )
         '( '[],b) as)




-- so we keep track of b' only and then tack change of state to the beginning and then (:[]) captures the last b
scanl''' :: (b -> a -> b) -> b -> [a] -> [b]
scanl''' f b' as = foldr (\a k b -> b : k (f b a)) (:[]) as b'

-- no cheating (ie without reverse)
type family Scanl (f :: k1 ~> k ~> k1) (b :: k1) (as :: [k]) :: [k1] where
  Scanl f b as =
      b &
      Foldr
         (Curry3Sym1
             (UnCurrySym1 ConsSym0 :.: AmpSym2 Tuple33'
                  (UnCurrySym1 Id :.: AmpSym2 Tuple23'   -- k
                      (UnCurrySym1 f :.: AmpSym2 Tuple33' Tuple13')  -- f b a
                  )
              )
         )
         SingSym0 as   -- (:[]) == SingSym0 == FlipSym2 ConsSym0 '[]

-- needed me to give the whole thing a return kind ie k else ghc complains   (d :: k)
type family Curry3Sym1 (f :: ((a, b), c) ~> d) :: (a ~> (b ~> (c ~> (d :: k)))) where
  Curry3Sym1 f = (CurrySym0 :.: CurrySym0) @@ f

type family Curry3 (f :: ((a, b), c) ~> d) (x :: a) (y :: b) (z :: c) :: d where
  Curry3 f a b c = (CurrySym0 :.: CurrySym0) @@ f @@ a @@ b @@ c

type family Tuple13' :: ((a, b), c) ~> a where
  Tuple13' = FstSym0 :.: FstSym0
type family Tuple13 (f :: ((a, b), c)) :: a where
  Tuple13 '( '(a,_), _) = a

type family Tuple23' :: ((a, b), c) ~> b where
  Tuple23' = SndSym0 :.: FstSym0
type family Tuple23 (f :: ((a, b), c)) :: b where
  Tuple23 '( '(_,b), _) = b


type family Tuple33' :: ((a, b), c) ~> c where
  Tuple33' = SndSym0
type family Tuple33 (f :: ((a, b), c)) :: c where
  Tuple33 '( '(_,_), c) = c

type family Maximum (xs :: [Nat]) :: Nat where
  Maximum xs = Foldr MaximumSym0 0 xs

data MaximumSym0 :: Nat ~> Nat ~> Nat
type instance Apply MaximumSym0 x = MaximumSym1 x

data MaximumSym1 (x :: Nat) :: Nat ~> Nat
type instance Apply (MaximumSym1 x) y = Max' x y

type family Max' x y where
  Max' x y = If (x <=? y) y x

-- has to match exactly -- could use applicative instance
type family ZipWithExact (f :: a ~> b ~> c) (as :: [a]) (bs :: [b]) :: [c] where
  ZipWithExact _ '[] '[] = '[]
  ZipWithExact f (a ': as) (b ': bs) = f @@ a @@ b ': ZipWithExact f as bs
  ZipWithExact _ as '[] = TypeError ('Text "lhs is bigger by " ':<>: 'ShowType (Len as))
  ZipWithExact _ '[] bs = TypeError ('Text "rhs is bigger by " ':<>: 'ShowType (Len bs))

data ZipWithExactSym0 :: (a ~> b ~> c) ~> [a] ~> [b] ~> [c]
type instance Apply ZipWithExactSym0 x = ZipWithExactSym1 x

data ZipWithExactSym1 :: (a ~> b ~> c) -> [a] ~> [b] ~> [c]
type instance Apply (ZipWithExactSym1 x) y = ZipWithExactSym2 x y

data ZipWithExactSym2 :: (a ~> b ~> c) -> [a] -> [b] ~> [c]
type instance Apply (ZipWithExactSym2 x y) z = ZipWithExact x y z

type family Transpose (xs :: [[a]]) :: [[a]] where
  Transpose '[] = '[]
  Transpose ( '[] ': _) = '[]
  Transpose (as ': ass) = Map HdSym0 (as ': ass) ': Transpose (Map TlSym0 (as ': ass))

type family Inits (xs :: [a]) :: [[a]] where
--  Inits xs = Map ReverseSym0 (Scanl (FlipSym1 ConsSym0) '[] xs)
--  Inits xs = Reverse (Map ReverseSym0 (Tails (Reverse xs)))
  Inits xs = Scanl SnocSym0 '[] xs

type family Tails (xs :: [a]) :: [[a]] where
  Tails xs = Scanr ConsSym0 '[] xs
--  Tails xs = xs ': Unfoldr (FmapSym1 (DupSym0 :.: SndSym0) :.: UnConsSym0) xs

type family Reverse (xs :: [a]) :: [a] where
  Reverse xs = Foldl (FlipSym1 ConsSym0) '[] xs

data ReverseSym0 :: [a] ~> [a]
type instance Apply ReverseSym0 x = Reverse x

-- Foldr only takes 3 args so have to apply the '[] afterwards
type family TakeWhile' p xs where
  TakeWhile' p xs =
     '[] & Foldr (Curry3Sym1 (WhenSym3 (p :.: Tuple13')   -- ((a, k), x)
                    (UnCurrySym1 ConsSym0 :.: AmpSym2 Tuple13' (UnCurrySym1 Id :.: AmpSym2 Tuple23' Tuple33'))  -- a : k x
                    (KSym1 '[])))
           Id xs

takeWhile' :: (a -> Bool) -> [a] -> [a]
takeWhile' p xs = foldr (\a k x -> if p a then a : k x else []) id xs []

-- same as UnCurrySym1 Id
data T2AppSym0 :: (a ~> b, a) ~> a ~> b
type instance Apply T2AppSym0 x = T2AppSym1 x

data T2AppSym1 :: (a ~> b, a) -> a ~> b
type instance Apply (T2AppSym1 x) y = T2App x y

-- (z :: a) z is the type and 'a' is the kind
type family T2App (fa :: (a ~> b, a)) (z :: a) :: b where T2App '(f,a) a = f @@ a

-- same as UnCurrySym1 Id :.: FirstSym1 (UnCurrySym1 Id)
data T3AppSym0 :: ((a ~> b ~> c, a), b) ~> c
type instance Apply T3AppSym0 x = T3App x

type family T3App f where T3App '( '(f,a),b) = f @@ a @@ b


data App2Sym0 :: (a ~> b ~> c) ~> a ~> b ~> c
type instance Apply App2Sym0 x = App2Sym1 x

data App2Sym1 :: (a ~> b ~> c) -> a ~> b ~> c
type instance Apply (App2Sym1 x) y = App2Sym2 x y

data App2Sym2 :: (a ~> b ~> c) -> a -> b ~> c
type instance Apply (App2Sym2 x y) z = App2 x y z

type family App2 x y z where App2 x y z = x @@ y @@ z

pnat :: forall n . KnownNat n => Int
pnat = fromIntegral (natVal (Proxy @n))

type family IsPrefixOf (arg :: [a]) (arg1 :: [a]) :: Bool where
  IsPrefixOf '[] _ = 'True
  IsPrefixOf _ '[] = 'False
  IsPrefixOf (a ': as) (a ': bs) = IsPrefixOf as bs
  IsPrefixOf (_ ': _) (_ ': _) = 'False

data IsPrefixOfSym0 :: [a] ~> [a] ~> Bool
type instance Apply IsPrefixOfSym0 x = IsPrefixOfSym1 x

data IsPrefixOfSym1 :: [a] -> [a] ~> Bool
type instance Apply (IsPrefixOfSym1 x) y = IsPrefixOf x y

type family IsSuffixOf (arg :: [a]) (arg1 :: [a]) :: Bool where
--  IsSuffixOf as bs = On IsPrefixOfSym0 ReverseSym0 as bs
  IsSuffixOf as bs = Any' (EqSym1 as) (Tails bs)

data IsSuffixOfSym0 :: [a] ~> [a] ~> Bool
type instance Apply IsSuffixOfSym0 x = IsSuffixOfSym1 x

data IsSuffixOfSym1 :: [a] -> [a] ~> Bool
type instance Apply (IsSuffixOfSym1 x) y = IsSuffixOf x y

type family IsInfixOf (arg :: [a]) (arg1 :: [a]) :: Bool where
  IsInfixOf as bs = Any' (IsPrefixOfSym1 as) (Tails bs)

data IsInfixOfSym0 :: [a] ~> [a] ~> Bool
type instance Apply IsInfixOfSym0 x = IsInfixOfSym1 x

data IsInfixOfSym1 :: [a] -> [a] ~> Bool
type instance Apply (IsInfixOfSym1 x) y = IsInfixOf x y

{-
>:kind! Any' (IsPrefixOfSym1 (S.ToList "cde")) $$ Tails $$ S.ToList "abcdef"
Any' (IsPrefixOfSym1 (S.ToList "cde")) $$ Tails $$ S.ToList "abcdef" :: Bool
= 'True
-}


-- peels off the Maybe / Tagged / Sum / These etc
-- doesnt work from :kind! without explicit forcing
-- not well defined!
type family UnWrap fa where
  UnWrap (_ a) = a
  UnWrap x = TypeError ('Text "UnWrap: not a type constructor fa=" ':<>: 'ShowType x)

type family UnWrap1 fab where
  UnWrap1 (_ a _) = a
--  UnWrap1 (f a) = a
  UnWrap1 x = TypeError ('Text "UnWrap1: not a two type constructor fab=" ':<>: 'ShowType x)

type family UnWrap2 fab where
  UnWrap2 (_ _ b) = b
--  UnWrap2 (f a) = a
  UnWrap2 x = TypeError ('Text "UnWrap2: not a two type constructor fab=" ':<>: 'ShowType x)

type family UnWrapBoth fab where
  UnWrapBoth (_ a b) = '(a,b)
  UnWrapBoth x = TypeError ('Text "UnWrapBoth: not a two type constructor fab=" ':<>: 'ShowType x)

type family UnWrap' fa where
  UnWrap' (_ a) = a
  UnWrap' x = x

type family Intercalate (d :: Symbol) (xs :: [Symbol]) :: Symbol where
  Intercalate _ '[] = ""
  Intercalate d (x ': xs) = Foldl (UnCurrySym1 StringSym0 :..: CurrySym1 (SecondSym1 (StringSym1 d))) x xs

data IntercalateSym0 :: Symbol ~> [Symbol] ~> Symbol
type instance Apply IntercalateSym0 x = IntercalateSym1 x

data IntercalateSym1 :: Symbol -> [Symbol] ~> Symbol
type instance Apply (IntercalateSym1 x) y = Intercalate x y

type family ElemList (x :: a) (xs :: [a]) :: Bool where
  ElemList _ '[] = 'False
  ElemList x (x ': _) = 'True
  ElemList x (_ ': xs) = ElemList x xs

--type family ElemList (x :: a) (xs :: [a]) :: Bool where
--  ElemList x xs = Foldr (OrSym0 :.: EqSym1 x) 'False xs

data ElemListSym0 :: a ~> [a] ~> Bool
type instance Apply ElemListSym0 x = ElemListSym1 x

data ElemListSym1 :: a -> [a] ~> Bool
type instance Apply (ElemListSym1 x) y = ElemList x y

type family Nub xs where
--  Nub xs = Foldl (CurrySym1 (WhenSym3 (UnCurrySym1 (FlipSym1 ElemListSym0)) FstSym0 (UnCurrySym1 (FlipSym1 ConsSym0)) Undefined)) '[] xs
  Nub xs = Reverse (Foldl NubImplSym0 '[] xs)

data NubImplSym0 :: [a] ~> a ~> [a]
type instance Apply NubImplSym0 x = NubImplSym1 x

data NubImplSym1 :: [a] -> a ~> [a]
type instance Apply (NubImplSym1 xs) x = If (ElemList x xs) xs (x ': xs)

type family GroupBy (f :: a ~> a ~> Bool) (args :: [a]) :: [[a]] where
  GroupBy f as = Foldr (GroupByImplSym1 f) '[] as

type family GroupByImpl (f :: a ~> a ~> Bool) (arg :: a) (args :: [[a]]) :: [[a]] where
  GroupByImpl _ a '[] = '[ '[a] ]
  GroupByImpl f a ((a' ': xs) ': xxs) = If (f @@ a @@ a') ((a ': a' ': xs) ': xxs) ('[a] ': (a' ': xs) ': xxs)

data GroupByImplSym0 :: (a ~> a ~> Bool) ~> a ~> [[a]] ~> [[a]]
type instance Apply GroupByImplSym0 x = GroupByImplSym1 x

data GroupByImplSym1 :: (a ~> a ~> Bool) -> a ~> [[a]] ~> [[a]]
type instance Apply (GroupByImplSym1 x) y = GroupByImplSym2 x y

data GroupByImplSym2 :: (a ~> a ~> Bool) -> a -> [[a]] ~> [[a]]
type instance Apply (GroupByImplSym2 x y) z = GroupByImpl x y z


type family All' (p :: k ~> Bool) (xs :: [k]) :: Bool where
  All' p xs = Foldr (AndSym0 :.: p) 'True xs

data All'Sym0 :: (k ~> Bool) ~> [k] ~> Bool
type instance Apply All'Sym0 x = All'Sym1 x

data All'Sym1 :: (k ~> Bool) -> [k] ~> Bool
type instance Apply (All'Sym1 x) y = All' x y

type family Any' (p :: k ~> Bool) (xs :: [k]) :: Bool where
  Any' p xs = Foldr (OrSym0 :.: p) 'False xs

data Any'Sym0 :: (k ~> Bool) ~> [k] ~> Bool
type instance Apply Any'Sym0 x = Any'Sym1 x

data Any'Sym1 :: (k ~> Bool) -> [k] ~> Bool
type instance Apply (Any'Sym1 x) y = Any' x y

{-
https://gitlab.haskell.org/ghc/ghc/issues/13962
We currently permit any and all uses of unsaturated type synonyms and type families in
GHCi's `:kind` command

We made a special case for :kind some years ago to allow queries like :kind Map. The user
sensibly wants Map's kind, and we should give it to them. So the TF-saturation requirement
is dropped in :kind

partial application of 'f'
all is good until you need a partially applied type synonym
ie if you dont need Sym* then all is good
works fine with constraints eg Show Ord etc
works fine for type constructors eg 'Just Maybe
doesnt work for type families cos not fully saturated although :kind! works
  :kind! works differently so does allow unsaturated type families
  :kind! MapT ((+) 4) '[3,5]
  :kind! MapT (AppendSymbol "tt") '["aaa","Bb"]
-}
type family MapT (f :: k -> k1) (xs :: [k]) :: [k1] where
  MapT _ '[]       = '[]
  MapT f (x ': xs) = f x ': MapT f xs

type family FoldrT (f :: k -> k1 -> k1) (x :: k1) (xs :: [k]) :: k1 where
  FoldrT _ z '[] = z
  FoldrT f z (x ': xs) = f x (FoldrT f z xs)

type family FoldlT (f :: k1 -> k -> k1) (x :: k1) (xs :: [k]) :: k1 where
  FoldlT _ z '[] = z
  FoldlT f z (x ': xs) = FoldlT f (f z x) xs

type family FlipConsT (xs :: [k]) (x :: k) :: [k] where
  FlipConsT xs x = x ': xs

type family ZipWithT (f :: k -> k1 -> k2) (xs :: [k]) (ys :: [k1]) :: [k2] where
  ZipWithT _ '[] '[] = '[]
  ZipWithT f (x ': xs) (y ': ys) = f x y ': ZipWithT f xs ys
  ZipWithT _ '[] (_ ': _) = TypeError ('Text "ZipWithT left list is empty")
  ZipWithT _ (_ ': _) '[] = TypeError ('Text "ZipWithT right list is empty")

-- this works too
type family ElemT (f :: k -> Bool) (xs :: [k]) :: Maybe k where
  ElemT _ '[] = 'Nothing
  ElemT p (x ': xs) = BoolT (ElemT p xs) ('Just x) (p x)

type family BoolT (false :: k) (true :: k) (b :: Bool) :: k where
  BoolT f _ 'False = f
  BoolT _ t 'True = t

{-
-- here's where it breaks down: need to pass (a,s) to AB f but would not be fully saturated
type family UnfoldrT (f :: s -> Maybe (a,s)) (arg :: s) :: [a] where
  UnfoldrT f s  = MaybeT '[] (AB f) (f s)

type family AB (f :: s -> Maybe (a,s)) (arg :: (a,s)) :: [a] where
  AB f '(a,s) = a ': UnfoldrT f s
-}
type family MaybeT (nothing :: k) (just :: a -> k) (m :: Maybe a) :: k where
  MaybeT n _ 'Nothing = n
  MaybeT _ j ('Just a) = j a

{-
>:kind! FoldrT (+) 99 '[1,2,3,4,5]
FoldrT (+) 99 '[1,2,3,4,5] :: Nat
= 114

>:kind! FoldrT '(:) '[99] '[1,2,3,4,5]
FoldrT '(:) '[99] '[1,2,3,4,5] :: [Nat]
= '[1, 2, 3, 4, 5, 99]

>:kind! FoldlT FlipConsT '[99] '[1,2,3,4,5]
FoldlT FlipConsT '[99] '[1,2,3,4,5] :: [Nat]
= '[5, 4, 3, 2, 1, 99]

>:kind! MapT 'Just '[1,5,5]
MapT 'Just '[1,5,5] :: [Maybe Nat]
= '['Just 1, 'Just 5, 'Just 5]

>:kind! MapT Const '[(),(),Void]
MapT Const '[(),(),Void] :: [k -> *]
= '[Const (), Const (), Const Void]

>:kind! MapT Show '[Int,Double]
MapT Show '[Int,Double] :: [Constraint]
= '[Show Int, Show Double]

>:kind! MapT Maybe '[Int,Double]
MapT Maybe '[Int,Double] :: [*]
= '[Maybe Int, Maybe Double]

-- only works with :kind!
>:kind! MapT ((+) 4) '[3,5]
MapT ((+) 4) '[3,5] :: [Nat]
= '[7, 9]

-- only works with :kind!
>:kind! MapT (AppendSymbol "tt") '["aaa","Bb"]
MapT (AppendSymbol "tt") '["aaa","Bb"] :: [Symbol]
= '["ttaaa", "ttBb"]

-- only works with :kind!
>:kind! FoldrT (+) 99 '[2,3,4]
FoldrT (+) 99 '[2,3,4] :: Nat
= 108

>:kind! ZipWithT '(,) '[99] '[1,2,3,4,5]
ZipWithT '(,) '[99] '[1,2,3,4,5] :: [(Nat, Nat)]
= '(99, 1) : (TypeError ...)

>:kind! ZipWithT '(,) '["a","b","c","d","e"] '[1,2,3,4,5]
ZipWithT '(,) '["a","b","c","d","e"] '[1,2,3,4,5] :: [(Symbol,
                                                       Nat)]
= '['("a", 1), '("b", 2), '("c", 3), '("d", 4), '("e", 5)]

>:kind! ElemT ((GL.<=?) 4) '[10,12,13]
ElemT ((GL.<=?) 4) '[10,12,13] :: Maybe Nat
= 'Just 10

>:kind! ElemT ((GL.<=?) 4) '[2,3,10,12,13]
ElemT ((GL.<=?) 4) '[2,3,10,12,13] :: Maybe Nat
= 'Just 10

>:kind! ElemT ((GL.<=?) 100) '[2,3,10,12,13]
ElemT ((GL.<=?) 100) '[2,3,10,12,13] :: Maybe Nat
= 'Nothing
-}


type family Foo (x :: Bool) (y :: Bool) :: Bool where
  Foo 'True _ = 'True
  Foo 'False b = b
type family Bar :: Bool -> Bool -> Bool where -- this is what gets returned!! but no args!
--  Bar 'True _ = 'True
--  Bar 'False b = b

{- same kind signature but they are different: first takes 2 args the second none
>:kind! Bar
Bar :: Bool -> Bool -> Bool
= Bar
>:kind! Foo
Foo :: Bool -> Bool -> Bool
= Foo
-}
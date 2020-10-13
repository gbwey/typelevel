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
module PApplicative where
import Data.Kind (Type)
import Data.Functor.Const (Const(Const))
import Data.Functor.Identity (Identity(Identity))
import Data.List.NonEmpty (NonEmpty(..))
import Data.Functor.Compose ( Compose(Compose) )
import PCore
import PFunctor
import PSemigroup
import PMonoid
import qualified Data.Semigroup as SG
import Data.These ( These(..) )
import Data.Proxy ( Proxy(..) )
import Data.Tagged ( Tagged(Tagged) )
import Data.Ord ( Down(Down) )
import Control.Applicative ( ZipList(ZipList) )
import Data.Constraint ( Constraint )

class PFunctor f => PApplicative (f :: Type -> Type) where
  type family Pure (arg :: a) :: f a
  type family (<*>) (arg :: f (a ~> b)) (arg1 :: f a) :: f b
  infixl 4 <*>

  type family (<*) (arg :: f a) (arg1 :: f b) :: f a
  type x <* xs = KSym0 <$> x <*> xs
  infixl 4 <*

  type family (*>) (arg :: f a) (arg1 :: f b) :: f b
  type x *> xs = FlipSym1 KSym0 <$> x <*> xs
  infixl 4 *>

  type family LiftA (arg :: (a ~> b)) (arg1 :: f a) :: f b
  type LiftA f as = Pure f <*> as

  type family LiftA2 (arg :: (a ~> b ~> c)) (arg1 :: f a) (arg2 :: f b) :: f c
  type LiftA2 f as bs = f <$> as <*> bs

instance PApplicative (These e) where
  type Pure a = 'That a
  type 'This x <*> 'This y = 'This (x <> y)
  type 'This x <*> 'That a = 'These x a
  --type 'This x <*> 'These y a = 'These (x <> y) a   -- compiles fine even tho wrong cos same kind as b!
  type 'This x <*> 'These y _ = 'This (x <> y)

  type 'That _ <*> 'This y = 'This y
  type 'That ab <*> 'That a = 'That (ab @@ a)
  type 'That ab <*> 'These y a = 'These y (ab @@ a)

  type 'These x _ <*> 'This y = 'This (x <> y)
  type 'These x ab <*> 'That a = 'These x (ab @@ a)
  type 'These x ab <*> 'These y a = 'These (x <> y) (ab @@ a)

instance PApplicative (Const z) where
  type Pure _ = 'Const Mempty
  type 'Const e <*> 'Const e1 = 'Const (e <> e1)

instance PApplicative Identity where
  type Pure a = 'Identity a
  type 'Identity ab <*> 'Identity a = 'Identity (ab @@ a)

instance PApplicative [] where
  type Pure a = '[a]
  type '[]  <*> _ = '[]
  type (ab ': abs) <*> as  = (ab <$> as) <> (abs <*> as)

instance PApplicative NonEmpty where
  type Pure a = a ':| '[]
  type (ab ':| abs) <*> (a ':| as)  = ab @@ a ':| (abs <*> as) -- leverage applicative instance []

instance PApplicative Maybe where
  type Pure a = 'Just a
  type 'Just ab <*> 'Just a  = 'Just (ab @@ a)
  type 'Nothing <*> _ = 'Nothing
  type _ <*> 'Nothing = 'Nothing



instance PApplicative (Either e) where
  type Pure a = 'Right a
  type 'Right ab <*> 'Right a  = 'Right (ab @@ a)
  type 'Left x <*> 'Left _ = 'Left x
  type 'Right _ <*> 'Left y = 'Left y
  type 'Left x <*> 'Right _ = 'Left x

instance PApplicative (Compose (g :: Type -> Type) h) where
  type Pure a = 'Compose (Pure (Pure a))
--  type Pure a = 'Compose ((PureSym0 :.: PureSym0) @@ a) -- this also works
  type 'Compose fgab <*> 'Compose fga = 'Compose (ApSym0 <$> fgab <*> fga)

instance PApplicative ((,) e) where
  type Pure a = '(Mempty, a)
  type '(x,ab) <*> '(x1,a) = '(x <> x1, ab @@ a)

data PureSym0 :: a ~> f a
type instance Apply PureSym0 x = Pure x

data ApSym0 :: f (a ~> b) ~> f a ~> f b
type instance Apply ApSym0 x = ApSym1 x

data ApSym1 :: f (a ~> b) -> f a ~> f b
type instance Apply (ApSym1 x) y = x <*> y

instance PApplicative Proxy where
  type Pure _ = 'Proxy
  type 'Proxy <*> 'Proxy = 'Proxy

instance PApplicative (Tagged z) where
  type Pure a = 'Tagged a
  type 'Tagged ab <*> 'Tagged a = 'Tagged (ab @@ a)

instance PApplicative SG.Option where
  type Pure a = 'SG.Option ('Just a)
  type 'SG.Option x <*> 'SG.Option y = 'SG.Option (x <*> y)

instance PApplicative Down where
  type Pure a = 'Down a
  type 'Down ab <*> 'Down a = 'Down (ab @@ a)

instance PApplicative SG.Dual where
  type Pure a = 'SG.Dual a
  type 'SG.Dual ab <*> 'SG.Dual a = 'SG.Dual (ab @@ a)

-- simpler
instance PApplicative ZipList where
  type Pure a = 'ZipList '[a]
  type 'ZipList abs <*> 'ZipList as = 'ZipList (ZipWithMin Id abs as)



type family UnZipList (z :: ZipList a) :: [a] where
  UnZipList ('ZipList as) = as

data UnZipListSym0 :: ZipList a ~> [a]
type instance Apply UnZipListSym0 x = UnZipList x

type family ConstraintCartesian (arg :: [k -> Constraint]) (arg2 :: [k]) :: Constraint where
  ConstraintCartesian xs ys = Mconcat (TyCon1Sym0 <$> xs <*> ys)


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
module PContravariant where
import Data.Proxy
import Data.Kind (Type)
import Data.Functor.Compose
import Data.Functor.Const
import PCore
import PFunctor

class PContravariant (f :: Type -> Type) where
  type family Contramap (arg :: b ~> a) (arg1 :: f (a :: Type)) :: f (b :: Type)
--  type Contramap x y = TypeError ('Text "PContravariant Contramap is undefined x=" ':<>: 'ShowType x ':<>: 'Text " y=" ':<>: 'ShowType y)

  type family (>$<) (arg :: b ~> a) (arg1 :: f (a :: Type)) :: f (b :: Type)
  type x >$< xs = Contramap x xs
  infixl 4 >$<

  type family (>$) (arg :: b) (arg1 :: f b) :: f a
  type x >$ xs = Contramap (KSym1 x) xs
  infixl 4 >$

  type family ($<) (arg1 :: f b) (arg :: b) :: f a
  type xs $< x = x >$ xs  -- just flipped version
  infixl 4 $<

data ContramapSym0 :: (b ~> a) ~> f a ~> f b
type instance Apply ContramapSym0 x = ContramapSym1 x

data ContramapSym1 :: (b ~> a) -> f a ~> f b
type instance Apply (ContramapSym1 x) y = Contramap x y


instance PContravariant Proxy where
  type Contramap _ 'Proxy = 'Proxy

instance PContravariant (Const z) where
  type Contramap _ ('Const e) = 'Const e


instance PContravariant (Compose (g :: Type -> Type) h) where
  type Contramap f ('Compose fg) = 'Compose (Contramap (ContramapSym1 f) fg)

-- more general than Contravariant cos also Functor
type family Phantom f where
  Phantom fa = ('() <$ fa) $< '()

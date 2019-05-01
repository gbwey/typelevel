{-# OPTIONS -Wall #-}
-- {-# OPTIONS -Wall -Wcompat -Wincomplete-record-updates -Wincomplete-uni-patterns #-}
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
-- {-# LANGUAGE KindSignatures #-} -- implied by TypeFamilies
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

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
  type Contramap f 'Proxy = 'Proxy

instance PContravariant (Const z) where
  type Contramap f ('Const e) = 'Const e


instance (PContravariant g, PContravariant h) => PContravariant (Compose g h) where
  type Contramap f ('Compose fg) = 'Compose (Contramap (ContramapSym1 f) fg)

-- more general than Contravariant cos also Functor
type family Phantom f where
  Phantom fa = ('() <$ fa) $< '()

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
module PDivisible where
import Data.Proxy
import Data.Kind (Type)
import Data.Functor.Const
import PCore
import PContravariant
import PMonoid
import PSemigroup

class PContravariant f => PDivisible (f :: Type -> Type) where
  type family Conquer :: f a
--  type Conquer = TypeError ('Text "PContravariant Conquer is undefined")

  type family Divide (abc :: a ~> (b, c)) (arg :: f b) (arg1 :: f c) :: f a
--  type Divide x y z = TypeError ('Text "PContravariant Divide is undefined x=" ':<>: 'ShowType x ':<>: 'Text " y=" ':<>: 'ShowType y ':<>: 'Text " z=" ':<>: 'ShowType z)

  type family Divided (arg :: f b) (arg1 :: f c) :: f (b,c)
  type Divided fb fc = Divide Id fb fc

instance PDivisible Proxy where
  type Conquer = 'Proxy
  type Divide _ 'Proxy 'Proxy = 'Proxy

instance PDivisible (Const z) where
  type Conquer = 'Const Mempty
  type Divide _ ('Const e) ('Const e1) = 'Const (e <> e1)


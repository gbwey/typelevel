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
module PFoldable1 where
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty(..))
import PCore
import PSemigroup
import PFoldable
import Data.Tagged ( Tagged(Tagged) )
import Data.Functor.Identity ( Identity(Identity) )
import Data.Functor.Compose ( Compose(Compose) )

-- how to enforce Semigroup?
class PFoldable t => PFoldable1 (t :: Type -> Type) where
  type family FoldMap1 (arg :: a ~> s) (arg1 :: t a) :: s
--  type FoldMap1 x y = TypeError ('Text "PFoldable1 FoldMap1 is undefined x=" ':<>: 'ShowType x ':<>: 'Text " y=" ':<>: 'ShowType y)

  type family Fold1 (arg :: t s) :: s
  type Fold1 xs = FoldMap1 Id xs
  type family ToNonEmpty (arg :: t a) :: NonEmpty a
  type ToNonEmpty xs = FoldMap1 Sing1Sym0 xs

data FoldMap1Sym0 :: (a ~> m) ~> t a ~> m
type instance Apply FoldMap1Sym0 x = FoldMap1Sym1 x

data FoldMap1Sym1 :: (a ~> m) -> t a ~> m
type instance Apply (FoldMap1Sym1 x) y = FoldMap1 x y


instance PFoldable1 ((,) z) where
  type FoldMap1 f '(_,a) = f @@ a

-- dont call FoldMap cos uses Mempty which is not defined for Foldable1 cos is semigroup
instance PFoldable1 NonEmpty where
  type FoldMap1 f (x ':| '[]) = f @@ x
  type FoldMap1 f (x ':| (y ': xs)) = f @@ x <> FoldMap1 f (y ':| xs)

instance PFoldable1 (Tagged a) where
  type FoldMap1 f ('Tagged a) = f @@ a

instance PFoldable1 Identity where
  type FoldMap1 f ('Identity a) = f @@ a

instance PFoldable1 (Compose (g :: Type -> Type) h) where
  type FoldMap1 f ('Compose gha) = FoldMap1 (FoldMap1Sym1 f) gha

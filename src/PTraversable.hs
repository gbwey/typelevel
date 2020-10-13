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
module PTraversable where
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty(..))
import Data.These ( These(..) )
import PCore
import PFoldable
import PFunctor
import PApplicative
import Data.Functor.Const ( Const(Const) )
import Data.Functor.Identity ( Identity(Identity) )
import Data.Functor.Compose ( Compose(Compose) )
import qualified Data.Semigroup as SG
import Data.Tagged ( Tagged(Tagged) )
import Data.Proxy ( Proxy(..) )
import Control.Applicative (ZipList(ZipList))

class (PFunctor t, PFoldable t) => PTraversable (t :: Type -> Type) where
  type family Traverse (afb :: a ~> f b) (xs :: t a) :: f (t b)
--  type Traverse x y = TypeError ('Text "PTraversable Traverse is undefined x=" ':<>: 'ShowType x ':<>: 'Text " y=" ':<>: 'ShowType y)

  type family Sequence (xs :: t (f a)) :: f (t a)
  type Sequence xs = Traverse Id xs

data TraverseSym0 :: (a ~> f b) ~> t a ~> f (t b)
type instance Apply TraverseSym0 x = TraverseSym1 x

data TraverseSym1 :: (a ~> f b) -> t a ~> f (t b)
type instance Apply (TraverseSym1 x) y = Traverse x y

instance PTraversable [] where
  type Traverse _ '[] = Pure '[]
  type Traverse afb (a ': as) = ConsSym0 <$> afb @@ a <*> Traverse afb as

instance PTraversable NonEmpty where
  type Traverse afb (a ':| as) = Cons1Sym0 <$> afb @@ a <*> Traverse afb as

instance PTraversable Maybe where
  type Traverse _ 'Nothing = Pure 'Nothing
  type Traverse afb ('Just a) = TyCon1Sym1 'Just <$> afb @@ a   -- how to lift 'Just to (a ~> Maybe a)

instance PTraversable (Either z) where
  type Traverse _ ('Left e) = Pure ('Left e)
  type Traverse afb ('Right a) = TyCon1Sym1 'Right <$> afb @@ a

instance PTraversable ((,) z) where
  type Traverse afb '(e, a) = TyCon1Sym1 ('(,) e) <$> afb @@ a

instance PTraversable Identity where
  type Traverse afb ('Identity a) = TyCon1Sym1 'Identity <$> afb @@ a

instance PTraversable (Const z) where
  type Traverse _ ('Const e) = Pure ('Const e)

instance PTraversable Proxy where
  type Traverse _ 'Proxy = Pure 'Proxy

instance PTraversable (Tagged z) where
  type Traverse afb ('Tagged a) = TyCon1Sym1 'Tagged <$> (afb @@ a)

instance PTraversable ZipList where
  type Traverse afb ('ZipList as) = TyCon1Sym1 'ZipList <$> Traverse afb as
data ComposeSym0 :: f (g a) ~> Compose f g a
type instance Apply ComposeSym0 x = 'Compose x

-- remember to partially apply ie not 'Compose <$> but instead ComposeSym0 <$>
instance PTraversable (Compose (g :: Type -> Type) h) where
  type Traverse f ('Compose fg) = ComposeSym0 <$> Traverse (TraverseSym1 f) fg

instance PTraversable (SG.Arg e) where
  type Traverse afb ('SG.Arg x a) = ArgSym1 x <$> afb @@ a

instance PTraversable (These e) where
  type Traverse _ ('This x) =  Pure ('This x)
  type Traverse afb ('That a) = ThatSym0 <$> afb @@ a
  type Traverse afb ('These x a) = TheseSym1 x <$> afb @@ a


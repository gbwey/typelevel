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
module PTraversableWithIndex where
import Data.List.NonEmpty (NonEmpty(..))
import PCore
import PFunctorWithIndex
import PFoldableWithIndex
import PTraversable
import Data.Proxy ( Proxy )
import Data.Tagged ( Tagged )
import Control.Applicative ( ZipList )
import Data.Functor.Identity ( Identity )
import Data.Functor.Compose ( Compose )

-- todo: how to enforce Applicative constraint for f in the Itraverse method
class (Traversable t, PFunctorWithIndex t, PFoldableWithIndex t) => PTraversableWithIndex t where
  type family Itraverse  (arg :: FWI (t a) ~> a ~> f b) (arg1 :: t a) :: f (t b)
  type Itraverse afb ta = Sequence (Imap afb ta)

-- cant do this!
--data ItraverseSym0 :: (FWI (t a) ~> a ~> f b) ~> t a ~> f (t b)
--type instance Apply ItraverseSym0 x = ItraverseSym1 x

data ItraverseSym1 :: (FWI (t a) ~> a ~> f b) -> t a ~> f (t b)
type instance Apply (ItraverseSym1 x) y = Itraverse x y

instance PTraversableWithIndex ((,) z) where
--  type Itraverse f '(e,a) = Traverse (UnCurrySym1 f) '(e, a)

instance PTraversableWithIndex [] where
--  type Itraverse f xs = UnCurrySym1 f <$> IToList' 0 xs

instance PTraversableWithIndex NonEmpty where
--  type Itraverse f (a ':| as) = (f @@ 0 @@ a) ':| (UnCurrySym1 f <$> IToList' 1 as)

instance PTraversableWithIndex Maybe where

instance PTraversableWithIndex Proxy where

instance PTraversableWithIndex (Tagged z) where

instance PTraversableWithIndex ZipList where

instance PTraversableWithIndex Identity where

-- doesnt compose cos 2 functions but only one index: we need i!
instance (PTraversableWithIndex g, PTraversableWithIndex h) => PTraversableWithIndex (Compose g h) where
--  type Itraverse f ('Compose fg) = 'Compose (Itraverse (Itraverse1Sym1 f) fg)

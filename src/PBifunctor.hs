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
module PBifunctor where
import Data.Proxy
import Data.Kind (Type)
import Data.Bifunctor
import Data.These
import PCore
import Data.Functor.Const
import Data.Tagged
import qualified Data.Semigroup as SG

class PBifunctor (bi :: k1 -> k2 -> Type) where
  type family Bimap (f :: a ~> b) (g :: c ~> d) (h :: bi a c) :: bi b d
--  type Bimap x y z = TypeError ('Text "PBifunctor Bimap is undefined x=" ':<>: 'ShowType x ':<>: 'Text " y=" ':<>: 'ShowType y ':<>: 'Text " z=" ':<>: 'ShowType z)

  type family Bifirst (f :: a ~> b) (h :: bi a x) :: bi b x
  type Bifirst f h = Bimap f Id h

  type family Bisecond (g :: c ~> d) (h :: bi x c) :: bi x d
  type Bisecond g h = Bimap Id g h

data BimapSym0 :: (a ~> b) ~> (c ~> d) ~> bi a c ~> bi b d
type instance Apply BimapSym0 x = BimapSym1 x

data BimapSym1 :: (a ~> b) -> (c ~> d) ~> bi a c ~> bi b d
type instance Apply (BimapSym1 x) y = BimapSym2 x y

data BimapSym2 :: (a ~> b) -> (c ~> d) -> bi a c ~> bi b d
type instance Apply (BimapSym2 x y) z = Bimap x y z


data BifirstSym0 :: (a ~> b) ~> bi a x ~> bi b x
type instance Apply BifirstSym0 x = BifirstSym1 x

data BifirstSym1 :: (a ~> b) -> bi a x ~> bi b x
type instance Apply (BifirstSym1 x) y = Bifirst x y


data BisecondSym0 :: (c ~> d) ~> bi x c ~> bi x d
type instance Apply BisecondSym0 x = BisecondSym1 x

data BisecondSym1 :: (c ~> d) -> bi x c ~> bi x d
type instance Apply (BisecondSym1 x) y = Bisecond x y

instance PBifunctor These where
  type Bimap f _ ('This a) = 'This (f @@ a)
  type Bimap _ g ('That b) = 'That (g @@ b)
  type Bimap f g ('These a b) = 'These (f @@ a) (g @@ b)

instance PBifunctor Either where
  type Bimap f _ ('Left a) = 'Left (f @@ a)
  type Bimap _ g ('Right b) = 'Right (g @@ b)

instance PBifunctor (,) where
  type Bimap f g '(a, b) = '(f @@ a, g @@ b)

instance PBifunctor Const where
  type Bimap f _ ('Const e) = 'Const (f @@ e)

instance PBifunctor Tagged where
  type Bimap _ g ('Tagged b) = 'Tagged (g @@ b)

data Proxy2 (a :: k) (b :: k1) = Proxy2 deriving Show
instance Bifunctor Proxy2 where
  bimap _ _ Proxy2 = Proxy2

proxy2 :: k a b -> Proxy2 a b
proxy2 _ = Proxy2

proxy2' :: k a -> Proxy2 a a
proxy2' _ = Proxy2

proxy2'' :: k a b -> Proxy a
proxy2'' _ = Proxy

instance PBifunctor SG.Arg where
  type Bimap f g ('SG.Arg e a) = 'SG.Arg (f @@ e) (g @@ a)


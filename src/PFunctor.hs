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
module PFunctor where
import Data.Proxy ( Proxy(..) )
import Data.Kind (Type)
import Data.Functor.Identity ( Identity(Identity) )
import Data.Functor.Const ( Const(Const) )
import qualified Data.Semigroup as SG
import Data.List.NonEmpty (NonEmpty(..))
import Data.Functor.Compose ( Compose(Compose) )
import Data.These ( These(..) ) -- add a functor instance and semigroup etc
import Data.Ord ( Down(Down) )
import PCore
import Data.Tagged ( Tagged(Tagged) )
import Control.Applicative ( ZipList(ZipList) )
import Data.Functor.Product ( Product(..) )
import Data.Void ( Void )

class PFunctor (f :: Type -> Type) where
  type family Fmap (arg :: a ~> b) (arg1 :: f a) :: f b
--  type Fmap x y = TypeError ('Text "PFunctor Fmap is undefined x=" ':<>: 'ShowType x ':<>: 'Text " y=" ':<>: 'ShowType y)

  type family (<$) (arg :: a) (arg1 :: f b) :: f a
  type x <$ xs = Fmap (KSym1 x) xs
  infixl 4 <$

  type family (<$>) (arg :: a ~> b) (arg1 :: f a) :: f b
  type x <$> xs = Fmap x xs
  infixl 4 <$>

  type family Vacuous (arg :: f Void) :: f a
  type Vacuous fv = AbsurdSym0 <$> fv



instance PFunctor [] where
  type Fmap _ '[] = '[]
  type Fmap f (x ': xs) = f @@ x ': Fmap f xs

-- leverage the fact that you know how to Fmap xs ie calls the above
instance PFunctor NonEmpty where
  type Fmap f (x ':| xs) = f @@ x ':| Fmap f xs

instance PFunctor Maybe where
  type Fmap _ 'Nothing = 'Nothing
  type Fmap f ('Just x) = 'Just (f @@ x)

instance PFunctor (Either e) where
  type Fmap _ ('Left x) = 'Left x
  type Fmap f ('Right x) = 'Right (f @@ x)

instance PFunctor ((,) z)  where
  type Fmap f '(e, a) = '(e, f @@ a)

instance PFunctor Proxy where
  type Fmap _ 'Proxy = 'Proxy

instance PFunctor (Tagged z) where
  type Fmap f ('Tagged a) = 'Tagged (f @@ a)

instance PFunctor (Const z) where
  type Fmap _ ('Const e) = 'Const e

instance PFunctor Identity where
  type Fmap f ('Identity a) = 'Identity (f @@ a)

-- careful with the variable names: f has to be different from g and h! cos foralled
-- FmapSym0 :.: FmapSym0 [this is cool but I like the other one cos dont have to @@ [could create a Fmap2Sym0 etc
instance PFunctor (Compose (g :: Type -> Type) h) where
  type Fmap f ('Compose fg) = 'Compose (Fmap (FmapSym1 f) fg) -- this was tricky but works
--  type Fmap f ('Compose fg) = 'Compose ((FmapSym0 :.: FmapSym0) @@ f @@ fg) -- this works as well


data FmapSym0 :: (a ~> b) ~> f a ~> f b
type instance Apply FmapSym0 x = FmapSym1 x

data FmapSym1 :: (a ~> b) -> f a ~> f b
type instance Apply (FmapSym1 x) y = Fmap x y



instance PFunctor SG.Sum where
  type Fmap f ('SG.Sum a) = 'SG.Sum (f @@ a)
instance PFunctor SG.Product where
  type Fmap f ('SG.Product a) = 'SG.Product (f @@ a)
instance PFunctor SG.Min where
  type Fmap f ('SG.Min a) = 'SG.Min (f @@ a)
instance PFunctor SG.Max where
  type Fmap f ('SG.Max a) = 'SG.Max (f @@ a)
instance PFunctor SG.First where
  type Fmap f ('SG.First a) = 'SG.First (f @@ a)
instance PFunctor SG.Last where
  type Fmap f ('SG.Last a) = 'SG.Last (f @@ a)

-- make sure that 'x' is different from 'a' and 'b'
instance PFunctor (These x) where
  type Fmap _ ('This a) = 'This a
  type Fmap f ('That b) = 'That (f @@ b)
  type Fmap f ('These a b) = 'These a (f @@ b)

{- when you use These a and then This a ie you mention the variable in the type! hence These x!
D:\haskell\typelevel\src\PFunctor.hs:114:16-22: error:
    * Expected kind `These a a0', but ` 'This a' has kind `These * a0'
    * In the second argument of `Fmap', namely `( 'This a)'
      In the type instance declaration for `Fmap'
      In the instance declaration for `PFunctor (These a)'
    |
114 |   type Fmap f ('This a) = 'This a
    |                ^^^^^^^
-}

instance PFunctor (SG.Arg e) where
  type Fmap f ('SG.Arg x y) = 'SG.Arg x (f @@ y)

instance PFunctor SG.Option where
  type Fmap f ('SG.Option x) = 'SG.Option (Fmap f x)

instance PFunctor Down where
  type Fmap f ('Down a) = 'Down (f @@ a)

instance PFunctor SG.Dual where
  type Fmap f ('SG.Dual a) = 'SG.Dual (f @@ a)

instance PFunctor ZipList where
  type Fmap f ('ZipList as) = 'ZipList (f <$> as)

instance PFunctor (Product g h) where
  type Fmap f ('Pair x y) = 'Pair (f <$> x) (f <$> y)

{-
--instance PFunctor ((~>) e) where

data ZZZSym0 :: (e -> a) ~> e ~> a
type instance Apply ZZZSym0 ea = ZZZSym1 ea

data ZZZSym1 :: (e -> a) -> e ~> a
type instance Apply (ZZZSym1 ea) e = ea e

data RZZZSym0 :: (e ~> a) ~> (e -> a)
type instance Apply RZZZSym0 ea = Undefined



instance PFunctor ((->) e) where
  type Fmap f ea = f :.: ZZZSym1 ea
--  type Fmap f ea = Undefined -- f :: (a ~> b)    ea :: (e -> a)
--instance PFunctor (YYYSym0 e) where

data YYYSym0 :: e ~> a
type instance Apply YYYSym0 e = Undefined
-}
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
module PMonad where
import Data.Kind (Type)
import Data.Functor.Identity ( Identity(Identity) )
import PCore
import PSemigroup
import PMonoid
import PApplicative
import PFunctor
import Data.These ( These(..) )
import Data.Ord ( Down(Down) )
import qualified Data.Semigroup as SG
import Data.Proxy ( Proxy(..) )
import Data.Tagged ( Tagged(Tagged) )
import Control.Applicative ( ZipList(ZipList) )

class PApplicative m => PMonad (m :: Type -> Type) where
  type family Return (arg :: a) :: m a
  type Return a = Pure a

  type family (>>=) (arg :: m a) (arg1 :: a ~> m b) :: m b
--  type x >>= y = TypeError ('Text "PMonad (>>=) is undefined x=" ':<>: 'ShowType x ':<>: 'Text " y=" ':<>: 'ShowType y)
  infixl 1 >>=

  type family (=<<) (arg1 :: a ~> m b) (arg :: m a) :: m b
  type amb =<< ma = ma >>= amb
  infixl 1 =<<

  type family Join (arg :: m (m a)) :: m a
  type Join mma = mma >>= Id

-- serious pain until i used pointfree.io to figure it out: exact xlation from (`fmap` mab) . flip id =<< ma
  type family Ap (f :: m (a ~> b)) (g :: m a) :: m b
-- wrong order: flipped around
--  type Ap mab ma = (FlipSym2 FmapSym0 mab :.: FlipSym1 Id) =<< ma
  type Ap mab ma = mab >>= (FlipSym2 FmapSym0 ma :.: Id)

  type family ApPair (f :: m a) (g :: m b) :: m (a,b)
  type ApPair ma mb = ma >>= (FlipSym2 FmapSym0 mb :.: PairSym0)


--data Ap1Sym0 :: m a ~> m b ~> m (a, b)
--type instance Apply Ap1Sym0 x = Ap1Sym1 x

--data Ap1Sym1 :: m a -> m b ~> m (a, b)
--type instance Apply (Ap1Sym1 ma) mb = ma >>= \a -> fmap (a,) mb



instance PMonad (These e) where
  type 'This x >>= _ = 'This x
  type 'That a >>= amb = amb @@ a
  type 'These x a >>= amb = 'This x <> amb @@ a

instance PMonad Identity where
  type 'Identity a >>= amb = amb @@ a

instance PMonad Proxy where
  type 'Proxy >>= _ = 'Proxy

instance PMonad (Tagged z) where
  type 'Tagged a >>= amb = amb @@ a

-- parens are important
instance PMonad [] where
  type '[] >>= _ = '[]
  type (a ': as) >>= amb = (amb @@ a) <> (as >>= amb)

instance PMonad ZipList where
  type 'ZipList '[] >>= _ = 'ZipList '[]
  type 'ZipList (a ': as) >>= amb = (amb @@ a) <> ('ZipList as >>= amb)

instance PMonad Maybe where
  type 'Nothing >>= _ = 'Nothing
  type 'Just a >>= amb = amb @@ a

instance PMonad (Either e) where
  type 'Left x >>= _ = 'Left x
  type 'Right a >>= amb = amb @@ a

instance PMonad ((,) e) where
  type Return a = '(Mempty, a)
  type '(x,a) >>= amb = First (SAppSym1 x) (amb @@ a)

instance PMonad Down where
  type 'Down a >>= amb = amb @@ a


--ap1 :: Monad m => m (a -> b) -> m a -> m b
--ap1 mab ma = join $ fmap (\a -> mab >>= \ab -> return (ab a)) ma

{- pointfree.io rox
(`fmap` mab) . flip id =<< ma

>:kind! Ap ('Just (PairSym1 "xx")) ('Just 444)
Ap ('Just (PairSym1 "xx")) ('Just 444) :: Maybe (Symbol, Nat)
= 'Just '("xx", 444)
-}
instance PMonad SG.Dual where
  type 'SG.Dual a >>= amb = amb @@ a

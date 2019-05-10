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

module PFunctorWithIndex where
import Data.List.NonEmpty (NonEmpty(..))
import PCore
import PFunctor
import Data.Functor.Identity
import Data.Functor.Compose
import Data.Proxy
import Data.Tagged
import Control.Applicative

class PFunctor t => PFunctorWithIndex t where
  type family Imap (arg :: FWI (t a) ~> a ~> b) (arg1 :: t a) :: t b

data ImapSym1 :: (FWI (t a) ~> a ~> b) -> t a ~> t b
type instance Apply (ImapSym1 x) y = Imap x y

instance PFunctorWithIndex ((,) z) where
  type Imap f '(e,a) = '(e, f @@ e @@ a)

instance PFunctorWithIndex [] where
  type Imap f xs = UnCurrySym1 f <$> IToList' 0 xs

instance PFunctorWithIndex NonEmpty where
  type Imap f (a ':| as) = (f @@ 0 @@ a) ':| (UnCurrySym1 f <$> IToList' 1 as)

instance PFunctorWithIndex Maybe where
  type Imap f x = (f @@ '()) <$> x

instance PFunctorWithIndex Proxy where
  type Imap f 'Proxy = 'Proxy

instance PFunctorWithIndex (Tagged s) where
  type Imap f ('Tagged a) = 'Tagged (f @@ '() @@ a)

instance PFunctorWithIndex ZipList where
  type Imap f ('ZipList as) = 'ZipList (Imap f as)

instance PFunctorWithIndex Identity where
  type Imap f ('Identity a) = 'Identity (f @@ '() @@ a)

-- doesnt compose cos 2 functions but only one index: we need i!
instance (PFunctorWithIndex g, PFunctorWithIndex h) => PFunctorWithIndex (Compose g h) where
--  type Imap f ('Compose fg) = 'Compose (Imap (ImapSym0 :.: (f :..: PairSym0)) fg)
  type Imap f ('Compose fg) = 'Compose (Imap (Imap1Sym1 f) fg)


type family Imap1 f i xs where
  Imap1 f i xs = Imap (f :.: PairSym1 i) xs

data Imap1Sym1 :: ((a1,FWI (t a2)) ~> (a2 ~> b)) -> a1 ~> t a2 ~> t b
type instance Apply (Imap1Sym1 x) y = Imap1Sym2 x y

data Imap1Sym2 :: ((a1,FWI (t a2)) ~> (a2 ~> b)) -> a1 -> t a2 ~> t b
type instance Apply (Imap1Sym2 x y) z = Imap1 x y z

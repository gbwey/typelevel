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
module PCombinators
  (
    module PAlign
  , module PAlternative
  , module PApplicative
  , module PBifunctor
  , module PBounded
  , module PChar
  , module PCombinators
  , module PComparison
  , module PContravariant
  , module PCore
  , module PDivisible
  , module PEnum
  , module PEq
  , module PEquivalence
  , module PFoldable
  , module PFoldable1
  , module PFoldableWithIndex
  , module PFunctor
  , module PFunctorWithIndex
  , module PLens
  , module PList
  , module PMap
  , module PMonad
  , module PMonoid
  , module PNum
  , module PN
  , module POrd
  , module PParser
  , module PPredicate
  , module PProfunctor
  , module PR
  , module PSemigroup
  , module PState
  , module PStateLR
  , module PTraversable
  , module PTraversableWithIndex
  ) where

import GHC.TypeNats (type (-))
import GHC.TypeLits (type (<=?))
import PAlign
import PAlternative
import PApplicative
import PBifunctor
import PBounded
import PChar
import PComparison
import PContravariant
import PCore
import PDivisible
import PEnum
import PEq
import PEquivalence
import PFoldable
import PFoldable1
import PFoldableWithIndex
import PFunctor
import PFunctorWithIndex
import PLens
import PList
import PMap
import PMonad
import PMonoid
import PN
import PNum
import POrd
import PParser
import PPredicate
import PProfunctor
import PR
import PSemigroup
import PState
import PStateLR
import PTraversable
import PTraversableWithIndex

type XS = '["ss","b","c"]

type family Test1 n where
  Test1 n = If (n <=? Length XS) (Take n XS) (XS <> Iterate (n  - Length XS) (FlipSym2 SAppSym0 "0") "x")

-- strict evaluation so this does not return! need to specify how much
--type family IterateForever f s where
--  IterateForever f a = a ': IterateForever f (f @@ a)



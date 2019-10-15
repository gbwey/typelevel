{-# OPTIONS -Wall #-}
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
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ConstraintKinds #-}

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

import GHC.TypeNats
import GHC.TypeLits hiding (natVal,natVal',SomeNat(..),someNatVal)
import GHC.Natural
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
import Data.Proxy
import Data.Tagged
import qualified Data.Symbol.Ascii as S

type XS = '["ss","b","c"]

type family Test1 n where
  Test1 n = If (n <=? Length XS) (Take n XS) (XS <> Iterate (n  - Length XS) (FlipSym2 SAppSym0 "0") "x")

-- strict evaluation so this does not return! need to specify how much
--type family IterateForever f s where
--  IterateForever f a = a ': IterateForever f (f @@ a)


taa :: forall (s :: Symbol) b . KnownSymbol s => Tagged s b -> String
taa (Tagged _) = symbolVal (Proxy @s)
{-
>case someSymbolVal "abd" of SomeSymbol p -> taaa (tagWith p True)
"abd"
it :: String

>taaa (Tagged @"abd" ())
"abd"
it :: String
-}

taa1 :: forall (s :: Symbol) (i :: Nat)
  . (
     -- (0 <=? Length (S.ToList s)) ~ 'True
      Length (S.ToList s) ~ i
    , KnownSymbol s
    , KnownNat (Length (S.ToList s))
    , KnownNat i
    )
   => Proxy s -> (String, Natural)
taa1 p = (symbolVal p, natVal (Proxy @(Length (S.ToList s))))

taa2 :: forall (s :: Symbol) (s1 :: Symbol) p
   . (
      Mconcat (Reverse (S.ToList s)) ~ s1
    , KnownSymbol s
--    , KnownSymbol s1
--    , KnownSymbol (Mconcat (Reverse (S.ToList s)))
   )
   => p s -> (String, String)
taa2 _ = (symbolVal (Proxy @s), "") -- symbolVal (Proxy @s1))

-- we can lift Nats (using someNatVal) and Symbols (using someSymbolVal)
-- but they are useless cos we cannot do anything with them
-- 'n' is not statically known so we cant do anything with it except grab the value as is
-- using SomeNat is runtime and ghc has already done its stuff so this is Stuck
-- we can pull the raw value down of course using natVal (symbolVal) but we cannot
-- derive any stuff at the type level
-- that means that stuff like Length / Replicate are not going to do anything cos
--   'n' is stuck
taa3 :: forall (n :: Nat)
  . (
     (n <=? 3) ~ 'True
     ,KnownNat n
    )
   => Proxy n -> Natural
taa3 = natVal

{-
>taa3 (Proxy @3)
3
it :: GHC.Natural.Natural
>taa3 (Proxy @4)

<interactive>:12:1: error:
    * Couldn't match type 'False with 'True
        arising from a use of `taa3'
    * In the expression: taa3 (Proxy @4)
      In an equation for `it': it = taa3 (Proxy @4)

-- ghc cannot calculate 'n' so cannot do anything with the constraint

>case someNatVal 3 of SomeNat p -> taa3 p
<interactive>:13:35: error:
    * Couldn't match type `n <=? 3' with 'True
        arising from a use of `taa3'
    * In the expression: taa3 p
      In a case alternative: SomeNat p -> taa3 p
      In the expression: case someNatVal 3 of { SomeNat p -> taa3 p }
    * Relevant bindings include
        p :: Proxy n (bound at <interactive>:13:30)
-}



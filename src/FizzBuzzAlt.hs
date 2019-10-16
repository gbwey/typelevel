{-# OPTIONS -Wall -Wcompat -Wincomplete-record-updates -Wincomplete-uni-patterns -Wredundant-constraints #-}
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
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}

module FizzBuzzAlt where
import GHC.TypeNats
import GHC.TypeLits hiding (natVal, natVal')
import PCore
import Data.Type.Equality
import PChar
import PMonoid
import PSemigroup
import PFunctor
import Data.These

data Fizz = Fizz
data Buzz = Buzz

instance PSemigroup Fizz where
  type 'Fizz <> 'Fizz = 'Fizz
  type SUnWrap 'Fizz = '()

instance PMonoid Fizz where
  type Mempty = 'Fizz

instance PSemigroup Buzz where
  type 'Buzz <> 'Buzz = 'Buzz
  type SUnWrap 'Buzz = '()

instance PMonoid Buzz where
  type Mempty = 'Buzz

type family FizzT (n :: Nat) :: Maybe Fizz where
  FizzT n = If (n `Mod` 3 == 0) ('Just 'Fizz) 'Nothing

type family BuzzT (n :: Nat) :: Maybe Buzz where
  BuzzT n = If (n `Mod` 5 == 0) ('Just 'Buzz) 'Nothing

type family Zap (n :: Nat) :: Maybe (These Fizz Buzz) where
  Zap n = (TyCon1Sym1 'This <$> FizzT n) <> (TyCon1Sym1 'That <$> BuzzT n)

type family UnZap (n :: Nat) :: Symbol where
  UnZap n = Maybe' (NatToString n)
                   (These'Sym3 (KSym1 "fizz") (KSym1 "buzz") (KSym1 (KSym1 "fizz")))
                   (Zap n)


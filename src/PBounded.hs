{-# OPTIONS -Wall -Wcompat -Wincomplete-record-updates -Wincomplete-uni-patterns -Wno-redundant-constraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}

module PBounded where
import Data.Proxy
import Data.Tagged
import Data.Functor.Identity
import Data.Functor.Const
import qualified Data.Semigroup as SG

class PBounded a where
  type family MinBound :: a
  type family MaxBound :: a

instance PBounded Bool where
  type MinBound = 'False
  type MaxBound = 'True

instance PBounded Ordering where
  type MinBound = 'LT
  type MaxBound = 'GT

instance (PBounded a, PBounded b) => PBounded (a, b) where
  type MinBound = '(MinBound, MinBound)
  type MaxBound = '(MaxBound, MaxBound)

instance (PBounded a, PBounded b, PBounded c) => PBounded (a, b, c) where
  type MinBound = '(MinBound, MinBound, MinBound)
  type MaxBound = '(MaxBound, MaxBound, MaxBound)

instance PBounded () where
  type MinBound = '()
  type MaxBound = '()

instance PBounded (Proxy a) where
  type MinBound = 'Proxy
  type MaxBound = 'Proxy

instance PBounded a => PBounded (Tagged s a) where
  type MinBound = 'Tagged MinBound
  type MaxBound = 'Tagged MaxBound

instance PBounded a => PBounded (Const a b) where
  type MinBound = 'Const MinBound
  type MaxBound = 'Const MaxBound

instance PBounded a => PBounded (Identity a) where
  type MinBound = 'Identity MinBound
  type MaxBound = 'Identity MaxBound

instance PBounded a => PBounded (SG.Dual a) where
  type MinBound = 'SG.Dual MinBound
  type MaxBound = 'SG.Dual MaxBound

instance PBounded a => PBounded (SG.Sum a) where
  type MinBound = 'SG.Sum MinBound
  type MaxBound = 'SG.Sum MaxBound

instance PBounded a => PBounded (SG.Product a) where
  type MinBound = 'SG.Product MinBound
  type MaxBound = 'SG.Product MaxBound

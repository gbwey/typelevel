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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NoStarIsType #-}
module PBounded where
import Data.Proxy ( Proxy(..) )
import Data.Tagged ( Tagged(Tagged) )
import Data.Functor.Identity ( Identity(Identity) )
import Data.Functor.Const ( Const(Const) )
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

instance PBounded (a, b) where
  type MinBound = '(MinBound, MinBound)
  type MaxBound = '(MaxBound, MaxBound)

instance PBounded (a, b, c) where
  type MinBound = '(MinBound, MinBound, MinBound)
  type MaxBound = '(MaxBound, MaxBound, MaxBound)

instance PBounded () where
  type MinBound = '()
  type MaxBound = '()

instance PBounded (Proxy a) where
  type MinBound = 'Proxy
  type MaxBound = 'Proxy

instance PBounded (Tagged s a) where
  type MinBound = 'Tagged MinBound
  type MaxBound = 'Tagged MaxBound

instance PBounded (Const a b) where
  type MinBound = 'Const MinBound
  type MaxBound = 'Const MaxBound

instance PBounded (Identity a) where
  type MinBound = 'Identity MinBound
  type MaxBound = 'Identity MaxBound

instance PBounded (SG.Dual a) where
  type MinBound = 'SG.Dual MinBound
  type MaxBound = 'SG.Dual MaxBound

instance PBounded (SG.Sum a) where
  type MinBound = 'SG.Sum MinBound
  type MaxBound = 'SG.Sum MaxBound

instance PBounded (SG.Product a) where
  type MinBound = 'SG.Product MinBound
  type MaxBound = 'SG.Product MaxBound

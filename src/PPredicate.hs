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

module PPredicate where
import PCore
import PContravariant
import PMonoid
import PSemigroup
import PDivisible
import Data.Kind (Type)

newtype PredicateX a = PredicateX { getPredicateX :: a ~> Bool }

type family UnPredicateX f where
  UnPredicateX ('PredicateX p) = p

instance PContravariant PredicateX where
  type Contramap f ('PredicateX p) = 'PredicateX (p :.: f)

instance PDivisible PredicateX where
  type Divide abc ('PredicateX p) ('PredicateX p1) = 'PredicateX (UnCurrySym1 AndSym0 :.: StarSym2 p p1 :.: abc)
  type Conquer = 'PredicateX (KSym1 'True)

instance PSemigroup (PredicateX (a :: Type)) where
  type p <> p1 = Divide DupSym0 p p1
  type SUnWrap ('PredicateX p) = p

instance PMonoid (PredicateX (a :: Type)) where
  type Mempty = Conquer -- 'PredicateX (KSym1 'True)


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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ConstraintKinds #-}

module PR where
import PCore
import PMonoid
import PSemigroup
import PFunctor
import PApplicative
import PMonad
import PFunctorWithIndex
import Data.Kind (Type)

newtype R e a = R { unR :: e ~> a }

-- needed for functorwithindex
type instance FWI (R e a) = e

-- need a applyable function to unwrap R
data UnRSym0 :: R e a ~> e ~> a
type instance Apply UnRSym0 rea = UnRSym1 rea

data UnRSym1 :: R e a -> e ~> a
type instance Apply (UnRSym1 rea) e = UnRSym2 rea e

type family UnRSym2 (x :: R e a) (arg1 :: e) where
  UnRSym2 ('R ea) e = ea @@ e

type family UnR (x :: R e a) where
  UnR ('R ea) = ea

-- instead of TyCon1Sym1 'R
data RSym0 :: (e ~> a) ~> R e a
type instance Apply RSym0 ea = 'R ea

data RBindSym0 :: (e ~> a) ~> (a ~> e ~> b) ~> e ~> b
type instance Apply RBindSym0 ea = RBindSym1 ea

data RBindSym1 :: (e ~> a) -> (a ~> e ~> b) ~> e ~> b
type instance Apply (RBindSym1 ea) aeb = RBindSym2 ea aeb

data RBindSym2 :: (e ~> a) -> (a ~> e ~> b) -> e ~> b
type instance Apply (RBindSym2 ea aeb) e = RBind ea aeb e

type family RBind ea aea e where RBind ea aea e = aea @@ (ea @@ e) @@ e


instance PApplicative (R e) where
  type Pure a = 'R $$ KSym1 a
  type 'R eab <*> 'R ea = 'R $$ SSym2 eab ea

instance PFunctor (R e) where
  type Fmap f ('R ea) = 'R $$ f :.: ea

instance PMonad (R e) where
  type 'R ea >>= amb = 'R (RBindSym2 ea (UnR (Fmap UnRSym0 ('R amb))))

instance PMonoid a => PMonoid (R e a) where
  type Mempty = 'R Mempty

instance PSemigroup a => PSemigroup (R e a) where
  type 'R ea <> 'R ea1 = 'R (ea <> ea1)
  type SUnWrap ('R ea) = ea


instance PFunctorWithIndex (R (e :: Type)) where
  type Imap f ('R ea) = 'R (UnCurrySym1 f :.: AmpSym2 (ToFWIR :.: AmpSym2 Id ea)  ea)

-- coercion worked from (e,a) to FWI (R e a)
data ToFWIR :: (e,a) ~> FWI (R e a)
type instance Apply ToFWIR '(e,a) = e




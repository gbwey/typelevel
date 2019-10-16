{-# OPTIONS -Wall -Wcompat -Wincomplete-record-updates -Wincomplete-uni-patterns -Wno-redundant-constraints #-}
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

module PState where
import PCore
import PMonoid
import PSemigroup
import PFunctor
import PApplicative
import PMonad
import PR

newtype STA s a = STA { unSTA :: s ~> (a, s) }
-- have to wrap and unwrap in R as we dont have Functor for ~> but do for R which wraps ~>
instance PFunctor (STA s) where
  type Fmap f ('STA sas) = 'STA (UnR (Fmap (FirstSym1 f) ('R sas)))
--  type Fmap f ('STA sas) = 'STA $$ UnRSym0 $ Fmap (FirstSym1 f) ('R sas)

-- magic tuples
instance PApplicative (STA s) where
  type Pure a = 'STA (TyCon1Sym1 ('(,) a))
  type 'STA sab <*> 'STA sa =
    'STA (AmpSym2
               (UnCurrySym1 Id :.: AmpSym2 FstSym0 (FstSym0 :.: SndSym0))
               (SndSym0 :.: SndSym0)
          :.: (SecondSym1 sa :.: sab)
         )

instance PMonad (STA s) where
  type 'STA sas >>= amb = 'STA (UnCurrySym1 Id :.: FirstSym1 (UnSTASym0 :.: amb) :.: sas)

instance PSemigroup a => PSemigroup (STA s a) where
  type sa <> sa1 = SAppSym0 <$> sa <*> sa1
  type SUnWrap ('STA x) = x

instance PMonoid a => PMonoid (STA s a) where
  type Mempty = Pure Mempty

type family Get :: STA s s where
  Get = 'STA DupSym0

type family Put (x :: s) :: STA s () where
  Put s = 'STA (PairSym1 '() :.: KSym1 s)

data PutSym0 :: s ~> STA s ()
type instance Apply PutSym0 x = Put x


type family Modify (f :: s ~> s) :: STA s () where
  Modify f = 'STA (PairSym1 '() :.: AppSym1 f)

data ModifySym0 :: (s ~> s) ~> STA s ()
type instance Apply ModifySym0 x = Modify x

data UnSTASym0 :: STA s a ~> (s ~> (a, s))
type instance Apply UnSTASym0 rea = UnSTASym1 rea

data UnSTASym1 :: STA s a -> (s ~> (a, s))
type instance Apply (UnSTASym1 rea) s = UnSTASym2 rea s

type family UnSTASym2 (x :: STA s a) (arg1 :: s) where
  UnSTASym2 ('STA sas) s = sas @@ s

type family UnSTA (x :: STA s a) where
  UnSTA ('STA sas) = sas

-- instead of TyCon1Sym1 'STA
data STASym0 :: (s ~> (a, s)) ~> STA s a
type instance Apply STASym0 sas = 'STA sas


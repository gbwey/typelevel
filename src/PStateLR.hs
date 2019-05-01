-- using STLRAppSym2 is an easier way to define applicative instead of using tuples
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

module PStateLR where
import PCore
import PBifunctor
import PMonoid
import PSemigroup
import PFunctor
import PApplicative
import PAlternative
import PMonad
import PR

newtype STLR e s a = STLR { unSTLR :: s ~> Either e (a, s) }
-- have to wrap and unwrap in R as we dont have Functor for ~> but do for R which wraps ~>
instance PMonoid e => PFunctor (STLR e s) where
  type Fmap f ('STLR sas) = 'STLR (UnR (Fmap (BisecondSym1 (FirstSym1 f)) ('R sas)))
--  type Fmap f ('STLR sas) = 'STLR $$ UnRSym0 $ Fmap (FirstSym1 f) ('R sas)

instance PMonoid e => PApplicative (STLR e s) where
  type Pure a = 'STLR (TyCon1Sym1 'Right :.: TyCon1Sym1 ('(,) a))
  type 'STLR sab <*> 'STLR sa =
    'STLR (STLRAppSym2 sab sa)

data STLRAppSym0 :: (s ~> Either e (a ~> b,s)) ~> (s ~> Either e (a,s)) ~> s ~> Either e (b,s)
type instance Apply STLRAppSym0 x = STLRAppSym1 x

data STLRAppSym1 :: (s ~> Either e (a ~> b,s)) -> (s ~> Either e (a,s)) ~> s ~> Either e (b,s)
type instance Apply (STLRAppSym1 x) y = STLRAppSym2 x y

data STLRAppSym2 :: (s ~> Either e (a ~> b,s)) -> (s ~> Either e (a,s)) -> s ~> Either e (b,s)
type instance Apply (STLRAppSym2 sab sa) s = STLRApp (sab @@ s) sa


type family STLRApp (lrab :: Either e (a ~> b,s)) (sa :: s ~> Either e (a,s)) :: Either e (b,s) where
  STLRApp ('Left e) sa = 'Left e
  STLRApp ('Right '(ab,s)) sa = Bisecond (FirstSym1 ab) (sa @@ s)

instance PMonoid e => PMonad (STLR e s) where
  type 'STLR sa >>= amb = 'STLR (STLRBindSym2 sa amb)

data STLRBindSym0 :: (s ~> Either e (a,s)) ~> (a ~> STLR e s b) ~> s ~> Either e (b,s)
type instance Apply STLRBindSym0 x = STLRBindSym1 x

data STLRBindSym1 :: (s ~> Either e (a,s)) -> (a ~> STLR e s b) ~> s ~> Either e (b,s)
type instance Apply (STLRBindSym1 x) y = STLRBindSym2 x y

data STLRBindSym2 :: (s ~> Either e (a,s)) -> (a ~> STLR e s b) -> s ~> Either e (b,s)
type instance Apply (STLRBindSym2 sa amb) s = STLRBind (sa @@ s) amb


type family STLRBind (lra :: Either e (a,s)) (amb :: a ~> STLR e s b) :: Either e (b,s) where
  STLRBind ('Left e) amb = 'Left e
  STLRBind ('Right '(a,s)) amb = (UnSTLR (amb @@ a)) @@ s

instance PSemigroup a => PSemigroup (STLR e s a) where
  type sa <> sa1 = SAppSym0 <$> sa <*> sa1
  type SUnWrap ('STLR x) = x

instance PMonoid a => PMonoid (STLR e s a) where
  type Mempty = Pure Mempty

type family GetP :: STLR e s s where
  GetP = 'STLR (TyCon1Sym1 'Right :.: DupSym0)

type family PutP (x :: s) :: STLR e s () where
  PutP s = 'STLR (TyCon1Sym1 'Right :.: PairSym1 '() :.: KSym1 s)

data PutPSym0 :: s ~> STLR e s ()
type instance Apply PutPSym0 x = PutP x


type family ModifyP (f :: s ~> s) :: STLR e s () where
  ModifyP f = 'STLR (TyCon1Sym1 'Right :.: PairSym1 '() :.: AppSym1 f)

data ModifyPSym0 :: (s ~> s) ~> STLR e s ()
type instance Apply ModifyPSym0 x = ModifyP x

data UnSTLRSym0 :: STLR e s a ~> (s ~> Either e (a, s))
type instance Apply UnSTLRSym0 rea = UnSTLRSym1 rea

data UnSTLRSym1 :: STLR e s a -> (s ~> Either e (a, s))
type instance Apply (UnSTLRSym1 rea) s = UnSTLRSym2 rea s

type family UnSTLRSym2 (x :: STLR e s a) (arg1 :: s) where
  UnSTLRSym2 ('STLR sas) s = sas @@ s

type family UnSTLR (x :: STLR e s a) where
  UnSTLR ('STLR sas) = sas

-- instead of TyCon1Sym1 'STLR
data STLRSym0 :: (s ~> Either e (a, s)) ~> STLR e s a
type instance Apply STLRSym0 sas = 'STLR sas


instance PMonoid e => PAlternative (STLR e s) where
  type Empty = 'STLR (KSym1 ('Left Mempty))
  type 'STLR p1 <|> 'STLR p2 = 'STLR (STLRAltSym2 p1 p2)

data STLRAltSym0 :: (s ~> Either e (a,s)) ~> (s ~> Either e (a,s)) ~> s ~> Either e (a,s)
type instance Apply STLRAltSym0 x = STLRAltSym1 x

data STLRAltSym1 :: (s ~> Either e (a,s)) -> (s ~> Either e (a,s)) ~> s ~> Either e (a,s)
type instance Apply (STLRAltSym1 x) y = STLRAltSym2 x y

data STLRAltSym2 :: (s ~> Either e (a,s)) -> (s ~> Either e (a,s)) -> s ~> Either e (a,s)
type instance Apply (STLRAltSym2 sa1 sa2) s = STLRAlt (sa1 @@ s) (sa2 @@ s)

type family STLRAlt lr1 lr2 where
  STLRAlt ('Right x) y = 'Right x
  STLRAlt x ('Right y) = 'Right y
  STLRAlt ('Left x) ('Left y) = 'Left (x <> y)

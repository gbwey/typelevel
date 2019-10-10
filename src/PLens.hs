{-# OPTIONS -Wall #-}
{-# OPTIONS -fprint-explicit-kinds #-}
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
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
module PLens where
import GHC.TypeNats
import GHC.TypeLits hiding (natVal,natVal')
import PCore
import PFunctor
import PMonoid
import PApplicative
import PTraversable
import Data.Functor.Identity
import Data.Functor.Const
import qualified Data.Semigroup as SG
import qualified Data.Monoid as MM
import qualified Data.Symbol.Ascii as S
import Data.List.NonEmpty (NonEmpty(..))

type PLensLike f s t a b = (a ~> f b) ~> s ~> f t
type PLensLike' f s a = (a ~> f a) ~> s ~> f s

type family Preview (l :: PLensLike' (Const (MM.First a)) s a) (arg1 :: s) where
  Preview l s = UnFirstM (UnConst (l @@ (TyCon1Sym1 'Const :.: TyCon1Sym1 'MM.First :.: TyCon1Sym1 'Just) @@ s))

data PreviewSym0 :: ((a ~> Const (MM.First a) a) ~> s ~> Const (MM.First a) s) ~> s ~> Maybe a
type instance Apply PreviewSym0 x = PreviewSym1 x

data PreviewSym1 :: ((a ~> Const (MM.First a) a) ~> s ~> Const (MM.First a) s) -> s ~> Maybe a
type instance Apply (PreviewSym1 x) y = Preview x y

type family LastOf (l :: PLensLike' (Const (MM.Last a)) s a) (arg1 :: s) where
  LastOf l s = UnLastM (UnConst (l @@ (TyCon1Sym1 'Const :.: TyCon1Sym1 'MM.Last :.: TyCon1Sym1 'Just) @@ s))

data LastOfSym0 :: ((a ~> Const (MM.Last a) a) ~> s ~> Const (MM.Last a) s) ~> s ~> Maybe a
type instance Apply LastOfSym0 x = LastOfSym1 x

data LastOfSym1 :: ((a ~> Const (MM.Last a) a) ~> s ~> Const (MM.Last a) s) -> s ~> Maybe a
type instance Apply (LastOfSym1 x) y = LastOf x y


type family ToListOf (l :: PLensLike' (Const [a]) s a) (arg1 :: s) where
  ToListOf l s = UnConst (l @@ (TyCon1Sym1 'Const :.: PureSym0) @@ s)

data ToListOfSym0 :: ((a ~> Const [a] a) ~> s ~> Const [a] s) ~> s ~> [a]
type instance Apply ToListOfSym0 x = ToListOfSym1 x

data ToListOfSym1 :: ((a ~> Const [a] a) ~> s ~> Const [a] s) -> s ~> [a]
type instance Apply (ToListOfSym1 x) y = ToListOf x y

type family Has (l :: PLensLike' (Const SG.Any) s a) (arg1 :: s) where
  Has l s = UnAny (UnConst (l @@ KSym1 ('Const ('SG.Any 'True)) @@ s))

type family View (l :: PLensLike' (Const a) s a) (arg1 :: s) where
  View l s = UnConst (l @@ TyCon1Sym1 'Const @@ s)

data ViewSym0 :: ((a ~> Const a a) ~> s ~> Const a s) ~> s ~> a
type instance Apply ViewSym0 x = ViewSym1 x

data ViewSym1 :: ((a ~> Const a a) ~> s ~> Const a s) -> s ~> a
type instance Apply (ViewSym1 x) y = View x y

type family s ^. l where
  s ^. l = View l s
infixl 8 ^.


type family SetL s l b where
  SetL s l b = Set l b s

type family (.~) s l b where
  (.~) s l b = Set l b s
infixr 4 .~

data SetLSym0 :: s ~> ((a ~> Identity a) ~> s ~> Identity s) ~> b ~> a
type instance Apply SetLSym0 s = SetLSym1 s

data SetLSym1 :: s -> ((a ~> Identity a) ~> s ~> Identity s) ~> b ~> a
type instance Apply (SetLSym1 s) l = SetLSym2 s l

data SetLSym2 :: s -> ((a ~> Identity a) ~> s ~> Identity s) -> b ~> a
type instance Apply (SetLSym2 s l) b = SetL s l b



type family UpdateL s l f where
  UpdateL s l f = Update l f s

type family (%~) s l f where
  (%~) s l f = Update l f s
infixr 4 %~

data UpdateLSym0 :: s ~> ((a ~> Identity a) ~> s ~> Identity s) ~> (a ~> b) ~> a
type instance Apply UpdateLSym0 s = UpdateLSym1 s

data UpdateLSym1 :: s -> ((a ~> Identity a) ~> s ~> Identity s) ~> (a ~> b) ~> a
type instance Apply (UpdateLSym1 s) l = UpdateLSym2 s l

data UpdateLSym2 :: s -> ((a ~> Identity a) ~> s ~> Identity s) -> (a ~> b) ~> a
type instance Apply (UpdateLSym2 s l) f = UpdateL s l f


type family (%%~) s l f where
  (%%~) s l f = UpdatePercent l f s
infixr 4 %%~

type family UpdatePercent (l :: PLensLike f s t a b) (ab :: a ~> f b) (arg1 :: s) where
  UpdatePercent l ab s = l @@ ab @@ s

data UpdatePercentSym0 :: ((a ~> f a) ~> s ~> f s) ~> (a ~> f b) ~> s ~> a
type instance Apply UpdatePercentSym0 x = UpdatePercentSym1 x

data UpdatePercentSym1 :: ((a ~> f a) ~> s ~> f s) -> (a ~> f b) ~> s ~> a
type instance Apply (UpdatePercentSym1 x) y = UpdatePercentSym2 x y

data UpdatePercentSym2 :: ((a ~> f a) ~> s ~> f s) -> (a ~> f b) -> s ~> a
type instance Apply (UpdatePercentSym2 x y) z = UpdatePercent x y z

type family s ^? l where
  s ^? l = Preview l s
infixl 8 ^?

type family s ^?! l where
  s ^?! l = Maybe' (TypeError ('Text "no value! empty fold")) Id (Preview l s)
infixl 8 ^?!

type family s ^.. l where
  s ^.. l = ToListOf l s
infixl 8 ^..

type family Set (l :: PLensLike Identity s t a b) (arg4 :: b) (arg5 :: s) where
  Set l b s = UnIdentity (l @@ KSym1 ('Identity b) @@ s)

data SetSym0 :: ((a ~> Identity a) ~> s ~> Identity s) ~> b ~> s ~> a
type instance Apply SetSym0 x = SetSym1 x

data SetSym1 :: ((a ~> Identity a) ~> s ~> Identity s) -> b ~> s ~> a
type instance Apply (SetSym1 x) y = SetSym2 x y

data SetSym2 :: ((a ~> Identity a) ~> s ~> Identity s) -> b -> s ~> a
type instance Apply (SetSym2 x y) z = Set x y z

type family Update (l :: PLensLike Identity s t a b) (ab :: a ~> b) (arg1 :: s) where
  Update l ab s = UnIdentity (l @@ (TyCon1Sym1 'Identity :.: ab) @@ s)

data UpdateSym0 :: ((a ~> Identity a) ~> s ~> Identity s) ~> (a ~> b) ~> s ~> a
type instance Apply UpdateSym0 x = UpdateSym1 x

data UpdateSym1 :: ((a ~> Identity a) ~> s ~> Identity s) -> (a ~> b) ~> s ~> a
type instance Apply (UpdateSym1 x) y = UpdateSym2 x y

data UpdateSym2 :: ((a ~> Identity a) ~> s ~> Identity s) -> (a ~> b) -> s ~> a
type instance Apply (UpdateSym2 x y) z = Update x y z

type family T_1 afb s where
  T_1 afb '(a,x) = FlipSym2 PairSym0 x <$> (afb @@ a)

data T_1Sym0 :: (a ~> f b) ~> (a,x) ~> f (b,x)
type instance Apply T_1Sym0 x = T_1Sym1 x

data T_1Sym1 :: (a ~> f b) -> (a,x) ~> f (b,x)
type instance Apply (T_1Sym1 x) y = T_1 x y


type family T_2 afb s where
  T_2 afb '(x,a) = PairSym1 x <$> (afb @@ a)

data T_2Sym0 :: (a ~> f b) ~> (x,a) ~> f (x,b)
type instance Apply T_2Sym0 x = T_2Sym1 x

data T_2Sym1 :: (a ~> f b) -> (x,a) ~> f (x,b)
type instance Apply (T_2Sym1 x) y = T_2 x y

type family T_13 afb s where
  T_13 afb '(a,x,y) = FlipSym2 (FlipSym2 (TyCon3Sym1 '(,,)) x) y <$> (afb @@ a)

data T_13Sym0 :: (a ~> f b) ~> (a,x,y) ~> f (b,x,y)
type instance Apply T_13Sym0 x = T_13Sym1 x

data T_13Sym1 :: (a ~> f b) -> (a,x,y) ~> f (b,x,y)
type instance Apply (T_13Sym1 x) y = T_13 x y


type family T_23 afb s where
  T_23 afb '(x,a,y) = FlipSym2 (TyCon3Sym2 '(,,) x) y <$> (afb @@ a)

data T_23Sym0 :: (a ~> f b) ~> (x,a,y) ~> f (x,b,y)
type instance Apply T_23Sym0 x = T_23Sym1 x

data T_23Sym1 :: (a ~> f b) -> (x,a,y) ~> f (x,b,y)
type instance Apply (T_23Sym1 x) y = T_23 x y

type family T_33 afb s where
  T_33 afb '(x,y,a) = TyCon3Sym3 '(,,) x y <$> (afb @@ a)

data T_33Sym0 :: (a ~> f b) ~> (x,y,a) ~> f (x,y,b)
type instance Apply T_33Sym0 x = T_33Sym1 x

data T_33Sym1 :: (a ~> f b) -> (x,y,a) ~> f (x,y,b)
type instance Apply (T_33Sym1 x) y = T_33 x y

type family IxList (i :: Nat) (afa :: a ~> f a) (as :: [a]) :: f [a] where
  IxList i afa as = Traverse (WhenSym3 (EqSym1 i :.: FstSym0) (afa :.: SndSym0) (PureSym0 :.: SndSym0)) (IToList' 0 as)

data IxListSym0 :: Nat ~> (a ~> f a) ~> [a] ~> f [a]
type instance Apply IxListSym0 x = IxListSym1 x

data IxListSym1 :: Nat -> (a ~> f a) ~> [a] ~> f [a]
type instance Apply (IxListSym1 x) y = IxListSym2 x y

data IxListSym2 :: Nat -> (a ~> f a) -> [a] ~> f [a]
type instance Apply (IxListSym2 x y) z = IxList x y z


type family IxNE (i :: Nat) (afb :: a ~> f a) (as :: NonEmpty a) :: f (NonEmpty a) where
  IxNE 0 afa (a ':| as) = FlipSym2 (TyCon2Sym1 '(:|)) as <$> (afa @@ a)
  IxNE i afa (a ':| as) = TyCon2Sym2 '(:|) a <$> IxList (i-1) afa as

data IxNESym0 :: Nat ~> (a ~> f a) ~> NonEmpty a ~> f (NonEmpty a)
type instance Apply IxNESym0 x = IxNESym1 x

data IxNESym1 :: Nat -> (a ~> f a) ~> NonEmpty a ~> f (NonEmpty a)
type instance Apply (IxNESym1 x) y = IxNESym2 x y

data IxNESym2 :: Nat -> (a ~> f a) -> NonEmpty a ~> f (NonEmpty a)
type instance Apply (IxNESym2 x y) z = IxNE x y z


type family IxString (i :: Nat) (afa :: Symbol ~> f Symbol) (as :: Symbol) :: f Symbol where
  IxString i afa ss = MconcatSym0 <$> IxList i afa (S.ToList ss)

data IxStringSym0 :: Nat ~> (a ~> f a) ~> Symbol ~> f Symbol
type instance Apply IxStringSym0 x = IxStringSym1 x

data IxStringSym1 :: Nat -> (a ~> f a) ~> Symbol ~> f Symbol
type instance Apply (IxStringSym1 x) y = IxStringSym2 x y

data IxStringSym2 :: Nat -> (a ~> f a) -> Symbol ~> f Symbol
type instance Apply (IxStringSym2 x y) z = IxString x y z

type family StringTraversal afb s where
  StringTraversal afb ss = Fmap MconcatSym0 (Traverse afb (S.ToList ss))

data StringTraversalSym0 :: (Symbol ~> f b) ~> Symbol ~> f b
type instance Apply StringTraversalSym0 x = StringTraversalSym1 x

data StringTraversalSym1 :: (Symbol ~> f b) -> Symbol ~> f b
type instance Apply (StringTraversalSym1 x) y = StringTraversal x y



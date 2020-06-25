-- Vec is an inductive defined vector that can be work in multiple dimensions
{-# OPTIONS -Wall #-}
{-# OPTIONS -Wno-compat #-}
{-# OPTIONS -Wincomplete-record-updates #-}
{-# OPTIONS -Wno-incomplete-uni-patterns #-}
{-# OPTIONS -Wno-redundant-constraints #-}
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
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PatternSynonyms #-}
module VectorN where
import qualified Data.Type.Equality as DTE
import Data.Proxy
import GHC.TypeNats
import GHC.TypeLits hiding (natVal,natVal')
import Data.Kind (Type)
import Control.Monad
import Data.Foldable
import Data.List
import Control.Lens hiding (Cons)
import Control.Applicative
import qualified Data.Semigroup as SG
import PMonoid
import PSemigroup
import PList
import PApplicative
import PFunctor
import PCore
import PTraversable
import PEq
import PFoldable
import PN
{-
src\VectorN.hs:33:8: warning: [-Wcompat-unqualified-imports]
    To ensure compatibility with future core libraries changes
    imports to Data.List should be
    either qualified or have an explicit import list.
   |
33 | import Data.List
   |        ^^^^^^^^^

src\VectorN.hs:82:3: warning: [-Woverlapping-patterns]
    Pattern match has inaccessible right hand side
    In an equation for ‘<>’: <> VZ VZ = ...
   |
82 |   VZ <> VZ = VZ
   |   ^^^^^^^^^^^^^

src\VectorN.hs:94:3: warning: [-Woverlapping-patterns]
    Pattern match has inaccessible right hand side
    In an equation for ‘<*>’: <*> VZ VZ = ...
   |
94 |   VZ <*> VZ = VZ
   |   ^^^^^^^^^^^^^^

src\VectorN.hs:159:1: warning: [-Woverlapping-patterns]
    Pattern match has inaccessible right hand side
    In an equation for ‘vzip’: vzip _ VZ VZ = ...
    |
159 | vzip _ VZ VZ = VZ
    | ^^^^^^^^^^^^^^^^^
-}

-- we want stuff to evaluate so use type family not type synonyms
type family Vec' (n :: Nat) a where
  Vec' n a = Vec (ToN n) a

instance (Applicative (Vec n), VPure n, Num a) => Num (Vec n a) where
  (+) = liftA2 (+)
  (-) = liftA2 (-)
  (*) = liftA2 (*)
  negate = fmap negate
  abs = fmap abs
  signum = fmap signum
  fromInteger = pure . fromInteger

data Vec n (a :: Type) where
  VZ :: Vec 'Z a
  VS :: a -> Vec n a -> Vec ('S n) a

infixr 1 `VS`

{-# COMPLETE (:&) #-}
pattern (:&) :: forall (n :: N) a.
                      () =>
                      forall (n1 :: N). (n ~ 'S n1) => a -> Vec n1 a -> Vec n a
pattern (:&) a v = VS a v

infixr 1 :&

data VSSym0 :: a ~> Vec n a ~> Vec ('S n) a
type instance Apply VSSym0 x = VSSym1 x

data VSSym1 :: a -> Vec n a ~> Vec ('S n) a
type instance Apply (VSSym1 x) y = 'VS x y

instance Semigroup a => Semigroup (Vec n a) where
  VZ <> VZ = VZ
  VS a va <> VS b vb = VS (a <> b) (va <> vb)

instance (VPure n, Monoid a) => Monoid (Vec n a) where
  mempty = vpure @n mempty

instance Functor (Vec n) where
  fmap _ VZ = VZ
  fmap f (VS a v) = VS (f a) (fmap f v)

instance Applicative (Vec 'Z) where
  pure _ = VZ
  VZ <*> VZ = VZ

instance (Applicative (Vec n), VPure n) => Applicative (Vec ('S n)) where
  pure = vpure -- @('S n) is not needed cos ghc can figure it out
  VS ab vab <*> VS a va = VS (ab a) (vab <*> va)

instance Foldable (Vec n) => FoldableWithIndex Int (Vec n) where
  ifoldMap iam = ifoldMap iam . toList

instance Functor (Vec n) => FunctorWithIndex Int (Vec n) where
  imap = vimap 0

vimap :: Num i => i -> (i -> a -> b) -> Vec n a -> Vec n b
vimap _ _ VZ = VZ
vimap i f (VS a v) = VS (f i a) (vimap (i+1) f v)

instance Traversable (Vec n) => TraversableWithIndex Int (Vec n) where
  itraverse = vitraverse 0

vitraverse :: (Num i, Applicative f) => i -> (i -> a -> f b) -> Vec n a -> f (Vec n b)
vitraverse _ _ VZ = pure VZ
vitraverse i f (VS a v) = VS <$> f i a <*> vitraverse (i+1) f v

instance Foldable (Vec n) where
  foldMap _ VZ = mempty
  foldMap f (VS a v) = f a <> foldMap f v

instance Traversable (Vec n) where
  traverse _ VZ = pure VZ
  traverse f (VS a v) = VS <$> f a <*> traverse f v

instance (KnownNat (ToNat n), Foldable (Vec n), Show a) => Show (Vec n a) where
  show v = "@" ++ show (nat @n) ++ " " ++ show (toList v)

len :: forall n a . (KnownNat (ToNat n)) => Vec n a -> Int
len _ = nat @n

-- gen3 is not at all useful: just playing with rankntypes
class Gen n where
  gen :: [a] -> Vec n a
  gen1 :: p n -> [a] -> Vec n a
  gen2 :: a -> (a -> a) -> Vec n a
  gen3 :: a -> (forall p x . KnownNat x => p x -> a -> a) -> Vec n a
instance Gen 'Z where
  gen _ = VZ
  gen1 _ _ = VZ
  gen2 _ _ = VZ
  gen3 _ _ = VZ
instance (KnownNat (ToNat n), Gen n) => Gen ('S n) where
  gen ~(a:as) = VS a (gen @n as)
  gen1 _ ~(a:as) = VS a (gen1 @n Proxy as)
  gen2 i f = VS i (gen2 @n (f i) f)
  gen3 i f = VS i (gen3 @n (f (Proxy @(ToNat n)) i) f)

gen' :: forall n a . Gen (ToN n) => [a] -> Vec (ToN n) a
gen' = gen

gen2' :: forall n a . Gen (ToN n) => a -> (a -> a) -> Vec (ToN n) a
gen2' = gen2

vapp :: Vec m a -> Vec n a -> Vec (m :+ n) a
vapp VZ w = w
vapp (VS a v) w = VS a (v `vapp` w)

vzip :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
vzip _ VZ VZ = VZ
vzip f (VS a v) (VS b w) = VS (f a b) (vzip f v w)

vzipN :: (a -> b -> c) -> Vec n a -> [b] -> Vec n c
vzipN _ VZ _ = VZ
vzipN f (VS a v) ~(b:bs) = VS (f a b) (vzipN f v bs)

-- works but use imap [functorwithindex]
vi :: Vec n a -> Vec n (Int,a)
vi = vi' 0

vi' :: forall n a . Int -> Vec n a -> Vec n (Int,a)
vi' _ VZ = VZ
vi' i (VS a v) = VS (i, a) (vi' (i+1) v)

vnest :: (a -> b -> c) -> Vec m a -> Vec n b -> Vec m (Vec n c)
vnest _ VZ _ = VZ
vnest f (VS a v) w = VS (fmap (f a) w) (vnest f v w)

-- vnest + vflat
vnest1 :: (a -> b -> c) -> Vec m a -> Vec n b -> Vec (m :* n) c
vnest1 _ VZ _ = VZ
vnest1 f (VS a v) w = fmap (f a) w `vapp` vnest1 f v w

vflat :: Vec m (Vec n a) -> Vec (m :* n) a
vflat VZ = VZ
vflat (VS v vs) = vapp v (vflat vs)

-- only defined for single dimensional vectors: see vheadLens or headv for more general version
-- another more generic vhead would take the head of every dimension: ie all dimensions are 1
vhead :: Vec ('S n) a -> a
vhead (VS a _) = a

-- a more generic vtail would take the tail of every dimension
  -- wouldnt be sensible for dimensions of 1 cos then you couldnt get to the next dimension if it was 1
vtail :: Vec ('S n) a -> Vec n a
vtail (VS _ v) = v

-- index into a Vec
class VInd i n where
  vind :: Vec n a -> a
instance VInd 'Z ('S n) where
  vind (VS a _) = a
instance VInd i n => VInd ('S i) ('S n) where
  vind (VS _ vs) = vind @i @n vs  -- need @i but not @n

-- better cos uses Nat
vind' :: forall i n a . VInd (ToN i) n => Vec n a -> a
vind' = vind @(ToN i)

-- type family to rewrite (Vec n a) (is :: [N]) to x where x is the resulting type!
-- should be based on length of 'is'
type family Rewrite a is where
  Rewrite a '[] = a
  Rewrite (Vec n a) (i ': is) = Rewrite a is

-- need a type class to calculate 'b' ie the result type
-- ie given 5 dimensions and we only search on 3 then we get some shape
class VIndN (is :: [N]) a where
  vindN :: a -> Rewrite a is

instance VIndN '[] a where
  vindN x = x

instance (VIndN is a, VInd i ('S n))
   => VIndN (i ': is) (Vec ('S n) a) where
  vindN x = vindN @is @a (vind @i @('S n) x)

-- convert from '[Nat] to '[N]
-- index into a multidimensional vector using Nats
vindN' :: forall is a . VIndN (ToNs is) a => a -> Rewrite a (ToNs is)
vindN' = vindN @(ToNs is)

vmatrixOLD :: forall m n o a . (Num a, Gen m, GenS o, VTrans m n, Foldable (Vec n), Foldable (Vec m), Foldable (Vec o), VTrans n o, KnownNat (ToNat m), KnownNat (ToNat o))
    => Vec m (Vec n a) -> Vec n (Vec o a) -> Vec m (Vec o a)
vmatrixOLD vs ws =
  mkMat @m @o (concat [ [a `vdot` b | a <- toList vs] | b <- toList (vtrans ws)])

-- matrix multiplication works and preserves types
vmatrix :: forall m n o a . (Num a, VTrans n o, Foldable (Vec n))
    => Vec m (Vec n a) -> Vec n (Vec o a) -> Vec m (Vec o a)
vmatrix vs ws = vnest vdot vs (vtrans ws)

type family Mat m n a where Mat m n a = Vec (ToN m) (Vec (ToN n) a)
type family Mat' m n a where Mat' m n a = UnDimX '[m,n] a -- equivalent

m1 :: Mat 3 5 Int
m1 = mkMat [3..] -- use genn' cos type safe

m2 :: Mat 5 2 Int
m2 = mkMat [7..]

vdot :: (Foldable (Vec n), Num a) => Vec n a -> Vec n a -> a
vdot = (sum .) . vzip (*)

class VPure n where
  vpure :: a -> Vec n a
instance VPure 'Z where
  vpure _ = VZ
instance VPure n => VPure ('S n) where
  vpure a = VS a (vpure a)

-- transpose a matrix
class VTrans m n where
  vtrans :: Vec m (Vec n a) -> Vec n (Vec m a)
instance VPure n => VTrans 'Z n where
  vtrans _ = vpure @n VZ
instance VTrans n 'Z where
  vtrans _ = VZ
-- again i keep missing the VTrans m n =>
instance VTrans m n => VTrans m ('S n) where
  vtrans z = VS (fmap vhead z) (vtrans @m @n (fmap vtail z)) -- dont need @m @n but good for debugging

-- singleton
vsing :: a -> Vec ('S 'Z) a
vsing a = VS a VZ

showMat :: forall m n a . (NToInts (Dim (Vec m (Vec n a))), Foldable (Vec m), Foldable (Vec n), Show a, Show (Vec m (Vec n a)), KnownNat (ToNat m), KnownNat (ToNat n))
   => Vec m (Vec n a) -> String
showMat mat = "@" ++ show (dimsP (toproxy mat)) ++ "\n" ++ intercalate "\n" (map (show . toList) (toList mat))

newtype ST s a = ST { unST :: s -> (a, s) }
instance Functor (ST s) where
  fmap f (ST g) = ST $ \s -> let (a, s') = g s in (f a, s')
instance Applicative (ST s) where
  pure a = ST (a,)
  ST sab <*> ST sa = ST $ \s -> let (ab,s') = sab s
                                    (a,s'') = sa s'
                                in (ab a, s'')
instance Monad (ST s) where
  return a = ST (a,)
  ST sa >>= amb = ST $ \s -> let (a, s') = sa s
                             in unST (amb a) s'

get :: ST s s
get = ST $ \s -> (s, s)

put :: s -> ST s ()
put s = ST $ const ((), s)

put' :: s -> ST s ()
put' = modify . const

modify :: (s -> s) -> ST s ()
modify f = ST $ \s -> ((), f s)

class GenN (dims :: [N]) a where
  genN :: ST [a] (UnDim dims a)
instance GenN '[] a where
  genN = ST $ \(s:ss) -> (s,ss)
instance GenS n => GenN '[n] a where
  genN = gens @n
-- added n0:n1:ns instead of n:ns to get rid of overlapping condition
instance (UnDim (n0 : n1 : ns) a ~ Vec n0 (UnDim (n1 : ns) a), KnownNat (ToNat n0), GenN (n1 : ns) a, GenS n0)
  => GenN (n0 ': n1 ': ns) a where
  genN = let w = genN @(n1 ': ns)
             nn = nat @n0
         in ST $ \s -> let (a,b) = unST (replicateM nn w) s
                           (c,_) = unST (gens @n0) a
                       in (c,b)

genn :: forall (ns :: [N]) a . GenN ns a => [a] -> UnDim ns a
genn as = fst $ unST (genN @ns @a) as

genn' :: forall (ns :: [Nat]) a . GenN (ToNs ns) a => [a] -> UnDim (ToNs ns) a
genn' as = fst $ unST (genN @(ToNs ns) @a) as

-- runtime error if not the exact number of items [ie if more]
-- always has runtime error if less than
gennExact' :: forall (ns :: [Nat]) a . (Show a, GenN (ToNs ns) a) => [a] -> Either String (UnDim (ToNs ns) a)
gennExact' as =
  let (x,y) = unST (genN @(ToNs ns) @a) as
  in if null y then Right x else Left $ "gennExact':had some left over data: " ++ show (take 10 y)

class GenS (n :: N) where
  gens :: ST [a] (Vec n a)
instance GenS 'Z where
  gens = pure VZ
instance GenS n => GenS ('S n) where
  gens = do
           ~(a:as) <- get
           put as
           v <- gens @n
           return $ VS a v

genNS :: forall n a . GenS (ToN n) => [a] -> Vec (ToN n) a
genNS as = fst $ unST gens as

gens' :: forall n a . GenS (ToN n) => ST [a](Vec (ToN n) a)
gens' = gens

-- use genn' for any dimensions
mkMat' :: forall m n a . (Gen (ToN m), GenS (ToN n), KnownNat m, KnownNat n)
   => [a] -> Vec (ToN m) (Vec (ToN n) a)
mkMat' as =
  let m = fromIntegral $ natVal (Proxy @m)
  in gen' @m $ fst $ unST (replicateM m (gens' @n)) as

-- use genn' for any dimensions
mkMat :: forall m n a . (Gen m, GenS n, KnownNat (ToNat m), KnownNat (ToNat n))
   => [a] -> Vec m (Vec n a)
mkMat as =
  let m = nat @m
  in gen @m $ fst $ unST (replicateM m (gens @n)) as

-- tricky: just added holes everywhere: and eventually it worked out
-- splits into two
class VSplit m where
  vsplit :: Vec (m :+ n) a -> (Vec m a, Vec n a)
instance VSplit 'Z where
  vsplit v = (VZ,v)
instance VSplit m => VSplit ('S m) where
  vsplit (VS a v) =
    let (x,y) = vsplit @m v
    in (VS a x, y)

-- splits into 2 vectors either side of a value! used for lens stuff when we need the value and the rest
class VSplitX m where
  vsplitX :: Vec ('S (m :+ n)) a -> (Vec m a, a, Vec n a)
instance VSplitX 'Z where
  vsplitX (VS a v) = (VZ, a, v)
instance VSplitX m => VSplitX ('S m) where
  vsplitX (VS a v) =
    let (vs1, a0, vs2) = vsplitX @m v
    in (VS a vs1, a0, vs2)

class VDrop m where
  vdrop :: Vec (m :+ n) a -> Vec n a
instance VDrop 'Z where
  vdrop v = v
instance VDrop m => VDrop ('S m) where
  vdrop (VS _ v) = vdrop @m v

class VTake m n where
  vtake :: Vec (m :+ n) a -> Vec m a
instance VTake 'Z n where
  vtake _ = VZ
instance VTake m n => VTake ('S m) n where
  vtake (VS a v) = VS a (vtake @m @n v)

vslice :: forall m n1 n2 a . (VDrop m, VTake (m :+ n1) n2) =>
     Vec ((m :+ n1) :+ n2) a -> Vec n1 a
vslice = vdrop @m . vtake @(m :+ n1) @n2

vslice' :: forall (m :: Nat) (n1 :: Nat) (n2 :: N) a .
   (VDrop (ToN m), VTake (ToN m :+ ToN n1) n2) =>
     Vec ((ToN m :+ ToN n1) :+ n2) a -> Vec (ToN n1) a
vslice' = vdrop @(ToN m) . vtake @(ToN m :+ ToN n1) @n2

-- this was going to be used for VSplitN but doesnt make a lot of sense
-- can only really split on the last dimension
-- creates a n-dimensional vector using is as the sizes and matches the type of v
type family DimZ (is :: [N]) (v :: Type) :: Type where
  DimZ (i ': is) (Vec n a) = Vec i (DimZ is a)
  DimZ '[] a = a

-- creates a n-dimensional vector using is as the sizes and matches the type of v but diff from n
type family DimZZ (is :: [N]) v where
  DimZZ (i ': is) (Vec n a) = Vec (Diff n i) (DimZZ is a)
  DimZZ '[] a = a

-- create the type of a multidimensional vector using kind [N]
type family UnDim (ns :: [N]) a where
  UnDim '[] a = a
  UnDim (n ': ns) a = Vec n (UnDim ns a)

-- easier to work with: UnDim variant
-- create the type of a multidimensional vector using kind [Nat]
type family UnDimX (ns :: [Nat]) a where
  UnDimX '[] a = a
  UnDimX (n ': ns) a = Vec (ToN n) (UnDimX ns a)

-- replaces UnDimX
type family UnDimX' ns a where
 UnDimX' ns a = Foldr (TyCon2Sym1 Vec :.: ToNSym0) a ns

-- which ones do i need? the value or typeapplications or a proxy for the value
-- can always use p a: cos just do pure a and then it is a proxy!
dims' :: forall a . (NToInts (Dim a)) => a -> [Int]
dims' _ = getNToInts @(Dim a)

dims :: forall a . (NToInts (Dim a)) => [Int]
dims = getNToInts @(Dim a)

dimsP :: forall a p . (NToInts (Dim a)) => p a -> [Int]
dimsP _ = getNToInts @(Dim a)

-- get dimensions of Vec as kind [N]
type family Dim v :: [N] where
  Dim (Vec n a) = n ': Dim a
  Dim a = '[]

-- get dimensions of Vec as kind [Nat]
type family DimX v :: [Nat] where
  DimX (Vec n a) = ToNat n ': DimX a
  DimX a = '[]

type family ToNs ns where ToNs ns = Map ToNSym0 ns

type family ToNats ns where ToNats ns = Map ToNatSym0 ns

dimsX :: forall a . (NatToInts (DimX a)) => [Int]
dimsX = getNatToInts @(DimX a)

-- replaces the above NToInts class
type family NToInts ns where NToInts ns = NatToInts (Map ToNatSym0 ns)

getNToInts :: forall (ns :: [N]) . NatToInts (Map ToNatSym0 ns) => [Int]
getNToInts = getNatToInts @(Map ToNatSym0 ns)

-- [Nat] to [Int]
class NatToInts (xs :: [Nat]) where
  getNatToInts :: [Int]
instance NatToInts '[] where
  getNatToInts = []
instance (KnownNat n, NatToInts ns) => NatToInts (n ': ns) where
  getNatToInts = fromIntegral (natVal (Proxy @n)) : getNatToInts @ns

-- pure @Proxy
toproxy :: a -> Proxy a
toproxy _ = Proxy


-- yurk!
class GU (i :: N) (n :: N) a where
  getAt :: Vec n a -> a
  updateAt :: a -> Vec n a -> Vec n a
--  guAt :: Functor f => (a -> f a) -> (Vec n a -> f (Vec n a))
instance GU 'Z ('S n) a where
  getAt (VS a _) = a
  updateAt a' (VS _ v) = VS a' v
--  guAt afa VZ = Identity VZ
instance GU i n a => GU ('S i) ('S n) a where
  getAt (VS _ v) = getAt @i @n v
  updateAt a' (VS a v) = VS a (updateAt @i @n a' v)

vlens :: forall (i :: N) (n :: N) a . GU i n a
   => Lens' (Vec n a) a
vlens afb v =
  let a = getAt @i v
  in fmap (\b -> updateAt @i b v) (afb a)

class VLens (is :: [N]) (ns :: [N]) a where
  vlensN :: Lens' (UnDimZ is ns a) a
  vlensN1 :: VLen ns ~ VLen is => UnDim ns a -> Lens' (UnDimZ is ns a) a
instance VLens '[] ns a where
  vlensN = id
  vlensN1 _ = id
instance (GU i n (UnDimZ is ns a), VLens is ns a) => VLens (i ': is) (n ': ns) a where
  vlensN = vlens @i @n . vlensN @is @ns
  vlensN1 _ = vlens @i @n . vlensN @is @ns

vlensN' :: forall (is :: [Nat]) (ns :: [Nat]) a . VLens (ToNs is) (ToNs ns) a => Lens' (UnDimZ (ToNs is) (ToNs ns) a) a
vlensN' = vlensN @(ToNs is) @(ToNs ns)

type family UnDimZ (is :: [N]) (ns :: [N]) a where
  UnDimZ '[] ns a = a
  UnDimZ (i ': is) (n ': ns) a = Vec n (UnDimZ is ns a)

type family UnDimZ' (i :: Nat) (ns :: [N]) a where
  UnDimZ' i ns a = Foldr (TyCon2Sym1 Vec) a (Take i ns)

-- matches exactly with UnDimZ
type family UnDimZ'' (is :: [N]) (ns :: [N]) a where
  UnDimZ'' is ns a = Foldr (TyCon2Sym1 Vec) a (Take (Length is) ns)
vtraversal :: Traversal (Vec n a) (Vec n b) a b
vtraversal _ VZ = pure VZ
vtraversal afb (VS a v) = VS <$> afb a <*> vtraversal afb v

type family VLen (ns :: [k]) :: N where
  VLen ns = ToNSym0 @@ Foldr (SumSym0 :.: KSym1 1) 0 ns

class VShow3 (ns :: [N]) a where
  vshow3 :: Show a => UnDim ns a -> String

instance VShow3 '[] a where -- plain 'a' cos not a Vec
  vshow3 (v :: a) = "zero dim: " ++ show v

instance KnownNat (ToNat n) => VShow3 '[n] a where
  vshow3 (v :: Vec n a)  = "one dim: " ++ show (nat @n) ++ " " ++ show v

instance (KnownNat (ToNat n1), KnownNat (ToNat n2)) => VShow3 '[n1, n2] a where
  vshow3 (v :: Vec n1 (Vec n2 a)) =
    let zs = "two dim: " ++ show (nat @n1, nat @n2) ++ " " ++ show v
        ys = intercalate "\n\n" $ toList $ v <&> \x1 ->
                    intercalate "_" $ toList $ x1 <&> \x2 -> show x2
    in zs ++ "\n" ++ ys

instance (NToInts (n1 ': n2 ': n3 ': ns), FoldMap (KnownNatSym0 :.: ToNatSym0) (n1 ': n2 ': n3 ': ns), Show (UnDim ns a))
  => VShow3 (n1 ': n2 ': n3 ': ns) a where
  vshow3 (v :: Vec n1 (Vec n2 (Vec n3 (UnDim ns a)))) =
    let zs = "multi dim: @(" ++ intercalate "_" (map show (getNToInts @(n1 ': n2 ': n3 ': ns))) ++ ") "
        ys = intercalate "\n\n" $ toList $ v <&> \x1 ->
                    intercalate "\n" $ toList $ x1 <&> \x2 ->
                            intercalate " || " $ toList $ x2 <&> \x3 -> show x3
    in zs ++ "\n" ++ ys

showv3 :: forall ns a v . (VShow3 ns a, ns ~ DimNS v, v ~ UnDim (DimNS v) (DimA v), a ~ DimA v, NToInts ns, Show a) => v -> String
showv3 v  =
  let ns = getNToInts @ns
  in show ns ++ vshow3 @ns @a v

pr :: (VShow3 (DimNS v) (DimA v), NToInts (DimNS v), Show v,
      Show (DimA v), UnDim (DimNS v) (DimA v) ~ v) =>
     v -> IO ()
pr = putStrLn . showv3

-- more general head: which goes all the way down: could use a VLens and just generate it for [0,0,0,0,..]
class VHead' (ns :: [N]) a where
  vhead' :: UnDim ns a -> a
instance VHead' '[] a where
  vhead' (a :: a) = a
instance VHead' '[ 'S n] a where
  vhead' (VS a _) = a
instance VHead' (n2 ': ns) a => VHead' ('S n1 ': n2 ': ns) a where
  vhead' (VS v _) = vhead' @(n2 ': ns) v

-- requires the caller to turn on AllowAmbiguousTypes!
-- why does this not work and yet below does! cant make 'a' as a return type work
-- this now works at home but didnt at work! ambiguoustypes?
headv :: forall ns a v . (DimNS v ~ ns, DimA v ~ a, UnDim ns a ~ v, VHead' ns a) => v -> a
headv = vhead' @ns @a

headx :: forall ns a v . (DimNS v ~ ns, DimA v ~ a, UnDim ns a ~ v, VHead' ns a) => UnDim ns a -> a
headx = vhead' @ns @(DimA (UnDim ns a))

headv' :: forall ns a v . (VHead' ns a, Show v, ns ~ DimNS v, v ~ UnDim (DimNS v) (DimA v), a ~ DimA v, NToInts ns, Show a) => v -> String
headv' v  =
  let ns = getNToInts @ns
  in show ns ++ " " ++ show (vhead' @ns @a v)

type family VRep n a where
  VRep ('S n) a = a ': VRep n a
  VRep 'Z a = '[]

vheadLens :: forall ns a v . (UnDimZ (VRep (VLen ns) 'Z) ns a ~ v, VLens (VRep (VLen ns) 'Z) ns a, ns ~ DimNS v, v ~ UnDim (DimNS v) (DimA v), a ~ DimA v)
  => v -> a
vheadLens v =
  let z = v ^. vlensN @(VRep (VLen ns) 'Z) @ns @a
  in  z  -- ++ show ns

type family DimNS v where
  DimNS (Vec n a) = n ': DimNS a
  DimNS a = '[]

type family DimA v where
  DimA (Vec n a) = DimA a
  DimA a = a

-- lifted tuples
type family DimP v :: [(N, Type)] where
  DimP (Vec n a) = '(n,a) ': DimP a
  DimP a = '[]


type family DimAll v where DimAll v = Second LstSym0 (UnZip (DimP v))

type family MAB :: (Symbol, A0 ~> B0) where
  MAB = '("dude", KSym1 'B0)

type family MA :: (Symbol, A0) where
  MA = '("after", 'A1)

-- this works on the type Vec ===
class PEq1 (a :: k) where
  type family (====) (a :: k) (b :: k) :: Bool
  type x ==== y = x DTE.== y

-- type family PPP (x :: a) (y :: a) :: Bool -- makes no sense cos we are lifting too high
-- ie there is nowhere to go above kind k: there is no meta kind
instance PEq1 'VZ where
  type 'VZ ==== 'VZ = 'True

instance (PEq1 a, PEq1 v) => PEq1 ('VS a v) where
  type 'VS a v ==== 'VS b w = a ==== b && v ==== w

instance PEq1 (Vec 'Z a) where
  type Vec 'Z a ==== Vec 'Z a1 = a ==== a1

instance PEq1 a => PEq1 (Vec ('S n) a) where
  type Vec ('S n) a ==== Vec ('S m) b = n ==== m && a ==== b

instance PEq1 (SG.Arg x y) where
  type SG.Arg x y ==== SG.Arg x1 y1 = x DTE.== x1

instance PEq1 SG.All where
  type SG.All ==== SG.All = 'True

-- default to DTE
instance PEq1 Int
instance PEq1 Bool
instance PEq1 Integer
instance PEq1 Double
instance PEq1 Nat
instance PEq1 Char
instance PEq1 a => PEq1 [a]
-- oops doesnt scale: we would need an entry for every Nat: lets stick with PEq
instance PEq1 10

instance PEq (Vec 'Z a) where
  type 'VZ === 'VZ = 'True
--  type x === y = x DTE.== y

-- have to use DTE.== else wont work!
instance PEq (Vec ('S n) a0) where
  type 'VS a v === 'VS a1 v1 = a === a1 && v === v1
  -- type x === y = x DTE.== y

instance PFunctor (Vec 'Z) where
  type Fmap f 'VZ = 'VZ

-- need TypeInType cos GADT?
instance PFunctor (Vec ('S n)) where
  type Fmap f ('VS a v) = 'VS (f @@ a) $$ Fmap f v

instance PApplicative (Vec 'Z) where
  type Pure a = 'VZ
  type 'VZ <*> 'VZ = 'VZ

instance PApplicative (Vec ('S n)) where
  type Pure a = 'VS a $$ Pure a
  type 'VS ab vab <*> 'VS a va = 'VS (ab @@ a) $$ vab <*> va

instance PFoldable (Vec 'Z) where
  type FoldMap am 'VZ = Mempty

instance PFoldable (Vec ('S n)) where
  type FoldMap am ('VS a v) = am @@ a <> FoldMap am v

instance PTraversable (Vec 'Z) where
  type Traverse afb 'VZ = Pure 'VZ

instance PTraversable (Vec ('S n)) where
  type Traverse afb ('VS a v) = VSSym0 <$> afb @@ a <*> Traverse afb v

instance PMonoid (Vec 'Z x) where
  type Mempty = 'VZ

instance PSemigroup (Vec 'Z x) where
  type 'VZ <> 'VZ = 'VZ
  type SUnWrap me = me

instance PSemigroup x => PSemigroup (Vec ('S n) x) where
  type 'VS a v <> 'VS a1 v1 = 'VS (a <> a1) (v <> v1)
  type SUnWrap ('VS a v) = 'VS (SUnWrap a) (SUnWrap v)

instance PMonoid x => PMonoid (Vec ('S n) x) where
  type Mempty = 'VS Mempty Mempty

data X :: Bool ~> Int

-- these 3 are all exactly the same!!
data V1 :: Bool -> TyFun a a -> Type
data Y1 (a :: Bool) :: TyFun x x -> Type
data Z1 (a :: Bool) (b :: TyFun x (x :: k)) :: Type

data V2 :: Bool -> TyFun Bool Bool -> Type
data Y2 (a :: Bool) :: TyFun a a -> Type -- different 'a'

-- this one put Bool inside the 'a'
data Z2 (a :: Bool) (b :: TyFun a a) :: Type
{-
checkTrueIsFalse :: 'True ~ 'False => ()
checkTrueIsFalse = ()

checkTrueIsTrue :: ('True ~ 'True => ()) -> ()
checkTrueIsTrue x = x
-}
type family VMin (m :: N) (n :: N) :: N where
  VMin 'Z n = 'Z
  VMin m 'Z = 'Z
  VMin ('S m) ('S n) = 'S (VMin m n)

vzipMinWith :: forall m n o a b c . VMin m n ~ o => (a -> b -> c) -> Vec m a -> Vec n b -> Vec o c
vzipMinWith _ VZ _ = VZ
vzipMinWith _ _ VZ = VZ
vzipMinWith f (VS a v) (VS b vv) = VS (f a b) (vzipMinWith f v vv)



data A0 = A0 | A1 | A2
data B0 = B0 | B1 | B2
data S0 = S0 | S1 | S2


instance PList (Vec 'Z) where
  type UnCons 'VZ = 'Nothing
  type UnSnoc 'VZ = 'Nothing

instance PList (Vec ('S n)) where
--  type UnCons 'VZ = 'Nothing
  type UnCons ('VS a v) = 'Just '(a, ToList v)

-- would be a different type if we remove one element! ie Vec (S n) becomes Vec n
-- what does unsnoc mean for a vector: drop a dimension and just get the last element or keep same dimension
-- simplified by returning a list and the value
  type UnSnoc ('VS a v) = UnSnoc (ToList ('VS a v))

velemIndex :: Eq a => a -> Vec n a -> Maybe (Fin n)
velemIndex _ VZ = Nothing
velemIndex x (VS a v)
  | a==x = Just FZ
  | otherwise = FS <$> velemIndex x v

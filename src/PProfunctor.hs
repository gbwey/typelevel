-- prisms are too hard: need a different representation
{-
A lens describes something isomorphic to a product with some extra context. A lens from s
to a indicates there exists c such that s is isomorphic to (c, a).

On the other hand, a prism from s to a indicates there exists c such that s is isomorphic
to (Either c a).
-}
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

module PProfunctor where
--import Data.Kind (Type)
import Data.Profunctor
--import Control.Lens.Prism
--import Control.Lens.Internal.Prism
import PCore
import PFunctor
import PBifunctor
import Data.Tagged
import PR

class PProfunctor p where
  type family Dimap (f :: b ~> a) (g :: c ~> d) (h :: p a c) :: p b d
  type Dimap f g h = Lmap f (Rmap g h)

  type family Lmap (f :: b ~> a) (h :: p a x) :: p b x
  type Lmap f h = Dimap f Id h

  type family Rmap (g :: c ~> d) (h :: p x c) :: p x d
  type Rmap g h = Dimap Id g h

data DimapSym0 :: (b ~> a) ~> (c ~> d) ~> p a c ~> p b d
type instance Apply DimapSym0 x = DimapSym1 x

data DimapSym1 :: (b ~> a) -> (c ~> d) ~> p a c ~> p b d
type instance Apply (DimapSym1 x) y = DimapSym2 x y

data DimapSym2 :: (b ~> a) -> (c ~> d) -> p a c ~> p b d
type instance Apply (DimapSym2 x y) z = Dimap x y z

data LmapSym0 :: (b ~> a) ~> p a x ~> p b x
type instance Apply LmapSym0 x = LmapSym1 x

data LmapSym1 :: (b ~> a) -> p a x ~> p b x
type instance Apply (LmapSym1 x) y = Lmap x y


data RmapSym0 :: (c ~> d) ~> p x c ~> p x d
type instance Apply RmapSym0 x = RmapSym1 x

data RmapSym1 :: (c ~> d) -> p x c ~> p x d
type instance Apply (RmapSym1 x) y = Rmap x y

{- cos had ~> instead of ->  ie
data RmapSym1 :: (c ~> d) ~> p x c ~> p x d   -- bad
data RmapSym1 :: (c ~> d) -> p x c ~> p x d   -- good

C:\haskell\typelevel\src\PProfunctor.hs:71:34-43: error:
    * Expected kind `p1 x1 c1 ~> p1 x1 d1',
        but `RmapSym1 x' has kind `*'
    * In the type `RmapSym1 x'
      In the type instance declaration for `Apply'
   |
71 | type instance Apply RmapSym0 x = RmapSym1 x
   |                                  ^^^^^^^^^^
-}

instance PProfunctor R where
  type Dimap f g ('R ea) = 'R (g :.: ea :.: f)

instance PProfunctor Tagged where
  type Dimap f g ('Tagged a) = 'Tagged (g @@ a)

class PProfunctor p => PChoice p  where
  type family Left' (h :: p a b) :: p (Either a c) (Either b c)
  type Left' p = Dimap SwapLRSym0 SwapLRSym0 (Right' p)

  type family Right' (h :: p a b) :: p (Either c a) (Either c b)
  type Right' p = Dimap SwapLRSym0 SwapLRSym0 (Left' p)

data Right'Sym0 :: p a b ~> p (Either c a) (Either c b)
type instance Apply Right'Sym0 x = Right' x

instance PChoice R where
  type Right' ('R ea) = 'R (Either'Sym2 (TyCon1Sym1 'Left) (TyCon1Sym1 'Right :.: ea))

instance PChoice Tagged where
  type Right' ('Tagged b) = 'Tagged ('Right b)


class PProfunctor p => PStrong p where
  type family First' (h :: p a b) :: p (a, c) (b, c)
  type First' p = Dimap SwapSym0 SwapSym0 (Second' p)

  type family Second' (h :: p a b) :: p (c, a) (c, b)
  type Second' p = Dimap SwapSym0 SwapSym0 (First' p)


instance PStrong R where
  type First' ('R ea) = 'R (FirstSym1 ea)

instance PStrong Tagged where
  type First' ('Tagged b) = 'Tagged Undefined

newtype RR e a = RR { unRR :: e -> a }

instance Profunctor RR where
  dimap f g (RR ea) = RR (g . ea . f)

instance Choice RR where
  right' (RR ea) = RR (either Left (Right . ea))



--type family PPrism :: (b -> t) -> (s -> Either t a) -> Prism s t a b
--prism bt seta = dimap seta (either pure (fmap bt)) . right'

data MarketP a b s t = MarketP (b ~> t) (s ~> Either t a)

instance PFunctor (MarketP a b s) where
  type Fmap f ('MarketP bt slr) = 'MarketP (f :.: bt) (BifirstSym1 f :.: slr )

instance PProfunctor (MarketP a b) where
  type Dimap f g ('MarketP bt slr) = 'MarketP (g :.: bt) (BifirstSym1 g :.: slr :.: f)

instance PChoice (MarketP a b) where
  type Right' ('MarketP bt slr) =
         'MarketP (TyCon1Sym1 'Right :.: bt)
         (Either'Sym2
           (TyCon1Sym1 'Left :.: TyCon1Sym1 'Left)
           (Either'Sym2 (TyCon1Sym1 'Left :.: TyCon1Sym1 'Right) (TyCon1Sym1 'Right) :.: slr)
         )
{-
type family LeftP :: PPrism (Either a c) (Either b c) a b where
  LeftP = MkPrism
            (TyCon1Sym1 'Left)
            (Either'Sym2 (TyCon1Sym1 'Right) (TyCon1Sym1 'Left :.: TyCon1Sym1 'Right))

-- :kind! MkPrism (TyCon1Sym1 'Just) (Maybe'Sym2 ('Left 'Nothing) (TyCon1Sym1 'Right))
type family MkPrism (bt :: b ~> t) (slr :: s ~> Either t a) :: PPrism s t a b where
--type family MkPrism bt slr where
  MkPrism bt seta =
     DimapSym2
           seta
           (Either'Sym2 PureSym0 (FmapSym1 bt))
     :.: Right'Sym0

type PPrism s t a b = forall p f . p a (f b) ~> p s (f t)
type PPrism' s a = forall p f . p a (f a) ~> p s (f s)

type family MkPrism' (bt :: b ~> s) (slr :: s ~> Maybe a) :: PPrism s s a b where
--type family MkPrism bt slr where
  MkPrism' bs sma = MkPrism bs Undefined


--type family UnPrism (p :: Prism s t a b) :: (b ~> t, s ~> Either t a) where
--  UnPrism p =

-}
{-
type APrismP s t a b = MarketP a b a (Identity b) ~> MarketP a b s (Identity t)

unPrism :: Prism s t a b -> (b -> t, s -> Either t a)
unPrism p =
  let -- bft   :: b -> Identity t
      -- setfa :: s -> Either (Identity t) a
      Market bft setfa = p (Market Identity Right)
      -- bt    :: b -> t
      -- seta  :: s -> Either t a
      bt = runIdentity . bft
      seta = either (Left . runIdentity) Right . setfa
  in (bt, seta)
-}
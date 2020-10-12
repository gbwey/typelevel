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
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NoStarIsType #-}
module PAlternative where
import GHC.TypeLits ( type (<=?) )
import Data.Kind (Type)
import Data.Functor.Compose ( Compose(Compose) )
import PCore
import PFunctor
import PFoldable
import PSemigroup
import PApplicative
import qualified Data.Semigroup as SG
import Data.Proxy ( Proxy(..) )
import Control.Applicative ( ZipList(ZipList) )

class PApplicative f => PAlternative (f :: Type -> Type) where
  type family (<|>) (arg :: f a) (arg1 :: f a) :: f a
--  type (<|>) x y = TypeError ('Text "PAlternative (<|>) is undefined x=" ':<>: 'ShowType x ':<>: 'Text " y=" ':<>: 'ShowType y)
  infixl 3 <|>

  type family Empty :: f a
--  type Empty = TypeError ('Text "PAlternative Empty is undefined")

  type family Optional (arg :: f a) :: f (Maybe a)
  type Optional fa = TyCon1Sym1 'Just <$> fa

-- dont know how to enforce Foldable t! need a separate class
class (PFoldable t, PAlternative f) => AsumC t f where
  type family Asum (arg :: t (f a)) :: f a
  type Asum tfa = Foldr AlternativeSym0 Empty (ToList tfa)

instance (PFoldable t, PAlternative f) => AsumC t f

data AlternativeSym0 :: f a ~> f a ~> f a
type instance Apply AlternativeSym0 x = AlternativeSym1 x

data AlternativeSym1 :: f a -> f a ~> f a
type instance Apply (AlternativeSym1 x) y = x <|> y

instance PAlternative [] where
  type Empty = '[]
  type as <|> bs = as <> bs

instance PAlternative ZipList where
  type Empty = 'ZipList '[]
  type 'ZipList as <|> 'ZipList bs =
         If (Length as <=? Length bs)
            ('ZipList (as <> Drop (Length as) bs))
            ('ZipList as)

instance PAlternative Maybe where
  type Empty = 'Nothing
  type 'Just a <|> _ = 'Just a
  type 'Nothing <|> y = y

instance PAlternative (Compose (g :: Type -> Type) h) where
  type Empty = 'Compose (Pure Empty)
  type 'Compose fga <|> 'Compose fga1 = 'Compose (AlternativeSym0 <$> fga <*> fga1)

instance PAlternative Proxy where
  type Empty = 'Proxy
  type 'Proxy <|> 'Proxy = 'Proxy

instance PAlternative SG.Option where
  type Empty = 'SG.Option 'Nothing
  type 'SG.Option x <|> 'SG.Option y = 'SG.Option (x <|> y)

-- type level parser on strings treating strings of length one as a character
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
module PParser where
import GHC.TypeNats (type (+), type(-))
import GHC.TypeLits (Symbol,Nat,TypeError,ErrorMessage(..),type (<=?))
import PCore
import PEnum
import PChar
import PEq
import POrd
import PNum
import PMonad
import PApplicative
import PAlternative
import PFunctor
import PBifunctor
import PMonoid
import PSemigroup
import PFoldable
import PStateLR
import qualified Data.Semigroup as SG
import qualified Data.Symbol.Ascii as S
import Data.Type.Equality ( type (==) )

type family PP s a where
  PP s a = STLR [Symbol] s a

type family PP' a where
  PP' a = STLR [Symbol] [Symbol] a

type family PSym (arg :: a ~> Bool) :: PP [a] a where
  PSym p = 'STLR (PSym'Sym1 p)

data PSymSym0 :: (a ~> Bool) ~> PP [a] a
type instance Apply PSymSym0 x = PSym x

type family PSym' (arg :: a ~> Bool) (st :: s) :: Either [Symbol] (a, [a]) where
  PSym' _ '[] = 'Left '["PSym: no data found"]
  PSym' p (a ': as) = If (p @@ a) ('Right '(a,as)) ('Left '["PSym: no match"])

data PSym'Sym0 :: (a ~> Bool) ~> s ~> Either [Symbol] (a, [a])
type instance Apply PSym'Sym0 x = PSym'Sym1 x

data PSym'Sym1 :: (a ~> Bool) -> s ~> Either [Symbol] (a, [a])
type instance Apply (PSym'Sym1 x) y = PSym' x y


type family Sym (arg :: a) :: PP [a] a where
  Sym a = PSym (EqSym1 a)

data SymSym0 :: a ~> PP [a] a
type instance Apply SymSym0 x = Sym x

type family NotP (arg :: STLR e s a) :: STLR e s () where
  NotP p = ((TyCon1Sym1 'Just <$> p) <|> Pure 'Nothing) >>= Maybe'Sym2 (Pure '()) (KSym1 (FailMsg "NotP failed"))

type family FailMsg (arg :: e) :: PP s a where
  FailMsg e = 'STLR (KSym1 ('Left '[e]))

type family AnySym :: STLR e [a] a where
  AnySym = PSym (KSym1 'True)

type family OneOf (arg1 :: [STLR e s a]) :: STLR e s a where
  OneOf '[] = Empty
  OneOf (x ': xs) = x <|> OneOf xs

type family OneOfVals x where
  OneOfVals as = PSym (FlipSym2 ElemSym0 as)

type family NotOneOfVals x where
  NotOneOfVals as = PSym (NotSym0 :.: FlipSym2 ElemSym0 as)

-- cant use Many / Some cos they loop -- strict language!
type family Token :: PP [Symbol] Symbol where
  Token = MconcatSym0 <$> 'STLR (TakeWhile1PSym1 (NotSym0 :.: IsSpacesSym0))

type family IsSpaces (xs :: Symbol) :: Bool where
--  IsSpaces xs = SUnWrap (FoldMap (TyCon1Sym1 'SG.All :.: FlipSym2 ElemSym0 '[" "]) (S.ToList xs))
  IsSpaces xs = IsSymbolClass (FlipSym2 ElemSym0 '[" "]) xs

data IsSpacesSym0 :: Symbol ~> Bool
type instance Apply IsSpacesSym0 xs = IsSpaces xs

type family IsSymbolClass (p :: Symbol ~> Bool) (xs :: Symbol) :: Bool where
  IsSymbolClass p xs = SUnWrap (FoldMap (TyCon1Sym1 'SG.All :.: p) (S.ToList xs))

data IsSymbolClassSym0 :: (Symbol ~> Bool) ~> Symbol ~> Bool
type instance Apply IsSymbolClassSym0 x = IsSymbolClassSym1 x

data IsSymbolClassSym1 :: (Symbol ~> Bool) -> Symbol ~> Bool
type instance Apply (IsSymbolClassSym1 x) y = IsSymbolClass x y


type family IsUpper (xs :: Symbol) :: Bool where
  IsUpper xs = IsSymbolClass (FlipSym2 ElemSym0 CharSetUpper) xs

data IsUpperSym0 :: Symbol ~> Bool
type instance Apply IsUpperSym0 xs = IsUpper xs


type family IsLower (xs :: Symbol) :: Bool where
  IsLower xs = IsSymbolClass (FlipSym2 ElemSym0 CharSetLower) xs

data IsLowerSym0 :: Symbol ~> Bool
type instance Apply IsLowerSym0 xs = IsLower xs


type family IsChar (xs :: Symbol) :: Bool where
  IsChar xs = IsUpper xs || IsLower xs

data IsCharSym0 :: Symbol ~> Bool
type instance Apply IsCharSym0 xs = IsChar xs


type family IsDigit (xs :: Symbol) :: Bool where
  IsDigit xs = IsSymbolClass (FlipSym2 ElemSym0 CharSetDigit) xs

data IsDigitSym0 :: Symbol ~> Bool
type instance Apply IsDigitSym0 xs = IsDigit xs


type family IsPunctuation (xs :: Symbol) :: Bool where
  IsPunctuation xs = IsSymbolClass (FlipSym2 ElemSym0 CharSetPunctuation) xs

data IsPunctuationSym0 :: Symbol ~> Bool
type instance Apply IsPunctuationSym0 xs = IsPunctuation xs


type family IsEof :: PP [a] Bool where
  IsEof = 'STLR IsEof'

data IsEof' :: [a] ~> Either [Symbol] (Bool, [a])
type instance Apply IsEof' '[] = 'Right '( 'True, '[] )
type instance Apply IsEof' (a ': as) = 'Right '( 'False, a ': as )

type family Eof where
  Eof = 'STLR Eof'

data Eof' :: [a] ~> Either [Symbol] ((), [a])
type instance Apply Eof' '[] = 'Right '( '(), '[] )
type instance Apply Eof' (_ ': _) = 'Left '["Eof: expected eof"]

type family CapitalWord where
  CapitalWord = (MconcatSym0 :..: TyCon2Sym1 '(:))
          <$> PSym IsUpperSym0 <?> "missing uppercase letter"
          <*> 'STLR (TyCon1Sym1 'Right :.: TakeWhilePSym1 IsLowerSym0)

type family CapitalWordC where
  CapitalWordC = (MconcatSym0 :..: TyCon2Sym1 '(:))
          <$> PSym IsUpperSym0 <?> "missing uppercase letter"
          <*> 'STLR (TyCon1Sym1 'Right :.: TakeWhilePSym1 IsLowerSym0)
          <* Eof -- peek (eof <|> (() <$ psym isSpace))


-- Fixed: todo: Ap is broken? should do one after the other but does it in parallel
type family CapitalWord1 where
  CapitalWord1 = Fmap MconcatSym0 (Ap (Ap (Pure ConsSym0) (PSym IsUpperSym0)) ('STLR (TyCon1Sym1 'Right :.: TakeWhilePSym1 IsLowerSym0)))

type family CapitalWord2 where
  CapitalWord2 = Fmap (UnCurrySym1 (MconcatSym0 :..: ConsSym0))
                      (ApPair
                         (PSym IsUpperSym0)
                         ('STLR (TyCon1Sym1 'Right :.: TakeWhilePSym1 IsLowerSym0))
                       )

-- always succeeds: if you want Some then do one then TakeWhileP
type family TakeWhileP (p :: a ~> Bool) (xs :: [a]) :: ([a], [a]) where
  TakeWhileP _ '[] = '( '[], '[] )
  TakeWhileP p (a ': as) = If (p @@ a) ('( '[a], '[] ) <> TakeWhileP p as) '( '[], a ': as )

data TakeWhilePSym0 :: (a ~> Bool) ~> [a] ~> ([a], [a])
type instance Apply TakeWhilePSym0 x = TakeWhilePSym1 x

data TakeWhilePSym1 :: (a ~> Bool) -> [a] ~> ([a], [a])
type instance Apply (TakeWhilePSym1 x) y = TakeWhileP x y


type family TakeWhile1P (p :: a ~> Bool) (xs :: [a]) :: Either [Symbol] ([a], [a]) where
  TakeWhile1P _ '[] = 'Left '["TakeWhile1P: no data"]
  TakeWhile1P p (a ': as) =
    If (p @@ a)
       ('Right ('( '[a], '[] ) <> TakeWhileP p as))
       ('Left '["TakeWhile1P: no match on first value"])

data TakeWhile1PSym0 :: (a ~> Bool) ~> [a] ~> Either [Symbol] ([a], [a])
type instance Apply TakeWhile1PSym0 x = TakeWhile1PSym1 x

data TakeWhile1PSym1 :: (a ~> Bool) -> [a] ~> Either [Symbol] ([a], [a])
type instance Apply (TakeWhile1PSym1 x) y = TakeWhile1P x y


type family (p :: STLR [e] s a) <?> (msg :: Symbol) :: STLR [e] s a where
  'STLR p <?> msg = 'STLR (BifirstSym1 (ConsSym1 msg) :.: p)

infixr 8 <?>

type family UnP (arg :: STLR e [Symbol] a) (ss :: Symbol) :: Either e (a, Symbol) where
  UnP ('STLR x) ss = SecondSym1 MconcatSym0 <$> (x @@ S.ToList ss)

type family ManyP (p :: PP [a] a) :: PP [a] [a] where
  ManyP ('STLR p) = 'STLR (ManyP'Sym1 p)

data ManyP'Sym0 :: ([a] ~> Either [Symbol] (a, [a])) ~> [a] ~> Either [Symbol] ([a], [a])
type instance Apply ManyP'Sym0 x = ManyP'Sym1 x

data ManyP'Sym1 :: ([a] ~> Either [Symbol] (a, [a])) -> [a] ~> Either [Symbol] ([a], [a])
type instance Apply (ManyP'Sym1 p) as = ManyP' p (p @@ as) as -- Either' (p @@ a) 'Right '( '[], '[])

type family ManyP' (p :: [a] ~> Either [Symbol] (a, [a])) (lr :: Either [Symbol] (a, [a])) (as :: [a]) :: Either [Symbol] ([a], [a]) where
  ManyP' _ ('Left _) as0 = 'Right '( '[], as0 )
  ManyP' p ('Right '(a, as)) _ = FirstSym1 (ConsSym1 a) <$> ManyP' p (p @@ as) as

type family SomeP (p :: PP [a] a) :: PP [a] [a] where
  SomeP ('STLR p) = ConsSym0 <$> 'STLR p <*> 'STLR (ManyP'Sym1 p)

type family IntP :: PP [Symbol] Nat where
  IntP = Fmap NatsToNatSym0 (FmapSym1 SymbolToNatSym0 <$> SomeP (PSym IsDigitSym0))

type family NatsToNat (arg :: [Nat]) :: Nat where
  NatsToNat xs = Foldl (SumSym0 :.: ProductSym1 10) 0 xs

data NatsToNatSym0 :: [Nat] ~> Nat
type instance Apply NatsToNatSym0 x = NatsToNat x

type family SymbolToNat (arg :: Symbol) :: Nat where
  SymbolToNat "0" = 0
  SymbolToNat "1" = 1
  SymbolToNat "2" = 2
  SymbolToNat "3" = 3
  SymbolToNat "4" = 4
  SymbolToNat "5" = 5
  SymbolToNat "6" = 6
  SymbolToNat "7" = 7
  SymbolToNat "8" = 8
  SymbolToNat "9" = 9
  SymbolToNat e = TypeError ('Text "SymbolToNat: Invalid digit found[" ':<>: 'ShowType e ':<>: 'Text "]")

data SymbolToNatSym0 :: Symbol ~> Nat
type instance Apply SymbolToNatSym0 x = SymbolToNat x


type family IntP' :: PP [Symbol] Int' where
  IntP' = Int'Sym0 <$> SignP <*> IntP

type family SignP :: PP [Symbol] Bool where
  SignP = ('True <$ Sym "+") <|> ('False <$ Sym "-") <|> Pure 'True

type family Negate (x :: Int') :: Int' where
  Negate ('Int' b n) = 'Int' (Not b) n

type family Abs (x :: Int') :: Int' where
  Abs ('Int' _ n) = 'Int' 'True n

type family IntSign afa s where
  IntSign afa ('Int' b n) = FlipSym2 (TyCon2Sym1 'Int') n <$> (afa @@ b)

data IntSignSym0 :: (Bool ~> f Bool) ~> Int' ~> f Int'
type instance Apply IntSignSym0 x = IntSignSym1 x

data IntSignSym1 :: (Bool ~> f Bool) -> Int' ~> f Int'
type instance Apply (IntSignSym1 x) y = IntSign x y

-- todo: not a great lens since we can change the number value but doesnt take the sign into account
-- would need to provide the sign else we cannot do this properly
type family IntNum afa s where
  IntNum afa ('Int' b n) = TyCon2Sym2 'Int' b <$> (afa @@ n)

data IntNumSym0 :: (Nat ~> f Nat) ~> Int' ~> f Int'
type instance Apply IntNumSym0 x = IntNumSym1 x

data IntNumSym1 :: (Nat ~> f Nat) -> Int' ~> f Int'
type instance Apply (IntNumSym1 x) y = IntNum x y



-- 0 can be +ve / -ve
instance PNum Int' where
  type FromInteger n = 'Int' 'True n
  type ToInteger ('Int' 'True n) = n
  type ToInteger ('Int' 'False n) = FailWhen (n==0) ('Text "Int': ToInteger: negative number for n=-" ':<>: 'ShowType n) n
  type PAdd ('Int' 'True n) ('Int' 'True n1) =  'Int' 'True (PAdd n n1)
  type PAdd ('Int' 'True n) ('Int' 'False n1) = If (n <=? n1) ('Int' 'False (n1 - n)) ('Int' 'True (n - n1))
  type PAdd ('Int' 'False n) ('Int' 'True n1) = If (n <=? n1) ('Int' 'True (n1 - n)) ('Int' 'False (n - n1))
  type PAdd ('Int' 'False n) ('Int' 'False n1) = 'Int' 'False (PAdd n n1)
  type PSub x ('Int' b1 n1) = PAdd x ('Int' (Not b1) n1)
  type PMult ('Int' b n) ('Int' b1 n1) = 'Int' (b == b1) (PMult n n1)


instance PEq Int' where
  type 'Int' 'True n === 'Int' 'True n1 = n == n1
  type 'Int' 'False n === 'Int' 'False n1 = n == n1
  type 'Int' 'True n === 'Int' 'False n1 = n == 0 && n1 == 0
  type 'Int' 'False n === 'Int' 'True n1 = n == 0 && n1 == 0

instance POrd Int' where
  type LessThanOrEqual ('Int' 'True n) ('Int' 'True n1) = LessThanOrEqual n n1
  type LessThanOrEqual ('Int' 'False n) ('Int' 'False n1) = LessThanOrEqual n1 n
  type LessThanOrEqual ('Int' 'True n) ('Int' 'False n1) = n == 0 && n1 == 0
  type LessThanOrEqual ('Int' 'False _) ('Int' 'True _) = 'True

instance PEnum Int' where
  type ToEnum n = 'Int' 'True n

  type FromEnum ('Int' 'True n) = n
  type FromEnum ('Int' 'False n) = FailWhen (n==0) ('Text "FromEnum Int' failed cos negative n=-" ':<>: 'ShowType n) n

  type ESucc ('Int' 'True n) = 'Int' 'True (n + 1)
  type ESucc ('Int' 'False n) = If (n==0) ('Int' 'True 1) ('Int' 'False (n - 1))

  type EPred ('Int' 'True n) = If (n==0) ('Int' 'False 1) ('Int' 'True (n - 1))
  type EPred ('Int' 'False n) = 'Int' 'False (n + 1)

  type EnumFromTo x y =
         UnOrdering (Compare x y)
                    (Iterate (1 + FromEnum (PSub y x)) ESuccSym0 x)
                    '[]
                    (FailWhen  'True ('Text "EnumFromTo Int' failed cos x<y x=" ':<>: 'ShowType x ':<>: 'Text " y=" ':<>: 'ShowType y) Undefined)

  type EnumFromThenTo x y z =
         EnumFromThenToImpl
           (LT' x y)
           (FromEnum (EPred (PSub y x)))  -- cant use default definition cos -ve numbers not defined in Nat so have to stay in Int'
           (EnumFromTo x z)



data Double' = Double' { dPositive :: !Bool,  dIntegral :: !Nat, dFractional :: !Nat }

data Double'Sym0 :: Bool ~> Nat ~> Nat ~> Double'
type instance Apply Double'Sym0 x = Double'Sym1 x

data Double'Sym1 :: Bool -> Nat ~> Nat ~> Double'
type instance Apply (Double'Sym1 x) y = Double'Sym2 x y

data Double'Sym2 :: Bool -> Nat -> Nat ~> Double'
type instance Apply (Double'Sym2 x y) z = 'Double' x y z


data Int' = Int' { iPositive :: !Bool,  iInt :: !Nat }

data Int'Sym0 :: Bool ~> Nat ~> Int'
type instance Apply Int'Sym0 x = Int'Sym1 x

data Int'Sym1 :: Bool -> Nat ~> Int'
type instance Apply (Int'Sym1 x) y = 'Int' x y




data IP = IP !Nat !Nat !Nat !Nat

data IPSym0 :: Nat ~> Nat ~> Nat ~> Nat ~> IP
type instance Apply IPSym0 x = IPSym1 x

data IPSym1 :: Nat -> Nat ~> Nat ~> Nat ~> IP
type instance Apply (IPSym1 x) y = IPSym2 x y

data IPSym2 :: Nat -> Nat -> Nat ~> Nat ~> IP
type instance Apply (IPSym2 x y) z = IPSym3 x y z

data IPSym3 :: Nat -> Nat -> Nat -> Nat ~> IP
type instance Apply (IPSym3 x y z) w = 'IP x y z w

type family IPP :: PP [Symbol] IP where
  IPP = IPSym0
        <$> IntP
        <* Sym "." <?> "missing first dot"
        <*> IntP
        <* Sym "." <?> "missing second dot"
        <*> IntP
        <* Sym "." <?> "missing third dot"
        <*> IntP

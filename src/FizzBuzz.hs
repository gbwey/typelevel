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

module FizzBuzz where
import GHC.TypeNats
import GHC.TypeLits hiding (natVal, natVal')
import PCore
import Data.Type.Equality
import PChar
import PSemigroup
import Data.Proxy
import PFoldable

type family Fizz (n :: Nat) :: Maybe Symbol where
  Fizz n = If (n `Mod` 3 == 0) ('Just "Fizz") 'Nothing

type family Buzz (n :: Nat) :: Maybe Symbol where
  Buzz n = If (n `Mod` 5 == 0) ('Just "Buzz") 'Nothing

type family FizzBuzz (n :: Nat) :: Symbol where
  FizzBuzz n = FromMaybe (NatToString n) (Fizz n <> Buzz n)
  --FizzBuzz n = FromMaybe (NatToString n) ((FizzSym0 <> BuzzSym0) @@ n)

data FizzBuzzSym0 :: Nat ~> Symbol
type instance Apply FizzBuzzSym0 x = FizzBuzz x

data FizzSym0 :: Nat ~> Maybe Symbol
type instance Apply FizzSym0 x = Fizz x

data BuzzSym0 :: Nat ~> Maybe Symbol
type instance Apply BuzzSym0 x = Buzz x

--t1 :: ((FizzBuzz 15 ~ "ss") => ()) -> ()
--t1 () = ()

t2 :: forall n . KnownSymbol (FizzBuzz n) => String
t2 = symbolVal (Proxy @(FizzBuzz n))

{-
>t2 @15
"FizzBuzz"
it :: String
>t2 @14
"14"
it :: String
>t2 @13
"13"
it :: String
-}

t3 :: forall (ns :: [Nat]) ss . (ss ~ Map FizzBuzzSym0 ns, GetStrings ss, FoldMap KnownSymbolSym0 ss) => [String]
t3 = getStrings @ss

{-
>t3 @'[1,5,3,4,15]
["1","Buzz","Fizz","4","FizzBuzz"]
it :: [String]

>:kind! Map (AmpSym2 Id FizzBuzzSym0) (EnumFromTo 0 15)
Map (AmpSym2 Id FizzBuzzSym0) (EnumFromTo 0 15) :: [(Nat, Symbol)]
= '['(0, "FizzBuzz"), '(1, "1"), '(2, "2"), '(3, "Fizz"),
    '(4, "4"), '(5, "Buzz"), '(6, "Fizz"), '(7, "7"), '(8, "8"),
    '(9, "Fizz"), '(10, "Buzz"), '(11, "11"), '(12, "Fizz"),
    '(13, "13"), '(14, "14"), '(15, "FizzBuzz")]
-}
type FizzList = '["F","i","z","z"]
type BuzzList = '["B","u","z","z"]

{-
>:kind! P.Map (P.AmpSym2 P.ISym0 P.FizzBuzzSym0) (P.EnumFromTo 0 50)
P.Map (P.AmpSym2 P.ISym0 P.FizzBuzzSym0) (P.EnumFromTo 0 50) :: [(Nat,
                                                                  Symbol)]
= '['(0, "FizzBuzz"), '(1, "1"), '(2, "2"), '(3, "Fizz"),
    '(4, "4"), '(5, "Buzz"), '(6, "Fizz"), '(7, "7"), '(8, "8"),
    '(9, "Fizz"), '(10, "Buzz"), '(11, "11"), '(12, "Fizz"),
    '(13, "13"), '(14, "14"), '(15, "FizzBuzz"), '(16, "16"),
    '(17, "17"), '(18, "Fizz"), '(19, "19"), '(20, "Buzz"),
    '(21, "Fizz"), '(22, "22"), '(23, "23"), '(24, "Fizz"),
    '(25, "Buzz"), '(26, "26"), '(27, "Fizz"), '(28, "28"),
    '(29, "29"), '(30, "FizzBuzz"), '(31, "31"), '(32, "32"),
    '(33, "Fizz"), '(34, "34"), '(35, "Buzz"), '(36, "Fizz"),
    '(37, "37"), '(38, "38"), '(39, "Fizz"), '(40, "Buzz"),
    '(41, "41"), '(42, "Fizz"), '(43, "43"), '(44, "44"),
    '(45, "FizzBuzz"), '(46, "46"), '(47, "47"), '(48, "Fizz"),
    '(49, "49"), '(50, "Buzz")]
-}
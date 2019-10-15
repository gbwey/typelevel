{-# LANGUAGE OverloadedStrings, DataKinds, TypeOperators, TypeApplications #-}
module Main where
import Data.Proxy
import PCombinators
import Data.Functor.Identity
import GHC.TypeNats
import Data.Proxy
import Test.Tasty
import Test.Tasty.HUnit

main :: IO ()
main = suite

suite :: IO ()
suite = defaultMain $ testGroup "Spec"
  [ testCase "typelevel.nats" $ (@?=) (getNats @'[2,4,3]) [2,4,3]
  , testCase "typelevel.strings" $ (@?=) (getStrings @'["ab","c","def"]) ["ab","c","def"]
  , testCase "typelevel.nats.enum.1" $ (@?=) (getNats @(EnumFromTo 12 15)) [12,13,14,15]
  , testCase "typelevel.nats.enum.2" $ (@?=) (getNats @(EnumFromTo 12 100)) [12..100]
  , testCase "typelevel.nats.mapfst" $ (@?=) (getNats @(Map FstSym0 '[ '(1,"ss"), '(77,"ddd"), '(200,"last") ])) [1,77,200]
  , testCase "typelevel.strings.mapsnd" $ (@?=) (getStrings @(Map SndSym0 '[ '(1,"ss"), '(77,"ddd"), '(200,"last") ])) ["ss","ddd","last"]
  , testCase "typelevel.natval" $ (@?=) (natVal (Proxy @(SUnWrap (FoldMap (SSumSym0 :.: FstSym0) '[ '(1,"ss"), '(77,"ddd"), '(200,"last") ])))) 278
  ]

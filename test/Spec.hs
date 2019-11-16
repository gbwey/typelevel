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
suite = defaultMain $ testGroup "TypeLevel"
  [ testCase "nats" $ (@?=) (getNats @'[2,4,3]) [2,4,3]
  , testCase "strings" $ (@?=) (getStrings @'["ab","c","def"]) ["ab","c","def"]
  , testCase "nats.enum.1" $ (@?=) (getNats @(EnumFromTo 12 15)) [12,13,14,15]
  , testCase "nats.enum.2" $ (@?=) (getNats @(EnumFromTo 12 100)) [12..100]
  , testCase "nats.mapfst" $ (@?=) (getNats @(Map FstSym0 '[ '(1,"ss"), '(77,"ddd"), '(200,"last") ])) [1,77,200]
  , testCase "strings.mapsnd" $ (@?=) (getStrings @(Map SndSym0 '[ '(1,"ss"), '(77,"ddd"), '(200,"last") ])) ["ss","ddd","last"]
  , testCase "natval" $ (@?=) (natVal (Proxy @(SUnWrap (FoldMap (SSumSym0 :.: FstSym0) '[ '(1,"ss"), '(77,"ddd"), '(200,"last") ])))) 278
  ]

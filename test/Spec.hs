{-# LANGUAGE OverloadedStrings, DataKinds, TypeOperators, TypeApplications #-}
module Main where
import Data.Proxy
import PCombinators
import Data.Functor.Identity
import GHC.TypeNats
import Data.Proxy
import EasyTest

main :: IO ()
main = run suite

suite :: Test ()
suite = tests
  [ scope "typelevel.nats" $ expectEq (getNats @'[2,4,3]) [2,4,3]
  , scope "typelevel.strings" $ expectEq (getStrings @'["ab","c","def"]) ["ab","c","def"]
  , scope "typelevel.nats.enum.1" $ expectEq (getNats @(EnumFromTo 12 15)) [12,13,14,15]
  , scope "typelevel.nats.enum." $ expectEq (getNats @(EnumFromTo 12 100)) [12..100]
  , scope "typelevel.nats.mapfst" $ expectEq (getNats @(Map FstSym0 '[ '(1,"ss"), '(77,"ddd"), '(200,"last") ])) [1,77,200]
  , scope "typelevel.strings.mapsnd" $ expectEq (getStrings @(Map SndSym0 '[ '(1,"ss"), '(77,"ddd"), '(200,"last") ])) ["ss","ddd","last"]
  , scope "typelevel.natval" $ expectEq (natVal (Proxy @(SUnWrap (FoldMap (SSumSym0 :.: FstSym0) '[ '(1,"ss"), '(77,"ddd"), '(200,"last") ])))) 278
  ]

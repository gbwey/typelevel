{-# LANGUAGE DataKinds, TypeOperators, TypeApplications #-}
module Main where
import Data.Proxy
import PCombinators
import Data.Functor.Identity
import GHC.TypeNats
import Data.Proxy

main :: IO ()
main = putStrLn "Test suite not yet implemented"


zz = getNats @'[2,4,3] == [2,4,3]

zz1 = getStrings @'["ab","c","def"] == ["ab","c","def"]

zz2 = getNats @(EnumFromTo 12 15) == [12,13,14,15]
zz3 = getNats @(EnumFromTo 12 100) == [12..100]

zz4 = getNats @(Map FstSym0 '[ '(1,"ss"), '(77,"ddd"), '(200,"last") ]) == [1,77,200]
zz4' = getStrings @(Map SndSym0 '[ '(1,"ss"), '(77,"ddd"), '(200,"last") ]) == ["ss","ddd","last"]

zz5 = natVal (Proxy @(SUnWrap (FoldMap (SSumSym0 :.: FstSym0) '[ '(1,"ss"), '(77,"ddd"), '(200,"last") ]))) == 278
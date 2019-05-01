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
-- {-# LANGUAGE KindSignatures #-} -- implied by TypeFamilies
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
-- {-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
module Test1 where
import Data.Type.Equality
import GHC.TypeNats
import GHC.TypeLits hiding (natVal,natVal')
import PCombinators
import VectorN
import qualified Data.Symbol.Ascii as S
--import qualified Data.Symbol.Utils as S -- just classes for extracting values
import Data.List.NonEmpty (NonEmpty(..))
import Data.Functor.Compose
import Data.Functor.Const
import Data.These
import qualified Data.Monoid as MM
import qualified Data.Semigroup as SG
import Data.Ord

type family SAS :: STA S0 A0 where
  SAS = 'STA (KSym1 '( 'A0, 'S0))

type family SAS1 :: S0 ~> (A0, S0) where
  SAS1 = KSym1 '( 'A0, 'S0)

type family AMB :: A0 ~> STA S0 B0 where
  AMB = KSym1 ('STA (KSym1 '( 'B0, 'S1)))


-- using PEq because we are using POrd : otherwise a lot safer to use DTE.==
-- PEq has correct implementations for equality for Int' (0 can be negative/positive -- they are the same for PEq and different for DTE.==)
-- and SG.Arg which uses ord and equality based on first arg only!
t111 :: ((
   AllF (PEqSym1 4) '[SuccSym0 @@ 3, SuccSym1 3] ~ 'True
  ,AllF (PEqSym1 10) '[SumSym0 @@ 3 @@ 7, SumSym1 3 @@ 7, 3 + 7] ~ 'True
  ,AllF (PEqSym1 '(13, "abc")) '[FirstSym0 @@ SuccSym0 @@ '(12, "abc"), FirstSym1 SuccSym0 @@ '(12, "abc"), First SuccSym0 '(12, "abc")] ~ 'True
  ,AllF (PEqSym1 '("xyz", 13)) '[(('R (PairSym1 "xyz" :.: PredSym0)) & UnRSym0) @@ 14] ~ 'True
  ,AllF (PEqSym1 ('S ('S ('S ('S ('S 'Z)))))) '[PSucc (ToN 4), FromInteger (PSucc 4), PPred (ToN 6), PSuccSym0 @@ ToN 4, PPredSym0 @@ ToN 6] ~ 'True
  ,AllF (PEqSym1 5) '[PSucc 4, PPred 6, ToInteger (PPred (ToN 6)), PSuccSym0 @@ 4, PPredSym0 @@ 6] ~ 'True
  ,AnyF (PEqSym1 4) '[1,2,4,5] ~ 'True
  ,AnyF (PEqSym1 7) '[1,2,4,5] ~ 'False
  ,((('R (PairSym1 "xyz" :.: PredSym0)) & UnRSym0) @@ 14) ~ '("xyz", 13)
  ,'[PSucc (ToN 4), FromInteger (PSucc 4), PPred (ToN 6), PSuccSym0 @@ ToN 4, PPredSym0 @@ ToN 6] ~ '[ 'S ('S ('S ('S ('S 'Z)))), 'S ('S ('S ('S ('S 'Z)))), 'S ('S ('S ('S ('S 'Z)))), 'S ('S ('S ('S ('S 'Z)))), 'S ('S ('S ('S ('S 'Z)))) ]
  ,(EqSym1 Nat @@ Nat) ~ 'True -- same as ==
  ,(Nat == Nat) ~ 'True
--  ,(Nat === Nat) ~ 'True   -- stuck
  ,(4 === 4) ~ 'True
  ,(4 === 5) ~ 'False
--  ,('[Int] === '[Bool]) ~ 'False -- stuck
  ,('[Int] == '[Bool]) ~ 'False
  ,([Int] == [Bool]) ~ 'False
  ,([Int] == [Int]) ~ 'True
--  ,([Int] === [Bool]) ~ 'False -- stuck
  ) => ()) -> ()
t111 x = x

t122 :: ((
    Break (EQSym1 4) (EnumFromTo 1 6) ~ '( '[1,2,3], '[4,5,6] )
   ,Span (LTSym1F 4) (EnumFromTo 2 7) ~ '( '[2,3], '[4,5,6,7] )
   ,Append '[2,3] '[4,5,6] ~ '[2,3,4,5,6]
   ,Lookup "k99" KV2 ~ 'Just 400
   ,Lookup "k9999" KV2 ~ 'Nothing
   ,Delete "k3" KV1 ~ '[ '("k2", 2), '("k99", 99), '("k5", 5)]
    ) => ()) -> ()
t122 x = x


t125 :: (UnionWith PAddSym0 KV1 KV2 ~
         '[ '("k2", 202)
          , '("k3", 3)
          , '("k99", 499)
          , '("k5", 5)
          , '("w1", 100)
          , '("w3", 300)
          , '("w5", 500)
          , '("w6", 600)] => ()) -> ()
t125 x = x

-- add version of vectorn that uses typelevel
t128 :: (FilterWithKey
          (On'Sym3
              AndSym0
              (FlipSym2 ElemSym0 '["k99","w5","k2"])
              (LTSym1F 500)
           ) KV2 ~ '[ '("k2", 200), '("k99", 400)] => ()) -> ()
t128 x = x

t129 :: (InsertWith PAddSym0 "k3" 12 KV1 ~ '[ '("k2", 2), '("k3", 15), '("k99", 99), '("k5", 5)] => ()) -> ()
t129 x = x

t130 :: (InsertWith PAddSym0 "k1" 17 KV1 ~ '[ '("k2", 2), '("k3", 3), '("k99", 99), '("k5", 5), '("k1", 17)] => ()) -> ()
t130 x = x

t131 :: (ElemAtMap 2 KV1 ~ 99 => ()) -> ()
t131 x = x

t132 :: (Singleton "aa" 2 `Union` Singleton "bb" 3 `Union` Singleton "bb" 4 ~ '[ '("aa", 2), '("bb", 3)] => ()) -> ()
t132 x = x

t133 :: (UnionWith PAddSym0 (Singleton "aa" 2 `Union` Singleton "bb" 3) (Singleton "bb" 4) ~ '[ '("aa", 2), '("bb", 7)] => ()) -> ()
t133 x = x

t134 :: (UnionsWith PAddSym0 '[Singleton "aa" 2, Singleton "bb" 3, Singleton "bb" 4] ~ '[ '("aa", 2), '("bb", 7)] => ()) -> ()
t134 x = x



type family KV1 where
  KV1 = ZipWithExact PairSym0 '["k2", "k3", "k99", "k5"] '[2,3,99,5]

type family KV2 where
  KV2 = ZipWithExact PairSym0 '["w1", "k2", "w3", "k99", "w5", "w6"] '[100,200,300,400,500,600]


t135 :: ((
           Reverse (S.ToList "sadf") ~ '["f","d","a","s"]
          ,(MconcatSym0 $ ReverseSym0 $ S.ToList "sadf") ~ "fdas"
          ,Traverse (TyCon1Sym1 'Just) (S.ToList "asdf") ~ 'Just '["a", "s", "d", "f"]
          ,Set (IxListSym1 4) 144 '[2,3,4] ~ '[2,3,4]
          ,Set (IxListSym1 1) 144 '[2,3,4] ~ '[2,144,4]
        ) => ()) -> ()
t135 x = x

t138 :: ((
          S.ReadNat "123" ~ 123
        , CmpSymbol "xyz" "xy" ~ 'GT
        , CmpSymbol "xyz" "xyz" ~ 'EQ
        , CmpSymbol "xy" "xyz" ~ 'LT
        ) => ()) -> ()
t138 x = x

t140 :: ((
          UnCons '[2,3,4] ~ 'Just '(2, '[3,4])
        , UnSnoc '[2,3,4] ~ 'Just '( '[2,3], 4 )
        , UnSnoc '[] ~ 'Nothing
        , UnCons '[] ~ 'Nothing
        , UnCons (2 ':| '[3,4]) ~ 'Just '(2, '[3,4])
        , UnSnoc (2 ':| '[3,4]) ~ 'Just '( '[2,3], 4 )
        , UnSnoc (7 ':| '[]) ~ 'Just '( '[], 7)
        , UnCons (6 ':| '[]) ~ 'Just '(6, '[])
        , ("sadf" <> "123" <> "xy") ~ "sadf123xy"
        ) => ()) -> ()
t140 x = x

t142 :: ((
          (UnPredicateX ('PredicateX (GTSym1F 2) <> 'PredicateX (LTSym1F 5)) @@ 1) ~ 'False
         ,(UnPredicateX ('PredicateX (GTSym1F 2) <> 'PredicateX (LTSym1F 5)) @@ 2) ~ 'False
         ,(UnPredicateX ('PredicateX (GTSym1F 2) <> 'PredicateX (LTSym1F 5)) @@ 3) ~ 'True
         ,(UnPredicateX ('PredicateX (GTSym1F 2) <> 'PredicateX (LTSym1F 5)) @@ 4) ~ 'True
         ,(UnPredicateX ('PredicateX (GTSym1F 2) <> 'PredicateX (LTSym1F 5)) @@ 5) ~ 'False
        ) => ()) -> ()
t142 x = x

t142a :: ((
          UnOption ('SG.Option ('Just ('SG.Sum 20)) <> 'SG.Option ('Just ('SG.Sum 12))) ~ 'Just ('SG.Sum 32)
         ,SUnWrap ('SG.Option ('Just ('SG.Sum 20)) <> 'SG.Option ('Just ('SG.Sum 12))) ~ 'Just 32
         ,SUnWrap (AA142a <> BB142a) ~ '( 'True, 48, 'Just "aa", 'Just "dd" )
         ,SUnWrap ('SG.Dual "abc" <> 'SG.Dual "def") ~ "defabc"
         ,SUnWrap (FoldMap (SAllSym0 :.: GTSym1F "ddd") '["abc","def","bbb","zz"]) ~ 'False
         ,SUnWrap (FoldMap (SAllSym0 :.: GTSym1F "a") '["abc","def","bbb","zz"]) ~ 'True
         ,SUnWrap (FoldMap (SAnySym0 :.: GTSym1F "ddd") '["abc","def","bbb","zz"]) ~ 'True
         ,SUnWrap (FoldMap (SAnySym0 :.: GTSym1F "zzz") '["abc","def","bbb","zz"]) ~ 'False
         ,SUnWrap ('( 'SG.Sum 32, 'SG.Dual "abc") <> '( 'SG.Sum 2, 'SG.Dual "def")) ~ '(34, "defabc")
         ,SUnWrap (CC142a <> DD142a <> EE142a) ~ FF142a
         ,SUnWrap (EE142a <> DD142a <> CC142a) ~ GG142a
         ,SUnWrap ('This ('SG.Sum 7) <> 'That ('SG.Min 19) <> 'These ('SG.Sum 5) ('SG.Min 2)) ~ 'These 12 2
         ,SUnWrap ('This ('SG.Sum 7) <> 'That ('SG.Min 19) <> 'That ('SG.Min 2)) ~ 'These 7 2
         ,SUnWrap ('This ('SG.Sum 7) <> 'That ('SG.Min 19) <> 'This ('SG.Sum 22)) ~ 'These 29 19
         ,SUnWrap ('Const ('SG.Sum 7) <> 'Const ('SG.Sum 12)) ~ 19
         ,Mempty ~ 'SG.Option 'Nothing
         ,Mempty ~ 'SG.Sum 0
         ,Mempty ~ 'SG.Sum 0
         ,Mempty ~ '( 'SG.Option 'Nothing, 'SG.Sum 0 )
         ,Mempty ~ '( 'SG.Dual ('SG.Option 'Nothing), 'SG.Dual ('SG.Any 'False), 'SG.All 'True )
         ,Mempty ~ '( 'MM.First 'Nothing, 'MM.Last 'Nothing )
         ,FoldMap1 (SingletonListSym0 :.: AmpSym2 SuccSym0 (KSym1 "x")) (3 ':| '[12,14,2]) ~ '[ '(4, "x"), '(13, "x"), '(15, "x"), '(3, "x") ]
        ) => ()) -> ()
t142a x = x

type AA142a =  '( 'SG.Any 'False, 'SG.Product 4, 'SG.Option ('Just ('SG.First "aa")), 'SG.Option ('Just ('SG.Last "bb")) )
type BB142a =  '( 'SG.Any 'True, 'SG.Product 12, 'SG.Option ('Just ('SG.First "cc")), 'SG.Option ('Just ('SG.Last "dd")) )
type CC142a = '( 'SG.Min 5, 'SG.Max 7, 'SG.Option ('Just ('MM.First ('Just "xyz"))) )
type DD142a = '( 'SG.Min 17, 'SG.Max 14, 'SG.Option ('Just ('MM.First ('Just "abc"))) )
type EE142a = '( 'SG.Min 2, 'SG.Max 3, 'SG.Option ('Just ('MM.First 'Nothing)) )
type FF142a = '(2, 14, 'Just ('Just "xyz"))
type GG142a = '(2, 14, 'Just ('Just "abc"))

t1251 :: ((
     (UnPredicateX ('PredicateX (LTSym1 10)) @@ 5) ~ 'False
    ,(UnPredicateX ('PredicateX (LTSym1 10)) @@ 15) ~ 'True
    ,(UnPredicateX (UnCurrySym1 PAddSym0 >$<('PredicateX (LTSym1 10))) @@ '(3,7)) ~ 'False
    ,(UnPredicateX (UnCurrySym1 PAddSym0 >$<('PredicateX (LTSym1 10))) @@ '(3,8)) ~ 'True
    ) => ()) -> ()
t1251 x = x

t1252 :: ((SuccSym0 <$> ('Compose ('Just '[2,3,4]))) ~ 'Compose ('Just '[3,4,5]) => ()) -> ()
t1252 x = x

t1253 :: (Sequence ('Just '[2,3,4]) ~ '[ 'Just 2, 'Just 3, 'Just 4] => ()) -> ()
t1253 x = x

t1254a :: ((
      Traverse (CaseWhenSym2 '[ '(BetweenSym2 0 2, ThisSym0), '(BetweenSym2 3 6, ThatSym0), '(GTSym1F 6, TheseSym1 999) ] ('These 0 0)) ('Just 23) ~ 'These 999 ('Just 23)
     ,Map (CaseFlipSym2 '[ '(0,"dude"), '(1, "hey"), '(2, "way") ] (Err "ss") :.: FlipSym2 ModSym0 3) '[1,4,5,2,3,99] ~ '["hey", "hey", "way", "way", "dude", "dude"]
      ) => ()) -> ()
t1254a x = x

t1254b :: (((Traverse (CaseWhenSym2 '[ '(BetweenSym2 0 2, ThisSym0), '(BetweenSym2 3 6, ThatSym0), '(GTSym1F 6, TheseSym1 999) ] ('These 0 0)) ('Compose ('Just ('Just 23)))) ~ 'These 999 ('Compose ('Just ('Just 23)))) => ()) -> ()
t1254b x = x

t1254c :: (((Traverse (CaseWhenSym2 '[ '(BetweenSym2 0 2, ThisSym0), '(BetweenSym2 3 6, ThatSym0), '(GTSym1F 6, TheseSym1 999) ] ('These 0 0)) ('Compose ('Just ('[23])))) ~ 'These 999 ('Compose ('Just ('[23])))) => ()) -> ()
t1254c x = x

t1257 :: ((Traverse (TyCon1Sym1 'Just :.: SuccSym0) '[2,3] ~ 'Just '[3,4]) => ()) -> ()
t1257 x = x

t1254 :: ((Traverse (CaseWhenSym2 '[ '(BetweenSym2 0 2, ThisSym0), '(BetweenSym2 3 6, ThatSym0), '(GTSym1F 6, TheseSym1 999) ] ('These 0 0))
              ('Compose ('Just '[0,3,4]))) ~ 'These 0 ('Compose ('Just '[3, 4])) => ()) -> ()
t1254 x = x

t1255 :: ((
           Between 3 6 2 ~ 'False
          ,Between 3 6 3 ~ 'True
          ,Between 3 6 4 ~ 'True
          ,Between 3 6 5 ~ 'True
          ,Between 3 6 6 ~ 'True
          ,Between 3 6 7 ~ 'False
          ,MinBound ~ 'Char1 "a"
          ,MaxBound ~ 'Char1 "z"
          ) => ()) -> ()
t1255 x = x

t1256 :: (Traverse (TyCon1Sym1 'Just :.: SuccSym0) ('Compose ('Just '[0,3,4])) ~ 'Just ('Compose ('Just '[1, 4, 5])) => ()) -> ()
t1256 x = x


t143 :: ((
    ('These "uu" 9 >>= KSym1 ('These "tt" 4)) ~ 'These "uutt" 4
   ,('These "uu" 9 >>= (TheseSym1 "tt" :.: SuccSym0)) ~ 'These "uutt" 10
   ) => ()) -> ()
t143 x = x

t146 :: ((
       (Compare 10 10 <> Compare "a" "b" <> Compare 'True 'False) ~ 'LT
       ,UnSTASym1 (SAS >>= AMB) @@ 'S0 ~ '( 'B0, 'S1 )
       ,FirstSym0 @@ SuccSym0 @@ '(1,"safd") ~ '(2, "safd")
       ,FirstSym1 SuccSym0 @@ '(1,"safd") ~ '(2, "safd")
       ,SecondSym0 @@ SuccSym0 @@ '("sadf",1) ~ '("sadf", 2)
       ,SecondSym1 SuccSym0 @@ '("sadf",1) ~ '("sadf", 2)
       ,Join '("ss", '("tt",33)) ~ '("sstt", 33)
       ,UnR (('R (KSym1 ('R SuccSym0))) >>= Id) @@ 123 ~ 124
       ,UnR (Join ('R (KSym1 ('R SuccSym0)))) @@ 12 ~ 13
       ,('SG.Arg 4 "b" `Compare` 'SG.Arg 4 "a") ~ 'EQ
       ,('SG.Arg 4 "z" `Compare` 'SG.Arg 5 "a") ~ 'LT
       ,('SG.Arg 4 "z" `Compare` 'SG.Arg 3 "a") ~ 'GT
       ,('Down 4 `Compare` 'Down 5) ~ 'GT
       ,('Down 4 `Compare` 'Down 3) ~ 'LT
       ,('Down 4 `Compare` 'Down 4) ~ 'EQ
        )  => ()) -> ()
t146 x = x

t148 :: ((
        (KSym1 (KSym1 'EQ) <> CompareSym0) @@ "c" @@ "b" ~ 'GT -- mappend across args: if m is a semigroup then so is a->b->m
       ,(CompareSym0 <> CompareSym0) @@ 10 @@ 12 ~ 'LT
       ,AmpSym2 (FlipSym2 SAppSym0 "xy") (PredSym0 :.: SReadNatSym0) @@ "123" ~ '("123xy",122)
       ,AmpSym2 (UnCurrySym1 Id) SndSym0 @@ '(PAddSym1 3,7) ~ '(10,7)
       ) => ()) -> ()
t148 x = x

t149 :: (((StarSym2 (FlipSym2 SAppSym0 "xy") (PredSym0 :.: SReadNatSym0) :.: DupSym0) @@ "123") ~ '("123xy",122)  => ()) -> ()
t149 x = x

t150 :: ((UnCurrySym1 AppSym0 :.: SwapSym0) @@ '(15,SuccSym0) ~ 16 => ()) -> ()
t150 x = x

t150a :: (
      (
      UnSTLR (Sym "a") @@ '[] ~ 'Left '["PSym: no data found"]
     ,UnSTLR (Sym "a") @@ '["x"] ~ 'Left '["PSym: no match"]
     ,UnSTLR (Sym "a") @@ '["a"] ~ 'Right '("a", '[])
     ,UnSTLR (Sym "a") @@ '["a","b","c"] ~ 'Right '("a", '["b", "c"])
     ,UnP CapitalWord "Xab__" ~ 'Right '("Xab", "__")
     ,UnP CapitalWord1 "Xab__" ~ 'Right '("Xab", "__")
     ,UnP CapitalWord2 "Xab__" ~ 'Right '("Xab", "__")
     ,UnP CapitalWord "ab" ~ 'Left '["missing uppercase letter", "PSym: no match"]
     ,UnP IsEof "" ~ 'Right '( 'True, "" )
     ,UnP IsEof "x" ~ 'Right '( 'False, "x" )

     ,UnP CapitalWordC "F" ~ 'Right '("F", "")
     ,UnP CapitalWordC "Fabcd" ~ 'Right '("Fabcd", "")
     ,UnP CapitalWordC "Fabcd_" ~ 'Left '["Eof: expected eof"]
     ,UnP Token "abcd  efg" ~ 'Right '("abcd", "  efg")
     ,UnP (ManyP (PSym IsLowerSym0)) "abc" ~ 'Right '( '["a", "b", "c"], "" )
     ,UnP (ManyP (PSym IsLowerSym0)) "abcEF" ~ 'Right '( '["a", "b", "c"], "EF" )

     ,UnP (SomeP (PSym IsLowerSym0)) "abcE" ~ 'Right '( '["a", "b", "c"], "E" )
     ,UnP (SomeP (PSym IsLowerSym0)) "XabcE" ~ 'Left '["PSym: no match"]
     ,UnP (ManyP (PSym IsLowerSym0)) "XabcE" ~ 'Right '( '[], "XabcE" )

     ,UnP IntP "123xyz" ~ 'Right '(123, "xyz")
     ,UnP (IntP' <* Eof) "+123_" ~ 'Left '["Eof: expected eof"]

     ,UnP IntP' "1234" ~ 'Right '( 'Int' 'True 1234, "" )
     ,UnP IntP' "-1234" ~ 'Right '( 'Int' 'False 1234, "" )
     ,UnP IntP' "+1234ABC" ~ 'Right '( 'Int' 'True 1234, "ABC" )

     ,UnP IPP "123.22.33.44" ~ 'Right '( 'IP 123 22 33 44, "" )

     ,UnP IPP "123.22.33" ~ 'Left '["missing third dot", "PSym: no data found"]

    ) => ()) -> ()
t150a x = x


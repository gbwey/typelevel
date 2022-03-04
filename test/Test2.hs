--  {-# OPTIONS -Wno-redundant-constraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
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
module Test2 where
import GHC.TypeNats (Nat, type (<=?), Div, KnownNat, natVal)
import GHC.TypeLits (KnownSymbol, symbolVal, Symbol)
import GHC.Natural (Natural)
import PCombinators
import VectorN
import FizzBuzz
import qualified Data.Symbol.Ascii as S
import Data.List.NonEmpty (NonEmpty(..))
import Data.Functor.Compose ( Compose(Compose) )
import Data.Functor.Identity ( Identity(Identity) )
import Data.These ( These(..) )
import qualified Data.Monoid as MM
import qualified Data.Semigroup as SG
import Data.Proxy ( Proxy(..) )
import Data.Tagged ( Tagged(Tagged) )
import Control.Applicative ( ZipList(ZipList), Const )
import Data.Constraint ( Constraint )
import Data.Void ( Void )

type family SAS :: STA S0 A0 where
  SAS = 'STA (KSym1 '( 'A0, 'S0))

type family SAS1 :: S0 ~> (A0, S0) where
  SAS1 = KSym1 '( 'A0, 'S0)

type family AMB :: A0 ~> STA S0 B0 where
  AMB = KSym1 ('STA (KSym1 '( 'B0, 'S1)))

-- lens compose forward as expected
t151 :: (
      (
       View T_1Sym0 '(123,'True) ~ 123
      ,View T_2Sym0 '(123,'True) ~ 'True
      ,View (T_2Sym0 :.: T_1Sym0) '("ss",'(123,'True)) ~ 123
      ,View (T_2Sym0 :.: T_2Sym0) '("ss",'(123,'True)) ~ 'True
      ,View (T_1Sym0 :.: T_2Sym0) '( '("ss", 'Left 1 :: Either Nat ()), '(123,'True)) ~ 'Left 1
      ,View (T_1Sym0 :.: T_2Sym0) '( '("ss", 'Left 1), '(123,'True)) ~ 'Left 1
      ,View (T_1Sym0 :.: T_2Sym0) '( '("ss", 99), '(123,'True)) ~ 99
      ,Update T_2Sym0 NotSym0 '(123,'True) ~ '(123, 'False)
      ,Set T_1Sym0 "dude" '(123,'True) ~ '("dude", 'True)
      ,Set (T_1Sym0 :.: T_1Sym0) "a" '( '(1,"x"), 'True) ~  '( '("a", "x"), 'True )
      ,Preview StringTraversalSym0 "abcd" ~ 'Just "a"
      ,LastOf StringTraversalSym0 "abcd" ~ 'Just "d"
      ,Preview (IxListSym1 3) '["a","b","c","d","e"] ~ 'Just "d"
      ,Preview (IxListSym1 99) '["a","b","c","d","e"] ~ 'Nothing
      ,Preview (IxNESym1 0) ("a" ':| '["b","c","d","e"]) ~ 'Just "a"
      ,Preview (IxNESym1 1) ("a" ':| '["b","c","d","e"]) ~ 'Just "b"
    ) => ()) -> ()
t151 x = x

t152 :: (
           (
             (FlipSym2 (FlipSym2 (TyCon3Sym1 '(,,)) 10) 'False @@ "x") ~ '("x",10,'False)
             ,(FlipSym2 (FlipSym2 (TyCon3Sym1 '(,,)) 'True) "x" @@ 1) ~ '(1, 'True, "x")
             ,(FlipSym2 (TyCon2Sym1 '(:|)) '[1,2,4] <$> 'Identity 44) ~ 'Identity (44 ':| '[1,2,4])
            ) => ()) -> ()
t152 x = x

t153 :: (
      (
       View T_13Sym0 '(123,'True,"sss") ~ 123
      ,View T_23Sym0 '(123,'True,"sss") ~ 'True
      ,View T_33Sym0 '(123,'True,"sss") ~ "sss"
      ,View (T_33Sym0 :.: T_1Sym0) '(123,'True,'(99,"sss")) ~ 99
      ,Preview TraverseSym0 '["a","b","c"] ~ 'Just "a"
      ,LastOf TraverseSym0 '["a","b","c"] ~ 'Just "c"
      ,Has (IxListSym1 4) '[2,3] ~ 'False
      ,Has (IxListSym1 1) '[2,3] ~ 'True
      ,Preview (IxListSym1 2) '["x","y","z","w"] ~ 'Just "z" -- use Preview cos makes more sense
      ,Preview (IxListSym1 5) '["x","y","z","w"] ~ 'Nothing
      ,View (IxListSym1 5) '["x","y","z","w"] ~ ""  -- no match so monoid
      ,View (IxListSym1 5) '[ 'Left "x", 'Right 1] ~ 'Left ""  -- no match so monoid
      ,Preview (IxListSym1 2) '[10,12,7] ~ 'Just 7
      ,Preview (IxListSym1 5) '[10,12,7] ~ 'Nothing
      ,ToListOf TraverseSym0 '["aa","bb"] ~ '["aa","bb"]
      ,ToListOf StringTraversalSym0 "asdf" ~ '["a","s","d","f"]
--      ,('("sss",'True) %~ T_2Sym0 $ NotSym0) ~ '("sss", 'False)
    ) => ()) -> ()
t153 x = x

t154 :: ((
          IToList (S.ToList "asdf") ~ '[ '(0, "a"), '(1, "s"), '(2, "d"), '(3, "f") ]
         ,Imap PairSym0 '["s","b","c"] ~ '[ '(0,"s"), '(1,"b"), '(2,"c") ]
         ,Imap PairSym0 ('Compose '[ 'Just "a", 'Just "b", 'Just "c"]) ~ 'Compose '[ 'Just '( '(0, '()), "a"), 'Just '( '(1, '()), "b"), 'Just '( '(2, '()), "c") ]
         ,IfoldMap (FlipSym1 KSym0) ('Compose '[ 'Just "a", 'Just "b", 'Just "c"]) ~ "abc"
         ,IfoldMap (KSym0 :.: SSumSym0 :.: FstSym0) ('Compose '[ 'Just "a", 'Just "b", 'Just "c"]) ~ 'MM.Sum 3
         ,(PairSym0 <$> 'ZipList '[1,2,3] <*> 'ZipList '["a","b","c"]) ~ 'ZipList '[ '(1, "a"), '(2, "b"), '(3, "c") ]
         ,('("sx",SuccSym0) <*> '("tw",6)) ~ '("sxtw", 7)
         ,Imap (TyCon1Sym1 'Just :..: PairSym0) '("ss",123) ~ '("ss", 'Just '("ss",123))
         ,Itraverse (TyCon1Sym1 'Just :..: PairSym0) '("ss",123) ~ 'Just '("ss", '("ss",123))
         ,IfoldMap (SingletonListSym0 :..: PairSym0) '("ss",123) ~ '[ '("ss",123) ]
         ,Imap PairSym0 'Proxy ~ 'Proxy
         ,( '("sss",'True) ^. T_1Sym0 ) ~ "sss"
         ,( '("sss",'True) ^. T_2Sym0 ) ~ 'True
         ,( '("sss",'True) %~ T_2Sym0 ) NotSym0 ~ '("sss", 'False)
         ,( '("sss",'True) .~ T_2Sym0 ) 45 ~ '("sss", 45)
         ,('(10,'True) %%~ T_1Sym0) (TyCon1Sym1 'Just :.: SuccSym0) ~ 'Just '(11, 'True)
--         ,( ('("sss",'True) %~ T_2Sym0) $ NotSym0) ~ '("sss", 'False) -- doesnt work from here
--         ,( '("sss",'True) %~ T_2Sym0 $$ NotSym0) ~ '("sss", 'False) -- works using kind! only
--         ,( NotSym0 & '("sss",'True) %~ T_2Sym0) ~ '("sss", 'False)
--         ,( NotSym0 &$ '("sss",'True) %~ T_2Sym0) ~ '("sss", 'False) -- works using kind! only
         , ('["a","b","c","d"] ^? IxListSym1 2) ~ 'Just "c"
         , ('["a","b","c","d"] ^? IxListSym1 24) ~ 'Nothing
         , ('["a","b","c","d"] ^?! IxListSym1 2) ~ "c"
--         , ('["a","b","c","d"] ^?! IxListSym1 24) ~ ""  -- typeerror
         , ('["a","b","c","d"] ^.. IxListSym1 2) ~ '["c"]
         , ('["a","b","c","d"] ^.. IxListSym1 20) ~ '[]
         , ( "helloworld" ^? IxStringSym1 3) ~ 'Just "l"
         , ( "asdfas" ^.. StringTraversalSym0) ~ '["a", "s", "d", "f", "a", "s"]
         , Update T_2Sym0 NotSym0 '("sss",'True) ~ '("sss", 'False)
         , (FromInteger 5 %~ IntNumSym0) SuccSym0 ~ 'Int' 'True 6
         , (Negate (FromInteger 5) ^. IntNumSym0) ~ 5
         , (Negate (FromInteger 5) ^. IntSignSym0) ~ 'False
         , (FromInteger 5 .~ IntNumSym0) 7 ~ 'Int' 'True 7
         ,( ESuccSym0 <$> 'Tagged ('S ('S 'Z)) ) ~ 'Tagged ('S ('S ('S 'Z)))
         ,( 'True <$ 'Tagged ('S ('S 'Z)) ) ~ 'Tagged 'True
         ,UnR (Imap PairSym0 ('R (KSym1 99))) @@ "abc" ~ '("abc",99)
         ,UnR (Imap PairSym0 ('R (AmpSym2 SuccSym0 PredSym0))) @@ 43 ~ '(43, '(44, 42))
         -- ziplist never had monoid or semigroup instance!
         ,('ZipList '[10,11,12] <|> 'ZipList '[1,2,3,4,5]) ~ 'ZipList '[10,11,12,4,5]
         ,('ZipList '[10,11,12,13,14] <|> 'ZipList '[1,2,3]) ~ 'ZipList '[10,11,12,13,14]
         ,('ZipList '[10,11,12,13,14] <|> 'ZipList '[1,2,3,4,5]) ~ 'ZipList '[10,11,12,13,14]
         ,('ZipList '[] <|> 'ZipList '[1,2,3,4,5]) ~ 'ZipList '[1,2,3,4,5]
         ,('ZipList '[10,11,12,13,14] <|> 'ZipList '[]) ~ 'ZipList '[10,11,12,13,14]
         ,SUnWrap ('ZipList '[ 'SG.Sum 10, 'SG.Sum 11, 'SG.Sum 12, 'SG.Sum 13, 'SG.Sum 14 ] <> 'ZipList '[ 'SG.Sum 1, 'SG.Sum 5, 'SG.Sum 1, 'SG.Sum 2]) ~ '[11,16,13,15,14]
         ,SUnWrap ('ZipList '[ 'SG.Sum 10, 'SG.Sum 11 ] <> 'ZipList '[ 'SG.Sum 1, 'SG.Sum 5, 'SG.Sum 1, 'SG.Sum 2]) ~ '[11,16,1,2]
         ,SUnWrap (Mempty <> 'ZipList '[ 'SG.Sum 10, 'SG.Sum 11 ] <> 'ZipList '[ 'SG.Sum 1, 'SG.Sum 5, 'SG.Sum 1, 'SG.Sum 2] <> Mempty) ~ '[11,16,1,2]
         ,( '("abc", 'True) ^.. T_1Sym0 :.: StringTraversalSym0) ~ '["a", "b", "c"]
         ,( '("abcd", 'True) .~ T_1Sym0 :.: IxStringSym1 2) "!!" ~ '("ab!!d", 'True)
         ,( '("abcd", 'True) %~ T_1Sym0 :.: IxStringSym1 2) (SAppSym1 "!!") ~ '("ab!!cd", 'True)
         ,Salign '[ 'These ('SG.Sum 4) "abc" ] '[ 'These ('SG.Sum 12) "def" , 'This ('SG.Sum 1) ] ~ '[ 'These ('MM.Sum 16) "abcdef", 'This ('MM.Sum 1) ]
         ,Salign '[ 'That  "abc" ] '[ 'These ('SG.Sum 12) "def" , 'This ('SG.Sum 1) ] ~  '[ 'These ('MM.Sum 12) "abcdef", 'This ('MM.Sum 1) ]
         ,Salign '["abc", "def", "d"] '["x",""] ~ '["abcx", "def", "d"]
         ,PadZip '[ 'That 1, 'This "x" ] '[ 'These "def" 22 , 'This "y", 'This "z" ] ~ '[ '( 'Just ('That 1), 'Just ('These "def" 22)), '( 'Just ('This "x"), 'Just ('This "y")), '( 'Nothing, 'Just ('This "z"))]
         ,Align '[ 'This 1, 'That "x"] '[] ~ '[ 'This ('This 1), 'This ('That "x") ]
         ,Align '[1,2,3] '[5] ~ '[ 'These 1 5, 'This 2, 'This 3 ]
         ,Align '[1,2,3] '[5,6,7,8] ~ '[ 'These 1 5, 'These 2 6, 'These 3 7, 'That 8 ]
         ,Align '[1,2,3] '["x"] ~ '[ 'These 1 "x", 'This 2, 'This 3 ]
         ,Align '[1,2,3] '["x","y","z","a","b"] ~ '[ 'These 1 "x", 'These 2 "y", 'These 3 "z", 'That "a", 'That "b" ]
         ,PartitionEithers '[ 'Left "s", 'Right 2, 'Left "t", 'Right 4, 'Right 6, 'Right 7 ] ~ '( '["s","t"], '[2,4,6,7] )
         ,PartitionThese '[ 'This "s", 'That 2, 'This "t", 'That 4, 'That 6, 'That 7 ] ~ '( '[], '( '["s","t"], '[2,4,6,7] ) )
         ,PartitionThese '[ 'These "s" 14, 'That 2, 'This "t", 'That 4, 'That 6, 'That 7 ] ~ '( '[ '("s", 14) ], '( '["t"], '[2,4,6,7] ) )
         ,Partition (EQSym1 0 :.: FlipSym2 ModSym0 2) '[2,5,3,1,6,7] ~ '( '[2, 6], '[5, 3, 1, 7] )
         ,Filter (EQSym1 0 :.: FlipSym2 ModSym0 2) '[2,5,3,1,6,7] ~ '[2,6]
         ,TakeWhile (FlipSym2 LTSym0 6) '[2,5,3,1,6,7] ~ '[2, 5, 3, 1]
         ,DropWhile (FlipSym2 LTSym0 6) '[2,5,3,1,6,7] ~ '[6,7]
         ,Sequence ('Right '[1,2,3]) ~  '[ 'Right 1, 'Right 2, 'Right 3 ]
         ,Sequence '[ 'Right 1, 'Right 2, 'Right 3 ] ~  'Right '[1,2,3]
         ,Sequence '[ 'Right 1, 'Right 2, 'Left "Asfd"] ~  'Left "Asfd"
         ,Transpose '[ '[1,2,3], '[4,5,6] ] ~ '[ '[1, 4], '[2, 5], '[3, 6] ]
     ) => ()) -> ()
t154 x = x


t154a :: (
      (
       UnfoldNat SumSym0 0 10 ~ 55
      ,UnfoldNat SumSym0 3 0 ~ 3
      ,IterateNat' 0 SuccSym0 0 ~ 0
      ,Iterate 0 SuccSym0 0 ~ '[]
      ,Iterate 4 (StringSym1 "0")  "c" ~ '["c", "0c", "00c", "000c"]
      ,Iterate 4 (FlipSym2 StringSym0 "0") "c" ~ '["c", "c0", "c00", "c000"]
    ) => ()) -> ()
t154a x = x


t154b :: ((
       Phantom ('Proxy :: Proxy Int) ~ ('Proxy :: Proxy Bool)
      ,(UnPredicateX (PAddSym1 1 >$< 'PredicateX (EqSym1 3)) @@ 2) ~ 'True
      ,(UnPredicateX (PAddSym1 1 >$< 'PredicateX (EqSym1 3)) @@ 1) ~ 'False
      ,(UnPredicateX (PAddSym1 1 >$< 'PredicateX (EqSym1 3)) @@ 3) ~ 'False
    ) => ()) -> ()
t154b x = x

t154c :: ((
          ToEnum 4 ~ 'Char1 "e"
         ,FromEnum ('Char1 "e") ~ 4
         ,ESucc ('Char1 "e") ~ 'Char1 "f"
         ,EPred ('Char1 "e") ~ 'Char1 "d"
         ,EnumFromTo ('Char1 "f") ('Char1 "f") ~ '[ 'Char1 "f" ]
         ,EnumFromTo ('Char1 "f") ('Char1 "i") ~ '[ 'Char1 "f", 'Char1 "g", 'Char1 "h", 'Char1 "i" ]
         ,EnumFromThenTo ('Char1 "a") ('Char1 "c") ('Char1 "z")
           ~ '[ 'Char1 "a", 'Char1 "c", 'Char1 "e", 'Char1 "g", 'Char1 "i",
               'Char1 "k", 'Char1 "m", 'Char1 "o", 'Char1 "q", 'Char1 "s",
               'Char1 "u", 'Char1 "w", 'Char1 "y" ]
    ) => ()) -> ()
t154c x = x


t155 :: (
      (
       PMult (Negate (FromInteger 3)) (FromInteger 7) ~ 'Int' 'False 21
      ,PAdd (Negate (FromInteger 3)) (FromInteger 7) ~ 'Int' 'True 4
      ,PAdd (Negate (FromInteger 9)) (FromInteger 7) ~ 'Int' 'False 2
      ,EnumFromThenTo ('Int' 'False 5) ('Int' 'False 3) ('Int' 'True 7) ~ '[ 'Int' 'False 5, 'Int' 'False 3, 'Int' 'False 1, 'Int' 'True 1, 'Int' 'True 3, 'Int' 'True 5, 'Int' 'True 7 ]
    ) => ()) -> ()
t155 x = x


t156 :: ((
--          EnumFromThenTo 4 4 4 ~ '[] -- typeerror
          EnumFromThenTo 4 5 4 ~ '[4]
         ,EnumFromThenTo 4 5 5 ~ '[4,5]
--         ,EnumFromThenTo 'False 'False 'False ~ '[] -- typeerror
         ,EnumFromThenTo 'False 'True 'False ~ '[ 'False ]
         ,EnumFromThenTo 'False 'True 'True ~ '[ 'False, 'True ]
         -- ,EnumFromThenTo 'Z ('S 'Z) (ToN 20) ~ '[]
         ,EnumFromTo 0 12 ~ '[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
         ,EnumFromTo 0 0 ~ '[0]
         ,EnumFromThenTo 0 3 59 ~ '[0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45, 48, 51, 54, 57]
         ,EnumFromThenTo 'Z ('S ('S ('S 'Z))) (ToN 53) ~ Map ToNSym0 '[0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45, 48, 51]
         ,EnumFromThenTo 'LT 'GT 'GT ~ '[ 'LT, 'GT ]
         ,EnumFromThenTo 'LT 'GT 'EQ ~ '[ 'LT ]
         ,EnumFromThenTo 'LT 'EQ 'EQ ~ '[ 'LT, 'EQ ]
         ,EnumFromThenTo 'LT 'EQ 'LT ~ '[ 'LT ]
-- ,EnumFromTo 'True 'False ~ '[]
-- ,EnumFromThenTo 4 4 5 ~ '[]
-- ,EnumFromThenTo 4 5 3 ~ '[]
          ) => ()) -> ()
t156 x = x

ts1 :: ((
      MergeSort '[5,3,1,2] ~ '[1,2,3,5]
     ,MergeSort '[1,1,1,1] ~ '[1,1,1,1]
     ,MergeSort '[1] ~ '[1]
     ,MergeSort '[] ~ '[]
     ,MergeSort '[4,3,2,1] ~ '[1,2,3,4]
     ,MergeSortOn LESym0 '[4,3,2,1] ~ '[1,2,3,4]
     ,MergeSortOn (OnSym2 LESym0 FstSym0) '[ '("d",0), '("a",12), '("b",8), '("b",7) ] ~ '[ '("a",12), '("b",8), '("b",7), '("d",0) ]
     ,QuickSort '[5,3,1,2] ~ '[1,2,3,5]
     ,QuickSort '[1,1,1,1] ~ '[1,1,1,1]
     ,QuickSort '[1] ~ '[1]
     ,QuickSort '[] ~ '[]
     ,QuickSort '[4,3,2,1] ~ '[1,2,3,4]
     ,QuickSortOn LESym0 '[4,3,2,1] ~ '[1,2,3,4]
     ,QuickSortOn (OnSym2 LESym0 FstSym0) '[ '("d",0), '("a",12), '("b",8), '("b",7) ] ~ '[ '("a",12), '("b",8), '("b",7), '("d",0) ]
     ,QuickSortOn (OnSym2 EqSym0 FstSym0) (Reverse '[ '("a",Bool), '("b",Int), '("c",Double) ]) ~ '[ '("a",Bool), '("b",Int), '("c",Double) ]
     ,DupsBy (OnSym2 EqSym0 FstSym0) '[ '("d",0), '("a",12), '("b",8), '("b",7) ] ~ '[ '("b",8), '("b",7) ]
     ,Dups '[2,3,1,4,2,7,1,2] ~ '[2,2,2,1,1]
     ,Tails '[1,2,3,4] ~ '[ '[1,2,3,4], '[2,3,4], '[3,4], '[4], '[] ]
     ,Inits '[1,2,3,4] ~ '[ '[], '[1], '[1,2], '[1,2,3], '[1,2,3,4]]
     ,Inits '[] ~ '[ '[] ]
     ,Tails '[] ~ '[ '[] ]
      ) => ()) -> ()
ts1 x = x

ts2 :: ((
       SplitAt 0 '[]  ~ '( '[], '[] )
      ,SplitAt 1 '["a"]  ~ '( '["a"], '[] )
      ,SplitAt 0 '["a"]  ~ '( '[], '["a"] )
      ,SplitAt 5 '[1,2,3,4,5,6,7]  ~ '( '[1,2,3,4,5], '[6,7] )
       ) => ()) -> ()
ts2 x = x

ts3 :: ((
       Subset '[] '[]  ~ 'True
      ,Subset '[1] '[]  ~ 'False
      ,Subset '[1,2] '[2,1,3]  ~ 'True
      ,Subset '[1,2,4] '[2,1,3]  ~ 'False
      ,Subset '[] '[ '("a",Int), '("b",Int), '("c",Double) ] ~ 'True
      ,Subset '[ '("b",Int), '("c",Double) ] '[ '("a",Int), '("b",Int), '("c",Double) ] ~ 'True
      ,Subset '[ '("c",Int), '("b",Double) ] '[ '("a",Int), '("b",Int), '("c",Double) ] ~ 'False
      ,Subset '[ '("c",Double), '("b",Int) ] '[ '("a",Int), '("b",Int), '("c",Double) ] ~ 'True
      ,Subset '[ '("c",Double), '("b",Int), '("b",Int) ] '[ '("a",Int), '("b",Int), '("c",Double) ] ~ 'False
      ,Subset '[ '("c",Double), '("b",Int), '("b",Int) ] '[ '("a",Int), '("b",Int), '("c",Double), '("b",Int) ] ~ 'True
       ) => ()) -> ()
ts3 x = x

ts4 :: ((
      Curry Id 99 "trueness" ~ '(99, "trueness")
     ,Curry FstSym0 99 "trueness" ~ 99
     ,(CurrySym0 :.: CurrySym0) @@ Id @@ 10 @@ 'True @@ "xx" ~ '( '(10, 'True), "xx" )
     ,(CurrySym0 :.: CurrySym0 :.: CurrySym0) @@ Id @@ 10 @@ 'True @@ "xx" @@ 12 ~ '( '( '(10, 'True), "xx" ), 12 )
     ,UnCurry AndSym0 (Curry Id 'True 'False) ~ 'False
     ,UnCurry OrSym0 (Curry Id 'True 'False) ~ 'True
     ,UnCurry AndSym0 (Curry Id 'True 'True) ~ 'True
     ,ConsSym0 @@ 1 @@ '[2,3,4] ~ '[1,2,3,4]
     ,ConsSym0' @@ 1 @@ '[2,3,4] ~ '[1,2,3,4]
     ,Foldl (FlipSym1 ConsSym0) '[99] '[1,5,6] ~ '[6,5,1,99]
     ,Foldr ConsSym0 '[99] '[1,5,6] ~ '[1,5,6,99]
     ,Foldr1 SumSym0 '[3,4,4] ~ 11
     ,FoldrNE SumSym0 (4 ':| '[1,2]) ~ 7
     ,Foldr (FlipSym1 KSym0) '[ '(22,"xx")] (ZipN 0 '["aa","b","c"]) ~ '[ '(22, "xx") ]
     ,UnfoldNat2 DupSym0 (5) "x" ~ '["x", "x", "x", "x", "x"]
     ,Foldr SumSym0 7 [1,5,6] ~ 19
     ) => ()) -> ()
ts4 x = x

tv1 :: ((
      AllF (EqSym1 (Vec' 2 (Vec' 3 (Vec' 4 Int)))) '[UnDimX' '[2,3,4] Int, UnDimX' '[2,3,4] Int] ~ 'True
     ,(***) HdSym0 LstSym0 (UnZip '[ '(0,"dude"), '(2,"fred"), '(3,"jim")]) ~ '(0, "jim")
     ,(FstSym0 $ HdSym0 @@ '[ '(1,'True), '(2,'False) ]) ~ 1
     ,Foldl (FlipSym1 ConsSym0) '[99] '[1,5,6] ~ '[6,5,1,99]
     ,Foldr ConsSym0 '[99] '[1,5,6] ~ '[1,5,6,99]
     ,Map ToNatSym0 '[ 'S ('S 'Z), 'Z, 'S 'Z] ~ '[2,0,1]
     ,'[ToNat ('S 'Z), ToNat ('S ('S 'Z))] ~ '[1,2]
     ,DimAll (Vec' 4 (Vec' 6 Int)) ~ '(ToNs '[4,6], Int)
     ,DimAll (Vec' 1 Int) ~ '(ToNs '[1], Int)
--     ,DimAll (Vec' 1 Int) ~ '(ToNs '[4], Int)
--     ,DimAll (Vec' 3 (Vec' 5 (Vec' 7 Integer))) ~ '(ToNs '[3,5,7], Int) --mismatch on Integer Int
     ,DimAll (Vec' 3 (Vec' 5 (Vec' 7 Int))) ~ '(ToNs '[3,5,7], Int)
     ,Subtract 4 3 ~ 1
     ,Subtract 9 3 ~ 6
     ,Subtract 0 0 ~ 0
     ,Div 3 2 ~ 1
     ,Div 17 3 ~ 5
     ,Map (StarSym2 SuccSym0 PredSym0) (ZipN 10 '[5,3,1,9]) ~ '[ '(11,4),'(12,2),'(13,0),'(14,8) ]
     ,ZipN 7 '[1,2,3,4,5] ~ '[ '(7, 1), '(8, 2), '(9, 3), '(10, 4), '(11, 5) ]
     ,ZipN 0 '["ab","c","defg","ghhg"] ~ '[ '(0, "ab"), '(1, "c"), '(2, "defg"), '(3, "ghhg") ]
     ) => ()) -> ()
tv1 x = x

ts5 :: ((
      FizzBuzz 15 ~ "FizzBuzz"
     ,FizzBuzz 14 ~ "14"
     ,FizzBuzz 2 ~ "2"
     ,(FizzBuzzSym0 <$> EnumFromTo 0 10) ~ '["FizzBuzz", "1", "2", "Fizz", "4", "Buzz", "Fizz", "7", "8", "Fizz", "Buzz"]
     ,AllF (IsPrefixOfSym1 '["F","i","z","z"] :.: SListSym0) (FizzBuzzSym0 <$> EnumFromThenTo 0 3 20) ~ 'True
     ,AllF (IsSuffixOfSym1 '["B","u","z","z"] :.: SListSym0) (FizzBuzzSym0 <$> EnumFromThenTo 0 5 20) ~ 'True
     ,IsSuffixOf (S.ToList "cde") (S.ToList "abcde") ~ 'True
     ,IsSuffixOf (S.ToList "cde") (S.ToList "cdecd") ~ 'False
     ,IsPrefixOf (S.ToList "cde") (S.ToList "cdef") ~ 'True
     ,IsPrefixOf (S.ToList "cde") (S.ToList "cd") ~ 'False
     ,IsInfixOf (S.ToList "cde") (S.ToList "abcd") ~ 'False
     ,IsInfixOf (S.ToList "cde") (S.ToList "abcdef") ~ 'True
     ,On IsSuffixOfSym0 SListSym0 "xy" "cdxy" ~ 'True
     ,On IsSuffixOfSym0 SListSym0 "xy" "xy" ~ 'True
     ,On IsSuffixOfSym0 SListSym0 "cd" "cdxy" ~ 'False
     ,AllF (EqSym1 "FizzBuzz") (FizzBuzzSym0 <$> EnumFromThenTo 0 15 50) ~ 'True
     ,NatToString 123456 ~ "123456"
     ,NatToString 0 ~ "0"
     ) => ()) -> ()
ts5 x = x

ts6 :: ((
      UnWrap (Maybe Int) ~ Int
     ,UnWrap ('Just 10) ~ 10
     ,UnWrap ('Just '(10,'False)) ~ '(10,'False)
     ,UnWrap1 '[ 10 ] ~ 10
     ,UnWrap1 '[ 10, 20, 30 ] ~ 10
     ,UnWrapBoth (These Int Double) ~ '(Int, Double)
     ,UnWrap1 (These Int Double) ~ Int
     ,UnWrap2 (These Int Double) ~ Double
     ,UnWrap (SG.Sum Int) ~ Int
     ,UnWrap2 (Either Int Double) ~ Double
     ,UnWrapBoth (Either String ()) ~ '(String, ())
     ) => ()) -> ()
ts6 x = x

ts7 :: ((
         Unique (Replicate 10 "a") ~ '["a","a_1","a_2","a_3","a_4","a_5","a_6","a_7","a_8","a_9"]
        ,UniquePair '[ '("a",Int), '("b",Bool), '("a",String) ] ~ '[ '("a",Int), '("b",Bool), '("a_1",String) ]
       ) => ()) -> ()
ts7 () = ()

ts8 :: ((
         ZipWithExact PairSym0 '["ab","c","defg","ghhg"] [3,4,5,6] ~ '[ '("ab", 3), '("c", 4), '("defg", 5), '("ghhg", 6) ]
        ,ZipWithExact PairSym0 '["ab","c","defg","ghhg"] (VRep (ToN 4) 'True) ~ '[ '("ab", 'True), '("c", 'True), '("defg", 'True), '("ghhg", 'True) ]
        ,ZipWithExact KSym0 '["ab","c","defg","ghhg"] (VRep (ToN 4) 'True) ~ '["ab", "c", "defg", "ghhg"]
        ,ZipWithExact (FlipSym1 KSym0) '["ab","c","defg","ghhg"] (VRep (ToN 4) 'True) ~ '[ 'True, 'True, 'True, 'True ]
       ) => ()) -> ()
ts8 () = ()

ts9 :: ((
          TakeWhile' (GTSym1F 50) '[10,99] ~ '[]
         ,TakeWhile' (GTSym1F 50) '[105,99] ~ '[105,99]
         ,TakeWhile' (GTSym1F 50) '[105,99,3] ~ '[105,99]
         ,Scanl SumSym0 9 '[1,2,3,4] ~ '[9, 10, 12, 15, 19]
         ,Maximum '[1,2,3,4,99,1,2,0] ~ 99
         ,Maximum '[] ~ 0
         ,MaximumBy (ComparingSym1 FstSym0) '[ '(10,"a"), '(2,"b"), '(10,"c") ] ~ '(10,"c")
         ,MinimumBy (ComparingSym1 FstSym0) '[ '(10,"a"), '(2,"b"), '(10,"c") ] ~ '(2,"b")
         ,GroupBy (EqSym0 :.: SuccSym0) '[1,4,7,1,3,2] ~ '[ '[1], '[4], '[7], '[1], '[3], '[2] ]
         ,GroupBy (EqSym0 :.: SuccSym0) '[1,2,3,4,7,1,3,2] ~ '[ '[1, 2, 3, 4], '[7], '[1], '[3], '[2] ]
         ,GroupBy (EqSym0 :.: SuccSym0) '[1,2,3,4,7,1,3,2,3] ~ '[ '[1, 2, 3, 4], '[7], '[1], '[3], '[2, 3] ]
         ,GroupBy EqSym0 '[1,2,3,3,7,3,5,5,5,7,9,9] ~ '[ '[1], '[2], '[3, 3], '[7], '[3], '[5, 5, 5], '[7], '[9, 9] ]
       ) => ()) -> ()
ts9 () = ()

ts10 :: ((
            ConstraintCartesian '[Show,Read] '[Int,Double] ~ (Show Int, (Show Double, (Read Int, (Read Double, () :: Constraint))))
--           ,DollarSym0 @@ Show @@ Int ~ Show Int
--           ,DollarSym1 Show @@ Int ~ Show Int
           ,TyCon1Sym0 @@ Show @@ Int ~ Show Int
           ,TyCon1Sym1 Show @@ Int ~ Show Int
           ,Mconcat (TyCon1Sym0 <$> '[Show,Read] <*> '[Int,Double]) ~ (Show Int, (Show Double, (Read Int, (Read Double, () :: Constraint))))
       ) => ()) -> ()
ts10 () = ()


-- Loop is a live hand grenade: it has to be thunked else it will explode as soon as you use it
-- hence we can only use LoopSym0

-- problem with If is that stuff gets evaluated before you pass stuff to If
type family UnBool b t f where
  UnBool 'True t _ = t @@ '()
  UnBool 'False _ f = f @@ '()

-- cant create a lazy thunk from a strict value: it has to be unprocessed in advance
-- KSym1 (Loop '()) will not work cos it evaluates the loop immediately

t222a :: (UnBool (0 <=? 4) (KSym1 '()) LoopSym0 ~ '() => ()) -> ()
t222a x = x

type family Test2 f b where
  Test2 f b = Test3 f (b <=? 0)

type family Test3 f t where
  Test3 _ 'True = '()
  Test3 f 'False = f @@ '()

-- loop but it never gets called
t222 :: (Test2 LoopSym0 0 ~ '() => ()) -> ()
t222 x = x


ts99 :: ((
  MapT 'Just '[1,5,5] ~ '[ 'Just 1, 'Just 5, 'Just 5 ]
 ,MapT Const '[(),(),Void] ~ '[Const (), Const (), Const Void]
 ,MapT Show '[Int,Double] ~ '[Show Int, Show Double]
 ,MapT Maybe '[Int,Double] ~ '[Maybe Int, Maybe Double]
-- ,MapT ((+) 4) '[3,5] ~ '[7, 9]   -- works using :kind! only (partially applied)
-- ,MapT (TL.AppendSymbol "tt") '["aaa","Bb"] ~ '["ttaaa", "ttBb"] -- works using :kind! only (partially applied)
-- ,FoldrT (+) 99 '[2,3,4] ~ 108 -- works using :kind! only (partially applied)
       ) => ()) -> ()
ts99 () = ()


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

t3 :: forall (ns :: [Nat]) ss . (ss ~ Map FizzBuzzSym0 ns, GetStrings ss) => [String]
t3 = getStrings @ss

{-
>t3 @'[1,5,3,4,15]
["1","Buzz","Fizz","4","FizzBuzz"]
it :: [String]
-}
{-
ff :: Mconcat (TyCon1Sym0 <$> '[Show, Read] <*> '[a,b]) => a -> b -> (String,String)
ff a b = (show a,show b)

gg :: ConstraintCartesian '[Show, Read] '[a,b] => a -> b -> (String,String)
gg a b = (show a,show b)
-}

{-
>:kind! ConstraintCartesian '[Show] '[Int] == (Show Int, (() :: Constraint))
ConstraintCartesian '[Show] '[Int] == (Show Int, (() :: Constraint)) :: Bool
= 'True

>:kind! ConstraintCartesian '[Show,Read] '[Int] == (Show Int, (Read Int, (() :: Constraint)))
ConstraintCartesian '[Show,Read] '[Int] == (Show Int, (Read Int, (() :: Constraint))) :: Bool
= 'True

>:kind! ConstraintCartesian '[Show,Read] '[Int,Double] == (Show Int, (Show Double, (Read Int, (Read Double, (() :: Constraint)))))
ConstraintCartesian '[Show,Read] '[Int,Double] == (Show Int, (Show Double, (Read Int, (Read Double, (() :: Constraint))))) :: Bool
= 'True
-}

taa :: forall (s :: Symbol) b . KnownSymbol s => Tagged s b -> String
taa (Tagged _) = symbolVal (Proxy @s)
{-
>case someSymbolVal "abd" of SomeSymbol p -> taaa (tagWith p True)
"abd"
it :: String

>taaa (Tagged @"abd" ())
"abd"
it :: String
-}

taa1 :: forall (s :: Symbol) (i :: Nat)
  . (
     -- (0 <=? Length (S.ToList s)) ~ 'True
      Length (S.ToList s) ~ i
    , KnownSymbol s
    , KnownNat (Length (S.ToList s))
    )
   => Proxy s -> (String, Natural)
taa1 p = (symbolVal p, natVal (Proxy @(Length (S.ToList s))))
{-
>taa1 @"abcdef" @123 Proxy

<interactive>:73:1: error:
    • Couldn't match type ‘6’ with ‘123’ arising from a use of ‘taa1’
    • In the expression: taa1 @"abcdef" @123 Proxy
      In an equation for ‘it’: it = taa1 @"abcdef" @123 Proxy

>taa1 @"abcdef" @6 Proxy
("abcdef",6)

>taa1 (Proxy @"abcdef")
("abcdef",6)
it :: (String, GHC.Natural.Natural)

>taa2 @"abc" @"cba" Proxy
("abc","")
it :: (String, String)
>taa2 @"abc" @"cbad" Proxy

<interactive>:66:1: error:
    • Couldn't match type ‘"cba"’ with ‘"cbad"’
        arising from a use of ‘taa2’
    • In the expression: taa2 @"abc" @"cbad" Proxy
      In an equation for ‘it’: it = taa2 @"abc" @"cbad" Proxy
-}
taa2 :: forall (s :: Symbol) (s1 :: Symbol) p
   . (
      Mconcat (Reverse (S.ToList s)) ~ s1
    , KnownSymbol s
--    , KnownSymbol s1
--    , KnownSymbol (Mconcat (Reverse (S.ToList s)))
   )
   => p s -> (String, String)
taa2 _ = (symbolVal (Proxy @s), "") -- symbolVal (Proxy @s1))

-- we can lift Nats (using someNatVal) and Symbols (using someSymbolVal)
-- but they are useless cos we cannot do anything with them
-- 'n' is not statically known so we cant do anything with it except grab the value as is
-- using SomeNat is runtime and ghc has already done its stuff so this is Stuck
-- we can pull the raw value down of course using natVal (symbolVal) but we cannot
-- derive any stuff at the type level
-- that means that stuff like Length / Replicate are not going to do anything cos
--   'n' is stuck
taa3 :: forall (n :: Nat)
  . (
     (n <=? 3) ~ 'True
     ,KnownNat n
    )
   => Proxy n -> Natural
taa3 = natVal

{-
>taa3 (Proxy @3)
3
it :: GHC.Natural.Natural

>taa3 (Proxy @4)

<interactive>:12:1: error:
    * Couldn't match type 'False with 'True
        arising from a use of `taa3'
    * In the expression: taa3 (Proxy @4)
      In an equation for `it': it = taa3 (Proxy @4)

-- ghc cannot calculate 'n' so cannot do anything with the constraint

>case someNatVal 3 of SomeNat p -> taa3 p
<interactive>:13:35: error:
    * Couldn't match type `n <=? 3' with 'True
        arising from a use of `taa3'
    * In the expression: taa3 p
      In a case alternative: SomeNat p -> taa3 p
      In the expression: case someNatVal 3 of { SomeNat p -> taa3 p }
    * Relevant bindings include
        p :: Proxy n (bound at <interactive>:13:30)
-}



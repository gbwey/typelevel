{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
module TestVector where
import VectorN
import PCombinators

v1 :: Vec' 3 Char
v1 = 'x' `VS` 'w' `VS` 'x' `VS` VZ

v2 :: Vec' 3 Int  -- redundant cos type is the value
v2 = 11 `VS` 33 `VS` 555 `VS` VZ

v3 :: Vec (ToN 7) Int
v3 = 11 `VS` 22 `VS` 33 `VS` 44 `VS` 55 `VS` 66 `VS` 77 `VS` VZ

{-
gen' @5 [12..] == (VS 12 (VS 13 (VS 14 (VS 14 (VS 16 VZ)))))

gen2' @3 4 succ == (VS 4 (VS 5 (VS 6 VZ)))

len' @('S ('S 'Z)) == 2

gen3 @(ToN 5) 0 (\p a -> natVal p) == (VS 0 (VS 4 (VS 3 (VS 2 (VS 1 VZ)))))

gen3 @(ToN 5) 0 (\p a -> a) == (VS 0 (VS 0 (VS 0 (VS 0 (VS 0 VZ)))))

imap (,) (gen' @5 ['a'..]) == (VS (0,'a') $ VS (1,'b') $ VS (2,'c') $ VS (3,'d') $ VS (4,'e') VZ)

vi (gen' @5 [12..]) == (VS (0,12) $ VS (1,13) $ VS (2,14) $ VS (3,15) $ VS (4,16) VZ)
-}
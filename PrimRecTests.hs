{-# LANGUAGE TemplateHaskell #-}

module PrimRecTests where

import Test.QuickCheck
import Test.QuickCheck.All
import DepTypes
import PrimRec

prop_prId_correct (NonNegative x) =
    interp prId (mkVect1 x) == x

prop_prPlus_correct (NonNegative x, NonNegative y) =
    interp prPlus (mkVect2 x y) == x + y

prop_prConst0_0_correct =
    interp prConst0 VNil == 0
prop_prConst0_1_correct (NonNegative x) =
    interp prConst0 (mkVect1 x) == 0
prop_prConst0_2_correct (NonNegative x, NonNegative y) =
    interp prConst0 (mkVect2 x y) == 0

prop_prMult_correct (NonNegative x, NonNegative y) =
    interp prMult (mkVect2 x y) == x * y

--prFact is very slow without native + and *, so only check it up to 8
prop_prFact_smallNumbers =
    [interp prFact (mkVect1 x) | x <- [0..8]] == [product [1..x] | x <- [0..8]]

prop_prPred_correct (NonNegative x) =
    interp prPred (mkVect1 x) == max 0 (x-1)

prop_prMonus_correct (NonNegative x, NonNegative y) =
    interp prMonus (mkVect2 x y) == max 0 (x-y)

prop_prMin_correct (NonNegative x, NonNegative y) =
    interp prMin (mkVect2 x y) == min x y

prop_prMax_correct (NonNegative x, NonNegative y) =
    interp prMax (mkVect2 x y) == max x y

prop_prSymmDiff_correct (NonNegative x, NonNegative y) =
    interp prSymmDiff (mkVect2 x y) == abs (x-y)

-- boundary at 0 to 1 most important, so test against [0..100], not general
prop_prBit_smallNumbers =
    [interp prBit (mkVect1 x) | x <- [0..100]] == 0 : replicate 100 1

prop_prNegBit_smallNumbers =
    [interp prNegBit (mkVect1 x) | x <- [0..100]] == 1 : replicate 100 0

 
runTests = $quickCheckAll

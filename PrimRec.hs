{-#LANGUAGE GADTs, StandaloneDeriving #-}

module PrimRec where

import DepTypes

-- syntactic representation of primitive recursive functions
-- Should PrProj additionally take a (U n), or remain polymorphic in num args?
data PrimRec n where
    PrZero :: PrimRec T0
    PrSucc :: PrimRec T1
    PrProj :: Fin n -> PrimRec n
    PrComp :: PrimRec m -> Vect m (PrimRec k) -> PrimRec k
    PrRDef :: PrimRec m -> PrimRec (TS (TS m)) -> PrimRec (TS m)
deriving instance Show (PrimRec n)

-- Try a polymorphic interpreter? I wish Haskell had better representation of
-- non-neg integers
interp :: (Num a, Ord a) => (PrimRec n) -> Vect n a -> a
interp pr args = case pr of
    PrZero -> 0
    PrSucc -> vhead args + 1
    PrProj i -> index args i
    PrComp f gs -> interp f $ fmap (\g -> interp g args) gs
    PrRDef f g -> h args where
        h (VCons x xs) = if x == 0 then interp f xs else -- TODO fail-fast negatives?
            let r = h (VCons (x-1) xs) in interp g (VCons r (VCons (x-1) xs))

--NOTE: doesn't negCheck recursively, so kinda useless
interpChecked :: (Num a, Ord a, Show a) => (PrimRec n) -> Vect n a -> a
interpChecked pr = interp pr . negCheck

negCheck :: (Num a, Ord a, Show a) => Vect n a -> Vect n a
negCheck xs = if vand (>0) xs then xs else error $ "negCheck failed for " ++ show xs

-- Useful abbreviations, for projections, polymorphic in type
pi0 = PrProj F0   :: PrimRec (TS n)
pi1 = PrProj fin1 :: PrimRec (TS (TS n))
pi2 = PrProj fin2 :: PrimRec (TS (TS (TS n)))
pi3 = PrProj fin3 :: PrimRec (TS (TS (TS (TS n))))
pi4 = PrProj fin4 :: PrimRec (TS (TS (TS (TS (TS n)))))
pi5 = PrProj fin5 :: PrimRec (TS (TS (TS (TS (TS (TS n))))))

-- Useful helpers

mkComp1 :: PrimRec T1 -> PrimRec n -> PrimRec n
mkComp1 f g = PrComp f $ mkVect1 g

mkComp2 :: PrimRec T2 -> PrimRec n -> PrimRec n -> PrimRec n
mkComp2 f g1 g2 = PrComp f $ mkVect2 g1 g2

mkFlip :: PrimRec T2 -> PrimRec T2
mkFlip f = mkComp2 f pi1 pi0

-- Example functions (see Lemma 3I.7 of Moschovakis):

prId :: PrimRec T1
prId = pi0

prPlus :: PrimRec T2
prPlus = PrRDef prId $ mkComp1 PrSucc pi0

-- returns 0 for any args; polymorphic in number of args
prConst0 :: PrimRec n
prConst0 = PrComp PrZero VNil

prConst1 :: PrimRec n
prConst1 = mkComp1 PrSucc prConst0

prMult :: PrimRec T2
prMult = PrRDef prConst0 $ mkComp2 prPlus pi2 pi0

prFact :: PrimRec T1
prFact = PrRDef prConst1 $ mkComp2 prMult (mkComp1 PrSucc pi1) pi0

-- predecessor (or 0)
prPred :: PrimRec T1
prPred = PrRDef PrZero pi1

-- monus x y = max(x-y, 0)
prMonus :: PrimRec T2
prMonus = mkFlip $ PrRDef prId $ mkComp1 prPred pi0

-- max x y = (monus x y) + y
prMax :: PrimRec T2
prMax = mkComp2 prPlus prMonus pi1

-- min x y = x `monus` (x `monus` y)
prMin :: PrimRec T2
prMin = mkComp2 prMonus pi0 prMonus

-- Skipping n-ary min/max for now. There would be no unified formula, so would
-- probably want some way of folding over args?

prSymmDiff :: PrimRec T2
prSymmDiff = mkComp2 prPlus prMonus (mkFlip prMonus)

prBit :: PrimRec T1
prBit = PrRDef PrZero prConst1

prNegBit :: PrimRec T1
prNegBit = PrRDef prConst1 prConst0

-- Lemma 3I.8 ...in progress

-- { PrProj 0, PrProj 1, ..., PrProj (n-1) }
getProjs :: U n -> Vect n (PrimRec n)
getProjs = fmap PrProj . getFins

-- (mkPrSum h) y xs = sum [h i xs | i <- [0..y-1]]
--mkPrSum :: U (TS n) -> PrimRec (TS n) -> PrimRec (TS n)
--mkPrSum (US u) h = PrRDef prConst0 $ mkComp2 prPlus pi0 $
--    PrComp h $ vtail $ getProjs (US u)


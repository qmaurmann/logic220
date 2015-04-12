{-#LANGUAGE GADTs, StandaloneDeriving #-}

module PrimRec where

import Vect

data PrimRec n where
    PrZero :: PrimRec TZ
    PrSucc :: PrimRec T1
    PrProj :: Fin n -> PrimRec n
    PrComp :: PrimRec m -> Vect m (PrimRec k) -> PrimRec k
    PrRDef :: PrimRec m -> PrimRec (TS (TS m)) -> PrimRec (TS m)
deriving instance Show (PrimRec n)

-- Try a polymorphic interpreter? I wish Haskell had better representation of non-neg integers
interp :: (Num a, Ord a) => (PrimRec n) -> Vect n a -> a
interp pr args = case pr of
    PrZero -> 0
    PrSucc -> index args FZ + 1
    PrProj i -> index args i
    PrComp f gs -> interp f $ fmap (\g -> interp g args) gs
    PrRDef f g -> h args where
        h (VCons x xs) = if x == 0 then interp f xs else -- TODO fail-fast negatives?
            let r = h (VCons (x-1) xs) in interp g (VCons r (VCons x xs))

interpChecked :: (Num a, Ord a, Show a) => (PrimRec n) -> Vect n a -> a
interpChecked pr = interp pr . negCheck

negCheck :: (Num a, Ord a, Show a) => Vect n a -> Vect n a
negCheck xs = if vand (>0) xs then xs else error $ "negCheck failed for " ++ show xs

-- Useful abbreviations, polymorphic in type
pi0 = PrProj FZ   :: PrimRec (TS n)
pi1 = PrProj fin1 :: PrimRec (TS (TS n))
pi2 = PrProj fin2 :: PrimRec (TS (TS (TS n)))
pi3 = PrProj fin3 :: PrimRec (TS (TS (TS (TS n))))
pi4 = PrProj fin4 :: PrimRec (TS (TS (TS (TS (TS n)))))
pi5 = PrProj fin5 :: PrimRec (TS (TS (TS (TS (TS (TS n))))))


-- Example functions:
prId :: PrimRec T1
prId = pi0

prPlus :: PrimRec T2
prPlus = PrRDef prId $ PrComp PrSucc $ mkVect1 pi0

prConstZ :: PrimRec n
prConstZ = PrComp PrZero VNil

prMult :: PrimRec T2
prMult = PrRDef prConstZ $ PrComp prPlus $ mkVect2 pi2 pi0



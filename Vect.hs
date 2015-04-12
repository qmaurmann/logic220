{-#LANGUAGE GADTs, StandaloneDeriving #-}

module Vect where

-- Type level naturals. Is there a way to disallow nonsense like S Char ?
data TZ
data TS n

-- Lists of length n
data Vect n a where
    VNil :: Vect TZ a
    VCons :: a -> Vect n a -> Vect (TS n) a
deriving instance (Show a) => Show (Vect n a)

-- type of numbers less than n
data Fin n where
    FZ :: Fin (TS n)  -- zero less than every successor
    FS :: Fin n -> Fin (TS n)
deriving instance Show (Fin n)

-- they work together. can GHC recognize that the pattern match is complete? impossible to pass Nil here.
index :: Vect n a -> Fin n -> a
index (VCons x _) FZ = x
index (VCons _ xs) (FS fn) = index xs fn

instance Functor (Vect n) where
    fmap g v = case v of
        VNil -> VNil
        VCons x xs -> VCons (g x) (fmap g xs)

vand :: (a -> Bool) -> Vect n a -> Bool
vand p = vfoldr (&&) True . fmap p

vfoldl :: (a -> b -> a) -> a -> Vect n b -> a
vfoldl _ a VNil = a
vfoldl f a (VCons b bs) = vfoldl f (f a b) bs

vfoldr :: (a -> b -> b) -> b -> Vect n a -> b
vfoldr _ b VNil = b
vfoldr f b (VCons a as) = vfoldr f (f a b) as

-- Handy abbreviations

type T1 = TS TZ
type T2 = TS T1
type T3 = TS T2
type T4 = TS T3
type T5 = TS T4

mkVect1 a = VCons a VNil
mkVect2 a b = VCons a $ mkVect1 b
mkVect3 a b c = VCons a $ mkVect2 b c
mkVect4 a b c d = VCons a $ mkVect3 b c d
mkVect5 a b c d e = VCons a $ mkVect4 b c d e

fin0 = FZ
fin1 = FS fin0
fin2 = FS fin1
fin3 = FS fin2
fin4 = FS fin3
fin5 = FS fin4



-- is there a way to do addition/concatenation :: Vect n a -> Vect m a -> Vect (n+m) a ?
data Plus m n

data PlusProof p s where
    LZero :: PlusProof (Plus TZ n) n  -- proof that 0 + n = n
    LSucc :: PlusProof (Plus m n) s -> PlusProof (Plus (TS m) n) (TS s) -- proof that S(m) + n = S(m+n)

deriving instance Show (PlusProof p s)

concatWithProof :: PlusProof (Plus m n) s -> Vect m a -> Vect n a -> Vect s a
concatWithProof LZero VNil ys = ys
concatWithProof (LSucc pp) (VCons x xs) ys = VCons x $ concatWithProof pp xs ys

-- is there a way to get the compiler to unify e.g. Plus (S (S Z)) (S (S (S Z))) with S (S (S (S (S Z))))
-- by automatically generating the proof for those types?
-- One tricky thing is that to e.g. add 2 to a number, I need to provide the polymorphic proof
-- LSucc (LSucc LZero) :: PlusProof (Plus (S (S Z)) s) (S (S s))
-- Where the inner LSucc has type for "adding to 0" and outer type for "adding to 1"... so e.g. iterate doesn't work


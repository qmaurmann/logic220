{-#LANGUAGE GADTs, StandaloneDeriving #-}

module DepTypes where

-- Type level naturals. Is there a way to disallow nonsense like TS Char ?
data T0
data TS n

-- Lists of length n
data Vect n a where
    VNil :: Vect T0 a
    VCons :: a -> Vect n a -> Vect (TS n) a
deriving instance (Eq a) => Eq (Vect n a)
deriving instance (Ord a) => Ord (Vect n a)
deriving instance (Show a) => Show (Vect n a)

-- type of numbers less than n
data Fin n where
    F0 :: Fin (TS n)  -- zero less than every successor
    FS :: Fin n -> Fin (TS n)
deriving instance Eq (Fin n)
deriving instance Ord (Fin n)
deriving instance Show (Fin n)

-- they work together. can GHC recognize that the pattern match is complete?
-- impossible to pass Nil here.
index :: Vect n a -> Fin n -> a
index (VCons x _) F0 = x
index (VCons _ xs) (FS fn) = index xs fn

vhead :: Vect (TS n) a -> a
vhead = (`index` F0)

vtail :: Vect (TS n) a -> Vect n a
vtail (VCons _ xs) = xs

-- the idea of U is to unify type an value level nats
data U n where    
    U0 :: U T0
    US :: U n -> U (TS n)
deriving instance Eq (U n)
deriving instance Ord (U n)
deriving instance Show (U n)

-- For example U is needed to write the following function, which generates
-- the values of Fin n type in increasing order
getFins :: U n -> Vect n (Fin n)
getFins U0 = VNil
getFins (US u) = VCons F0 $ fmap FS $ getFins u

instance Functor (Vect n) where
    fmap g v = case v of
        VNil -> VNil
        VCons x xs -> VCons (g x) (fmap g xs)

vand :: (a -> Bool) -> Vect n a -> Bool
vand p = vfoldr (&&) True . fmap p

vor :: (a -> Bool) -> Vect n a -> Bool
vor p = vfoldr (||) False . fmap p

vfoldl :: (a -> b -> a) -> a -> Vect n b -> a
vfoldl _ a VNil = a
vfoldl f a (VCons b bs) = vfoldl f (f a b) bs

vfoldr :: (a -> b -> b) -> b -> Vect n a -> b
vfoldr _ b VNil = b
vfoldr f b (VCons a as) = vfoldr f (f a b) as

-- Handy abbreviations

type T1 = TS T0
type T2 = TS T1
type T3 = TS T2
type T4 = TS T3
type T5 = TS T4

mkVect1 a = VCons a VNil
mkVect2 a b = VCons a $ mkVect1 b
mkVect3 a b c = VCons a $ mkVect2 b c
mkVect4 a b c d = VCons a $ mkVect3 b c d
mkVect5 a b c d e = VCons a $ mkVect4 b c d e

fin0 = F0
fin1 = FS fin0
fin2 = FS fin1
fin3 = FS fin2
fin4 = FS fin3
fin5 = FS fin4

u1 = US U0
u2 = US u1
u3 = US u2
u4 = US u3
u5 = US u4

-- is there a way to do addition/concatenation :: Vect n a -> Vect m a -> Vect (n+m) a ?
data Plus m n

data PlusProof p s where
    -- proof that 0 + n = n
    LZero :: PlusProof (Plus T0 n) n
    -- proof that S(m) + n = S(m+n)
    LSucc :: PlusProof (Plus m n) s -> PlusProof (Plus (TS m) n) (TS s)
deriving instance Show (PlusProof p s)

concatWithProof :: PlusProof (Plus m n) s -> Vect m a -> Vect n a -> Vect s a
concatWithProof LZero VNil ys = ys
concatWithProof (LSucc pp) (VCons x xs) ys = VCons x $ concatWithProof pp xs ys


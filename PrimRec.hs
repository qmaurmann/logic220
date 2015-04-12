{-#LANGUAGE GADTs, StandaloneDeriving #-}

-- Type level naturals. Is there a way to disallow nonsense like S Char ?
data Z
data S n

-- Lists of length n
data Vect n a where
    Nil :: Vect Z a
    Cons :: a -> Vect n a -> Vect (S n) a
deriving instance (Show a) => Show (Vect n a)

-- type of numbers less than n
data Fin n where
    FZ :: Fin (S n)  -- zero less than every successor
    FS :: Fin n -> Fin (S n)
deriving instance Show (Fin n)

-- they work together. can GHC recognize that the pattern match is complete? impossible to pass Nil here.
index :: Vect n a -> Fin n -> a
index (Cons x _) FZ = x
index (Cons _ xs) (FS fn) = index xs fn

instance Functor (Vect n) where
    fmap g v = case v of
        Nil -> Nil
        Cons x xs -> Cons (g x) (fmap g xs)



-- is there a way to do addition/concatenation :: Vect n a -> Vect m a -> Vect (n+m) a ?
data Plus m n

data PlusProof p s where
    LZero :: PlusProof (Plus Z n) n  -- proof that 0 + n = n
    LSucc :: PlusProof (Plus m n) s -> PlusProof (Plus (S m) n) (S s) -- proof that S(m) + n = S(m+n)

deriving instance Show (PlusProof p s)

concatWithProof :: PlusProof (Plus m n) s -> Vect m a -> Vect n a -> Vect s a
concatWithProof LZero Nil ys = ys
concatWithProof (LSucc pp) (Cons x xs) ys = Cons x $ concatWithProof pp xs ys

-- is there a way to get the compiler to unify e.g. Plus (S (S Z)) (S (S (S Z))) with S (S (S (S (S Z))))
-- by automatically generating the proof for those types?
-- One tricky thing is that to e.g. add 2 to a number, I need to provide the polymorphic proof
-- LSucc (LSucc LZero) :: PlusProof (Plus (S (S Z)) s) (S (S s))
-- Where the inner LSucc has type for "adding to 0" and outer type for "adding to 1"... so e.g. iterate doesn't work



-- Even without addition, I should be able to implement PrimRec in Haskell, right?

data PrimRec n where
    PrZero :: PrimRec Z
    PrSucc :: PrimRec (S Z)
    PrProj :: Fin n -> PrimRec n
    PrComp :: PrimRec m -> Vect m (PrimRec k) -> PrimRec k
    PrRDef :: PrimRec m -> PrimRec (S (S m)) -> PrimRec (S m)
deriving instance Show (PrimRec n)

-- Try a polymorphic interpreter? I wish Haskell had better representation of non-neg integers
interp :: (Num a, Ord a) => (PrimRec n) -> Vect n a -> a
interp pr args = case pr of
    PrZero -> 0
    PrSucc -> index args FZ + 1
    PrProj i -> index args i
    PrComp f gs -> interp f $ fmap (\g -> interp g args) gs
    PrRDef f g -> h args where
        h (Cons x xs) = if x == 0 then interp f xs else -- TODO fail-fast negatives?
            let r = h (Cons (x-1) xs) in interp g (Cons r (Cons x xs))

interpChecked :: (Num a, Ord a, Show a) => (PrimRec n) -> Vect n a -> a
interpChecked pr = interp pr . negCheck

negCheck :: (Num a, Ord a, Show a) => Vect n a -> Vect n a
negCheck xs = if vand (>0) xs then xs else error $ "negCheck failed for " ++ show xs

vand :: (a -> Bool) -> Vect n a -> Bool
vand p = vfoldr (&&) True . fmap p

vfoldl :: (a -> b -> a) -> a -> Vect n b -> a
vfoldl _ a Nil = a
vfoldl f a (Cons b bs) = vfoldl f (f a b) bs

vfoldr :: (a -> b -> b) -> b -> Vect n a -> b
vfoldr _ b Nil = b
vfoldr f b (Cons a as) = vfoldr f (f a b) as

prPlus :: PrimRec (S (S Z))
prPlus = PrRDef (PrProj FZ) $ PrComp PrSucc $ Cons (PrProj FZ) Nil
-- seems to work!


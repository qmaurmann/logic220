module Arithmetic where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Maybe (fromMaybe)

data Variable = Variable String deriving (Eq, Ord, Show)

data Term = Zero | VarTerm Variable | Succ Term | Plus Term Term | Times Term Term
    deriving (Eq, Ord, Show)

data Form = Bottom | Equals Term Term | Arrow Form Form | Exists Variable Form
    deriving (Eq, Ord, Show)

data ExtTerm = ExtTerm Term (Set Variable) deriving (Eq, Ord, Show)
data ExtForm = ExtForm Form (Set Variable) deriving (Eq, Ord, Show)

-- Haskell records are annoying (and derive Show badly), but having getters is helpful
getTerm (ExtTerm t _) = t
getVarsT (ExtTerm _ vs) = vs
getForm (ExtForm f _) = f
getVarsF (ExtForm _ vs) = vs

-- Smart constructors for ExtTerm and ExtForm. An ExtTerm or -Formula made using
-- only smart constructors will have as variable set exactly the set of free
-- vars in the term, in particular will be a full extended formula
mkZero = ExtTerm Zero Set.empty
mkVarTerm v = ExtTerm (VarTerm v) (Set.singleton v)
mkSucc (ExtTerm t vs) = ExtTerm (Succ t) vs
mkPlus (ExtTerm t1 vs1) (ExtTerm t2 vs2) = ExtTerm (Plus t1 t2) (Set.union vs1 vs2)
mkTimes (ExtTerm t1 vs1) (ExtTerm t2 vs2) = ExtTerm (Times t1 t2) (Set.union vs1 vs2)

-- Smart constructors for FullExtForm
mkBottom = ExtForm Bottom Set.empty
mkEquals (ExtTerm t1 vs1) (ExtTerm t2 vs2) = ExtForm (Equals t1 t2) (Set.union vs1 vs2)
mkArrow (ExtForm f1 vs1) (ExtForm f2 vs2) = ExtForm (Arrow f1 f2) (Set.union vs1 vs2)
mkExists v (ExtForm f vs) = ExtForm (Exists v f) (Set.delete v vs)
-- derived smart constructors
mkNot f = mkArrow f mkBottom
mkOr f1 f2 = mkArrow (mkNot f1) f2
mkAnd f1 f2 = mkNot $ mkOr (mkNot f1) (mkNot f2)
mkForall v f = mkNot $ mkExists v $ mkNot f
-- TODO mkExistsUnique v f

-- example functions?

-- TODO: actually test substTerm and substForm.
substTerm :: ExtTerm -> Map Variable ExtTerm -> ExtTerm
substTerm (ExtTerm t vs) bindings = case t of
    Zero -> mkZero
    VarTerm v -> fromMaybe (mkVarTerm v) (Map.lookup v bindings)
    Succ t1 -> mkSucc (recurse t1)
    Plus t1 t2 -> mkPlus (recurse t1) (recurse t2)
    Times t1 t2 -> mkTimes (recurse t1) (recurse t2)
  where
    recurse term = substTerm (ExtTerm term vs) bindings

substForm :: ExtForm -> Map Variable ExtTerm -> ExtForm
substForm (ExtForm f vs) bindings = case f of
    Bottom -> mkBottom
    Equals t1 t2 -> mkEquals (recurseT t1) (recurseT t2)
    Arrow f1 f2 -> mkArrow (recurseF f1) (recurseF f2)
    Exists v f1 -> mkExists v (substForm (ExtForm f1 vs) (Map.delete v bindings))
  where
    recurseT term = substTerm (ExtTerm term vs) bindings
    recurseF form = substForm (ExtForm form vs) bindings

-- TODO: how ready am I to start the PrimRec -> FullExtForm compiler?


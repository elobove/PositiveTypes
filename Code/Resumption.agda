{- Doesn't type-check because Resumption isn't strictly positive -}

module Resumption where

data Cont (r : Set) (a : Set) : Set where
  c : ((a → r) → r) → Cont r a

-- Resumption is not strictly positive, because it occurs in the second argument
-- to Cont in the type of the constructor More in the definition of Resumption.

data Resumption (r : Set) (a : Set) : Set where
  Done : a → Resumption r a
  More : (Cont r (Resumption r a)) → Resumption r a

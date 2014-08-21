{- Doesn't type-check because Resumption isn't strictly positive -}

module Resumption where

data Cont (R A : Set) : Set where
  c : ((A → R) → R) → Cont R A

-- Resumption is not strictly positive, because it occurs in the second argument
-- to Cont in the type of the constructor more in the definition of Resumption.

data Resumption (R A : Set) : Set where
  done : A → Resumption R A
  more : Cont R (Resumption R A) → Resumption R A

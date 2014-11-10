-- From: Ralph Matthes (2000). Lambda Calculus:  A Case
-- for Inductive Definitions. § 8.1.

-- Creation date: 7 October 2014

{-# LANGUAGE UnicodeSyntax #-}

module Continuations where

-- Binary tree
data Btree = L Int | N Int Btree Btree

-- Continuations : non-strictly positive
data Cont = D | C ((Cont → [Int]) → [Int])

apply :: Cont → (Cont → [Int]) → [Int]
apply D     g = g D
apply (C f) g = f g

breadth :: Btree → Cont → Cont
breadth (L x)     k = C $ \g → x : (apply k g)
breadth (N x s t) k = C $ \g → x : (apply k (g . breadth s . breadth t))

-- Iteration on the data type Cont
ex :: Cont → [Int]
ex D     = []
ex (C f) = f ex

breadthfirst :: Btree → [Int]
breadthfirst t = ex $ breadth t D

-- Example
extree :: Btree
extree = N 1 (N 2 (L 7) (N 3 (L 5) (L 4))) (N 4 (N 6 (L 2) (L 9)) (L 8))

result :: [Int]
result = breadthfirst extree

exList :: [Int]
exList = [1,2,4,7,3,6,8,5,4,2,9]

ok :: Bool
ok = result == exList

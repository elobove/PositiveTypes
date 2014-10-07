-- From: Ralph Matthes (2000). Lambda Calculus:  A Case
-- for Inductive Defnitions. § 8.1.

-- Creation date: 7 October 2014

{-# LANGUAGE UnicodeSyntax #-}

module Continuations where

-- Binary tree
data Btree = L Int | N Int Btree Btree

-- List of Natural numbers
data List = Nil | Cons Int List
          deriving (Show, Eq)

-- Continuations : non-strictly positive
data Cont = D | C ((Cont → List) → List)

apply :: Cont → (Cont → List) → List
apply D     g = g D
apply (C f) g = f g

breadth :: Btree → Cont → Cont
breadth (L x)     k = C $ \g → Cons x (apply k g)
breadth (N x s t) k = C $ \g → Cons x (apply k (g . breadth s . breadth t))

-- Iteration on the data type Cont
ex :: Cont → List
ex D     = Nil
ex (C f) = f ex

breadthfirst :: Btree → List
breadthfirst t = ex $ breadth t D

-- Example
extree :: Btree
extree = N 1 (N 2 (L 7) (N 3 (L 5) (L 4))) (N 4 (N 6 (L 2) (L 9)) (L 8))

result :: List
result = breadthfirst extree

exList :: List
exList = Cons 1
         (Cons 2
          (Cons 4
           (Cons 7
            (Cons 3 (Cons 6 (Cons 8 (Cons 5 (Cons 4 (Cons 2 (Cons 9 Nil))))))))))

ok :: Bool
ok = result == exList

commonList :: List → [Int]
commonList Nil         = []
commonList (Cons x xs) = x : commonList xs

prettyR :: [Int]
prettyR  = commonList result

prettyEx :: [Int]
prettyEx = commonList exList

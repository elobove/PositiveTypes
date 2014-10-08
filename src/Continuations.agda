-- From: Ralph Matthes (2000). Lambda Calculus:  A Case
-- for Inductive Defnitions. § 8.1.

-- Tested with Agda 2.4.2 and the standard library 0.8.1.

-- Creation date: 7 October 2014

{-# OPTIONS --no-positivity-check #-}
module Continuations where

open import Data.Nat
open import Data.List
open import Function using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Btree : Set where
  L : (x : ℕ) → Btree
  N : (x : ℕ) (l r : Btree) → Btree

data Cont : Set where
  D : Cont
  C : ((Cont → List ℕ) → List ℕ) → Cont

apply : Cont → (Cont → List ℕ) → List ℕ
apply D     g = g D
apply (C f) g = f g

breadth : Btree → Cont → Cont
breadth (L x)     k = C $ λ g → x ∷ (apply k g)
breadth (N x s t) k = C $ λ g → x ∷ (apply k (g ∘ breadth s ∘ breadth t))

{-# NO_TERMINATION_CHECK #-}
ex : Cont → List ℕ
ex D     = []
ex (C f) = f ex

breadthfirst : Btree → List ℕ
breadthfirst t = ex $ breadth t D

-- Example
one : ℕ
one = suc zero

two : ℕ
two = suc one

three : ℕ
three = suc two

four : ℕ
four = suc three

five : ℕ
five = suc four

six : ℕ
six = suc five

seven : ℕ
seven = suc six

eight : ℕ
eight = suc seven

nine : ℕ
nine = suc eight

extree : Btree
extree = N one (N two (L seven) (N three (L five) (L four)))
               (N four (N six (L two) (L nine)) (L eight))

result : List ℕ
result = breadthfirst extree

exList : List ℕ
exList = one ∷ two ∷ four ∷ seven ∷ three ∷ six ∷
         eight ∷ five ∷ four ∷ two ∷ nine ∷ []

ok : result ≡ exList
ok = refl

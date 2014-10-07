{-# OPTIONS --no-termination-check  --no-positivity-check #-}
module Continuations where

open import Data.Nat
open import Function using (_∘_; _$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Btree : Set where
  L : (x : ℕ) → Btree
  N : (x : ℕ) (l r : Btree) → Btree

data List : Set where
  nil  : List
  cons : (x : ℕ) → List → List

data Cont : Set where
  D : Cont
  C : ((Cont → List) → List) → Cont

apply : Cont → (Cont → List) → List
apply D     g = g D
apply (C f) g = f g

breadth : Btree → Cont → Cont
breadth (L x)     k = C $ λ g → cons x (apply k g)
breadth (N x s t) k = C $ λ g → cons x (apply k (g ∘ breadth s ∘ breadth t))

ex : Cont → List
ex D     = nil
ex (C f) = f ex

breadthfirst : Btree → List
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

result : List
result = breadthfirst extree

exList : List
exList = cons one (cons two (cons four (cons seven (cons three (cons six
         (cons eight (cons five (cons four (cons two (cons nine nil))))))))))

ok : result ≡ exList
ok = refl

{-# OPTIONS --no-positivity-check #-}
module ContApia where

infixl 9 _∙_
infixr 5 _∷_

postulate
  D         : Set
  zero [] d : D
  succ      : D → D
  _∙_ _∷_   : D → D → D
  lam       : (D → D) → D
  node      : D → D → D → D
  cont      : ((D → D) → D) → D

data N : D → Set where
  nzero : N zero
  nsucc : ∀ {n} → N n → N (succ n)

-- List of Natural numbers
data ListN : D → Set where
  lnnil  : ListN []
  lncons : ∀ {n ns} → N n → ListN ns → ListN (n ∷ ns)

-- Binary Nat Tree
data Btree : D → Set where
  Leaf : ∀ {x} → N x → Btree x
  Node : ∀ {x l r} → N x → Btree l → Btree r → Btree (node x l r)

-- Continuations
data Cont : D → Set where
  D' : Cont d
  C' : ∀ {f xs ys} → ((Cont f → ListN xs) → ListN ys) →
    Cont (cont lam)

apply : ∀ {f xs} → Cont f → (Cont f → ListN xs) → ListN xs
apply D'     h = h D'
apply (C' k) h = k h
{-# ATP definition apply #-}

-- breadth : ∀ {t f} → Btree t → Cont f → Cont f
-- breadth (Leaf x)     k = C' ( λ g → x ∷ (apply k g) )
-- breadth (Node x s t) k = C' ( λ g → x ∷ (apply k (g ∙ breadth s ∙ breadth t)))
-- {-# ATP definition breadth #-}

-- Example
one   = succ zero
two   = succ one
three = succ two
four  = succ three
five  = succ four
six   = succ five
seven = succ six
eight = succ seven
nine  = succ eight

1N : N one
1N = nsucc nzero

2N : N two
2N = nsucc 1N

3N : N three
3N = nsucc 2N

4N : N four
4N = nsucc 3N

5N : N five
5N = nsucc 4N

6N : N six
6N = nsucc 5N

7N : N seven
7N = nsucc 6N

8N : N eight
8N = nsucc 7N

9N : N nine
9N = nsucc 8N

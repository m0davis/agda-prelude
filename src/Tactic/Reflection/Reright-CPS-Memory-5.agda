module Tactic.Reflection.Reright-CPS-Memory-5 where

{-
In the below code, I observe a non-linearity in Agda's use of space and time.

* Why does `normalise-slow` use so much time as compared to `normalise-quick`?
* Why does `normalise-space-leak` use so much space?
* Why does `show-quick` use more time than `normalise-quick`?
-}

open import Agda.Builtin.List
open import Agda.Builtin.Nat

-- build a list of replicated items
replicate : Nat → Nat → List Nat
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x

-- get the last element of a list (0 if the list is empty)
-- I use this in the tests below to rule-out the possibility of problems arising from large items passed to emacs
safeLast : List Nat → Nat
safeLast [] = 0
safeLast (x ∷ []) = x
safeLast (x ∷ xs) = safeLast xs

-- using continuation passing style to fully evaluate a list and then apply to it the given function
id-List& : List Nat → ∀ {b} {B : Set b} → (List Nat → B) → B
--id-List& : List Nat → {B : Set} → (List Nat → B) → B
--id-List& : List Nat → (List Nat → List Nat) → List Nat
id-List& [] f = f []
id-List& (x ∷ xs) f = id-List& xs λ xs → f (x ∷ xs)

id : List Nat → List Nat
id x = x

-- a trivial way of using id-List&
id-ListNat : List Nat → List Nat
id-ListNat xs = id-List& xs λ xs → xs

quick slow space-leak : List Nat
-- some test cases
quick      = replicate 1000 0
slow       = replicate 2000 0
space-leak = replicate 2000000 10000

infixr 0 _,_
data Pair (A B : Set) : Set where
  _,_ : A → B → Pair A B

Suc : Nat → Nat
Suc n = n
{-# INLINE Suc #-}

id-Nat& : Nat → {B : Set} → (Nat → B) → B
id-Nat& zero f = f zero
id-Nat& (suc n) f = id-Nat& n λ n → f (Suc n)

replicate-quick replicate-slow replicate-space-leak : List Nat
replicate-quick       = {!quick!}
replicate-slow        = {!slow!}
replicate-space-leak  = {!id-Nat& (safeLast space-leak) λ s → s , s , s!}

normalise-quick normalise-slow normalise-space-leak : List Nat
-- test each of these using C-c C-n
normalise-quick       = {! (id-ListNat quick)!}      -- runs quickly
normalise-slow        = {! (id-ListNat slow)!}       -- runs slowly (over 2x slower than normalise-quick)
normalise-space-leak  = {!safeLast (id-ListNat space-leak)!} -- runs slowly and eats lots of memory

postulate
  show : List Nat → Set

show-quick      : show (id-ListNat quick)
show-slow       : show (id-ListNat slow)
show-space-leak : show (id-ListNat space-leak)
-- test each of these using C-u C-u C-c C-,
show-quick      = {!!} -- runs more slowly than normalise-quick
show-slow       = {!!} -- also runs slowly
show-space-leak = {!!} -- runs slowly and eats lots of memory

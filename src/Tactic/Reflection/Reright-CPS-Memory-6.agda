module Tactic.Reflection.Reright-CPS-Memory-6 where

{-
In the below code, I observe a non-linearity in Agda's use of space and time.

* Why does `normalise-slow` use so much time as compared to `normalise-quick`?
* Why does `normalise-space-leak` use so much space?
* Why does `show-quick` use more time than `normalise-quick`?
-}

open import Agda.Builtin.List
open import Agda.Builtin.Nat

-- build a list of replicated items
replicate : ∀ {a} {A : Set a} → Nat → A → List A
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x

-- using continuation passing style to fully evaluate a list and then apply to it the given function
--id-List& : ∀ {A : Set} → List A → {B : Set} → (List A → B) → B
id-List& : List Nat → (List Nat → List Nat) → List Nat
id-List& [] f = f []
id-List& (x ∷ xs) f = id-List& xs λ xs → f (x ∷ xs)

-- a trivial way of using id-List&
id-ListNat : List Nat → List Nat
id-ListNat xs = id-List& xs λ xs → xs

quick slow space-leak : List Nat
-- some test cases
quick      = replicate 1000 0
slow       = replicate 2000 0
space-leak = replicate 4000 0

normalise-quick normalise-slow normalise-space-leak : List Nat
-- test each of these using C-c C-n
normalise-quick       = {!id-ListNat quick!}      -- runs quickly
normalise-slow        = {!id-ListNat slow!}       -- runs slowly (over 2x slower than normalise-quick)
normalise-space-leak  = {!id-ListNat space-leak!} -- runs slowly and eats lots of memory

postulate
  show : List Nat → Set

show-quick      : show (id-ListNat quick)
show-slow       : show (id-ListNat slow)
show-space-leak : show (id-ListNat space-leak)
-- test each of these using C-u C-u C-c C-,
show-quick      = {!!} -- runs more slowly than normalise-quick
show-slow       = {!!} -- also runs slowly
show-space-leak = {!!} -- runs slowly and eats lots of memory

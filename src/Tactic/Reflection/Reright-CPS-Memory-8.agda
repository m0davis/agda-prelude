module Tactic.Reflection.Reright-CPS-Memory-8 where

{- Performance issue with deeply-nested lambdas -}

{-
In the code below, `foo` should normalise linearly in the size of its argument, yet Agda's actual normalisation behavior is non-linear.
-}

open import Agda.Builtin.Nat

foo : Nat → (Nat → Nat) → Nat
foo zero f = f zero
foo (suc n) f = foo n λ n → f (suc n)

test-1 : Nat
test-1 = {!foo 2000 (λ n → n)!} -- C-c C-n is fast

test-2 : Nat
test-2 = {!foo 10000 (λ n → n)!} -- C-c C-n generates a space leak

{- steps to normalise `foo 3 (λ n → n)`
foo 3                            (λ n → n)
foo (suc 2)                      (λ n → n)
foo 2                     (λ n → (λ n → n) (suc 2))
foo (suc 1)               (λ n → (λ n → n) (suc 2))
foo 1              (λ n → (λ n → (λ n → n) (suc 2)) (suc 1))
foo (suc 0)        (λ n → (λ n → (λ n → n) (suc 2)) (suc 1))
foo 0       (λ n → (λ n → (λ n → (λ n → n) (suc 2)) (suc 1)) (suc 0))
(λ n → (λ n → (λ n → (λ n → n) (suc 2)) (suc 1)) (suc 0)) 0
       (λ n → (λ n → (λ n → n) (suc 2)) (suc 1)) (suc 0)
              (λ n → (λ n → n) (suc 2)) (suc 1)
                     (λ n → n) (suc 2)
                                suc 2
-}

foo' : Nat → (Nat → Nat) → Nat
foo' zero    f = f zero
foo' (suc n) f = foo' n (fsuc f) where
  fsuc : (Nat → Nat) → Nat → Nat
  fsuc f n = f (suc n)

test-3 : Nat
test-3 = {!foo' 10000 (λ n → n)!}

foo'' : Nat → (Nat → Nat) → Nat
foo'' zero    f = f zero
foo'' (suc n) f = foo' n (fsuc f) where
  fsuc = λ f n → f (suc n)


test-4 : Nat
test-4 = {!foo'' 3500000 (λ { n → n })!}

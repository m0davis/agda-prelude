module Tactic.Reflection.Reright-CPS-Memory-7 where

{-
In the code below, I note that the test of `bar` generates a space leak yet the (quite similar) `foo` is fast. I'm guessing that only the reason `foo` is fast has to do with some optimization in Agda having to do with the trivial lambda abstraction, `λ n → n`. Is that correct?

In any case, I am surprised by the space leak from `bar`. I've outlined below what I think the steps of evaluation are and it's linear in the size of the argument passed to `bar`.
-}

open import Agda.Builtin.Nat

foo : Nat → (Nat → Nat) → Nat
foo zero f = f zero
foo (suc n) f = foo n λ n → f n

test-foo : Nat
test-foo = {!foo 90000 λ n → n!} -- C-c C-n is fast

{- steps to evaluate foo 3 (λ n → n)
foo 3       (λ n → n)
foo (suc 2) (λ n → n)
foo 2       (λ n → (λ n → n) 2)
foo (suc 1) (λ n → (λ n → n) 2)
foo 1       (λ n → (λ n → (λ n → n) 2) 1)
foo (suc 0) (λ n → (λ n → (λ n → n) 2) 1)
foo 0       (λ n → (λ n → (λ n → (λ n → n) 2) 1) 0)
(λ n → (λ n → (λ n → (λ n → n) 2) 1) 0) 0
(λ n → (λ n → (λ n → n) 2) 1) 0
(λ n → (λ n → n) 2) 1
(λ n → n) 2
2
-}

bar : Nat → (Nat → Nat) → Nat
bar zero f = f zero
bar (suc n) f = bar n λ n → f (suc n)

test-bar-1 : Nat
test-bar-1 = {!bar 2000 λ n → n!} -- C-c C-n is fast

test-bar-2 : Nat
test-bar-2 = {!bar 10000 λ n → n!} -- C-c C-n generates a space leak

{- steps to evaluate bar 3 (λ n → n)
bar 3                            (λ n → n)
bar (suc 2)                      (λ n → n)
bar 2                     (λ n → (λ n → n) (suc 2))
bar (suc 1)               (λ n → (λ n → n) (suc 2))
bar 1              (λ n → (λ n → (λ n → n) (suc 2)) (suc 1))
bar (suc 0)        (λ n → (λ n → (λ n → n) (suc 2)) (suc 1))
bar 0       (λ n → (λ n → (λ n → (λ n → n) (suc 2)) (suc 1)) (suc 0))
(λ n → (λ n → (λ n → (λ n → n) (suc 2)) (suc 1)) (suc 0)) 0
       (λ n → (λ n → (λ n → n) (suc 2)) (suc 1)) (suc 0)
              (λ n → (λ n → n) (suc 2)) (suc 1)
                     (λ n → n) (suc 2)
                                suc 2
-}

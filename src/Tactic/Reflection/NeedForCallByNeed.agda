module Tactic.Reflection.NeedForCallByNeed where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

max : Nat → Nat → Nat
max n m with n < m
... | true = m
... | false = n

max42 : Nat → Nat
max42 = max 42

test : max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 100)))))))))))))))))))))))))))))) ≡ 100
test = refl

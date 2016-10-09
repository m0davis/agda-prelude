-- compare agda issue 426
module Tactic.Reflection.SharingExamples where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

M : Nat -> Nat -> Nat
M 0       k = 0
M (suc n) k
  with suc (M n k)
... | r
  with r < k
... | true = r
... | false = 0

test-M : M 100 10 ≡ 0
test-M = refl -- fast with --sharing, otherwise slow

case_of_ : ∀ {a} {A : Set a} {b} {B : Set b} → A → (A → B) → B
case_of_ x f = f x

S : Nat → Nat
S n = case n < zero of λ
      { true  → zero
      ; false → suc n }

S!! : Nat → Nat → Nat
S!! 0 n = S n
S!! (suc d) n with S!! d n
... | S!d with S!d < 0
... | true = zero
... | false = suc S!d

test-S!! : S!! 20 0 ≡ 21
test-S!! = refl

test-S : S(S(S(S(S(S(S(1))))))) ≡ 8
test-S = refl


module Prelude.Memoization where

open import Prelude.Product
open import Prelude.Equality

Mem : ∀ {a} {A : Set a} → A → Set a
Mem x = Σ _ (_≡ x)

μ₀ : ∀ {a b} {A : Set a} {B : Set b} → Σ A (λ _ → B) → A
μ₀ = fst

open import Tactic.Reflection
open import Prelude.Nat
open import Prelude
open import Tactic.Reflection.Quote

macro
  μ₂ : Term → Tactic
  μ₂ f hole = do
    case maybeSafe f of λ
    { nothing → typeError [ strErr "unexpected: term is not safe" ]
    ; (just f) → hole =′ `λ (`λ (def₁ (quote μ₀) (applyTerm (weaken 2 f) (vArg (var₀ 1) ∷ vArg (var₀ 0) ∷ [])))) }


module Prelude.List.Memoized where

open import Prelude.Memoization
open import Prelude.Product

open import Prelude.Nat
open import Prelude.Function
open import Prelude.Equality
open import Prelude.Semiring

open import Agda.Builtin.List public

lengthμ : ∀ {a} {A : Set a} → (xs : List A) → Nat × Mem xs
lengthμ []       = 0 , putμ refl
lengthμ (x ∷ xs) =
  case lengthμ xs of λ
  { (lengthμ-xs , putμ xs) →
    1 + lengthμ-xs , putμ (cong (x ∷_) xs) }

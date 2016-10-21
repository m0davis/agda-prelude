
module Prelude.List.Memoized where

open import Prelude.Memoization
open import Prelude.Product
open import Prelude.Equality.Memoized

open import Prelude.Decidable
open import Prelude.List

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

--- Equality ---

private

  decμ-∷ : ∀ {a} {A : Set a} {x : A} {xs : List A} {y : A}
             {ys : List A} → (Dec (x ≡ y) × Mem x × Mem y) → (Dec (xs ≡ ys) × Mem xs × Mem ys) → Dec (x ∷ xs ≡ y ∷ ys) × Mem (x ∷ xs) × Mem (y ∷ ys)
  decμ-∷ (x≡y , putμ x-refl , putμ y-refl) (xs≡ys , putμ xs-refl , putμ ys-refl) =
    (case x≡y , xs≡ys of λ
    { (yes refl , yes refl) → yes refl
    ; (_ , no neq) → no λ eq → neq (cons-inj-tail eq)
    ; (no neq , _) → no λ eq → neq (cons-inj-head eq) }) ,
    putμ (cong₂ _∷_ x-refl xs-refl) ,
    putμ (cong₂ _∷_ y-refl ys-refl)

  eqμList : ∀ {a} {A : Set a} {{EqμA : Eqμ A}} (xs ys : List A) → Dec (xs ≡ ys) × Mem xs × Mem ys
  eqμList [] [] = yes refl , putμ refl , putμ refl
  eqμList [] (_ ∷ _) = no (λ ()) , putμ refl , putμ (cong₂ _∷_ refl refl)
  eqμList (_ ∷ _) [] = no (λ ()) , putμ (cong₂ _∷_ refl refl) , putμ refl
  eqμList (x ∷ xs) (y ∷ ys) = decμ-∷ (x ==μ y) (eqμList xs ys)

instance
  EqμList : ∀ {a} {A : Set a} {{EqμA : Eqμ A}} → Eqμ (List A)
  _==μ_ {{EqμList}} = eqμList

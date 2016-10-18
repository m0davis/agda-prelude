
module Prelude.Equality.Memoized where

open import Prelude.Memoization
open import Prelude.Product
open import Prelude.Decidable

open import Agda.Builtin.Equality public

record Eqμ {a} (A : Set a) : Set a where
  infix 4 _==μ_
  field
    _==μ_ : (x y : A) → Dec (x ≡ y) × Mem x × Mem y

open Eqμ {{...}} public

-- Decidable equality helpers --

decEqμ₁ : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} → (∀ {x y} → f x ≡ f y → x ≡ y) →
            ∀ {x y} → (x==y? : Dec (x ≡ y)) → Dec (f x ≡ f y) × Mem x==y?
decEqμ₁ f-inj (yes refl) = yes refl , (yes refl , refl)
decEqμ₁ f-inj (no  neq)  = no (λ eq → neq (f-inj eq)) , (no neq , refl)

decEqμ₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {f : A → B → C} →
           (∀ {x y z w} → f x y ≡ f z w → x ≡ z) →
           (∀ {x y z w} → f x y ≡ f z w → y ≡ w) →
           ∀ {x y z w} → (x==y? : Dec (x ≡ y)) → (z==w? : Dec (z ≡ w)) →
           Dec (f x z ≡ f y w) × Mem x==y? × Mem z==w?
decEqμ₂ f-inj₁ f-inj₂ (no neq)    z==w?     = no (λ eq → neq (f-inj₁ eq)) ,
                                              (no neq , refl) ,
                                              (z==w? , refl)
decEqμ₂ f-inj₁ f-inj₂  x==y?     (no neq)   = no (λ eq → neq (f-inj₂ eq)) ,
                                              (x==y? , refl) ,
                                              (no neq , refl)
decEqμ₂ f-inj₁ f-inj₂ (yes refl) (yes refl) = yes refl ,
                                              (yes refl , refl) ,
                                              (yes refl , refl)

{-# INLINE decEqμ₁ #-}
{-# INLINE decEqμ₂ #-}

-- Instances --

instance
  EqμEq : ∀ {a} {A : Set a} {x y : A} → Eqμ (x ≡ y)
  _==μ_ {{EqμEq}} refl refl = yes refl ,
                              (refl , refl) ,
                              (refl , refl)

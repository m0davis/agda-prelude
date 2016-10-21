
module Prelude.Equality.Memoized where

open import Prelude.Memoization
open import Prelude.Product
open import Prelude.Decidable
open import Prelude.Equality
open import Prelude.Function

open import Agda.Builtin.Equality public

record Eqμ {a} (A : Set a) : Set a where
  infix 4 _==μ_
  field
    _==μ_ : (x y : A) → Dec (x ≡ y) × Mem x × Mem y

open Eqμ {{...}} public

-- Decidable equality helpers --

decEqμ₁ : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} → (∀ {x y} → f x ≡ f y → x ≡ y) →
            ∀ {x y} → (x==μy? : Dec (x ≡ y) × Mem x × Mem y) → Dec (f x ≡ f y) × Mem (f x) × Mem (f y)
decEqμ₁ {f = f} f-inj (x==y? , putμ x-refl , putμ y-refl) =
  (case x==y? of λ
  { (no neq) → no λ eq → neq (f-inj eq)
  ; (yes refl) → yes refl }) ,
  putμ (cong f x-refl) ,
  putμ (cong f y-refl)

decEqμ₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {f : A → B → C} →
            (∀ {x y z w} → f x y ≡ f z w → x ≡ z) →
            (∀ {x y z w} → f x y ≡ f z w → y ≡ w) →
            ∀ {x y z w} → (x==μy? : Dec (x ≡ y) × Mem x × Mem y) → (z==μw? : Dec (z ≡ w) × Mem z × Mem w) →
            Dec (f x z ≡ f y w) × Mem (f x z) × Mem (f y w)
decEqμ₂ {f = f} f-inj₁ f-inj₂ (x==y? , putμ x-refl , putμ y-refl) (z==w? , putμ z-refl , putμ w-refl) =
  (case x==y? , z==w? of λ
  { (no neq , _) → no λ eq → neq (f-inj₁ eq)
  ; (_ , no neq) → no λ eq → neq (f-inj₂ eq)
  ; (yes refl , yes refl) → yes refl }) ,
  putμ (cong₂ f x-refl z-refl) ,
  putμ (cong₂ f y-refl w-refl)

{-# INLINE decEqμ₁ #-}
{-# INLINE decEqμ₂ #-}

-- Instances --

instance
  EqμEq : ∀ {a} {A : Set a} {x y : A} → Eqμ (x ≡ y)
  _==μ_ {{EqμEq}} refl refl = yes refl ,
                              (refl , refl) ,
                              (refl , refl)

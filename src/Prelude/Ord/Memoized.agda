module Prelude.Ord.Memoized where

open import Prelude.Memoization
open import Prelude.Product

open import Agda.Primitive
open import Prelude.Equality
open import Prelude.Decidable
open import Prelude.Bool
open import Prelude.Function

open import Prelude.Ord public

isLessμ : ∀ {a} {A : Set a} {R : A → A → Set a} {x y} → (c : Comparison R x y) → Bool × Mem c
isLessμ (less    _) = true , (_ , refl)
isLessμ (equal   _) = false , (_ , refl)
isLessμ (greater _) = false , (_ , refl)
{-# INLINE isLessμ #-}

isGreaterμ : ∀ {a} {A : Set a} {R : A → A → Set a} {x y} → (c : Comparison R x y) → Bool × Mem c
isGreaterμ (less    _) = false , (_ , refl)
isGreaterμ (equal   _) = false , (_ , refl)
isGreaterμ (greater _) = true , (_ , refl)
{-# INLINE isGreaterμ #-}

open import Tactic.Reflection

record Ordμ {a} (A : Set a) : Set (lsuc a) where
  infix 4 _<μ_ _≤μ_
  field
    _<μ_ : (l : A) → (r : A) → Set a × Mem l × Mem r
    _≤μ_ : (l : A) → (r : A) → Set a × Mem l × Mem r
    compareμ     : ∀ x y → Comparison (μ₂ _<μ_) x y × Mem x × Mem y
    eq-to-leqμ   : ∀ {x y} → (x≡y : x ≡ y) → μ₀ (x ≤μ y) × Mem x × Mem y × Mem x≡y
    lt-to-leqμ   : ∀ {x y} → (x<μy : fst (x <μ y)) → μ₀ (x ≤μ y) × Mem x × Mem y × Mem x<μy
    leq-to-lteqμ : ∀ {x y} → (x≤μy : fst (x ≤μ y)) → LessEq (μ₂ _<μ_) x y × Mem x × Mem y × Mem x≤μy

open Ordμ {{...}} public

{-# DISPLAY Ordμ._<μ_ _ a b = a <μ b #-}
{-# DISPLAY Ordμ._≤μ_ _ a b = a ≤μ b #-}
{-# DISPLAY Ordμ.compareμ     _ a b = compareμ a b #-}
{-# DISPLAY Ordμ.eq-to-leqμ   _ eq = eq-to-leqμ eq #-}
{-# DISPLAY Ordμ.lt-to-leqμ   _ eq = lt-to-leqμ eq #-}
{-# DISPLAY Ordμ.leq-to-lteqμ _ eq = leq-to-lteqμ eq #-}

module _ {a} {A : Set a} {{_ : Ordμ A}} where

  _>μ_ : (l : A) → (r : A) → Set a × Mem l × Mem r
  a >μ b =
    case b <μ a of λ
    { (b<μa , b , a) → b<μa , a , b }

  _≥μ_ : (l : A) → (r : A) → Set a × Mem l × Mem r
  a ≥μ b =
    case b ≤μ a of λ
    { (b≤μa , b , a) → b≤μa , a , b }

  infix 4 _>μ_ _≥μ_ _<?μ_ _≤?μ_ _>?μ_ _≥?μ_

  _<?μ_ : (l : A) → (r : A) → Bool × Mem l × Mem r
  x <?μ y =
    case compareμ x y of λ
    { (c , x , y) → μ₀ (isLessμ c) , x , y }

  _>?μ_ : (l : A) → (r : A) → Bool × Mem l × Mem r
  _>?μ_ a b =
    case flip _<?μ_ a b of λ
    { (b<?μa , b , a) → b<?μa , a , b }

  _≤?μ_ : (l : A) → (r : A) → Bool × Mem l × Mem r
  x ≤?μ y =
    case y <?μ x of λ
    { (y<?μx , y , x) → not y<?μx , x , y }

  _≥?μ_ : (l : A) → (r : A) → Bool × Mem l × Mem r
  x ≥?μ y =
    case x <?μ y of λ
    { (x<?μy , x , y) → not x<?μy , x , y }

  minμ : (l : A) → (r : A) → A × Mem l × Mem r
  minμ x y =
    case x <?μ y of λ
    { (x<?μy , x'@(x , _) , y'@(y , _)) → (if x<?μy then x else y) , x' , y' }

  maxμ : (l : A) → (r : A) → A × Mem l × Mem r
  maxμ x y =
    case x >?μ y of λ
    { (x>?μy , x'@(x , _) , y'@(y , _)) → (if x>?μy then x else fst y') , (_ , refl) , y' }

--- Instances ---

-- Default implementation of _≤_ --

defaultOrdμ : ∀ {a} {A : Set a} {_<μ_ : (l : A) → (r : A) → Set a × Mem l × Mem r} → (∀ x y → Comparison (λ l r → μ₀ (_<μ_ l r)) x y × Mem x × Mem y) → Ordμ A
Ordμ._<μ_         (defaultOrdμ {_<μ_ = _<μ_} compareμ) = _<μ_
Ordμ._≤μ_        (defaultOrdμ {_<μ_ = _<μ_} compareμ) = λ l r → LessEq (μ₂ _<μ_) l r , (_ , refl) , (_ , refl)
Ordμ.compareμ     (defaultOrdμ compareμ) = compareμ
Ordμ.eq-to-leqμ   (defaultOrdμ compareμ) = λ x≡y → equal x≡y , (_ , refl) , (_ , refl) , (_ , refl)
Ordμ.lt-to-leqμ   (defaultOrdμ compareμ) = λ x<y → less x<y , (_ , refl) , (_ , refl) , (_ , refl)
Ordμ.leq-to-lteqμ (defaultOrdμ compareμ) = λ x<μy → x<μy , (_ , refl) , (_ , refl) , (_ , refl)

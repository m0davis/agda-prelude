
module Prelude.Nat where

open import Prelude.Unit
open import Prelude.Empty
open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Equality
open import Prelude.Equality.Unsafe using (eraseEquality)
open import Prelude.Function
open import Prelude.Ord
open import Prelude.Number
open import Prelude.Semiring

open import Agda.Builtin.Nat public
  renaming ( _+_        to _+N_
           ; _*_        to _*N_
           ; _-_        to _-N_
           ; _==_       to eqNat
           ; _<_        to lessNat
           ; div-helper to divAux
           ; mod-helper to modAux )

{-# DISPLAY _+N_ = _+_ #-}
{-# DISPLAY _-N_ = _-_ #-}
{-# DISPLAY _*N_ = _*_ #-}

--- Semiring ---

instance
  NumberNat : Number Nat
  Number.Constraint NumberNat _ = ⊤
  Number.fromNat    NumberNat n = n

  SemiringNat : Semiring Nat
  zro {{SemiringNat}} = 0
  one {{SemiringNat}} = 1
  _+_ {{SemiringNat}} = _+N_
  _*_ {{SemiringNat}} = _*N_

  SubtractiveNat : Subtractive Nat
  _-_    {{SubtractiveNat}}   = _-N_
  negate {{SubtractiveNat}} _ = 0

--- Equality ---

NonZero : Nat → Set
NonZero zero    = ⊥
NonZero (suc _) = ⊤

suc-inj : ∀ {n m} → suc n ≡ suc m → n ≡ m
suc-inj refl = refl

private
  eqNatSound : ∀ n m → IsTrue (eqNat n m) → n ≡ m
  eqNatSound zero zero _ = refl
  eqNatSound zero (suc m) ()
  eqNatSound (suc n) zero ()
  eqNatSound (suc n) (suc m) p rewrite eqNatSound n m p = refl

  eqNatComplete : ∀ n m → IsFalse (eqNat n m) → ¬ (n ≡ m)
  eqNatComplete zero zero () eq
  eqNatComplete zero (suc m) neq ()
  eqNatComplete (suc n) zero neq ()
  eqNatComplete (suc n) (suc m) neq eq = eqNatComplete n m neq (suc-inj eq)

  decEqNat : (n m : Nat) → Dec (n ≡ m)
  decEqNat n m with eqNat n m | eqNatSound n m | eqNatComplete n m
  ... | true  | eq | _   = yes (eraseEquality (eq true))
  ... | false | _  | neq = no  (eraseNegation (neq false))
  {-# INLINE decEqNat #-}

instance
  EqNat : Eq Nat
  _==_ {{EqNat}} = decEqNat

--- Division and modulo ---

infixl 7 natDiv natMod
syntax natDiv m n = n div m
natDiv : (m : Nat) {{nz : NonZero m}} → Nat → Nat
natDiv zero {{}} n
natDiv (suc m) n = divAux 0 m n m

syntax natMod m n = n mod m
natMod : (m : Nat) {{nz : NonZero m}} → Nat → Nat
natMod zero {{}} n
natMod (suc m) n = modAux 0 m n m

{-# INLINE natMod #-}
{-# INLINE natDiv #-}

--- Comparison ---

data LessNat n m : Set where
  diff : ∀ k (eq : m ≡ suc k +N n) → LessNat n m

{-# DISPLAY LessNat a b = a < b #-}
{-# DISPLAY LessNat a (Nat.suc b) = a ≤ b #-}

pattern diff! k = diff k refl
{-# DISPLAY diff k refl = diff! k #-}

private
  add-zero : ∀ n → n ≡ n +N 0
  add-zero zero = refl
  add-zero (suc n) = cong suc (add-zero n)

  add-suc : ∀ n m → n +N suc m ≡ suc n +N m
  add-suc zero m = refl
  add-suc (suc n) m = cong suc (add-suc n m)

  lemLessNatMinus : ∀ n m → IsTrue (lessNat n m) → m ≡ suc (m -N suc n) +N n
  lemLessNatMinus  _       zero  ()
  lemLessNatMinus  zero   (suc m) _   = cong suc $ add-zero m
  lemLessNatMinus (suc n) (suc m) n<m rewrite add-suc (m -N suc n) n = cong suc (lemLessNatMinus n m n<m)

  lemNoLessEqual : ∀ n m → ¬ IsTrue (lessNat n m) → ¬ IsTrue (lessNat m n) → n ≡ m
  lemNoLessEqual zero zero _ _ = refl
  lemNoLessEqual zero (suc m) h₁ h₂ = ⊥-elim (h₁ true)
  lemNoLessEqual (suc n) zero h₁ h₂ = ⊥-elim (h₂ true)
  lemNoLessEqual (suc n) (suc m) h₁ h₂ = cong suc (lemNoLessEqual n m h₁ h₂)

  -- Using eraseEquality here lets us not worry about the performance of the
  -- proofs.
  compareNat : ∀ n m → Comparison LessNat n m
  compareNat n m with decBool (lessNat n m)
  ... | yes p = less (diff (m -N suc n) (eraseEquality (lemLessNatMinus n m p)))
  ... | no np₁ with decBool (lessNat m n)
  ...             | yes p  = greater (diff (n -N suc m) (eraseEquality (lemLessNatMinus m n p)))
  ...             | no np₂ = equal (eraseEquality (lemNoLessEqual n m np₁ np₂))
  {-# INLINE compareNat #-}

private
  nat-lt-to-leq : ∀ {x y} → LessNat x y → LessNat x (suc y)
  nat-lt-to-leq (diff k eq) = diff (suc k) (cong suc eq)

  nat-eq-to-leq : ∀ {x y} → x ≡ y → LessNat x (suc y)
  nat-eq-to-leq eq = diff 0 (cong suc (sym eq))

  nat-from-leq : ∀ {x y} → LessNat x (suc y) → LessEq LessNat x y
  nat-from-leq (diff zero eq)    = equal (sym (suc-inj eq))
  nat-from-leq (diff (suc k) eq) = less (diff k (suc-inj eq))

instance
  OrdNat : Ord Nat
  Ord._<_         OrdNat = LessNat
  Ord._≤_         OrdNat a b = LessNat a (suc b)
  Ord.compare     OrdNat = compareNat
  Ord.eq-to-leq   OrdNat = nat-eq-to-leq
  Ord.lt-to-leq   OrdNat = nat-lt-to-leq
  Ord.leq-to-lteq OrdNat = nat-from-leq

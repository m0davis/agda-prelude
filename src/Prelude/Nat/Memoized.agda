
module Prelude.Nat.Memoized where

open import Prelude.Memoization
open import Prelude.Ord.Memoized
open import Prelude.Nat
open import Prelude.Bool
open import Prelude.Equality
open import Prelude.Equality.Memoized
open import Prelude.Product
open import Prelude.Empty
open import Prelude.Decidable
open import Prelude.Erased
open import Prelude.Equality.Unsafe
open import Prelude.Function

private
  decEqμNat : (n m : Nat) → Dec (n ≡ m) × Mem n × Mem m
  decEqμNat zero zero = yes refl , putμ refl , putμ refl
  decEqμNat zero (suc m) = no (λ ()) , putμ refl , putμ (cong suc refl)
  decEqμNat (suc n) zero = no (λ ()) , putμ (cong suc refl) , putμ refl
  decEqμNat (suc n) (suc m) = --decEqμ₁ suc-inj (decEqμNat n m)
                              decEq₁ suc-inj (n == m) , putμ (cong suc refl) , putμ (cong suc refl)
  {-# INLINE decEqμNat #-}

instance
  EqμNat : Eqμ Nat
  _==μ_ {{EqμNat}} = decEqμNat

-- -- private
-- --   nat-lt-to-leqμ : ∀ {x y} → LessNat x y → LessNat x (suc y)
-- --   nat-lt-to-leqμ (diff k eq) = diff (suc k) (cong suc eq)

-- --   nat-eq-to-leq : ∀ {x y} → x ≡ y → LessNat x (suc y)
-- --   nat-eq-to-leq eq = diff 0 (cong suc (sym eq))

-- --   nat-from-leq : ∀ {x y} → LessNat x (suc y) → LessEq LessNat x y
-- --   nat-from-leq (diff zero eq)    = equal (sym (suc-inj eq))
-- --   nat-from-leq (diff (suc k) eq) = less (diff k (suc-inj eq))

-- -- instance
-- --   OrdμNat : Ordμ Nat
-- --   Ordμ._<_         OrdμNat = LessNat
-- --   Ordμ._≤_         OrdμNat a b = LessNat a (suc b)
-- --   Ordμ.compare     OrdμNat = compareNat
-- --   Ordμ.eq-to-leq   OrdμNat = nat-eq-to-leq
-- --   Ordμ.lt-to-leq   OrdμNat = nat-lt-to-leq
-- --   Ordμ.leq-to-lteq OrdμNat = nat-from-leq

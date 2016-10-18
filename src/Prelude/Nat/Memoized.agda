
module Prelude.Nat.Memoized where

open import Prelude.Memoization
open import Prelude.Ord.Memoized
open import Prelude.Nat

-- private
--   nat-lt-to-leqμ : ∀ {x y} → LessNat x y → LessNat x (suc y)
--   nat-lt-to-leqμ (diff k eq) = diff (suc k) (cong suc eq)

--   nat-eq-to-leq : ∀ {x y} → x ≡ y → LessNat x (suc y)
--   nat-eq-to-leq eq = diff 0 (cong suc (sym eq))

--   nat-from-leq : ∀ {x y} → LessNat x (suc y) → LessEq LessNat x y
--   nat-from-leq (diff zero eq)    = equal (sym (suc-inj eq))
--   nat-from-leq (diff (suc k) eq) = less (diff k (suc-inj eq))

-- instance
--   OrdμNat : Ordμ Nat
--   Ordμ._<_         OrdμNat = LessNat
--   Ordμ._≤_         OrdμNat a b = LessNat a (suc b)
--   Ordμ.compare     OrdμNat = compareNat
--   Ordμ.eq-to-leq   OrdμNat = nat-eq-to-leq
--   Ordμ.lt-to-leq   OrdμNat = nat-lt-to-leq
--   Ordμ.leq-to-lteq OrdμNat = nat-from-leq

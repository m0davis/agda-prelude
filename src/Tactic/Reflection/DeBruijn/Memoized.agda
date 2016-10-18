
module Tactic.Reflection.DeBruijn.Memoized where

open import Prelude.Memoization

open import Prelude
open import Builtin.Reflection
open import Container.Traversable

record DeBruijnμ {a} (A : Set a) : Set a where
  field
    strengthenFromμ : (from n : Nat) → (t : A) → Maybe A × Mem from × Mem n × Mem t
    weakenFromμ     : (from n : Nat) → (t : A) → A × Mem from × Mem n × Mem t

  strengthenμ : (n : Nat) → (t : A) → Maybe A × Mem n × Mem t × Mem A
  strengthenμ 0 = λ t → just t , (_ , refl) , (_ , refl) , (_ , refl)
  strengthenμ (suc n) = λ t →
    case strengthenFromμ 0 (suc n) t of λ
    { (strengthenFrom0n' , _ , n' , t') → strengthenFrom0n' , n' , t' , (_ , refl) }

  -- weakenμ : Nat → A → A
  -- weakenμ zero = id
  -- weakenμ n    = weakenFrom 0 n

{-# OPTIONS --rewriting #-}
module Builtin.Nat.Memoized where

open import Prelude.Memoization

open import Prelude.Product
open import Prelude.Equality
open import Prelude.Function

open import Agda.Builtin.Nat using (Nat; suc; zero)

_+μ_ : (n : Nat) → (m : Nat) → Nat × Mem n × Mem m
zero  +μ m = m , (_ , refl) , (_ , refl)
suc n +μ m =
  case n +μ m of λ
  { (n+μm , (n' , n'≡n) , (m' , m'=m)) →
    suc n+μm , (suc n' , cong suc n'≡n) , (m , refl) }

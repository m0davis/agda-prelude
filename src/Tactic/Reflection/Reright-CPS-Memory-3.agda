module Tactic.Reflection.Reright-CPS-Memory-3 where

open import Agda.Primitive

open import Prelude.Decidable
open import Prelude.Equality
open import Prelude.Nat
open import Prelude.Bool
open import Prelude.List

open import Prelude.Function
open import Prelude.Strict

id-List& : ∀ {a} {A : Set a} → List A → {B : Set} → (List A → B) → B
id-List& [] f = f []
id-List& (x ∷ xs) f = id-List& xs λ xs → f (x ∷ xs)

module M1 where
  c&r-& : List Nat → Bool
  c&r-& t = id-List& t λ t' → isNo $ t == t'

  c&r-let : List Nat → Bool
  c&r-let t = let t' = t in isNo $ t == t'

  c&r-&' : List Nat → List Nat
  c&r-&' t = id-List& t λ t' → t'

  test : c&r-& (replicate 4000 0) ≡ false
  test = {!c&r-& (replicate 4000 0)!}

{-
replicate : ∀ {a} {A : Set a} → Nat → A → List A
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x
-}
{- normalise: c&r-& (replicate 4 0)

c&r-& (replicate 4 0)
  c&r-& (t = replicate 4 0) =
    id-List& t λ t' → isNo $ t == t'
id-List& (replicate 4 0)
         λ t' → isNo $ (replicate 4 0) == t'
  replicate (suc (n = 3)) (x = 0) =
    0 ∷ replicate 3 0
id-List& (0 ∷ replicate 3 0)
         λ t' → isNo $ (replicate 4 0) == t'
id-List& (replicate 3 0)
         λ xs → (λ t' → isNo $ (replicate 4 0) == t')
                (0 ∷ xs)
id-List& (0 ∷ replicate 2 0)
         λ xs → (λ t' → isNo $ (replicate 4 0) == t')
                (0 ∷ xs)
id-List& (replicate 2 0)
         λ xs → (λ xs → (λ t' → isNo $ (replicate 4 0) == t')
                        (0 ∷ xs))
                (0 ∷ xs)
...
id-List& (replicate 1 0)
         λ xs → (λ xs → (λ xs → (λ t' → isNo $ (replicate 4 0) == t')
                                (0 ∷ xs))
                        (0 ∷ xs))
                (0 ∷ xs)
id-List& (replicate 0 0)
         λ xs → (λ xs → (λ xs → (λ xs → (λ t' → isNo $ (replicate 4 0) == t')
                                        (0 ∷ xs))
                                (0 ∷ xs))
                        (0 ∷ xs))
                (0 ∷ xs)
id-List& []
         λ xs → (λ xs → (λ xs → (λ xs → (λ t' → isNo $ (replicate 4 0) == t')
                                        (0 ∷ xs))
                                (0 ∷ xs))
                        (0 ∷ xs))
                (0 ∷ xs)
(λ xs → (λ xs → (λ xs → (λ xs → (λ t' → isNo $ (replicate 4 0) == t')
                                 (0 ∷ xs))
                         (0 ∷ xs))
                 (0 ∷ xs))
         (0 ∷ xs))
 []
(λ xs → (λ xs → (λ xs → (λ t' → isNo $ (replicate 4 0) == t')
                         (0 ∷ xs))
                 (0 ∷ xs))
         (0 ∷ xs))
 (0 ∷ [])
(λ xs → (λ xs → (λ t' → isNo $ (replicate 4 0) == t')
                 (0 ∷ xs))
         (0 ∷ xs))
 (0 ∷ (0 ∷ []))
(λ xs → (λ t' → isNo $ (replicate 4 0) == t')
         (0 ∷ xs))
 (0 ∷ (0 ∷ (0 ∷ [])))
(λ t' → isNo $ (replicate 4 0) == t')
 (0 ∷ (0 ∷ (0 ∷ (0 ∷ []))))
isNo $ (replicate 4 0) == (0 ∷ (0 ∷ (0 ∷ (0 ∷ []))))
-}

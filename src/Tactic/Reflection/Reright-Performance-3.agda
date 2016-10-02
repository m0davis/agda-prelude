module Tactic.Reflection.Reright-Performance-3 where

open import Prelude.Decidable
open import Prelude.Equality
open import Prelude.Nat
open import Prelude.Bool
open import Prelude.Ord
open import Prelude.List
open import Prelude.Function
open import Prelude.Strict

data Tree : Set where
  deeper : Tree → Tree → Tree
  wider : Nat → List Tree → Tree

sucNat : Nat → Nat
sucNat n
 with n <? 0
... | true = n
... | false = suc n

mutual
  sucTree : Tree → Tree
  sucTree (deeper t₁ t₂) = deeper (sucTree t₁) (sucTree t₂)
--  sucTree (wider n ts) = wider (sucNat n) (sucTrees ts)
  sucTree (wider n ts) = case n <? 0 of λ { true → wider n (sucTrees ts) ; false → wider (suc n) (sucTrees ts) }

  sucTrees : List Tree → List Tree
  sucTrees [] = []
  sucTrees (t ∷ ts) = sucTree t ∷ sucTrees ts

deeper-inj₁ : ∀ {t₁ t₁′ t₂ t₂′} → deeper t₁ t₂ ≡ deeper t₁′ t₂′ → t₁ ≡ t₁′
deeper-inj₁ refl = refl

deeper-inj₂ : ∀ {t₁ t₁′ t₂ t₂′} → deeper t₁ t₂ ≡ deeper t₁′ t₂′ → t₂ ≡ t₂′
deeper-inj₂ refl = refl

wider-inj₁ : ∀ {n n′ ts ts′} → wider n ts ≡ wider n′ ts′ → n ≡ n′
wider-inj₁ refl = refl

wider-inj₂ : ∀ {n n′ ts ts′} → wider n ts ≡ wider n′ ts′ → ts ≡ ts′
wider-inj₂ refl = refl

mutual
  eqTree : (x y : Tree) → Dec (x ≡ y)
  eqTree (deeper t₁ t₂) (deeper t₁′ t₂′) = decEq₂ deeper-inj₁ deeper-inj₂ (eqTree t₁ t₁′) (eqTree  t₂ t₂′)
  eqTree (deeper _ _) (wider _ _) = no (λ ())
  eqTree (wider _ _) (deeper _ _) = no (λ ())
  eqTree (wider n ts) (wider n′ ts′) = decEq₂ wider-inj₁ wider-inj₂ (n == n′) (eqTrees ts ts′)

  eqTrees : (x y : List Tree) → Dec (x ≡ y)
  eqTrees [] [] = yes refl
  eqTrees [] (_ ∷ _) = no (λ ())
  eqTrees (_ ∷ _) [] = no (λ ())
  eqTrees (t ∷ ts) (t′ ∷ ts′) = decEq₂ cons-inj-head cons-inj-tail (eqTree t t′) (eqTrees ts ts′)

instance
  EqTree : Eq Tree
  _==_ {{EqTree}} = eqTree

{-# TERMINATING #-}
_r[_/_] : Tree → Tree → Tree → Tree
tree r[ to / from ]
 with tree == from
... | yes _ = to
... | no _
 with tree
... | deeper treeₗ treeᵣ = deeper (treeₗ r[ to / from ]) (treeᵣ r[ sucTree to / sucTree from ])
... | wider n trees = wider n (map (_r[ to / from ]) trees)

module Test₀ where
  source : Tree
  source = wider 0 []

  target : Tree
  target = wider 1 []

  test : source r[ target / source ] ≡ target
  test = refl

infixr 0 _→→_
_→→_ : Tree → Tree → Tree
l →→ r = deeper l r

w₀ : Nat → Tree
w₀ n = wider n []

w₁ : Nat → Tree → Tree
w₁ n t₁ = wider n (t₁ ∷ [])

w₂ : Nat → Tree → Tree → Tree
w₂ n t₁ t₂ = wider n (t₁ ∷ t₂ ∷ [])

module Test₁ where
  source : Tree
  source =
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 41073) →→
    w₀ 0

  target : Tree
  target =
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    (w₀ 0 →→ w₂ 3 (w₀ 1) (w₀ 2)  →→ w₀ 5 →→ w₂ 0 (w₂ 3 (w₀ 42) (w₀ 0)) (w₀ 7) →→ w₂ 5 (w₀ 0) (w₂ 3 (w₀ 3) (w₀ 3)) →→ w₀ 19730410) →→
    w₀ 0

  test : source r[ w₀ 19730410 / w₀ 0 ] ≡ target
  test = {!!}

v₀ : Nat → Tree
v₀ 0 = w₀ 0
v₀ (suc n) = w₁ n (v₀ n)

v₀* : Nat → Tree → Tree
v₀* 0 t = t
v₀* (suc n) t = w₁ n (v₀* n t)

w* : Nat → Tree
w* n = wider n (replicate n (w₀ n))

module Test₂ where
  source : Tree
  source = v₀ 5 →→ v₀ 3

  target : Tree
  target = v₀* 5 (v₀ 1) →→ v₀ 3

  test : source r[ v₀ 1 / v₀ 0 ] ≡ target
  test = {!refl!}

module Test₃ where
  source : Tree
  source = v₀ 41 →→ w* 100 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ w* 100

  target : Tree
  target = v₀* 41 (v₀ 1) →→ w* 100 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ v₀ 41 →→ w* 100

  test : source r[ v₀ 1 / v₀ 0 ] ≡ target
  test = {!refl!}

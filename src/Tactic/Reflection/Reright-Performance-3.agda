module Tactic.Reflection.Reright-Performance-3 where

open import Prelude.Decidable
open import Prelude.Equality
open import Prelude.Nat
open import Prelude.Bool
open import Prelude.Ord
open import Prelude.List
open import Prelude.Function
open import Prelude.Strict
open import Prelude.Product

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
  test = refl

u : Nat → Nat → Tree
u 0 n = wider n []
u (suc d) n = deeper (u d n) (u d n)

module Test₄ where
  forest : List Tree
  forest = u 3 0 ∷
           []

  deadwood : Tree
  deadwood = v₀ 1

  oak : Tree
  oak = v₀ 5

  bonsai : Tree
  bonsai = u 10 0

  fast : List Tree × List Tree
  fast = go forest where
    go : List Tree → List Tree × List Tree
    go [] = [] , []
    go (t ∷ ts) = if (isNo $ t == t r[ oak / deadwood ]) then
                    snd (go ts) , t r[ oak / deadwood ] ∷ snd (go ts)
                  else
                    go ts

  slow : List Tree × List Tree
  slow = [] , go forest where
    go : List Tree → List Tree
    go [] = []
    go (t ∷ ts) = if (isNo $ t == t r[ oak / deadwood ]) then
                    t r[ oak / deadwood ] ∷ go ts
                  else
                    go ts

  try : List Tree × List Tree → Tree
  try method = helper method
    where
    helper : List Tree × List Tree → Tree
    helper (_ , ts) = let l = length ts in bonsai r[ w₀ l / w₀ l ]

  doit-fast : try fast ≡ w₀ 0
  doit-fast = {!C-u C-u C-c C-,!}

  doit-slow : try slow ≡ w₀ 0
  doit-slow = {!try slow!}


module Test₅ where
  make-deep-tree : Nat → Nat → Tree
  make-deep-tree 0 n = wider n []
  make-deep-tree (suc d) n = deeper (u d n) (u d n)

  make-wide-tree : Nat → Tree
  make-wide-tree 0 = wider 0 []
  make-wide-tree (suc n) = wider n (make-wide-tree n ∷ [])

  forest : List Tree
  forest = make-deep-tree 10 0 ∷ []

  deadwood : Tree
  deadwood = make-wide-tree 1

  oak : Tree
  oak = make-wide-tree 1

  bonsai : Tree
  bonsai = make-deep-tree 10 0

  fast : List Tree × List Tree
  fast = go forest where
    go : List Tree → List Tree × List Tree
    go [] = [] , []
    go (t ∷ ts) = if (isNo $ t == t r[ oak / deadwood ]) then
                    snd (go ts) , t r[ oak / deadwood ] ∷ snd (go ts)
                  else
                    go ts

  slow : List Tree × List Tree
  slow = [] , go forest where
    go : List Tree → List Tree
    go [] = []
    go (t ∷ ts) = if (isNo $ t == t r[ oak / deadwood ]) then
                    t r[ oak / deadwood ] ∷ go ts
                  else
                    go ts

  try : List Tree × List Tree → Tree
  try (_ , ts) = let l = length ts in bonsai r[ w₀ l / w₀ l ]

  test-area : Set × Set
  test-area = {!try fast!} , {!try slow!}

module Test₆ where
  deep-tree : Tree
  deep-tree = make-deep-tree 10 where
    make-deep-tree : Nat → Tree
    make-deep-tree 0 = wider 0 []
    make-deep-tree (suc d) = deeper (make-deep-tree d) (make-deep-tree d)

  wide-tree : Tree
  wide-tree = make-wide-tree 1 where
    make-wide-tree : Nat → Tree
    make-wide-tree 0 = wider 0 []
    make-wide-tree (suc n) = wider n (make-wide-tree n ∷ [])

  fast : List Tree × List Tree
  fast = go (deep-tree ∷ []) where
    go : List Tree → List Tree × List Tree
    go [] = [] , []
    go (t ∷ ts) = if (isNo $ t == t r[ wide-tree / wide-tree ]) then
                    snd (go ts) , t r[ wide-tree / wide-tree ] ∷ snd (go ts)
                  else
                    go ts

  slow : List Tree × List Tree
  slow = [] , go (deep-tree ∷ []) where
    go : List Tree → List Tree
    go [] = []
    go (t ∷ ts) = if (isNo $ t == t r[ wide-tree / wide-tree ]) then
                    t r[ wide-tree / wide-tree ] ∷ go ts
                  else
                    go ts

  try : List Tree × List Tree → Tree
  try (_ , ts) = let l = length ts in deep-tree r[ wider l [] / wider l [] ]

  test-area : Set × Set
  test-area = {!try fast!} , {!try slow!}

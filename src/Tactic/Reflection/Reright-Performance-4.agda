module Tactic.Reflection.Reright-Performance-4 where

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

mutual
  sucTree : Tree → Tree
  sucTree (deeper t₁ t₂) = deeper (sucTree t₁) (sucTree t₂)
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

module Tactic.Reflection.AgdaIssue-loop-forever-1 where
  open import Prelude

  postulate
    Term : Set
    Arg : Set → Set
  VarSet = List Nat
  Type = Term

  postulate
    freeVars'' : VarSet
    foldr' : ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → List A → B
    mapM' : (Nat → Maybe VarSet) → List Nat → Maybe (List VarSet)

  {-# TERMINATING #-}
  freeDependencies' : List (Arg Type) → Maybe VarSet
  freeDependencies' Γ = foldr' _∪_ freeVars'' <$> mapM' go freeVars'' where
    postulate
      _∪_ : VarSet → VarSet → VarSet

    go : Nat → Maybe VarSet
    go v = freeDependencies' Γ

  postulate
    Γᶜ : List (Arg Type)

  [iᶜ∣iᶜ∈FVᴬ] : VarSet
  [iᶜ∣iᶜ∈FVᴬ] = maybe [] id $ freeDependencies' Γᶜ

  postulate
    LENGTH : VarSet → Nat

  qux : Nat
  qux = suc {-$-} (LENGTH [iᶜ∣iᶜ∈FVᴬ])

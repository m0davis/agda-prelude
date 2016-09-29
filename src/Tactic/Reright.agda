module Tactic.Reright where

open import Prelude
open import Tactic.Reflection
open import Tactic.Reflection.Debug

foo₁ : ∀ (a : Level) {A : Set a} {F : Set a → Set a} {f : A → A} (G : (∀ {b} {B : Set b} → B))
       → (H : (λ x → A) F)
       → Set
foo₁ = {!!} -- showFun

-- *L*abeled Terms and Types encode the 'var' constructor of 'Term' as a name rather than a debruijn index

data LSort   : Set
data LClause : Set
data LTerm   : Set
LType = LTerm

Label = Nat

data LTerm where
  var       : (x : Label) (args : List (Arg LTerm)) → LTerm
  con       : (c : Name) (args : List (Arg LTerm)) → LTerm
  def       : (f : Name) (args : List (Arg LTerm)) → LTerm
  lam       : (v : Visibility) (t : Abs LTerm) → LTerm
  pat-lam   : (cs : List LClause) (args : List (Arg LTerm)) → LTerm
  pi        : (x : Label) (a : Arg LType) (b : Abs LType) → LTerm
  agda-sort : (s : LSort) → LTerm
  lit       : (l : Literal) → LTerm
  meta      : (x : Meta) → List (Arg LTerm) → LTerm
  unknown   : LTerm

data LSort where
  set     : (t : LTerm) → LSort
  lit     : (n : Nat) → LSort
  unknown : LSort

data LClause where
  clause        : (ps : List (Arg Pattern)) (t : LTerm) → LClause
  absurd-clause : (ps : List (Arg Pattern)) → LClause

{-
Term→LTerm      (a : Label)
                (A : Set a)
                (F : Set a → Set a)
                (FA : F A)
                (X : (b : Label)
                     (B : Set b)
                     (G : Set b → Set a)
                     (GB : G B))
                (FFA : F (F A))
                → Set a
              ⇒ (0 : Label)
                (1 : Set 0)
                (2 : Set 0 → Set 0)
                (3 : 2 1 → 2 1)
                (4 : (5 : Label)
                     (6 : Set 5)
                     (7 : Set 5 → Set 0)
                     (8 : 7 6))
                (9 : 2 (2 1))
                → (10 : Set 0)
           OR ⇒ (0 : Label)
                (1 : Set 0)
                (2 : Set 0 → Set 0)
                (3 : 2 1 → 2 1)
                (8 : (4 : Label)
                     (5 : Set 4)
                     (6 : Set 4 → Set 0)
                     (7 : 6 5))
                (9 : 2 (2 1))
                → (10 : Set 0)
-}
{-
   Term→LTerm next-available-label
              inner-most-labels
              outermost-first-context
   ⇒ next-available-label ×
     labeled-context
-}
open import Control.Monad.State
open import Control.Monad.Identity

mutual
  ArgTerm→ArgLTerm : List Nat → Arg Term → StateT Nat Identity (Arg LTerm)
  ArgTerm→ArgLTerm = {!!}

  Term→LTerm : List Nat → Term → StateT Nat Maybe LTerm
  Term→LTerm Γ (var x args) = lift {!!}
  {-
     do
     n ← get -|
     -- args' ← (fmap (runStateT n ∘ Term→LTerm Γ) <$> args) -|
     return (var {!index!} {!!})
  -}
  Term→LTerm Γ (con c args) = {!!}
  Term→LTerm Γ (def f args) = {!!}
  Term→LTerm Γ (lam v t) = {!!}
  Term→LTerm Γ (pat-lam cs args) = {!!}
  Term→LTerm Γ (pi a b) = {!!}
  Term→LTerm Γ (agda-sort s) = {!!}
  Term→LTerm Γ (lit l) = {!!}
  Term→LTerm Γ (meta x x₁) = {!!}
  Term→LTerm Γ unknown = {!!}

LTerm→Term : LTerm → Maybe Term
LTerm→Term = {!!}

nextAvailableLabel : LTerm → Nat
nextAvailableLabel = {!!}

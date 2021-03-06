
module Tactic.Nat.Auto where

open import Prelude
open import Builtin.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Reflection

open import Tactic.Nat.NF
open import Tactic.Nat.Exp
open import Tactic.Nat.Reflect
open import Tactic.Nat.Auto.Lemmas

open Tactic.Nat.Reflect public using (cantProve; invalidGoal)

module _ {Atom : Set} {{_ : Eq Atom}} {{_ : Ord Atom}} where
  liftNFEq : ∀ (e₁ : Exp Atom) e₂ ρ → ⟦ norm e₁ ⟧n ρ ≡ ⟦ norm e₂ ⟧n ρ → ⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ
  liftNFEq e₁ e₂ ρ H = eraseEquality $
    ⟦ e₁      ⟧e ρ ≡⟨ sound e₁ ρ ⟩
    ⟦ norm e₁ ⟧n ρ ≡⟨ H ⟩
    ⟦ norm e₂ ⟧n ρ ≡⟨ sound e₂ ρ ⟩ʳ
    ⟦ e₂      ⟧e ρ ∎

  unliftNFEq : ∀ (e₁ : Exp Atom) e₂ ρ → ⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ → ⟦ norm e₁ ⟧n ρ ≡ ⟦ norm e₂ ⟧n ρ
  unliftNFEq e₁ e₂ ρ H =
    ⟦ norm e₁ ⟧n ρ ≡⟨ sound e₁ ρ ⟩ʳ
    ⟦ e₁      ⟧e ρ ≡⟨ H ⟩
    ⟦ e₂      ⟧e ρ ≡⟨ sound e₂ ρ ⟩
    ⟦ norm e₂ ⟧n ρ ∎

  auto-proof : ∀ e₁ e₂ ρ → Maybe (⟦ e₁ ⟧e ρ ≡ ⟦ e₂ ⟧e ρ)
  auto-proof e₁ e₂ ρ with norm e₁ == norm e₂
  auto-proof e₁ e₂ ρ    | no  _    = nothing
  auto-proof e₁ e₂ ρ    | yes nfeq = just (liftNFEq e₁ e₂ ρ (cong (λ n → ⟦ n ⟧n ρ) nfeq))

auto-tactic : Type → Tactic
auto-tactic t hole =
  caseM termToEq t of
  λ { nothing → unify hole $ failedProof (quote invalidGoal) t
    ; (just ((e₁ , e₂) , Γ)) →
      unify hole $
      getProof (quote cantProve) t $
        def (quote auto-proof)
            ( vArg (` e₁)
            ∷ vArg (` e₂)
            ∷ vArg (quotedEnv Γ)
            ∷ [] )
    }

macro
  auto : Tactic
  auto = on-goal auto-tactic

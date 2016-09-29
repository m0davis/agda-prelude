module Tactic.Reflection.Debug where

open import Prelude
open import Tactic.Reflection
open import Tactic.Reflection.Quote

macro
  showContext : Tactic
  showContext hole = do
    Γ ← getContext -|
    typeError [ termErr (` Γ) ]

  showFun : Tactic
  showFun hole = do
    Γ ← getContext -|
    G ← inferType hole -|
    typeError [ termErr (` (telPi (reverse Γ) G)) ]

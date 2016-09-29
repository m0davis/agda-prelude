--{-# OPTIONS --show-implicit #-}
module Reright-bug where
  open import Prelude
  open import Tactic.Reflection.Reright3
  open import Agda.Builtin.Reflection
  open import Tactic.Reflection
  open import Tactic.Reflection.Quote

  macro
    showDefinition : Name → Tactic
    showDefinition n hole = do
      n-clauses ← getClauses n -|
      case index n-clauses 0 of λ {
        (just (clause _ (def rewrite-name _))) → do
          rewrite-clauses ← getClauses rewrite-name -|
          rewrite-type ← getType rewrite-name -|
          typeError ( termErr (` n-clauses) ∷
                      termErr (` rewrite-name) ∷
                      termErr (  rewrite-type) ∷
                      termErr (` rewrite-type) ∷
                      termErr (` rewrite-clauses) ∷
                      [] )
       ;_ → return tt
       }

  module Ess where
    postulate
      S : Set
      S≡S : S ≡ S
      s : S

    test-rewrite : s ≡ s
    test-rewrite rewrite S≡S = {!!}

    FOO : Set
    FOO = {!showDefinition test-rewrite!} --

    test : s ≡ s
    test = helper S S≡S {!!} -- reright-debug S≡S {!!}
      where
      helper : (w : Set) → w ≡ S → s ≡ s → _≡_ {lzero} {S} s s
      helper ._ refl f = f

    _`≡_ = def₂ (quote _≡_)
    `S = def₀ (quote S)
    `s = def₀ (quote s)
    `S≡S = def₀ (quote S≡S)

    helper-type : Type
    helper-type = set₀ `→
                  var₀ 0 `≡ `S `→
                  `s `≡ `s `→
                  -- def (quote _≡_) (hArg (def₀ (quote lzero)) ∷ hArg `S ∷ vArg `s ∷ vArg `s ∷ []) -- `s `≡ `s
                  def (quote _≡_) (hArg (def₀ (quote lzero)) ∷ hArg (var₀ 1) ∷ vArg `s ∷ vArg `s ∷ []) -- `s `≡ `s


    helper-patterns : List (Arg Pattern)
    helper-patterns = vArg dot ∷ vArg (con₀ (quote refl)) ∷ vArg (var "f") ∷ []

    helper-term : Term
    helper-term = var₀ 0

    helper-call-args : List (Arg Term)
    helper-call-args = vArg unknown ∷ vArg `S≡S ∷ []

    macro
      define-and-call-helper : Tactic
      define-and-call-helper hole = do
        n ← freshName "helper" -|
        define (vArg n) helper-type [ clause helper-patterns helper-term ] ~|
        hole =′ def n helper-call-args

    test₂ : s ≡ s
    test₂ = {!!} -- define-and-call-helper {!!}

  module Tee where
    test' : (T : Set) (T≡T : T ≡ T) (t : T) → t ≡ t
    test' T T≡T t = {!!} -- reright-debug T≡T {!!}

  module You (U : Set) (U≡U : U ≡ U) (u : U) where
    test'' : u ≡ u
    test'' = {!!} -- reright U≡U ?

  module ORIG where
    postulate
      A₀ : Set
      B₀ : Set
      A₀≡B₀ : A₀ ≡ B₀
      R : (A : Set) (x y : A) → Set

    test-rewrite : (a₀ : A₀) → R A₀ a₀ a₀
    test-rewrite a₀ rewrite A₀≡B₀ = {!showDefinition test!}

    test-reright : (a₀ : A₀) → R A₀ a₀ a₀
    test-reright a₀ = -- reright-debug A₀≡B₀ ?
                      helper A₀≡B₀ a₀ {!!}
                      -- ?
      where
      helper : {w : Set} (w≡R : w ≡ B₀) (a₀' : w) → ((a₀'' : B₀) → R B₀ a₀'' a₀'') → R w a₀' a₀'
      helper {._} refl a₀' f = f a₀'

    -- when we change the type of a variable such that [w/L], there may be other terms that depend on

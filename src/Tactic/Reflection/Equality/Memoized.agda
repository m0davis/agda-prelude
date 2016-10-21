
module Tactic.Reflection.Equality.Memoized where

open import Prelude.Memoization
open import Prelude.Equality.Memoized
open import Prelude.Nat.Memoized

open import Prelude
open import Builtin.Reflection
open import Builtin.Float
open import Builtin.Float.Memoized
open import Prelude.Char.Memoized
open import Prelude.List.Memoized
open import Prelude.String.Memoized
open import Builtin.Reflection.Memoized

instance
  EqμVisibility : Eqμ Visibility
  _==μ_ {{EqμVisibility}} visible  visible  = yes refl , putμ refl , putμ refl
  _==μ_ {{EqμVisibility}} visible  hidden   = no (λ ()) , putμ refl , putμ refl
  _==μ_ {{EqμVisibility}} visible  instance′ = no (λ ()) , putμ refl , putμ refl
  _==μ_ {{EqμVisibility}} hidden   visible  = no (λ ()) , putμ refl , putμ refl
  _==μ_ {{EqμVisibility}} hidden   hidden   = yes refl , putμ refl , putμ refl
  _==μ_ {{EqμVisibility}} hidden   instance′ = no (λ ()) , putμ refl , putμ refl
  _==μ_ {{EqμVisibility}} instance′ visible  = no (λ ()) , putμ refl , putμ refl
  _==μ_ {{EqμVisibility}} instance′ hidden   = no (λ ()) , putμ refl , putμ refl
  _==μ_ {{EqμVisibility}} instance′ instance′ = yes refl , putμ refl , putμ refl

  EqμRelevance : Eqμ Relevance
  _==μ_ {{EqμRelevance}} relevant   relevant   = yes refl , putμ refl , putμ refl
  _==μ_ {{EqμRelevance}} relevant   irrelevant = no (λ ()) , putμ refl , putμ refl
  _==μ_ {{EqμRelevance}} irrelevant relevant   = no (λ ()) , putμ refl , putμ refl
  _==μ_ {{EqμRelevance}} irrelevant irrelevant = yes refl , putμ refl , putμ refl

  EqμArgInfo : Eqμ ArgInfo
  _==μ_ {{EqμArgInfo}} (arg-info v r) (arg-info v₁ r₁) = decEqμ₂ arg-info-inj₁ arg-info-inj₂ (v ==μ v₁) (r ==μ r₁)

  EqμArg : ∀ {A} {{EqμA : Eqμ A}} → Eqμ (Arg A)
  _==μ_ {{EqμArg}} (arg i x) (arg i₁ x₁) =
    case i ==μ i₁ , x ==μ x₁ of λ
    { ((i==i₁ , putμ i-refl , putμ i₁-refl) ,
       (x==x₁ , putμ x-refl , putμ x₁-refl)) →
      decEq₂ arg-inj₁ arg-inj₂ i==i₁ x==x₁ ,
      putμ (cong₂ arg i-refl x-refl) ,
      putμ (cong₂ arg i₁-refl x₁-refl) }

  EqμAbs : ∀ {A} {{EqμA : Eqμ A}} → Eqμ (Abs A)
  _==μ_ {{EqμAbs}} (abs s x) (abs s₁ x₁) =
    case s ==μ s₁ , x ==μ x₁ of λ
    { ((s==s₁ , putμ s-refl , putμ s₁-refl) ,
       (x==x₁ , putμ x-refl , putμ x₁-refl)) →
      decEq₂ abs-inj₁ abs-inj₂ s==s₁ x==x₁ ,
      putμ (cong₂ abs s-refl x-refl) ,
      putμ (cong₂ abs s₁-refl x₁-refl) }

  EqμLiteral : Eqμ Literal
  _==μ_ {{EqμLiteral}} = eqμLit
    where
      eqμLit : ∀ x y → Dec (x ≡ y) × Mem x × Mem y
      eqμLit (nat    x) (nat    y) = decEqμ₁ nat-inj    (x ==μ y)
      eqμLit (float  x) (float  y) = decEqμ₁ float-inj  (x ==μ y)
      eqμLit (char   x) (char   y) = decEqμ₁ char-inj   (x ==μ y)
      eqμLit (string x) (string y) = decEqμ₁ string-inj (x ==μ y)
      eqμLit (name   x) (name   y) = decEqμ₁ name-inj   (x ==μ y)
      eqμLit (meta   x) (meta   y) = decEqμ₁ meta-inj   (x ==μ y)

      eqμLit (nat    x) (float  y) = no (λ()) , putμ (cong nat    refl) , putμ (cong float  refl)
      eqμLit (nat    x) (char   y) = no (λ()) , putμ (cong nat    refl) , putμ (cong char   refl)
      eqμLit (nat    x) (string y) = no (λ()) , putμ (cong nat    refl) , putμ (cong string refl)
      eqμLit (nat    x) (name   y) = no (λ()) , putμ (cong nat    refl) , putμ (cong name   refl)
      eqμLit (nat    x) (meta   y) = no (λ()) , putμ (cong nat    refl) , putμ (cong meta   refl)
      eqμLit (float  x) (nat    y) = no (λ()) , putμ (cong float  refl) , putμ (cong nat    refl)
      eqμLit (float  x) (char   y) = no (λ()) , putμ (cong float  refl) , putμ (cong char   refl)
      eqμLit (float  x) (string y) = no (λ()) , putμ (cong float  refl) , putμ (cong string refl)
      eqμLit (float  x) (name   y) = no (λ()) , putμ (cong float  refl) , putμ (cong name   refl)
      eqμLit (float  x) (meta   y) = no (λ()) , putμ (cong float  refl) , putμ (cong meta   refl)
      eqμLit (char   x) (nat    y) = no (λ()) , putμ (cong char   refl) , putμ (cong nat    refl)
      eqμLit (char   x) (float  y) = no (λ()) , putμ (cong char   refl) , putμ (cong float  refl)
      eqμLit (char   x) (string y) = no (λ()) , putμ (cong char   refl) , putμ (cong string refl)
      eqμLit (char   x) (name   y) = no (λ()) , putμ (cong char   refl) , putμ (cong name   refl)
      eqμLit (char   x) (meta   y) = no (λ()) , putμ (cong char   refl) , putμ (cong meta   refl)
      eqμLit (string x) (nat    y) = no (λ()) , putμ (cong string refl) , putμ (cong nat    refl)
      eqμLit (string x) (float  y) = no (λ()) , putμ (cong string refl) , putμ (cong float  refl)
      eqμLit (string x) (char   y) = no (λ()) , putμ (cong string refl) , putμ (cong char   refl)
      eqμLit (string x) (name   y) = no (λ()) , putμ (cong string refl) , putμ (cong name   refl)
      eqμLit (string x) (meta   y) = no (λ()) , putμ (cong string refl) , putμ (cong meta   refl)
      eqμLit (name   x) (nat    y) = no (λ()) , putμ (cong name   refl) , putμ (cong nat    refl)
      eqμLit (name   x) (float  y) = no (λ()) , putμ (cong name   refl) , putμ (cong float  refl)
      eqμLit (name   x) (char   y) = no (λ()) , putμ (cong name   refl) , putμ (cong char   refl)
      eqμLit (name   x) (string y) = no (λ()) , putμ (cong name   refl) , putμ (cong string refl)
      eqμLit (name   x) (meta   y) = no (λ()) , putμ (cong name   refl) , putμ (cong meta   refl)
      eqμLit (meta   x) (nat    y) = no (λ()) , putμ (cong meta   refl) , putμ (cong nat    refl)
      eqμLit (meta   x) (float  y) = no (λ()) , putμ (cong meta   refl) , putμ (cong float  refl)
      eqμLit (meta   x) (char   y) = no (λ()) , putμ (cong meta   refl) , putμ (cong char   refl)
      eqμLit (meta   x) (string y) = no (λ()) , putμ (cong meta   refl) , putμ (cong string refl)
      eqμLit (meta   x) (name   y) = no (λ()) , putμ (cong meta   refl) , putμ (cong name   refl)

private
  eqμSort   : (x y : Sort)    → Dec (x ≡ y) × Mem x × Mem y
  eqμTerm   : (x y : Term)    → Dec (x ≡ y) × Mem x × Mem y
  eqμPat    : (x y : Pattern) → Dec (x ≡ y) × Mem x × Mem y
  eqμClause : (x y : Clause)  → Dec (x ≡ y) × Mem x × Mem y

private
  eqμArgTerm : (x y : Arg Term) → Dec (x ≡ y) × Mem x × Mem y
  eqμArgTerm (arg i x) (arg i₁ x₁) = decEqμ₂ arg-inj₁ arg-inj₂ (i ==μ i₁) (eqμTerm x x₁)

  eqμArgPat : (x y : Arg Pattern) → Dec (x ≡ y) × Mem x × Mem y
  eqμArgPat (arg i x) (arg i₁ x₁) = decEqμ₂ arg-inj₁ arg-inj₂ (i ==μ i₁) (eqμPat x x₁)

  eqμAbsTerm : (x y : Abs Term) → Dec (x ≡ y) × Mem x × Mem y
  eqμAbsTerm (abs s x) (abs s₁ x₁) = decEqμ₂ abs-inj₁ abs-inj₂ (s ==μ s₁) (eqμTerm x x₁)

  eqμPats : (x y : List (Arg Pattern)) → Dec (x ≡ y) × Mem x × Mem y
  eqμPats [] [] = yes refl , putμ refl , putμ refl
  eqμPats [] (x ∷ xs) = no (λ ()) , putμ refl , putμ (cong₂ _∷_ refl refl)
  eqμPats (x ∷ xs) [] = no (λ ()) , putμ (cong₂ _∷_ refl refl) , putμ refl
  eqμPats (x ∷ xs) (y ∷ ys) = decEqμ₂ cons-inj-head cons-inj-tail (eqμArgPat x y) (eqμPats xs ys)

  eqμArgs : (x y : List (Arg Term)) → Dec (x ≡ y) × Mem x × Mem y
  eqμArgs [] [] = yes refl , putμ refl , putμ refl
  eqμArgs [] (x ∷ xs) = no (λ ()) , putμ refl , putμ (cong₂ _∷_ refl refl)
  eqμArgs (x ∷ xs) [] = no (λ ()) , putμ (cong₂ _∷_ refl refl) , putμ refl
  eqμArgs (x ∷ xs) (y ∷ ys) = decEqμ₂ cons-inj-head cons-inj-tail (eqμArgTerm x y) (eqμArgs xs ys)

  eqμClauses : (x y : List Clause) → Dec (x ≡ y) × Mem x × Mem y
  eqμClauses [] [] = yes refl , putμ refl , putμ refl
  eqμClauses [] (x ∷ xs) = no (λ ()) , putμ refl , putμ (cong₂ _∷_ refl refl)
  eqμClauses (x ∷ xs) [] = no (λ ()) , putμ (cong₂ _∷_ refl refl) , putμ refl
  eqμClauses (x ∷ xs) (y ∷ ys) = decEqμ₂ cons-inj-head cons-inj-tail (eqμClause x y) (eqμClauses xs ys)

  eqμTerm (var x args) (var x₁ args₁) = decEqμ₂ var-inj₁ var-inj₂ (x ==μ x₁) (eqμArgs args args₁)
  eqμTerm (con c args) (con c₁ args₁) = decEqμ₂ con-inj₁ con-inj₂ (c ==μ c₁) (eqμArgs args args₁)
  eqμTerm (def f args) (def f₁ args₁) = decEqμ₂ def-inj₁ def-inj₂ (f ==μ f₁) (eqμArgs args args₁)
  eqμTerm (meta x args) (meta x₁ args₁) = decEqμ₂ meta-inj₁ meta-inj₂ (x ==μ x₁) (eqμArgs args args₁)
  eqμTerm (lam v x) (lam v₁ y) = decEqμ₂ lam-inj₁ lam-inj₂ (v ==μ v₁) (eqμAbsTerm x y)
  eqμTerm (pi t₁ t₂) (pi t₃ t₄) = decEqμ₂ pi-inj₁ pi-inj₂ (eqμArgTerm t₁ t₃) (eqμAbsTerm t₂ t₄)
  eqμTerm (agda-sort x) (agda-sort x₁) = decEqμ₁ sort-inj (eqμSort x x₁)
  eqμTerm (lit l) (lit l₁)   = decEqμ₁ lit-inj (l ==μ l₁)
  eqμTerm (pat-lam c args) (pat-lam c₁ args₁) = decEqμ₂ pat-lam-inj₁ pat-lam-inj₂ (eqμClauses c c₁) (eqμArgs args args₁)
  eqμTerm unknown unknown = yes refl , putμ refl , putμ refl

  eqμTerm (var x args) (con c args₁)  = no (λ ()) , putμ (cong₂ var refl refl) , putμ (cong₂ con refl refl)
  eqμTerm (var x args) (def f args₁)  = no (λ ()) , putμ (cong₂ var refl refl) , putμ (cong₂ def refl refl)
  eqμTerm (var x args) (lam v y)      = no (λ ()) , putμ (cong₂ var refl refl) , putμ (cong₂ lam refl refl)
  eqμTerm (var x args) (pi t₁ t₂)     = no (λ ()) , putμ (cong₂ var refl refl) , putμ (cong₂ pi refl refl)
  eqμTerm (var x args) (agda-sort x₁) = no (λ ()) , putμ (cong₂ var refl refl) , putμ (cong agda-sort refl)
  eqμTerm (var x args) (lit x₁)       = no (λ ()) , putμ (cong₂ var refl refl) , putμ (cong lit refl)
  eqμTerm (var x args) unknown        = no (λ ()) , putμ (cong₂ var refl refl) , putμ refl
  eqμTerm (con c args) (var x args₁)  = no (λ ()) , putμ (cong₂ con refl refl) , putμ (cong₂ var refl refl)
  eqμTerm (con c args) (def f args₁)  = no (λ ()) , putμ (cong₂ con refl refl) , putμ (cong₂ def refl refl)
  eqμTerm (con c args) (lam v y)      = no (λ ()) , putμ (cong₂ con refl refl) , putμ (cong₂ lam refl refl)
  eqμTerm (con c args) (pi t₁ t₂)     = no (λ ()) , putμ (cong₂ con refl refl) , putμ (cong₂ pi refl refl)
  eqμTerm (con c args) (agda-sort x)  = no (λ ()) , putμ (cong₂ con refl refl) , putμ (cong agda-sort refl)
  eqμTerm (con c args) (lit x)        = no (λ ()) , putμ (cong₂ con refl refl) , putμ (cong lit refl)
  eqμTerm (con c args) unknown        = no (λ ()) , putμ (cong₂ con refl refl) , putμ refl
  eqμTerm (def f args) (var x args₁)  = no (λ ()) , putμ (cong₂ def refl refl) , putμ (cong₂ var refl refl)
  eqμTerm (def f args) (con c args₁)  = no (λ ()) , putμ (cong₂ def refl refl) , putμ (cong₂ con refl refl)
  eqμTerm (def f args) (lam v y)      = no (λ ()) , putμ (cong₂ def refl refl) , putμ (cong₂ lam refl refl)
  eqμTerm (def f args) (pi t₁ t₂)     = no (λ ()) , putμ (cong₂ def refl refl) , putμ (cong₂ pi refl refl)
  eqμTerm (def f args) (agda-sort x)  = no (λ ()) , putμ (cong₂ def refl refl) , putμ (cong agda-sort refl)
  eqμTerm (def f args) (lit x)        = no (λ ()) , putμ (cong₂ def refl refl) , putμ (cong lit refl)
  eqμTerm (def f args) unknown        = no (λ ()) , putμ (cong₂ def refl refl) , putμ refl
  eqμTerm (lam v x) (var x₁ args)     = no (λ ()) , putμ (cong₂ lam refl refl) , putμ (cong₂ var refl refl)
  eqμTerm (lam v x) (con c args)      = no (λ ()) , putμ (cong₂ lam refl refl) , putμ (cong₂ con refl refl)
  eqμTerm (lam v x) (def f args)      = no (λ ()) , putμ (cong₂ lam refl refl) , putμ (cong₂ def refl refl)
  eqμTerm (lam v x) (pi t₁ t₂)        = no (λ ()) , putμ (cong₂ lam refl refl) , putμ (cong₂ pi refl refl)
  eqμTerm (lam v x) (agda-sort x₁)    = no (λ ()) , putμ (cong₂ lam refl refl) , putμ (cong agda-sort refl)
  eqμTerm (lam v x) (lit x₁)          = no (λ ()) , putμ (cong₂ lam refl refl) , putμ (cong lit refl)
  eqμTerm (lam v x) unknown           = no (λ ()) , putμ (cong₂ lam refl refl) , putμ refl
  eqμTerm (pi t₁ t₂) (var x args)     = no (λ ()) , putμ (cong₂ pi refl refl) , putμ (cong₂ var refl refl)
  eqμTerm (pi t₁ t₂) (con c args)     = no (λ ()) , putμ (cong₂ pi refl refl) , putμ (cong₂ con refl refl)
  eqμTerm (pi t₁ t₂) (def f args)     = no (λ ()) , putμ (cong₂ pi refl refl) , putμ (cong₂ def refl refl)
  eqμTerm (pi t₁ t₂) (lam v y)        = no (λ ()) , putμ (cong₂ pi refl refl) , putμ (cong₂ lam refl refl)
  eqμTerm (pi t₁ t₂) (agda-sort x)    = no (λ ()) , putμ (cong₂ pi refl refl) , putμ (cong agda-sort refl)
  eqμTerm (pi t₁ t₂) (lit x)          = no (λ ()) , putμ (cong₂ pi refl refl) , putμ (cong lit refl)
  eqμTerm (pi t₁ t₂) unknown          = no (λ ()) , putμ (cong₂ pi refl refl) , putμ refl
  eqμTerm (agda-sort x) (var x₁ args) = no (λ ()) , putμ (cong agda-sort refl) , putμ (cong₂ var refl refl)
  eqμTerm (agda-sort x) (con c args)  = no (λ ()) , putμ (cong agda-sort refl) , putμ (cong₂ con refl refl)
  eqμTerm (agda-sort x) (def f args)  = no (λ ()) , putμ (cong agda-sort refl) , putμ (cong₂ def refl refl)
  eqμTerm (agda-sort x) (lam v y)     = no (λ ()) , putμ (cong agda-sort refl) , putμ (cong₂ lam refl refl)
  eqμTerm (agda-sort x) (pi t₁ t₂)    = no (λ ()) , putμ (cong agda-sort refl) , putμ (cong₂ pi refl refl)
  eqμTerm (agda-sort x) (lit x₁)      = no (λ ()) , putμ (cong agda-sort refl) , putμ (cong lit refl)
  eqμTerm (agda-sort x) unknown       = no (λ ()) , putμ (cong agda-sort refl) , putμ refl
  eqμTerm (lit x) (var x₁ args)       = no (λ ()) , putμ (cong lit refl) , putμ (cong₂ var refl refl)
  eqμTerm (lit x) (con c args)        = no (λ ()) , putμ (cong lit refl) , putμ (cong₂ con refl refl)
  eqμTerm (lit x) (def f args)        = no (λ ()) , putμ (cong lit refl) , putμ (cong₂ def refl refl)
  eqμTerm (lit x) (lam v y)           = no (λ ()) , putμ (cong lit refl) , putμ (cong₂ lam refl refl)
  eqμTerm (lit x) (pi t₁ t₂)          = no (λ ()) , putμ (cong lit refl) , putμ (cong₂ pi refl refl)
  eqμTerm (lit x) (agda-sort x₁)      = no (λ ()) , putμ (cong lit refl) , putμ (cong agda-sort refl)
  eqμTerm (lit x) unknown             = no (λ ()) , putμ (cong lit refl) , putμ refl
  eqμTerm unknown (var x args)        = no (λ ()) , putμ refl , putμ (cong₂ var refl refl)
  eqμTerm unknown (con c args)        = no (λ ()) , putμ refl , putμ (cong₂ con refl refl)
  eqμTerm unknown (def f args)        = no (λ ()) , putμ refl , putμ (cong₂ def refl refl)
  eqμTerm unknown (lam v y)           = no (λ ()) , putμ refl , putμ (cong₂ lam refl refl)
  eqμTerm unknown (pi t₁ t₂)          = no (λ ()) , putμ refl , putμ (cong₂ pi refl refl)
  eqμTerm unknown (agda-sort x)       = no (λ ()) , putμ refl , putμ (cong agda-sort refl)
  eqμTerm unknown (lit x)             = no (λ ()) , putμ refl , putμ (cong lit refl)

  eqμTerm (var _ _) (meta _ _)        = no (λ ()) , putμ (cong₂ var refl refl) , putμ (cong₂ meta refl refl)
  eqμTerm (con _ _) (meta _ _)        = no (λ ()) , putμ (cong₂ con refl refl) , putμ (cong₂ meta refl refl)
  eqμTerm (def _ _) (meta _ _)        = no (λ ()) , putμ (cong₂ def refl refl) , putμ (cong₂ meta refl refl)
  eqμTerm (lam _ _) (meta _ _)        = no (λ ()) , putμ (cong₂ lam refl refl) , putμ (cong₂ meta refl refl)
  eqμTerm (pi _ _) (meta _ _)         = no (λ ()) , putμ (cong₂ pi refl refl) , putμ (cong₂ meta refl refl)
  eqμTerm (agda-sort _) (meta _ _)    = no (λ ()) , putμ (cong agda-sort refl) , putμ (cong₂ meta refl refl)
  eqμTerm (lit _) (meta _ _)          = no (λ ()) , putμ (cong lit refl) , putμ (cong₂ meta refl refl)
  eqμTerm unknown (meta _ _)          = no (λ ()) , putμ refl , putμ (cong₂ meta refl refl)
  eqμTerm (meta _ _) (var _ _)        = no (λ ()) , putμ (cong₂ meta refl refl) , putμ (cong₂ var refl refl)
  eqμTerm (meta _ _) (con _ _)        = no (λ ()) , putμ (cong₂ meta refl refl) , putμ (cong₂ con refl refl)
  eqμTerm (meta _ _) (def _ _)        = no (λ ()) , putμ (cong₂ meta refl refl) , putμ (cong₂ def refl refl)
  eqμTerm (meta _ _) (lam _ _)        = no (λ ()) , putμ (cong₂ meta refl refl) , putμ (cong₂ lam refl refl)
  eqμTerm (meta _ _) (pi _ _)         = no (λ ()) , putμ (cong₂ meta refl refl) , putμ (cong₂ pi refl refl)
  eqμTerm (meta _ _) (agda-sort _)    = no (λ ()) , putμ (cong₂ meta refl refl) , putμ (cong agda-sort refl)
  eqμTerm (meta _ _) (lit _)          = no (λ ()) , putμ (cong₂ meta refl refl) , putμ (cong lit refl)
  eqμTerm (meta _ _) unknown          = no (λ ()) , putμ (cong₂ meta refl refl) , putμ refl

  eqμTerm (var _ _) (pat-lam _ _)     = no (λ ()) , putμ (cong₂ var refl refl) , putμ (cong₂ pat-lam refl refl)
  eqμTerm (con _ _) (pat-lam _ _)     = no (λ ()) , putμ (cong₂ con refl refl) , putμ (cong₂ pat-lam refl refl)
  eqμTerm (def _ _) (pat-lam _ _)     = no (λ ()) , putμ (cong₂ def refl refl) , putμ (cong₂ pat-lam refl refl)
  eqμTerm (lam _ _) (pat-lam _ _)     = no (λ ()) , putμ (cong₂ lam refl refl) , putμ (cong₂ pat-lam refl refl)
  eqμTerm (pi _ _) (pat-lam _ _)      = no (λ ()) , putμ (cong₂ pi refl refl) , putμ (cong₂ pat-lam refl refl)
  eqμTerm (meta _ _) (pat-lam _ _)    = no (λ ()) , putμ (cong₂ meta refl refl) , putμ (cong₂ pat-lam refl refl)
  eqμTerm (agda-sort _) (pat-lam _ _) = no (λ ()) , putμ (cong agda-sort refl) , putμ (cong₂ pat-lam refl refl)
  eqμTerm (lit _) (pat-lam _ _)       = no (λ ()) , putμ (cong lit refl) , putμ (cong₂ pat-lam refl refl)
  eqμTerm unknown (pat-lam _ _)       = no (λ ()) , putμ refl , putμ (cong₂ pat-lam refl refl)
  eqμTerm (pat-lam _ _) (var _ _)     = no (λ ()) , putμ (cong₂ pat-lam refl refl) , putμ (cong₂ var refl refl)
  eqμTerm (pat-lam _ _) (con _ _)     = no (λ ()) , putμ (cong₂ pat-lam refl refl) , putμ (cong₂ con refl refl)
  eqμTerm (pat-lam _ _) (def _ _)     = no (λ ()) , putμ (cong₂ pat-lam refl refl) , putμ (cong₂ def refl refl)
  eqμTerm (pat-lam _ _) (lam _ _)     = no (λ ()) , putμ (cong₂ pat-lam refl refl) , putμ (cong₂ lam refl refl)
  eqμTerm (pat-lam _ _) (pi _ _)      = no (λ ()) , putμ (cong₂ pat-lam refl refl) , putμ (cong₂ pi refl refl)
  eqμTerm (pat-lam _ _) (meta _ _)    = no (λ ()) , putμ (cong₂ pat-lam refl refl) , putμ (cong₂ meta refl refl)
  eqμTerm (pat-lam _ _) (agda-sort _) = no (λ ()) , putμ (cong₂ pat-lam refl refl) , putμ (cong agda-sort refl)
  eqμTerm (pat-lam _ _) (lit _)       = no (λ ()) , putμ (cong₂ pat-lam refl refl) , putμ (cong lit refl)
  eqμTerm (pat-lam _ _) unknown       = no (λ ()) , putμ (cong₂ pat-lam refl refl) , putμ refl

  eqμSort (set t) (set t₁) = decEqμ₁ set-inj (eqμTerm t t₁)
  eqμSort (lit n) (lit n₁) = decEqμ₁ slit-inj (n ==μ n₁)
  eqμSort unknown unknown = yes refl , putμ refl , putμ refl
  eqμSort (set t) (lit n) = no (λ ()) , putμ (cong set refl) , putμ (cong lit refl)
  eqμSort (set t) unknown = no (λ ()) , putμ (cong set refl) , putμ refl
  eqμSort (lit n) (set t) = no (λ ()) , putμ (cong lit refl) , putμ (cong set refl)
  eqμSort (lit n) unknown = no (λ ()) , putμ (cong lit refl) , putμ refl
  eqμSort unknown (set t) = no (λ ()) , putμ refl , putμ (cong set refl)
  eqμSort unknown (lit n) = no (λ ()) , putμ refl , putμ (cong lit refl)

  eqμPat (con c ps) (con c₁ ps₁) = decEqμ₂ pcon-inj₁ pcon-inj₂ (c ==μ c₁) (eqμPats ps ps₁)
  eqμPat  dot        dot         = yes refl , putμ refl , putμ refl
  eqμPat (var s)    (var s₁)     = decEqμ₁ pvar-inj (s ==μ s₁)
  eqμPat (lit l)    (lit l₁)     = decEqμ₁ plit-inj (l ==μ l₁)
  eqμPat (proj f)   (proj f₁)    = decEqμ₁ proj-inj (f ==μ f₁)
  eqμPat  absurd     absurd      = yes refl , putμ refl , putμ refl

  eqμPat (con _ _) dot      = no (λ ()) , putμ (cong₂ con refl refl) , putμ refl
  eqμPat (con _ _) (var _)  = no (λ ()) , putμ (cong₂ con refl refl) , putμ (cong var refl)
  eqμPat (con _ _) (lit _)  = no (λ ()) , putμ (cong₂ con refl refl) , putμ (cong lit refl)
  eqμPat (con _ _) (proj _) = no (λ ()) , putμ (cong₂ con refl refl) , putμ (cong proj refl)
  eqμPat (con _ _) absurd   = no (λ ()) , putμ (cong₂ con refl refl) , putμ refl

  eqμPat dot (con _ _) = no (λ ()) , putμ refl , putμ (cong₂ con refl refl)
  eqμPat dot (var _)   = no (λ ()) , putμ refl , putμ (cong var refl)
  eqμPat dot (lit _)   = no (λ ()) , putμ refl , putμ (cong lit refl)
  eqμPat dot (proj _)  = no (λ ()) , putμ refl , putμ (cong proj refl)
  eqμPat dot absurd    = no (λ ()) , putμ refl , putμ refl

  eqμPat (var _) (con _ _) = no (λ ()) , putμ (cong var refl) , putμ (cong₂ con refl refl)
  eqμPat (var _) dot       = no (λ ()) , putμ (cong var refl) , putμ refl
  eqμPat (var _) (lit _)   = no (λ ()) , putμ (cong var refl) , putμ (cong lit refl)
  eqμPat (var _) (proj _)  = no (λ ()) , putμ (cong var refl) , putμ (cong proj refl)
  eqμPat (var _) absurd    = no (λ ()) , putμ (cong var refl) , putμ refl

  eqμPat (lit _) (con _ _) = no (λ ()) , putμ (cong lit refl) , putμ (cong₂ con refl refl)
  eqμPat (lit _) dot       = no (λ ()) , putμ (cong lit refl) , putμ refl
  eqμPat (lit _) (var _)   = no (λ ()) , putμ (cong lit refl) , putμ (cong var refl)
  eqμPat (lit _) (proj _)  = no (λ ()) , putμ (cong lit refl) , putμ (cong proj refl)
  eqμPat (lit _) absurd    = no (λ ()) , putμ (cong lit refl) , putμ refl

  eqμPat (proj _) (con _ _) = no (λ ()) , putμ (cong proj refl) , putμ (cong₂ con refl refl)
  eqμPat (proj _) dot       = no (λ ()) , putμ (cong proj refl) , putμ refl
  eqμPat (proj _) (var _)   = no (λ ()) , putμ (cong proj refl) , putμ (cong var refl)
  eqμPat (proj _) (lit _)   = no (λ ()) , putμ (cong proj refl) , putμ (cong lit refl)
  eqμPat (proj _) absurd    = no (λ ()) , putμ (cong proj refl) , putμ refl

  eqμPat absurd (con _ _) = no (λ ()) , putμ refl , putμ (cong₂ con refl refl)
  eqμPat absurd dot       = no (λ ()) , putμ refl , putμ refl
  eqμPat absurd (var _)   = no (λ ()) , putμ refl , putμ (cong var refl)
  eqμPat absurd (lit _)   = no (λ ()) , putμ refl , putμ (cong lit refl)
  eqμPat absurd (proj _)  = no (λ ()) , putμ refl , putμ (cong proj refl)

  eqμClause (clause ps t)      (clause ps₁ t₁)     = decEqμ₂ clause-inj₁ clause-inj₂ (eqμPats ps ps₁) (eqμTerm t t₁)
  eqμClause (absurd-clause ps) (absurd-clause ps₁) = decEqμ₁ absurd-clause-inj (eqμPats ps ps₁)
  eqμClause (clause _ _) (absurd-clause _) = no (λ ()) , putμ (cong₂ clause refl refl) , putμ (cong absurd-clause refl)
  eqμClause (absurd-clause _) (clause _ _) = no (λ ()) , putμ (cong absurd-clause refl) , putμ (cong₂ clause refl refl)

instance
  EqμTerm : Eqμ Term
  _==μ_ {{EqμTerm}} = eqμTerm

  EqμSort : Eqμ Sort
  _==μ_ {{EqμSort}} = eqμSort

  EqμClause : Eqμ Clause
  _==μ_ {{EqμClause}} = eqμClause

  EqμPattern : Eqμ Pattern
  _==μ_ {{EqμPattern}} = eqμPat

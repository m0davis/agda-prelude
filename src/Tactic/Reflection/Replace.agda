module Tactic.Reflection.Replace where
  open import Prelude

  open import Container.Traversable

  open import Tactic.Reflection
  open import Tactic.Reflection.Equality

  record TermReplacer (A : Set) : Set where
    field
      _r[_/_] : A → Term → Term → A

  open TermReplacer ⦃ ... ⦄ public

  private
    mutual
      {-# TERMINATING #-}
      -- p r₀[ r / l ] = replace l with r in p
      _r₀[_/_] : Term → Term → Term → Term
      {-
      p r₀[ r / l ] with p == l
      p r₀[ r / l ] | yes _ = r
      (var x args) r₀[ r / l ] | no _ = var x (args r₂[ r / l ])
      con c args r₀[ r / l ] | no _ = con c $ args r₂[ r / l ]
      def f args r₀[ r / l ] | no _ = def f $ args r₂[ r / l ]
      lam v t r₀[ r / l ] | no _ = lam v $ t r₁[ weaken 1 r / weaken 1 l ] -- lam v <$> t r₁[ weaken 1 r / weaken 1 l ]
      pat-lam cs args r₀[ r / l ] | no _ = let w = length args in pat-lam (replaceClause (weaken w l) (weaken w r) <$> cs) $ args r₂[ r / l ]
      pi a b r₀[ r / l ] | no _ = pi (a r₁[ r / l ]) (b r₁[ weaken 1 r / weaken 1 l ])
      agda-sort s r₀[ r / l ] | no _ = agda-sort $ replaceSort l r s
      lit l r₀[ r / l₁ ] | no _ = lit l
      meta x args r₀[ r / l ] | no _ = meta x $ args r₂[ r / l ]
      unknown r₀[ r / l ] | no _ = unknown
      -}
      p r₀[ r / l ] with isYes (p == l)
      ... | true = r
      ... | false = case p of λ
            { (var x args) → case args r₂[ r / l ] of λ args' → var x args'
            ; (con c args) → con c $ args r₂[ r / l ]
            ; (def f args) → def f $ args r₂[ r / l ]
            ; (lam v t) → lam v $ t r₁[ weaken 1 r / weaken 1 l ] -- lam v <$> t r₁[ weaken 1 r / weaken 1 l ]
            ; (pat-lam cs args) → let w = length args in pat-lam (replaceClause (weaken w l) (weaken w r) <$> cs) $ args r₂[ r / l ]
            ; (pi a b) → case a r₁[ r / l ] of λ a' →
                         case weaken 1 r of λ wr →
                         case weaken 1 l of λ wl →
                         case b r₁[ wr / wl ] of λ b' →
                         pi a' b'
            ; (agda-sort s) → agda-sort $ replaceSort l r s
            ; (lit l) → lit l
            ; (meta x args) → meta x $ args r₂[ r / l ]
            ; unknown → unknown
            }
      {-
      p r₀[ r / l ] =
        ifYes p == l
          then r
          else case p of λ
            { (var x args) → var x $ args r₂[ r / l ]
            ; (con c args) → con c $ args r₂[ r / l ]
            ; (def f args) → def f $ args r₂[ r / l ]
            ; (lam v t) → lam v $ t r₁[ weaken 1 r / weaken 1 l ] -- lam v <$> t r₁[ weaken 1 r / weaken 1 l ]
            ; (pat-lam cs args) → let w = length args in pat-lam (replaceClause (weaken w l) (weaken w r) <$> cs) $ args r₂[ r / l ]
            ; (pi a b) → pi (a r₁[ r / l ]) (b r₁[ weaken 1 r / weaken 1 l ])
            ; (agda-sort s) → agda-sort $ replaceSort l r s
            ; (lit l) → lit l
            ; (meta x args) → meta x $ args r₂[ r / l ]
            ; unknown → unknown
            }
      -}

      replaceClause : Term → Term → Clause → Clause
      replaceClause l r (clause pats x) = clause pats $ x r₀[ r / l ]
      replaceClause l r (absurd-clause pats) = absurd-clause pats

      replaceSort : Term → Term → Sort → Sort
      replaceSort l r (set t) = set $ t r₀[ r / l ]
      replaceSort l r (lit n) = lit n
      replaceSort l r unknown = unknown

      _r₁[_/_] : {T₀ : Set → Set} {{_ : Functor T₀}} {{_ : Traversable T₀}} → T₀ Term → Term → Term → T₀ Term
      p r₁[ r / l ] = _r₀[ r / l ] <$> p

      _r₂[_/_] : {T₀ T₁ : Set → Set} {{_ : Functor T₀}} {{_ : Traversable T₀}} {{_ : Functor T₁}} {{_ : Traversable T₁}} → T₁ (T₀ Term) → Term → Term → T₁ (T₀ Term)
      p r₂[ r / l ] = fmap _r₀[ r / l ] <$> p

  instance
    TermTR : TermReplacer Term
    TermReplacer._r[_/_] TermTR = _r₀[_/_]

    ArgTermTR : TermReplacer (Arg Term)
    TermReplacer._r[_/_] ArgTermTR = λ x r l → _r₀[ r / l ] <$> x

  -- Γ R[ L / R ] = replace L with R in Γ
  _R[_/_] : List (Arg Type) → Type → Type → List (Arg Type)
  Γ R[ L / R ] = go Γ (strengthen 1 L) (strengthen 1 R) where
    go : List (Arg Type) → Maybe Term → Maybe Term → List (Arg Type)
    --go (γ ∷ Γ) (just L) (just R) = (caseF γ of _r[ L / R ]) ∷ go Γ (strengthen 1 L) (strengthen 1 R)
    go (γ ∷ Γ) (just L) (just R) = (_r[ L / R ] <$> γ) ∷ go Γ (strengthen 1 L) (strengthen 1 R)
    go Γ _ _ = Γ

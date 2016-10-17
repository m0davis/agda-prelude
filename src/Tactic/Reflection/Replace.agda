module Tactic.Reflection.Replace where
  open import Prelude

  open import Container.Traversable

  open import Tactic.Reflection
  open import Tactic.Reflection.Equality

  record TermReplacer (A : Set) : Set where
    field
      depth=_∣_r[_/_] : Nat → A → Term → Term → A

    _r[_/_] = depth= 0 ∣_r[_/_]

  open TermReplacer ⦃ ... ⦄ public

  private
    mutual
      {-# TERMINATING #-}
      -- p r₀[ r / l ] = replace l with r in p
      depth=_∣_r₀[_/_] : Nat → Term → Term → Term → Term
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
      depth= d ∣ p r₀[ r / l ] with isYes (p == weaken d l)
      ... | true = weaken d r
      ... | false = case p of λ
            { (var x args) → case depth= d ∣ args r₂[ r / l ] of λ args' → var x args'
            ; (con c args) → con c $ depth= d ∣ args r₂[ r / l ]
            ; (def f args) → def f $ depth= d ∣ args r₂[ r / l ]
            ; (lam v t) → lam v $ depth= (suc d) ∣ t r₁[ r / l ] -- lam v <$> t r₁[ weaken 1 r / weaken 1 l ]
            ; (pat-lam cs args) → let w = length args in pat-lam (replaceClause (d + w) l r <$> cs) $ depth= d ∣ args r₂[ r / l ]
            ; (pi a b) → pi (depth= d ∣ a r₁[ r / l ]) (depth= (suc d) ∣ b r₁[ r / l ])
            ; (agda-sort s) → agda-sort $ replaceSort d l r s
            ; (lit l) → lit l
            ; (meta x args) → meta x $ depth= d ∣ args r₂[ r / l ]
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

      replaceClause : Nat → Term → Term → Clause → Clause
      replaceClause d l r (clause pats x) = clause pats $ depth= d ∣ x r₀[ r / l ]
      replaceClause d l r (absurd-clause pats) = absurd-clause pats

      replaceSort : Nat → Term → Term → Sort → Sort
      replaceSort d l r (set t) = set $ depth= d ∣ t r₀[ r / l ]
      replaceSort d l r (lit n) = lit n
      replaceSort d l r unknown = unknown

      depth=_∣_r₁[_/_] : Nat → {T₀ : Set → Set} {{_ : Functor T₀}} {{_ : Traversable T₀}} → T₀ Term → Term → Term → T₀ Term
      depth= d ∣ p r₁[ r / l ] = depth= d ∣_r₀[ r / l ] <$> p

      depth=_∣_r₂[_/_] : Nat → {T₀ T₁ : Set → Set} {{_ : Functor T₀}} {{_ : Traversable T₀}} {{_ : Functor T₁}} {{_ : Traversable T₁}} → T₁ (T₀ Term) → Term → Term → T₁ (T₀ Term)
      depth= d ∣ p r₂[ r / l ] = fmap depth= d ∣_r₀[ r / l ] <$> p

  instance
    TermTR : TermReplacer Term
    TermReplacer.depth=_∣_r[_/_] TermTR = depth=_∣_r₀[_/_]

    ArgTermTR : TermReplacer (Arg Term)
    TermReplacer.depth=_∣_r[_/_] ArgTermTR = λ d x r l → depth= d ∣_r₀[ r / l ] <$> x

  -- Γ R[ L / R ] = replace L with R in Γ
  _R[_/_] : List (Arg Type) → Type → Type → List (Arg Type)
  Γ R[ L / R ] = go Γ (strengthen 1 L) (strengthen 1 R) where
    go : List (Arg Type) → Maybe Term → Maybe Term → List (Arg Type)
    --go (γ ∷ Γ) (just L) (just R) = (caseF γ of _r[ L / R ]) ∷ go Γ (strengthen 1 L) (strengthen 1 R)
    go (γ ∷ Γ) (just L) (just R) = (_r[ L / R ] <$> γ) ∷ go Γ (strengthen 1 L) (strengthen 1 R)
    go Γ _ _ = Γ

  record TermReplacer' (A : Set) : Set where
    field
      _r'[_/_] : A → Term → Term → Maybe A

  open TermReplacer' ⦃ ... ⦄ public

  private
    mutual
      {-# TERMINATING #-}
      -- p r₀[ r / l ] = replace l with r in p
      _r₀'[_/_] : Term → Term → Term → Maybe Term
      p r₀'[ r / l ] with p == l
      p r₀'[ r / l ] | yes _ = just r
      var x args r₀'[ r / l ] | no _ =
        var x <$> args r₂'[ r / l ]
      con c args r₀'[ r / l ] | no _ =
        con c <$> args r₂'[ r / l ]
      def f args r₀'[ r / l ] | no _ =
        def f <$> args r₂'[ r / l ]
      lam v t r₀'[ r / l ] | no _ =
        lam v <$> t r₁'[ weaken 1 r / weaken 1 l ]
      pat-lam cs args r₀'[ r / l ] | no _ =
        let w = length args
            cs' = replaceClauses' (weaken w l) (weaken w r) cs
            args' = args r₂'[ r / l ]
        in
          case cs' , args' of λ
          { (nothing , nothing  ) → nothing
          ; (just cs , nothing  ) → just (pat-lam cs args)
          ; (nothing , just args) → just (pat-lam cs args)
          ; (just cs , just args) → just (pat-lam cs args) }
      pi a b r₀'[ r / l ] | no _ =
        let a' = a r₁'[ r / l ]
            b' = b r₁'[ weaken 1 r / weaken 1 l ]
        in
          case a' , b' of λ
          { (nothing , nothing) → nothing
          ; (just a  , nothing) → just (pi a b)
          ; (nothing , just b ) → just (pi a b)
          ; (just a  , just b ) → just (pi a b) }
      agda-sort s r₀'[ r / l ] | no _ =
          maybe nothing (just ∘ agda-sort) $ replaceSort' l r s
      lit l r₀'[ r / l₁ ] | no _ = nothing
      meta x args r₀'[ r / l ] | no _ =
        meta x <$> args r₂'[ r / l ]
      unknown r₀'[ r / l ] | no _ = nothing

      replaceClauses' : Term → Term → List Clause → Maybe (List Clause)
      replaceClauses' l r [] = nothing
      replaceClauses' l r (c ∷ cs) =
        let c' = replaceClause' l r c
            cs' = replaceClauses' l r cs
        in
          case c' , cs' of λ
          { (nothing , nothing) → nothing
          ; (just c  , nothing) → just (c ∷ cs)
          ; (nothing , just cs) → just (c ∷ cs)
          ; (just c  , just cs) → just (c ∷ cs) }

      replaceClause' : Term → Term → Clause → Maybe Clause
      replaceClause' l r (clause pats x) = clause pats <$> x r₀'[ r / l ]
      replaceClause' l r (absurd-clause pats) = nothing

      replaceSort' : Term → Term → Sort → Maybe Sort
      replaceSort' l r (set t) = set <$> t r₀'[ r / l ]
      replaceSort' l r (lit n) = nothing
      replaceSort' l r unknown = nothing

      _r₁'[_/_] : {T₀ : Set → Set} {{_ : Functor T₀}} {{_ : Traversable T₀}} → T₀ Term → Term → Term → Maybe (T₀ Term)
      p r₁'[ r / l ] = traverse _r₀'[ r / l ] p

      _r₂'[_/_] : List (Arg Term) → Term → Term → Maybe (List (Arg Term))
      [] r₂'[ r / l ] = nothing
      (p ∷ ps) r₂'[ r / l ] =
        let ps' = ps r₂'[ r / l ]
            p'  = p  r₁'[ r / l ]
        in
        case (p' , ps') of λ
        { (nothing , nothing) → nothing
        ; (just p  , nothing) → just (p ∷ ps)
        ; (nothing , just ps) → just (p ∷ ps)
        ; (just p  , just ps) → just (p ∷ ps) }

  instance
    TermTR' : TermReplacer' Term
    TermReplacer'._r'[_/_] TermTR' = _r₀'[_/_]

    ArgTermTR' : TermReplacer' (Arg Term)
    TermReplacer'._r'[_/_] ArgTermTR' = λ x r l → traverse _r₀'[ r / l ] x

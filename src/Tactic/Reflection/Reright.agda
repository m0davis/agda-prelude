module Tactic.Reflection.Reright where
  open import Prelude

  open import Tactic.Reflection
  open import Tactic.Reflection.Match
  open import Tactic.Reflection.Replace
  open import Tactic.Reflection.Quote

  private
    {-# TERMINATING #-}
    reorderVars : List Nat → Term → Term
    reorderVars xs (var x args) = var (maybe x id (index xs x)) (fmap (reorderVars xs) <$> args)
    reorderVars xs (con c args) = con c ((fmap ∘ fmap) (reorderVars xs) args)
    reorderVars xs (def f args) = def f (fmap (reorderVars xs) <$> args)
    reorderVars xs (lam v t) = lam v (reorderVars (0 ∷ weaken 1 xs) <$> t)
    reorderVars xs (pat-lam cs args) = pat-lam (fmap (reorderVarsInClause xs) cs) ((fmap ∘ fmap) (reorderVars xs) args) where
      reorderVarsInClause : List Nat → Clause → Clause -- TODO reorder patterns?
      reorderVarsInClause xs (clause ps t) = (clause ps (reorderVars xs t))
      reorderVarsInClause xs (absurd-clause ps) = (absurd-clause ps)
    reorderVars xs (pi a b) = pi (reorderVars xs <$> a) (reorderVars (0 ∷ weaken 1 xs) <$> b)
    reorderVars xs (agda-sort (set t)) = agda-sort (set (reorderVars xs t))
    reorderVars xs (agda-sort (lit n)) = agda-sort (lit n)
    reorderVars xs (agda-sort unknown) = agda-sort unknown
    reorderVars xs (lit l) = lit l
    reorderVars xs (meta x args) = meta x $ (fmap ∘ fmap) (reorderVars xs) args
    reorderVars xs unknown = unknown

    -- replace the iᵗʰ element of xs with the value y
    setElem : Nat → ∀ {a} {A : Set a} → A → List A → List A
    setElem i y xs =
      let xs' = splitAt i xs
      in
      fst xs' ++ (y ∷ drop 1 (snd xs'))

    record Request : Set where
      field
        l≡r : Term
        A : Type
        L R : Type
        Γ : List (Arg Type)
        𝐺 : Type

      {-
                             <------- helper-type--------- ... -->
         <------- Γ ------->        <------ Γ[w/L] ------>
         γ₀ γ₁ ... γᵢ ... γₙ w w≡R γ'₀ γ'₁ ... γ'ⱼ ... γ'ₘ

         γ' = γ'ⱼ
      -}
      Γ[w/L]×indexes[Γ]  : List (Arg Type × Nat)
      Γ[w/L]×indexes[Γ] = go 0 0 (from 0 for (length Γ + 2)) Γ where
        go : Nat → Nat → List Nat → List (Arg Type) → List (Arg Type × Nat)
        go _ _ _ [] = []
        go i j osⱼ (γ ∷ γs) =
          let n = length Γ - 1
              L' = weaken (2 + j) L
              γ' = weaken ((n - i) + 3 + j) γ
              w' = var₀ (suc j)
              γ'[w'/L'] = γ' r[ w' / L' ]
              γ'[w'/L'][reordered] = reorderVars osⱼ <$> γ'[w'/L']
              γ≢l≡r = isNo $ var₀ (n - i) == l≡r
              γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
          in
          if γ≢l≡r && γ'≠γ'[w'/L'][reordered] then (
            let osⱼ′ = splitAt (j + 3 + n - i) (0 ∷ weaken 1 osⱼ)
                osⱼ₊₁ = fst osⱼ′ ++ (0 ∷ drop 1 (snd osⱼ′))
            in
            (γ'[w'/L'][reordered] , i) ∷ go (suc i) (suc j) osⱼ₊₁ γs
          ) else
            go (suc i) j (0 ∷ weaken 1 osⱼ) γs

      Γ[w/L] : List (Arg Type)
      Γ[w/L] = fst <$> Γ[w/L]×indexes[Γ]

      indexes[Γ] : List Nat
      indexes[Γ] = snd <$> Γ[w/L]×indexes[Γ]

      ∣Γᴸ∣ = length Γ[w/L]

      {-
         <---------------------- helper-type------------------ ... -->
               <---- Γ[w/L] ----->   <------ Γ[R/L] ------->
         w w≡R γ₀ γ₁ ... γᵢ ... γₙ ( γ'₀ γ'₁ ... γ'ᵢ ... γ'ₙ )
         n = ∣Γᴸ∣ - 1 = length Γ[w/L] - 1
      -}
      Γ[R/L] : List (Arg Type)
      Γ[R/L] = go 0 Γ[w/L] where
        go : Nat → List (Arg Type) → List (Arg Type)
        go _ [] = []
        go i (γ ∷ γs) =
          -- γ is the index[γ]ᵗʰ element of Γ[w/L]
          let n = ∣Γᴸ∣ - 1
              γ' = weakenFrom i ∣Γᴸ∣ γ
              w' = var₀ (i + n + 2)
              R' = weaken (2 + ∣Γᴸ∣ + i) R
              γ'[R'/w'] = γ' r[ R' / w' ]
          in
            γ'[R'/w'] ∷ go (suc i) γs

      {-
         Γ             Γ[w/L]   Γ[R/L]
         0 ... n w w≡R 0 ... m (0 ... m → 𝐺[R/L]) → 𝐺[w/L]
      -}
      𝐺[R/L] : Type
      𝐺[R/L] =
        let os = from 0 for (2 * ∣Γᴸ∣ + 2 + length Γ)
            os′ = go 0 indexes[Γ] os
            𝐺' = weaken (2 * ∣Γᴸ∣ + 2) (𝐺 r[ R / L ])
        in
          reorderVars os′ 𝐺'
        where

        go : Nat → List Nat → List Nat → List Nat
        go _ [] ns = ns
        go j (i ∷ is) ns = go (suc j) is $ setElem (2 * ∣Γᴸ∣ + 2 + (length Γ - 1) - i) ((∣Γᴸ∣ - 1) - j) ns

      𝐺[w/L] : Type
      𝐺[w/L] =
        let os = from 0 for (1 + ∣Γᴸ∣ + 2 + length Γ)
            os′ = go 0 indexes[Γ] os
            𝐺' = (weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / weaken (3 + ∣Γᴸ∣) L ]
        in
          reorderVars os′ 𝐺'
        where

        go : Nat → List Nat → List Nat → List Nat
        go _ [] ns = ns
        go j (i ∷ is) ns = go (suc j) is $ setElem (1 + ∣Γᴸ∣ + 2 + (length Γ - 1) - i) (1 + (∣Γᴸ∣ - 1) - j) ns


      w : Arg Type
      w = hArg A

      w≡R : Arg Type
      w≡R = vArg (def₂ (quote _≡_) (var₀ 0) (weaken 1 R))

      helper-type : Type
      helper-type = telPi ((w ∷ w≡R ∷ Γ[w/L]) ++ [ vArg (telPi Γ[R/L] 𝐺[R/L]) ]) 𝐺[w/L]

      helper-patterns : List (Arg Pattern)
      helper-patterns = (hArg dot ∷ vArg (con₀ (quote refl)) ∷ telePat Γ[w/L]) ++ [ vArg (var "_") ]

      helper-term : Term
      helper-term = var 0 (weaken 1 (teleArgs Γ[w/L]))

      helper-call-args : List (Arg Term)
      helper-call-args = hArg unknown ∷ vArg l≡r ∷ helper-call-args' where
        helper-call-args' : List (Arg Term)
        helper-call-args' = (λ { (γ[w/L] , index[γ]) → var₀ (length Γ - index[γ] - 1) <$ γ[w/L] }) <$> Γ[w/L]×indexes[Γ]

    getRequest : Term → Term → TC Request
    getRequest l≡r hole = do
      L≡R ← inferType l≡r -|
      L≡R-matched ← maybe (typeError (strErr "not an equality" ∷ termErr l≡r ∷ termErr L≡R ∷ [])) pure $
        match 3 (def (quote _≡_) (hArg unknown ∷ (hArg (var₀ 0)) ∷ (vArg (var₀ 1)) ∷ (vArg (var₀ 2)) ∷ [])) L≡R -|
      𝐺 ← inferFunRange hole -|
      Γ ← getContext -|
      case L≡R-matched of λ { (A ∷ L ∷ R ∷ []) →
        pure $ record { l≡r = l≡r ; A = A ; L = L ; R = R ; Γ = reverse Γ ; 𝐺 = 𝐺 } }

  macro
    reright-debug : Term → Tactic
    reright-debug l≡r hole =
      q ← getRequest l≡r hole -|
      let open Request q in
      typeError ( strErr "reright-debug"     ∷
                  strErr "\nl≡r:"            ∷ termErr (` (Request.l≡r q))      ∷
                  strErr "\nA:"              ∷ termErr (` A)                    ∷
                  strErr "\nL:"              ∷ termErr (` L)                    ∷
                  strErr "\nR:"              ∷ termErr (` R)                    ∷
                  strErr "\nΓ:"              ∷ termErr (` Γ)                    ∷
                  strErr "\n𝐺:"              ∷ termErr (` 𝐺)                    ∷
                  strErr "\nΓ[w/L]:"         ∷ termErr (` Γ[w/L])               ∷
                  strErr "\nindexes[Γ]:"     ∷ termErr (` indexes[Γ])           ∷
                  strErr "\n∣Γᴸ∣:"           ∷ termErr (` ∣Γᴸ∣)                 ∷
                  strErr "\nΓ[R/L]:"         ∷ termErr (` Γ[R/L])               ∷
                  strErr "\n𝐺[R/L]:"         ∷ termErr (` 𝐺[R/L])               ∷
                  strErr "\n𝐺[w/L]:"         ∷ termErr (` 𝐺[w/L])               ∷
                  strErr "\nw:"              ∷ termErr (` w)                    ∷
                  strErr "\nw≡R:"            ∷ termErr (` w≡R)                  ∷
                  strErr "helper-type:"      ∷ termErr helper-type              ∷
                  strErr "helper-patterns:"  ∷ termErr (` helper-patterns)      ∷
                  strErr "helper-term:"      ∷ termErr (` helper-term)          ∷
                  strErr "helper-call-args:" ∷ termErr (` helper-call-args)     ∷
                  [] )

    reright : Term → Tactic
    reright l≡r hole =
      q ← getRequest l≡r hole -|
      n ← freshName "reright" -|
      let open Request q in
      catchTC (typeError [ strErr "error defining helper function" ]) (define (vArg n) helper-type [ clause helper-patterns helper-term ]) ~|
      unify hole (def n helper-call-args)

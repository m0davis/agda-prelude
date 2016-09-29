module Tactic.Reflection.Reright where
  open import Prelude

  open import Tactic.Reflection
  open import Tactic.Reflection.Match
  open import Tactic.Reflection.Replace
  open import Tactic.Reflection.Quote

  private
    weakenList : List Nat → List Nat
    weakenList [] = []
--    weakenList (x ∷ xs) = (if ((_<?_ $! x) $! 0) then x else suc x) ∷ weakenList xs

    weakenList (x ∷ xs) with x <? 0
    ... | true = x ∷ weakenList xs
    ... | false = (suc x) ∷ weakenList xs

    weakenList' : List Nat → List Nat
    weakenList' [] = []
    weakenList' (x ∷ xs) with x <? 0
    ... | true = x ∷ weakenList' xs
    ... | false = (x + 1) ∷ weakenList' xs

    weakenList'' : List Nat → List Nat
    weakenList'' [] = []
    weakenList'' (x ∷ xs) = (if x <? 0 then x else suc x) ∷ weakenList xs

    weakenOrder : List (Nat × Nat) → List (Nat × Nat)
    weakenOrder [] = []
    weakenOrder ((x , n) ∷ xs) = (suc x , suc n) ∷ weakenOrder xs

    orderingToReplacement : List Nat → List (Nat × Nat)
    orderingToReplacement xs = go 0 xs where
      go : Nat → List Nat → List (Nat × Nat)
      go n [] = []
      go n (x ∷ xs) with n == x
      ... | yes _ = go (suc n) xs
      ... | no _ = (n , x) ∷ go (suc n) xs

    replaceVar : Nat → List (Nat × Nat) → Nat → Nat
    replaceVar d [] x = x
    replaceVar d ((x-d , n-d) ∷ xns) x with x == x-d + d
    ... | yes _ = n-d + d
    ... | no _ = replaceVar d xns x
{-
    reorderVars' : Nat → Nat → List (Nat × Nat) → Term → Term
    reorderVars' 0 _ _ x = x
    reorderVars' (suc n) d xns (var x args) = var (replaceVar d xns x) (fmap (reorderVars' n d xns) <$> args)
    reorderVars' (suc n) d xns (con c args) = con c ((fmap ∘ fmap) (reorderVars' n d xns) args)
    reorderVars' (suc n) d xns (def f args) = def f (fmap (reorderVars' n d xns) <$> args)
    reorderVars' (suc n) d xns (lam v t) = lam v (reorderVars' n (suc d) xns <$> t)
    reorderVars' (suc n) d xns (pat-lam cs args) = pat-lam (fmap (reorderVars'InClause n d xns) cs) ((fmap ∘ fmap) (reorderVars' n d xns) args) where
      reorderVars'InClause : Nat → Nat → List (Nat × Nat) → Clause → Clause -- TODO reorder patterns?
      reorderVars'InClause n d xns (clause ps t) = (clause ps (reorderVars' n d xns t))
      reorderVars'InClause n d xns (absurd-clause ps) = (absurd-clause ps)
    reorderVars' (suc n) d xns (pi a b) = pi (reorderVars' n d xns <$> a) (reorderVars' n (suc d) xns <$> b)
    reorderVars' (suc n) d xns (agda-sort (set t)) = agda-sort (set (reorderVars' n d xns t))
    reorderVars' (suc n') d xns (agda-sort (lit n)) = agda-sort (lit n')
    reorderVars' (suc n) d xns (agda-sort unknown) = agda-sort unknown
    reorderVars' (suc n) d xns (lit l) = lit l
    reorderVars' (suc n) d xns (meta x args) = meta x $ (fmap ∘ fmap) (reorderVars' n d xns) args
    reorderVars' (suc n) d xns unknown = unknown

    reorderVars-fast : List (Nat × Nat) → Term → Term
    reorderVars-fast xs t = reorderVars' 99 0 xs t

    reorderVars-slow : List Nat → Term → Term
    reorderVars-slow xs t = reorderVars' 99 0 (orderingToReplacement xs) t
-}

  {-
    reorderVars' : Nat → List Nat → Term → Term
    reorderVars' _ _ x = x -- maybe unknown id (strengthen 1 (weaken 1 x))
  -}

    reorderVars' : Nat → List Nat → Term → Term
    reorderVars' 0 _ x = x
    reorderVars' (suc n) xs (var x args) = var (maybe x id (index xs x)) (fmap (reorderVars' n xs) <$> args)
    reorderVars' (suc n) xs (con c args) = con c ((fmap ∘ fmap) (reorderVars' n xs) args)
    reorderVars' (suc n) xs (def f args) = def f (fmap (reorderVars' n xs) <$> args)
    reorderVars' (suc n) xs (lam v t) = lam v (reorderVars' n (0 ∷ weaken 1 xs) <$> t)
    reorderVars' (suc n) xs (pat-lam cs args) = pat-lam (fmap (reorderVars'InClause n xs) cs) ((fmap ∘ fmap) (reorderVars' n xs) args) where
      reorderVars'InClause : Nat → List Nat → Clause → Clause -- TODO reorder patterns?
      reorderVars'InClause n xs (clause ps t) = (clause ps (reorderVars' n xs t))
      reorderVars'InClause n xs (absurd-clause ps) = (absurd-clause ps)
    reorderVars' (suc n) xs (pi a b) = pi (reorderVars' n xs <$> a) (reorderVars' n (0 ∷ weaken 1 xs) <$> b)
    reorderVars' (suc n) xs (agda-sort (set t)) = agda-sort (set (reorderVars' n xs t))
    reorderVars' (suc n') xs (agda-sort (lit n)) = agda-sort (lit n')
    reorderVars' (suc n) xs (agda-sort unknown) = agda-sort unknown
    reorderVars' (suc n) xs (lit l) = lit l
    reorderVars' (suc n) xs (meta x args) = meta x $ (fmap ∘ fmap) (reorderVars' n xs) args
    reorderVars' (suc n) xs unknown = unknown

    reorderVars-slow : List Nat → Term → Term
    reorderVars-slow xs t = reorderVars' 99 xs t

{-
    reorderVars' : Nat → Term → Term
    reorderVars' 0 x = x
    reorderVars' (suc n) (var x args) = var x (fmap (reorderVars' n) <$> args)
    reorderVars' (suc n) (con c args) = con c ((fmap ∘ fmap) (reorderVars' n) args)
    reorderVars' (suc n) (def f args) = def f (fmap (reorderVars' n) <$> args)
    reorderVars' (suc n) (lam v t) = lam v (reorderVars' n <$> t)
    reorderVars' (suc n) (pat-lam cs args) = pat-lam (fmap (reorderVars'InClause n) cs) ((fmap ∘ fmap) (reorderVars' n) args) where
      reorderVars'InClause : Nat → Clause → Clause -- TODO reorder patterns?
      reorderVars'InClause n (clause ps t) = (clause ps (reorderVars' n t))
      reorderVars'InClause n (absurd-clause ps) = (absurd-clause ps)
    reorderVars' (suc n) (pi a b) = pi (reorderVars' n <$> a) (reorderVars' n <$> b)
    reorderVars' (suc n) (agda-sort (set t)) = agda-sort (set (reorderVars' n t))
    reorderVars' (suc n') (agda-sort (lit n)) = agda-sort (lit n')
    reorderVars' (suc n) (agda-sort unknown) = agda-sort unknown
    reorderVars' (suc n) (lit l) = lit l
    reorderVars' (suc n) (meta x args) = meta x $ (fmap ∘ fmap) (reorderVars' n) args
    reorderVars' (suc n) unknown = unknown
-}
{-
    reorderVars' : Nat → List Nat → Term → Term
    reorderVars' 0 _ x = x
    reorderVars' (suc n) [] (var x args) = var x (fmap (reorderVars' n []) <$> args)
    reorderVars' (suc n) (x' ∷ xs') (var x args) = var x' (fmap (reorderVars' n (x' ∷ xs')) <$> args)
    reorderVars' (suc n) xs (con c args) = con c ((fmap ∘ fmap) (reorderVars' n xs) args)
    reorderVars' (suc n) xs (def f args) = def f (fmap (reorderVars' n xs) <$> args)
    reorderVars' (suc n) xs (lam v t) = lam v (reorderVars' n (0 ∷ weaken 1 xs) <$> t)
    reorderVars' (suc n) xs (pat-lam cs args) = pat-lam (fmap (reorderVars'InClause n xs) cs) ((fmap ∘ fmap) (reorderVars' n xs) args) where
      reorderVars'InClause : Nat → List Nat → Clause → Clause -- TODO reorder patterns?
      reorderVars'InClause n xs (clause ps t) = (clause ps (reorderVars' n xs t))
      reorderVars'InClause n xs (absurd-clause ps) = (absurd-clause ps)
    reorderVars' (suc n) xs (pi a b) = pi (reorderVars' n xs <$> a) (reorderVars' n (0 ∷ weaken 1 xs) <$> b)
    reorderVars' (suc n) xs (agda-sort (set t)) = agda-sort (set (reorderVars' n xs t))
    reorderVars' (suc n') xs (agda-sort (lit n)) = agda-sort (lit n')
    reorderVars' (suc n) xs (agda-sort unknown) = agda-sort unknown
    reorderVars' (suc n) xs (lit l) = lit l
    reorderVars' (suc n) xs (meta x args) = meta x $ (fmap ∘ fmap) (reorderVars' n xs) args
    reorderVars' (suc n) xs unknown = unknown
-}
{-
    reorderVars' : Nat → List Nat → Term → Term
    reorderVars' 0 _ x = x
    reorderVars' (suc n) xs (var x args) = var (length xs) (fmap (reorderVars' n xs) <$> args)
    reorderVars' (suc n) xs (con c args) = con c ((fmap ∘ fmap) (reorderVars' n xs) args)
    reorderVars' (suc n) xs (def f args) = def f (fmap (reorderVars' n xs) <$> args)
    reorderVars' (suc n) xs (lam v t) = lam v (reorderVars' n (0 ∷ weaken 1 xs) <$> t)
    reorderVars' (suc n) xs (pat-lam cs args) = pat-lam (fmap (reorderVars'InClause n xs) cs) ((fmap ∘ fmap) (reorderVars' n xs) args) where
      reorderVars'InClause : Nat → List Nat → Clause → Clause -- TODO reorder patterns?
      reorderVars'InClause n xs (clause ps t) = (clause ps (reorderVars' n xs t))
      reorderVars'InClause n xs (absurd-clause ps) = (absurd-clause ps)
    reorderVars' (suc n) xs (pi a b) = pi (reorderVars' n xs <$> a) (reorderVars' n (0 ∷ weaken 1 xs) <$> b)
    reorderVars' (suc n) xs (agda-sort (set t)) = agda-sort (set (reorderVars' n xs t))
    reorderVars' (suc n') xs (agda-sort (lit n)) = agda-sort (lit n')
    reorderVars' (suc n) xs (agda-sort unknown) = agda-sort unknown
    reorderVars' (suc n) xs (lit l) = lit l
    reorderVars' (suc n) xs (meta x args) = meta x $ (fmap ∘ fmap) (reorderVars' n xs) args
    reorderVars' (suc n) xs unknown = unknown
-}
    {-
    --{-# TERMINATING #-}
    reorderVars : List Nat → Term → Term
    reorderVars xs t = reorderVars' 99 xs t
    -}
    {-
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
    -}

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
      {-
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
              γ'[w'/L'][reordered] = reorderVars-fast (orderingToReplacement osⱼ) <$> γ'[w'/L']
              γ≢l≡r = isNo $ var₀ (n - i) == l≡r
              γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
          in
          if γ≢l≡r && γ'≠γ'[w'/L'][reordered] then (
            let --osⱼ′ = splitAt (j + 3 + n - i) (0 ∷ weaken 1 osⱼ)
                --osⱼ₊₁ = fst osⱼ′ ++ (0 ∷ drop 1 (snd osⱼ′))
                osⱼ₊₁ = 0 ∷ weaken 1 osⱼ
            in
            (γ'[w'/L'][reordered] , i) ∷ go (suc i) (suc j) osⱼ₊₁ γs
          ) else
            go (suc i) j (0 ∷ weaken 1 osⱼ) γs
      -}
      {-
      Γ[w/L]×indexes[Γ]  : List (Arg Type × Nat)
      Γ[w/L]×indexes[Γ] = go 0 0 (from 0 for (length Γ + 2)) Γ where
        go : Nat → Nat → List Nat → List (Arg Type) → List (Arg Type × Nat)
        go _ _ _ [] = []
        go i j osⱼ (γ ∷ γs) =
          (reorderVars-fast (orderingToReplacement osⱼ) <$> γ , i) ∷ go (suc i) j (0 ∷ weaken 1 osⱼ) γs
      -}

      {-
      Γ[w/L]'  : List (Arg Type)
      Γ[w/L]' = go (from 0 for (length Γ + 2)) Γ where
        go : List Nat → List (Arg Type) → List (Arg Type)
        go _ [] = []
        go osⱼ (γ ∷ γs) =
          (reorderVars-fast (orderingToReplacement osⱼ) <$> γ) ∷ (go (0 ∷ (weaken 1 osⱼ)) γs)
      -}

      Γ[w/L]'  : List (Arg Type)
      Γ[w/L]' = go (from 0 for (length Γ + 2)) Γ where
        go : List Nat → List (Arg Type) → List (Arg Type)
        go _ [] = []
        go osⱼ (γ ∷ γs) =
          (reorderVars-slow osⱼ <$> γ) ∷ (go (0 ∷ (weakenList'' osⱼ)) γs)

      {-
      Γ[w/L]×indexes[Γ]  : List (Arg Type × Nat)
      Γ[w/L]×indexes[Γ] = go 0 0 [] Γ where
        go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat)
        go _ _ _ [] = []
        go i j osⱼ (γ ∷ γs) =
          let n = length Γ - 1
              L' = weaken (2 + j) L
              γ' = weaken ((n - i) + 3 + j) γ
              w' = var₀ (suc j)
              γ'[w'/L'] = γ' r[ w' / L' ]
              γ'[w'/L'][reordered] = reorderVars-fast osⱼ <$> γ'[w'/L']
              γ≢l≡r = isNo $ var₀ (n - i) == l≡r
              γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
          in
          if γ≢l≡r && γ'≠γ'[w'/L'][reordered] then
            (γ'[w'/L'][reordered] , i) ∷ go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ (weakenOrder osⱼ)) γs
          else
            go (suc i) j (weakenOrder osⱼ) γs
      -}

      {-
      Γ[w/L] : List (Arg Type)
      Γ[w/L] = fst <$> Γ[w/L]×indexes[Γ]
      --Γ[w/L] = vArg unknown ∷ []

      indexes[Γ] : List Nat
      indexes[Γ] = snd <$> Γ[w/L]×indexes[Γ]
      --indexes[Γ] = 30 ∷ []

      ∣Γᴸ∣ = length Γ[w/L]
      -}
{-

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
-}

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
                  strErr "\nΓ[w/L]':"        ∷ termErr (` Γ[w/L]')              ∷
{-
                  strErr "\nΓ[w/L]:"         ∷ termErr (` Γ[w/L])               ∷
                  strErr "\nindexes[Γ]:"     ∷ termErr (` indexes[Γ])           ∷
                  strErr "\n∣Γᴸ∣:"           ∷ termErr (` ∣Γᴸ∣)                 ∷
-}
{-
                  strErr "\nΓ[R/L]:"         ∷ termErr (` Γ[R/L])               ∷
                  strErr "\n𝐺[R/L]:"         ∷ termErr (` 𝐺[R/L])               ∷
                  strErr "\n𝐺[w/L]:"         ∷ termErr (` 𝐺[w/L])               ∷
                  strErr "\nw:"              ∷ termErr (` w)                    ∷
                  strErr "\nw≡R:"            ∷ termErr (` w≡R)                  ∷
                  strErr "helper-type:"      ∷ termErr helper-type              ∷
                  strErr "helper-patterns:"  ∷ termErr (` helper-patterns)      ∷
                  strErr "helper-term:"      ∷ termErr (` helper-term)          ∷
                  strErr "helper-call-args:" ∷ termErr (` helper-call-args)     ∷
-}
                  [] )
{-
    reright : Term → Tactic
    reright l≡r hole =
      q ← getRequest l≡r hole -|
      n ← freshName "reright" -|
      let open Request q in
      catchTC (typeError [ strErr "error defining helper function" ]) (define (vArg n) helper-type [ clause helper-patterns helper-term ]) ~|
      unify hole (def n helper-call-args)
-}

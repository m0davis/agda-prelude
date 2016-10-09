module Tactic.Reflection.Reright where
  open import Prelude

  open import Tactic.Reflection
  open import Tactic.Reflection.Match
  open import Tactic.Reflection.Replace
  open import Tactic.Reflection.Quote

  open import Agda.Builtin.Size


  data Sort'   : {_ : Size} → Set
  data Clause' : {_ : Size} → Set
  data Term'   : {_ : Size} → Set
  Type' = Term'

  data Term' where
    var       : (x : Nat) {i : Size} {j : Size< i} (args : List (Arg (Term' {j}))) → Term' {i}
    con       : (c : Name) (args : List (Arg Term')) → Term'
    def       : (f : Name) (args : List (Arg Term')) → Term'
    lam       : (v : Visibility) (t : Abs Term') → Term'
    pat-lam   : (cs : List Clause') (args : List (Arg Term')) → Term'
    pi        : (a : Arg Type') (b : Abs Type') → Term'
    agda-sort : (s : Sort') → Term'
    lit       : (l : Literal) → Term'
    meta      : (x : Meta) → List (Arg Term') → Term'
    unknown   : Term'

  data Sort' where
    set     : (t : Term') → Sort'
    lit     : (n : Nat) → Sort'
    unknown : Sort'

  data Clause' where
    clause        : (ps : List (Arg Pattern)) (t : Term') → Clause'
    absurd-clause : (ps : List (Arg Pattern)) → Clause'


  private
    Reordering = List (Nat × Nat)

    weakenReordering : Reordering → Reordering
    weakenReordering [] = []
    weakenReordering ((x , n) ∷ xs) = (suc x , suc n) ∷ weakenReordering xs

    replaceVar : Nat → Reordering → Nat → Nat
    replaceVar d [] x = x
    replaceVar d ((x-d , n-d) ∷ xns) x with x == x-d + d
    ... | yes _ = n-d + d
    ... | no _ = replaceVar d xns x

    reverse& : ∀ {a} {A : Set a} → List A → ∀ {b} {B : Set b} → (List A → B) → B
    reverse& xs f = go xs [] f where
      go : ∀ {a} {A : Set a} → List A → List A → ∀ {b} {B : Set b} → (List A → B) → B
      go [] xs f = f xs
      go (m ∷ ms) xs f = go ms (m ∷ xs) f

    {-# TERMINATING #-}
    reorderVars : Reordering → Term → Term
    reorderVars os t = reverse& os (λ os → go 0 os t) where
      go : Nat → Reordering → Term → Term
      go d xns (var x args) = var (replaceVar d xns x) (fmap (go d xns) <$> args)
      go d xns (con c args) = con c ((fmap ∘ fmap) (go d xns) args)
      go d xns (def f args) = def f (fmap (go d xns) <$> args)
      go d xns (lam v t) = lam v (go (suc d) xns <$> t)
      go d xns (pat-lam cs args) = pat-lam (fmap (reorderVarsInClause d xns) cs) ((fmap ∘ fmap) (go d xns) args) where
        reorderVarsInClause : Nat → Reordering → Clause → Clause -- TODO reorder patterns?
        reorderVarsInClause d xns (clause ps t) = clause ps (go d xns t)
        reorderVarsInClause d xns (absurd-clause ps) = absurd-clause ps
      go d xns (pi a b) = pi (go d xns <$> a) (go (suc d) xns <$> b)
      go d xns (agda-sort (set t)) = agda-sort (set (go d xns t))
      go d xns (agda-sort (lit n)) = agda-sort (lit n)
      go d xns (agda-sort unknown) = agda-sort unknown
      go d xns (lit l) = lit l
      go d xns (meta x args) = meta x $ (fmap ∘ fmap) (go d xns) args
      go d xns unknown = unknown

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
      Γ[w/L]×indexes[Γ] = go 0 0 [] Γ where
        go : Nat → Nat → Reordering → List (Arg Type) → List (Arg Type × Nat)
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
          if γ≢l≡r && γ'≠γ'[w'/L'][reordered] then
            (γ'[w'/L'][reordered] , i) ∷ go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenReordering osⱼ) γs
          else
            go (suc i) j osⱼ γs

      Γ[w/L] : List (Arg Type)
      Γ[w/L] = fst <$> Γ[w/L]×indexes[Γ]

      indexes[Γ] : List Nat
      indexes[Γ] = snd <$> Γ[w/L]×indexes[Γ]

      length& : ∀ {a} {A : Set a} → List A → ∀ {b} {B : Set b} → (Nat → B) → B
      length& {A = A} xs {B = B} f = helper 0 xs where
        helper : Nat → List A → B
        helper l [] = f l
        helper l (x ∷ xs) = helper (suc l) xs

      {-
         <---------------------- helper-type--------------------- -->
               <---- Γ[w/L] ----->   <------ Γ[R/L] ------->
         w w≡R γ₀ γ₁ ... γᵢ ... γₙ ( γ'₀ γ'₁ ... γ'ᵢ ... γ'ₙ ) 𝐺[w/L]
         n = ∣Γᴸ∣ - 1 = length Γ[w/L] - 1
      -}
      Γ[R/L] : List (Arg Type)
      Γ[R/L] = length& Γ[w/L] (go 0 Γ[w/L]) where
        go : Nat → List (Arg Type) → Nat → List (Arg Type)
        go _ [] _ = []
        go i (γ ∷ γs) ∣Γᴸ∣ =
          -- γ is the index[γ]ᵗʰ element of Γ[w/L]
          let n = ∣Γᴸ∣ - 1
              γ' = weakenFrom i ∣Γᴸ∣ γ
              w' = var₀ (i + n + 2)
              R' = weaken (2 + ∣Γᴸ∣ + i) R
              γ'[R'/w'] = γ' r[ R' / w' ]
          in
            γ'[R'/w'] ∷ go (suc i) γs ∣Γᴸ∣

      {-
         Γ             Γ[w/L]   Γ[R/L]
         0 ... n w w≡R 0 ... m (0 ... m → 𝐺[R/L]) → 𝐺[w/L]
      -}
      𝐺[R/L] : Type
      𝐺[R/L] = length& Γ[w/L]×indexes[Γ] λ ∣Γᴸ∣ →
        let os = go ∣Γᴸ∣ 0 indexes[Γ] []
            𝐺' = weaken (2 * ∣Γᴸ∣ + 2) (𝐺 r[ R / L ])
        in
          reorderVars os 𝐺'
        where

        go : Nat → Nat → List Nat → Reordering → Reordering
        go _ _ [] ns = ns
        go ∣Γᴸ∣ j (i ∷ is) ns = go ∣Γᴸ∣ (suc j) is $ (2 * ∣Γᴸ∣ + 2 + (length Γ - 1) - i , (∣Γᴸ∣ - 1) - j) ∷ ns

      𝐺[w/L] : Type
      𝐺[w/L] = length& Γ[w/L]×indexes[Γ] go where
        go : Nat → Type
        go ∣Γᴸ∣ =
          let os = os' 0 indexes[Γ] []
              𝐺' = (weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / weaken (3 + ∣Γᴸ∣) L ]
          in
            reorderVars os 𝐺'
          where

          os' : Nat → List Nat → Reordering → Reordering
          os' _ [] ns = ns
          os' j (i ∷ is) ns = os' (suc j) is $ (1 + ∣Γᴸ∣ + 2 + (length Γ - 1) - i , 1 + (∣Γᴸ∣ - 1) - j) ∷ ns

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
      typeError ( strErr "reright-debug"          ∷
                  strErr "\nl≡r:"                 ∷ termErr (` (Request.l≡r q))      ∷
                  strErr "\nA:"                   ∷ termErr (` A)                    ∷
                  strErr "\nL:"                   ∷ termErr (` L)                    ∷
                  strErr "\nR:"                   ∷ termErr (` R)                    ∷
                  strErr "\nΓ:"                   ∷ termErr (` Γ)                    ∷
                  strErr "\nlength Γ:"            ∷ termErr (` (length Γ))           ∷
                  strErr "\n𝐺:"                   ∷ termErr (` 𝐺)                   ∷
                  strErr "\nΓ[w/L]×indexes[Γ]:"   ∷ termErr (` Γ[w/L]×indexes[Γ])    ∷
                  strErr "\nΓ[w/L]:"              ∷ termErr (` Γ[w/L])               ∷
                  strErr "\nindexes[Γ]:"          ∷ termErr (` indexes[Γ])           ∷
                  strErr "\nΓ[R/L]:"              ∷ termErr (` Γ[R/L])               ∷
                  strErr "\n𝐺[R/L]:"              ∷ termErr (` 𝐺[R/L])               ∷
                  strErr "\n𝐺[w/L]:"              ∷ termErr (` 𝐺[w/L])               ∷
                  strErr "\nw:"                   ∷ termErr (` w)                    ∷
                  strErr "\nw≡R:"                 ∷ termErr (` w≡R)                  ∷
                  strErr "helper-type:"           ∷ termErr helper-type              ∷
                  strErr "helper-patterns:"       ∷ termErr (` helper-patterns)      ∷
                  strErr "helper-term:"           ∷ termErr (` helper-term)          ∷
                  strErr "helper-call-args:"      ∷ termErr (` helper-call-args)     ∷
                  [] )

    reright : Term → Tactic
    reright l≡r hole =
      q ← getRequest l≡r hole -|
      n ← freshName "reright" -|
      let open Request q in
      catchTC (typeError [ strErr "error defining helper function" ]) (define (vArg n) helper-type [ clause helper-patterns helper-term ]) ~|
      unify hole (def n helper-call-args)

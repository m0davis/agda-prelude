module Tactic.Reflection.Reright where

open import Prelude

open import Tactic.Reflection
open import Tactic.Reflection.Match
open import Tactic.Reflection.Replace
open import Tactic.Reflection.Quote

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

  -- cps-style: this forces normalisation up to constructors for a List and makes stuff go faster (TODO feels hacky)
  reverse& : ∀ {a} {A : Set a} → List A → ∀ {b} {B : Set b} → (List A → B) → B
  reverse& xs f = go xs [] f where
    go : ∀ {a} {A : Set a} → List A → List A → ∀ {b} {B : Set b} → (List A → B) → B
    go [] xs f = f xs
    go (m ∷ ms) xs f = go ms (m ∷ xs) f

  reverse-Nat& : List Nat → ∀ {b} {B : Set b} → (List Nat → B) → B
  reverse-Nat& xs f = go xs [] f where
    go : List Nat → List Nat → ∀ {b} {B : Set b} → (List Nat → B) → B
    go [] xs f = f xs
    go (zero ∷ ms) xs f = go ms (zero ∷ xs) f
    go ((suc m) ∷ ms) xs f = go ms ((suc m) ∷ xs) f

  length& : ∀ {a} {A : Set a} → List A → ∀ {b} {B : Set b} → (Nat → B) → B
  length& {A = A} xs {B = B} f = helper 0 xs where
    helper : Nat → List A → B
    helper l [] = f l
    helper l (x ∷ xs) = helper (suc l) xs

  id-Nat'& : ∀ {b} {B : Set b} → Nat → (Nat → B) → B
  id-Nat'& = helper 0 where
    helper : ∀ {b} {B : Set b} → Nat → Nat → (Nat → B) → B
    helper n' zero f = f n'
    helper n' (suc n) f = helper (suc n') n f

  id-Reordering'& : Reordering → ∀ {b} {B : Set b} → (Reordering → B) → B
  id-Reordering'& = helper [] where
    helper : Reordering → Reordering → ∀ {b} {B : Set b} → (Reordering → B) → B
    helper os' [] f = f os'
    helper os' ((o , s) ∷ oss) f = id-Nat'& o λ o' → id-Nat'& s λ s' → helper ((o' , s') ∷ os') oss f

  id-Nat& : ∀ {b} {B : Set b} → Nat → (Nat → B) → B
  id-Nat& zero f = f zero
  id-Nat& (suc n) f = f (suc n)

  id-Reordering& : Reordering → ∀ {b} {B : Set b} → (Reordering → B) → B
  id-Reordering& = helper [] where
    helper : Reordering → Reordering → ∀ {b} {B : Set b} → (Reordering → B) → B
    helper os' [] f = f os'
    helper os' ((zero , zero) ∷ oss) f = helper ((zero , zero) ∷ os') oss f
    helper os' ((zero , suc s) ∷ oss) f = helper ((zero , suc s) ∷ os') oss f
    helper os' ((suc o , zero) ∷ oss) f = helper ((suc o , zero) ∷ os') oss f
    helper os' ((suc o , suc s) ∷ oss) f = helper ((suc o , suc s) ∷ os') oss f

  CPS : Set → Set₁
  CPS X = X → ∀ {B : Set} → (X → B) → B

  mutual
    id-Term& : CPS Term
    id-Term& (var x args) f = id-ListArgTerm& args λ args → f (var x args)
    id-Term& (con c args) f = id-ListArgTerm& args λ args → f (con c args)
    id-Term& (def f args) f₁ = id-ListArgTerm& args λ args → f₁ (def f args)
    id-Term& (lam v t) f = id-AbsTerm& t λ t → f (lam v t)
    id-Term& (pat-lam cs args) f = id-ListClause& cs λ cs → id-ListArgTerm& args λ args → f (pat-lam cs args)
    id-Term& (pi a b) f = id-ArgTerm& a λ a → id-AbsTerm& b λ b → f (pi a b)
    id-Term& (agda-sort s) f = id-Sort& s λ s → f (agda-sort s)
    id-Term& (lit l) f = f (lit l)
    id-Term& (meta x args) f = id-ListArgTerm& args λ args → f (meta x args)
    id-Term& unknown f = f unknown

    id-ArgTerm& : CPS (Arg Term)
    id-ArgTerm& (arg i x) f = id-Term& x λ x → f (arg i x)

    id-AbsTerm& : CPS (Abs Term)
    id-AbsTerm& (abs s x) f = id-Term& x λ x → f (abs s x)

    id-Clause& : CPS Clause
    id-Clause& (clause ps t) f = id-Term& t λ t → f (clause ps t)
    id-Clause& (absurd-clause ps) f = f (absurd-clause ps)

    id-ListClause& : CPS (List Clause)
    id-ListClause& [] f = f []
    id-ListClause& (x ∷ xs) f = id-Clause& x λ x → id-ListClause& xs λ xs → f (x ∷ xs)

    id-Sort& : CPS Sort
    id-Sort& (set t) f = id-Term& t λ t → f (set t)
    id-Sort& (lit n) f = f (lit n)
    id-Sort& unknown f = f unknown

    id-ListArgTerm& : CPS (List (Arg Term))
    id-ListArgTerm& [] f = f []
    id-ListArgTerm& (x ∷ xs) f = id-ArgTerm& x λ x → id-ListArgTerm& xs λ xs → f (x ∷ xs)

  id-ListArgTermNat& : CPS (List (Arg Term × Nat))
  id-ListArgTermNat& [] f = f []
  id-ListArgTermNat& ((x , n) ∷ xs) f = id-ArgTerm& x λ x → id-ListArgTermNat& xs λ xs → f ((x , n) ∷ xs)

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

  {-
                         <------- helper-type--------- ... -->
     <------- Γ ------->        <------ Γ[w/L] ------>
     γ₀ γ₁ ... γᵢ ... γₙ w w≡R γ'₀ γ'₁ ... γ'ⱼ ... γ'ₘ

     γ' = γ'ⱼ
  -}
  {-
                           <------- helper-type--------- ... -->
     <------- Γ --------->       <------ Γ[w/L] ------>
     γₙ γₙ₋₁ ... γᵢ ... γ₀ w w≡R γ'₀ γ'₁ ... γ'ⱼ ... γ'ₘ

     γ' = γ'ⱼ




                         <-------- helper-type---------- ... -->
     <------- Γ ------->        <------- Γ[w/L] ------->
     γ₀ γ₁ ... γᵢ ... γₙ w w≡R γ'ₘ γ'ₘ₋₁ ... γ'ⱼ ... γ'₀

     γ' = γ'ⱼ
  -}
  Γ[w/L]×indexes[Γ]&  : (l≡r : Term) → (L : Type) → (Γ : List (Arg Type)) (∣Γ∣ : Nat) → ∀ {B : Set} → (List (Arg Type × Nat) → B) → B
  Γ[w/L]×indexes[Γ]& l≡r L Γ ∣Γ∣ f =
    go 0 0 [] Γ [] f
    where
    go : Nat → Nat → Reordering → List (Arg Type) → List (Arg Type × Nat) → ∀ {B : Set} → (List (Arg Type × Nat) → B) → B
    go _ _ _   []       cc f = f cc
    go i j osⱼ (γ ∷ γs) cc f =
      let n = ∣Γ∣ - 1
          γ≢l≡r = isNo $ var₀ (n - i) == l≡r
          L' = weaken (2 + j) L
          γ' = weaken ((n - i) + 3 + j) γ
          w' = var₀ (suc j)
          γ'[w'/L'] = {-id-ArgTerm& γ' λ γ' → id-Term& L' λ L' →-} γ' r[ w' / L' ]
          --γ'[w'/L'] = maybe γ' id γ'[w'/L']?
          γ'[w'/L'][reordered] = reorderVars osⱼ <$> γ'[w'/L']
      in
      if γ≢l≡r then
        --id-ArgTerm& γ'[w'/L'][reordered] (λ γ'[w'/L'][reordered] →
        (let γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
        in
        if γ'≠γ'[w'/L'][reordered] then
          go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenReordering osⱼ) γs ((γ'[w'/L'][reordered] , i) ∷ cc) f
        else
          go (suc i) j osⱼ γs cc f
        )
        --)
      else
        go (suc i) j osⱼ γs cc f

  ∣Γᴸ|& : List (Arg Type × Nat) → ∀ {b} {B : Set b} → (Nat → B) → B
  ∣Γᴸ|& Γ[w/L]×indexes[Γ] f = length& Γ[w/L]×indexes[Γ] f

  Γ[w/L]& : List (Arg Type × Nat) → ∀ {b} {B : Set b} → (List (Arg Type) → B) → B
  Γ[w/L]& Γ[w/L]×indexes[Γ] f = f (fst <$> Γ[w/L]×indexes[Γ])

  indexes[Γ]& : List (Arg Type × Nat) → ∀ {b} {B : Set b} → (List Nat → B) → B
  indexes[Γ]& Γ[w/L]×indexes[Γ] f = f (snd <$> Γ[w/L]×indexes[Γ])

  {-
     <---------------------- helper-type--------------------- -->
           <---- Γ[w/L] ----->   <------ Γ[R/L] ------->
     w w≡R γ₀ γ₁ ... γᵢ ... γₙ ( γ'₀ γ'₁ ... γ'ᵢ ... γ'ₙ ) 𝐺[w/L]
     n = ∣Γᴸ∣ - 1 = length Γ[w/L] - 1
  -}
  Γ[R/L]& : (R : Type) → (Γ[w/L] : List (Arg Type)) (∣Γᴸ| : Nat) → ∀ {b} {B : Set b} → (List (Arg Type) → B) → B
  Γ[R/L]& R Γ[w/L] ∣Γᴸ∣ = go 0 Γ[w/L] [] where
    go : Nat → List (Arg Type) → List (Arg Type) → ∀ {b} {B : Set b} → (List (Arg Type) → B) → B
    go _ [] cc f = f cc
    go i (γ ∷ γs) cc f =
      -- γ is the index[γ]ᵗʰ element of Γ[w/L]
      let n  = ∣Γᴸ∣ - 1
          γ' = weakenFrom (n - i) ∣Γᴸ∣ γ
          w' = var₀ (2 * n - i + 2)
          R' = weaken (2 + ∣Γᴸ∣ + (n - i)) R
          γ'[R'/w'] = γ' r[ R' / w' ]
      in
        go (suc i) γs (γ'[R'/w'] ∷ cc) f

  {-
     Γ             Γ[w/L]   Γ[R/L]
     0 ... n w w≡R 0 ... m (0 ... m → 𝐺[R/L]) → 𝐺[w/L]
  -}
  𝐺[R/L]-Reordering& : (∣Γ∣ : Nat) → (indexes[Γ] : List Nat) (∣Γᴸ∣ : Nat) →
                       ∀ {b} {B : Set b} → (Reordering → B) → B
  𝐺[R/L]-Reordering& ∣Γ∣ indexes[Γ] ∣Γᴸ∣ =
    go 0 indexes[Γ] []
    where
    go : Nat → List Nat → Reordering → ∀ {b} → {B : Set b} → (Reordering → B) → B
    go _ []       cc f = f cc
    go j (i ∷ is) cc f = go (suc j) is ((2 * ∣Γᴸ∣ + 2 + (∣Γ∣ - 1) - i , j) ∷ cc) f

  𝐺[R/L]& : (𝐺 : Type) (R : Type) (L : Type) (os : Reordering) (∣Γᴸ∣ : Nat) →
            ∀ {b} {B : Set b} → (Type → B) → B
  𝐺[R/L]& 𝐺 R L os ∣Γᴸ∣ f =
    f (reorderVars os (weaken (2 * ∣Γᴸ∣ + 2) (𝐺 r[ R / L ])))

  𝐺[w/L]-Reordering& : (∣Γ∣ : Nat) → (indexes[Γ] : List Nat) (∣Γᴸ∣ : Nat) →
                       ∀ {b} {B : Set b} → (Reordering → B) → B
  𝐺[w/L]-Reordering& ∣Γ∣ indexes[Γ] ∣Γᴸ∣ =
    go 0 indexes[Γ] []
    where
    go : Nat → List Nat → Reordering → ∀ {b} → {B : Set b} → (Reordering → B) → B
    go _ []       cc f = f cc
    go j (i ∷ is) cc f = go (suc j) is ((1 + ∣Γᴸ∣ + 2 + (∣Γ∣ - 1) - i , 1 + j) ∷ cc) f

  𝐺[w/L]& : (𝐺 : Type) (L : Type) (os : Reordering) (∣Γᴸ∣ : Nat) →
            ∀ {b} {B : Set b} → (Type → B) → B
  𝐺[w/L]& 𝐺 L os ∣Γᴸ∣ f =
    f (reorderVars os (weaken (3 + ∣Γᴸ∣) 𝐺 r[ var₀ (2 + ∣Γᴸ∣) / weaken (3 + ∣Γᴸ∣) L ]))

  w& : (A : Type) → ∀ {b} {B : Set b} → (Arg Type → B) → B
  w& A f = f (hArg A)

  w≡R& : (R : Type) → ∀ {b} {B : Set b} → (Arg Type → B) → B
  w≡R& R f = f (vArg (def₂ (quote _≡_) (var₀ 0) (weaken 1 R)))

  record Request : Set where
    field
      l≡r : Term
      A : Type
      L : Term
      R : Term
      Γ : List (Arg Type)
      𝐺 : Type

  getRequest : Term → Term → TC Request
  getRequest l≡r hole = do
    L≡R ← inferType l≡r -|
    L≡R-matched ← maybe (typeError (strErr "not an equality" ∷ termErr l≡r ∷ termErr L≡R ∷ [])) pure $
      match 3 (def (quote _≡_) (hArg unknown ∷ (hArg (var₀ 0)) ∷ (vArg (var₀ 1)) ∷ (vArg (var₀ 2)) ∷ [])) L≡R -|
    𝐺 ← inferFunRange hole -|
    Γ ← getContext -|
    reverse& Γ λ Γ →
    case L≡R-matched of λ { (A ∷ L ∷ R ∷ []) →
      pure $ record { l≡r = l≡r ; A = A ; L = L ; R = R ; Γ = Γ ; 𝐺 = 𝐺 } }

  record Response : Set where
    field
      l≡r : Term
      w : Arg Type
      w≡R : Arg Type
      Γ[w/L] Γ[R/L] : List (Arg Type)
      𝐺[R/L] 𝐺[w/L] : Type
      Γ[w/L]×indexes[Γ] : List (Arg Type × Nat)
      ∣Γ∣ : Nat

    helper-type : Type
    helper-type = telPi ((w ∷ w≡R ∷ reverse Γ[w/L]) ++ [ vArg (telPi Γ[R/L] 𝐺[R/L]) ]) 𝐺[w/L]

    helper-patterns : List (Arg Pattern)
    helper-patterns = (hArg dot ∷ vArg (con₀ (quote refl)) ∷ telePat Γ[w/L]) ++ [ vArg (var "_") ]

    helper-term : Term
    helper-term = var 0 (weaken 1 (teleArgs Γ[w/L]))

    helper-call-args : List (Arg Term)
    helper-call-args = hArg unknown ∷ vArg l≡r ∷ helper-call-args' where
      helper-call-args' : List (Arg Term)
      helper-call-args' = (λ { (γ[w/L] , index[γ]) → var₀ (∣Γ∣ - index[γ] - 1) <$ γ[w/L] }) <$> reverse Γ[w/L]×indexes[Γ]

  getResponse : Request → Response
  getResponse q =
    let open Request q in
      length& Γ λ ∣Γ∣ →
      Γ[w/L]×indexes[Γ]& l≡r L Γ ∣Γ∣ λ Γ[w/L]×indexes[Γ] →
      id-ListArgTermNat& Γ[w/L]×indexes[Γ] λ Γ[w/L]×indexes[Γ] →
      ∣Γᴸ|& Γ[w/L]×indexes[Γ] λ ∣Γᴸ∣ →
      indexes[Γ]& Γ[w/L]×indexes[Γ] λ indexes[Γ] →
      Γ[w/L]& Γ[w/L]×indexes[Γ] λ Γ[w/L] →
      Γ[R/L]& R Γ[w/L] ∣Γᴸ∣ λ Γ[R/L] →
      𝐺[R/L]-Reordering& ∣Γ∣ indexes[Γ] ∣Γᴸ∣ λ 𝐺[R/L]-Reordering →
      𝐺[R/L]& 𝐺 R L 𝐺[R/L]-Reordering ∣Γᴸ∣ λ 𝐺[R/L] →
      𝐺[w/L]-Reordering& ∣Γ∣ indexes[Γ] ∣Γᴸ∣ λ 𝐺[w/L]-Reordering →
      𝐺[w/L]& 𝐺 L 𝐺[w/L]-Reordering ∣Γᴸ∣ λ 𝐺[w/L] →
      record
        { l≡r = l≡r
        ; w = w& A id
        ; w≡R = w≡R& R id
        ; Γ[w/L] = Γ[w/L]
        ; Γ[R/L] = Γ[R/L]
        ; 𝐺[R/L] = 𝐺[R/L]
        ; 𝐺[w/L] = 𝐺[w/L]
        ; Γ[w/L]×indexes[Γ] = Γ[w/L]×indexes[Γ]
        ; ∣Γ∣ = ∣Γ∣
        }

macro
  reright : Term → Tactic
  reright l≡r hole =
    q ← getRequest l≡r hole -|
    n ← freshName "reright" -|
    let open Response (getResponse q) in
    catchTC (typeError [ strErr "error defining helper function" ]) (define (vArg n) helper-type [ clause helper-patterns helper-term ]) ~|
    unify hole (def n helper-call-args)

  reright-debug : Term → Tactic
  reright-debug l≡r hole =
    q ← getRequest l≡r hole -|
    let open Response (getResponse q) in
    ∣Γᴸ|& Γ[w/L]×indexes[Γ] λ ∣Γᴸ∣ →
    typeError ( strErr "reright-debug"            ∷
                strErr "Γ:"                       ∷ termErr (` (length (Request.Γ q)))    ∷
                strErr "l≡r:"                     ∷ termErr (` (Response.l≡r (getResponse q)))    ∷
                strErr "∣Γ∣:"                     ∷ termErr (` ∣Γ∣)                               ∷
                strErr "∣Γᴸ∣:"                    ∷ termErr (` ∣Γᴸ∣)                              ∷
              --strErr "Γ:"                       ∷ termErr (` (Request.Γ q))                     ∷
              --strErr "Γ[w/L]×indexes[Γ]:"       ∷ termErr (` Γ[w/L]×indexes[Γ])                 ∷
                strErr "\n𝐺[w/L]:"                ∷ termErr (` 𝐺[w/L])                           ∷
              --strErr "helper-type:"             ∷ termErr helper-type                           ∷
              --strErr "helper-type:"             ∷ termErr (` helper-type)                       ∷
              --strErr "helper-patterns:"         ∷ termErr (` helper-patterns)                   ∷
              --strErr "helper-term:"             ∷ termErr (` helper-term)                       ∷
              --strErr "helper-call-args:"        ∷ termErr (` helper-call-args)                  ∷
                [] )

-- -- -- -- macro
-- -- -- --   reright-debug : Term → Tactic
-- -- -- --   reright-debug l≡r hole =
-- -- -- --     q ← getRequest l≡r hole -|
-- -- -- --     let open Request q in
-- -- -- --     typeError ( strErr "reright-debug"          ∷
-- -- -- --                 strErr "\nl≡r:"                 ∷ termErr (` (Request.l≡r q))      ∷
-- -- -- --                 strErr "\nA:"                   ∷ termErr (` A)                    ∷
-- -- -- --                 strErr "\nL:"                   ∷ termErr (` L)                    ∷
-- -- -- --                 strErr "\nR:"                   ∷ termErr (` R)                    ∷
-- -- -- --                 strErr "\nΓ:"                   ∷ termErr (` Γ)                    ∷
-- -- -- --                 strErr "\nlength Γ:"            ∷ termErr (` (length Γ))           ∷
-- -- -- --                 strErr "\n𝐺:"                   ∷ termErr (` 𝐺)                   ∷
-- -- -- --                 strErr "\nΓ[w/L]×indexes[Γ]:"   ∷ termErr (` Γ[w/L]×indexes[Γ])    ∷
-- -- -- --                 strErr "\nΓ[w/L]:"              ∷ termErr (` Γ[w/L])               ∷
-- -- -- --                 strErr "\nindexes[Γ]:"          ∷ termErr (` indexes[Γ])           ∷
-- -- -- --                 strErr "\nΓ[R/L]:"              ∷ termErr (` Γ[R/L])               ∷
-- -- -- --                 strErr "\n𝐺[R/L]:"              ∷ termErr (` 𝐺[R/L])               ∷
-- -- -- --                 strErr "\nRE𝐺[R/L]:"            ∷ termErr (` reorderings-𝐺[R/L])   ∷
-- -- -- --                 strErr "\n𝐺[w/L]:"              ∷ termErr (` 𝐺[w/L])               ∷
-- -- -- --                 strErr "\nw:"                   ∷ termErr (` w)                    ∷
-- -- -- --                 strErr "\nw≡R:"                 ∷ termErr (` w≡R)                  ∷
-- -- -- --                 strErr "helper-type:"           ∷ termErr helper-type              ∷
-- -- -- --                 strErr "helper-patterns:"       ∷ termErr (` helper-patterns)      ∷
-- -- -- --                 strErr "helper-term:"           ∷ termErr (` helper-term)          ∷
-- -- -- --                 strErr "helper-call-args:"      ∷ termErr (` helper-call-args)     ∷
-- -- -- --                 [] )

-- -- -- --   reright-debug-0 : Term → Tactic
-- -- -- --   reright-debug-0 l≡r hole =
-- -- -- --     q ← getRequest l≡r hole -|
-- -- -- --     let open Request q in
-- -- -- --     typeError ( strErr "reright-debug"          ∷
-- -- -- --                 strErr "\nl≡r:"                 ∷ termErr (` (Request.l≡r q))      ∷
-- -- -- --                 strErr "\nA:"                   ∷ termErr (` A)                    ∷
-- -- -- --                 strErr "\nL:"                   ∷ termErr (` L)                    ∷
-- -- -- --                 strErr "\nR:"                   ∷ termErr (` R)                    ∷
-- -- -- --                 strErr "\nΓ:"                   ∷ termErr (` Γ)                    ∷
-- -- -- --                 strErr "\nlength Γ:"            ∷ termErr (` (length Γ))           ∷
-- -- -- --                 strErr "\n𝐺:"                   ∷ termErr (` 𝐺)                   ∷
-- -- -- --                 [] )

-- -- -- --   reright-debug-1 : Term → Tactic
-- -- -- --   reright-debug-1 l≡r hole =
-- -- -- --     q ← getRequest l≡r hole -|
-- -- -- --     let open Request q in
-- -- -- --     typeError ( strErr "reright-debug"          ∷
-- -- -- --                 strErr "\nΓ[w/L]×indexes[Γ]:"   ∷ termErr (` Γ[w/L]×indexes[Γ])    ∷
-- -- -- --                 [] )

-- -- -- --   reright-debug-i : Term → Tactic
-- -- -- --   reright-debug-i l≡r hole =
-- -- -- --     q ← getRequest l≡r hole -|
-- -- -- --     let open Request q in
-- -- -- --     typeError ( strErr "reright-debug"          ∷
-- -- -- --                 strErr "\nl≡r:"                 ∷ termErr (` (Request.l≡r q))      ∷
-- -- -- --                 strErr "\nindexes[Γ]:"          ∷ termErr (` indexes[Γ])           ∷
-- -- -- --                 [] )

-- -- -- --   reright-debug-2 : Term → Tactic
-- -- -- --   reright-debug-2 l≡r hole =
-- -- -- --     q ← getRequest l≡r hole -|
-- -- -- --     let open Request q in
-- -- -- --     typeError ( strErr "reright-debug"          ∷
-- -- -- --                 strErr "\nΓ[R/L]:"              ∷ termErr (` Γ[R/L])               ∷
-- -- -- --                 [] )

-- -- -- --   reright-debug-3 : Term → Tactic
-- -- -- --   reright-debug-3 l≡r hole =
-- -- -- --     q ← getRequest l≡r hole -|
-- -- -- --     let open Request q in
-- -- -- --     typeError ( strErr "reright-debug"          ∷
-- -- -- --                 strErr "\n𝐺[R/L]:"              ∷ termErr (` 𝐺[R/L])               ∷
-- -- -- --                 [] )

-- -- -- --   reright-debug-4 : Term → Tactic
-- -- -- --   reright-debug-4 l≡r hole =
-- -- -- --     q ← getRequest l≡r hole -|
-- -- -- --     let open Request q in
-- -- -- --     typeError ( strErr "reright-debug"          ∷
-- -- -- --                 strErr "\n𝐺[w/L]:"              ∷ termErr (` 𝐺[w/L])               ∷
-- -- -- --                 [] )

-- -- -- --   reright : Term → Tactic
-- -- -- --   reright l≡r hole =
-- -- -- --     q ← getRequest l≡r hole -|
-- -- -- --     n ← freshName "reright" -|
-- -- -- --     let open Request q in
-- -- -- --     catchTC (typeError [ strErr "error defining helper function" ]) (define (vArg n) helper-type [ clause helper-patterns helper-term ]) ~|
-- -- -- --     unify hole (def n helper-call-args)

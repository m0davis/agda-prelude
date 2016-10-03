module Tactic.Reflection.Reright-Performance-2 where
  module fast-vs-slow-something₂ where
    open import Prelude

    open import Tactic.Reflection
    open import Tactic.Reflection.Match
    open import Tactic.Reflection.Replace
    open import Tactic.Reflection.Quote

    record Request : Set where
      field
        l≡r : Term
        A : Type
        L R : Type
        Γ : List (Arg Type)
        𝐺 : Type

      something-fast  : List (Arg Type) × List (Arg Type)
      something-fast = go Γ where
        go : List (Arg Type) → List (Arg Type) × List (Arg Type)
        go [] = [] , []
        go (γ ∷ γs) = if (isNo $ γ == γ r[ var₀ 0 / var₀ 0 ]) then
                        (let goo = go γs in snd goo , (γ r[ var₀ 0 / var₀ 0 ] ∷ snd goo))
                      else
                        go γs

      something-slow  : List (Arg Type) × List (Arg Type)
      something-slow = ([] , go Γ) where
        go : List (Arg Type) → List (Arg Type)
        go [] = []
        go (γ ∷ γs) = if (isNo $ γ == γ r[ var₀ 0 / var₀ 0 ]) then
                        (let goo = go γs in γ r[ var₀ 0 / var₀ 0 ] ∷ goo)
                      else
                        go γs

      try-something : Type
      try-something = helper something-fast
        where
        helper : _ × List (Arg Type) → Type
        helper (_ , Γw) = let |L| = length (Γw) in 𝐺 r[ var₀ |L| / var₀ |L| ]

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
                    strErr "\ntry-something:"         ∷ termErr (` try-something)               ∷
                    [] )

    tester : ∀ {a} → {A : Set a} → {x y : A} →
             {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
             {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
             {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
             {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
             {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
             {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
             {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
             {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
             {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
             {g : Set a → Set a} →
             x ≡ y →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             (A → Set₁ → A → Set) →
             Set
    tester x≡y = reright-debug x≡y {!!}

--   module fast-vs-slow-something₁ where
--     open import Prelude

--     open import Tactic.Reflection
--     open import Tactic.Reflection.Match
--     open import Tactic.Reflection.Replace
--     open import Tactic.Reflection.Quote

--     record Request : Set where
--       field
--         l≡r : Term
--         A : Type
--         L R : Type
--         Γ : List (Arg Type)
--         𝐺 : Type

--       something-fast₆  : List (Arg Type) × List (Arg Type)
--       something-fast₆ = go Γ where
--         go : List (Arg Type) → List (Arg Type) × List (Arg Type)
--         go [] = [] , []
--         go (γ ∷ γs)
--          with (isNo $ γ == γ r[ var₀ 0 / L ])
--         ... | true = let goo = go γs in snd goo , (γ r[ var₀ 0 / L ] ∷ snd goo)
--         ... | false = go γs

--       something-slow₆  : List (Arg Type) × List (Arg Type)
--       something-slow₆ = ([] , go Γ) where
--         go : List (Arg Type) → List (Arg Type)
--         go [] = []
--         go (γ ∷ γs)
--          with (isNo $ γ == γ r[ var₀ 0 / L ])
--         ... | true = let goo = go γs in γ r[ var₀ 0 / L ] ∷ goo
--         ... | false = go γs

--       something-fast₇  : List (Arg Type) × List (Arg Type)
--       something-fast₇ = go Γ where
--         go : List (Arg Type) → List (Arg Type) × List (Arg Type)
--         go [] = [] , []
--         go (γ ∷ γs) = if (isNo $ γ == γ r[ var₀ 0 / var₀ 0 ]) then
--                         (let goo = go γs in snd goo , (γ r[ var₀ 0 / var₀ 0 ] ∷ snd goo))
--                       else
--                         go γs

--       something-slow₇  : List (Arg Type) × List (Arg Type)
--       something-slow₇ = ([] , go Γ) where
--         go : List (Arg Type) → List (Arg Type)
--         go [] = []
--         go (γ ∷ γs) = if (isNo $ γ == γ r[ var₀ 0 / var₀ 0 ]) then
--                         (let goo = go γs in γ r[ var₀ 0 / var₀ 0 ] ∷ goo)
--                       else
--                         go γs

--       no-cps-𝐺[w/L]₄ : Type
--       no-cps-𝐺[w/L]₄ = helper something-slow₇
--         where
--         helper : _ × List (Arg Type) → Type
--         helper (_ , Γw) =
--           let |L| = length (Γw)
--               𝐺' = (weaken (3 + |L|) 𝐺) r[ var₀ (2 + |L|) / weaken (3 + |L|) L ]
--           in
--             𝐺'

--     getRequest : Term → Term → TC Request
--     getRequest l≡r hole = do
--       L≡R ← inferType l≡r -|
--       L≡R-matched ← maybe (typeError (strErr "not an equality" ∷ termErr l≡r ∷ termErr L≡R ∷ [])) pure $
--         match 3 (def (quote _≡_) (hArg unknown ∷ (hArg (var₀ 0)) ∷ (vArg (var₀ 1)) ∷ (vArg (var₀ 2)) ∷ [])) L≡R -|
--       𝐺 ← inferFunRange hole -|
--       Γ ← getContext -|
--       case L≡R-matched of λ { (A ∷ L ∷ R ∷ []) →
--         pure $ record { l≡r = l≡r ; A = A ; L = L ; R = R ; Γ = reverse Γ ; 𝐺 = 𝐺 } }

--     macro
--       reright-debug : Term → Tactic
--       reright-debug l≡r hole =
--         q ← getRequest l≡r hole -|
--         let open Request q in
--         typeError ( strErr "reright-debug"     ∷
--                     strErr "\n𝐺[w/L]:"         ∷ termErr (`
--                       no-cps-𝐺[w/L]₄
--                       )               ∷
--                     [] )

--     tester : ∀ {a} → {A : Set a} → {x y : A} →
--              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
--              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
--              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
--              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
--              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
--              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
--              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
--              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
--              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
--              {g : Set a → Set a} →
--              x ≡ y →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              (A → Set₁ → A → Set) →
--              Set
--     tester x≡y = {!!} -- reright-debug x≡y {!!}

-- --   module fast-vs-slow-something₀ where
-- --     open import Prelude

-- --     open import Tactic.Reflection
-- --     open import Tactic.Reflection.Match
-- --     open import Tactic.Reflection.Replace
-- --     open import Tactic.Reflection.Quote

-- --     weakenOrder : List (Nat × Nat) → List (Nat × Nat)
-- --     weakenOrder [] = []
-- --     weakenOrder ((x , n) ∷ xs) = (suc x , suc n) ∷ weakenOrder xs

-- --     replaceVar : Nat → List (Nat × Nat) → Nat → Nat
-- --     replaceVar d [] x = x
-- --     replaceVar d ((x-d , n-d) ∷ xns) x with x == x-d + d
-- --     ... | yes _ = n-d + d
-- --     ... | no _ = replaceVar d xns x

-- --     reorderVars' : Nat → Nat → List (Nat × Nat) → Term → Term
-- --     reorderVars' 0 _ _ x = x
-- --     reorderVars' (suc n) d [] (var x args) = var x (fmap (reorderVars' n d []) <$> args)
-- --     reorderVars' (suc n) d ((x-d , n-d) ∷ xns) (var x args) with x == x-d + d
-- --     ... | yes _ = var (n-d + d) (fmap (reorderVars' n d xns) <$> args)
-- --     ... | no _ = reorderVars' (suc n) d xns (var x args)
-- --     reorderVars' (suc n) d xns (con c args) = con c ((fmap ∘ fmap) (reorderVars' n d xns) args)
-- --     reorderVars' (suc n) d xns (def f args) = def f (fmap (reorderVars' n d xns) <$> args)
-- --     reorderVars' (suc n) d xns (lam v t) = lam v (reorderVars' n (suc d) xns <$> t)
-- --     reorderVars' (suc n) d xns (pat-lam cs args) = pat-lam (fmap (reorderVars'InClause n d xns) cs) ((fmap ∘ fmap) (reorderVars' n d xns) args) where
-- --       reorderVars'InClause : Nat → Nat → List (Nat × Nat) → Clause → Clause -- TODO reorder patterns?
-- --       reorderVars'InClause n d xns (clause ps t) = (clause ps (reorderVars' n d xns t))
-- --       reorderVars'InClause n d xns (absurd-clause ps) = (absurd-clause ps)
-- --     reorderVars' (suc n) d xns (pi a b) = pi (reorderVars' n d xns <$> a) (reorderVars' n (suc d) xns <$> b)
-- --     reorderVars' (suc n) d xns (agda-sort (set t)) = agda-sort (set (reorderVars' n d xns t))
-- --     reorderVars' (suc n') d xns (agda-sort (lit n)) = agda-sort (lit n')
-- --     reorderVars' (suc n) d xns (agda-sort unknown) = agda-sort unknown
-- --     reorderVars' (suc n) d xns (lit l) = lit l
-- --     reorderVars' (suc n) d xns (meta x args) = meta x $ (fmap ∘ fmap) (reorderVars' n d xns) args
-- --     reorderVars' (suc n) d xns unknown = unknown

-- --     reorderVars : List (Nat × Nat) → Term → Term
-- --     reorderVars xs t = reorderVars' 99 0 xs t

-- --     record Request : Set where
-- --       field
-- --         l≡r : Term
-- --         A : Type
-- --         L R : Type
-- --         Γ : List (Arg Type)
-- --         𝐺 : Type

-- -- -- TODO: Using this first "something" makes it slow to evaluate ` 𝐺[w/L] ...

-- --       something-fast  : Nat × List (Arg Type × Nat)
-- --       something-fast = go 0 0 [] Γ where
-- --         go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → Nat × List (Arg Type × Nat)
-- --         go _ _ _ [] = 0 , []
-- --         go i j osⱼ (γ ∷ γs) with length Γ - 1
-- --         ... | n with weaken (2 + j) L
-- --         ... | L' with weaken ((n - i) + 3 + j) γ
-- --         ... | γ' with (let w' = var₀ (suc j)
-- --                        in let γ'[w'/L'] = γ' r[ w' / L' ]
-- --                        in reorderVars osⱼ <$> γ'[w'/L'])
-- --         ... | γ'[w'/L'][reordered] with (let γ≢l≡r = isNo $ var₀ (n - i) == l≡r
-- --                                          in let γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
-- --                                          in γ≢l≡r && γ'≠γ'[w'/L'][reordered])
-- --         ... | true = let foo = go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs in (suc (length (snd foo)) , (γ'[w'/L'][reordered] , i) ∷ snd foo)
-- --         ... | false = go (suc i) j (weakenOrder osⱼ) γs

-- --       something-fast₂  : List (Arg Type × Nat) × List (Arg Type × Nat)
-- --       something-fast₂ = go 0 0 [] Γ where
-- --         go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat) × List (Arg Type × Nat)
-- --         go _ _ _ [] = [] , []
-- --         go i j osⱼ (γ ∷ γs) with length Γ - 1
-- --         ... | n with weaken (2 + j) L
-- --         ... | L' with weaken ((n - i) + 3 + j) γ
-- --         ... | γ' with (let w' = var₀ (suc j)
-- --                        in let γ'[w'/L'] = γ' r[ w' / L' ]
-- --                        in reorderVars osⱼ <$> γ'[w'/L'])
-- --         ... | γ'[w'/L'][reordered] with (let γ≢l≡r = isNo $ var₀ (n - i) == l≡r
-- --                                          in let γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
-- --                                          in γ≢l≡r && γ'≠γ'[w'/L'][reordered])
-- --         ... | true = let foo = go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs in (snd foo , (γ'[w'/L'][reordered] , i) ∷ snd foo)
-- --         ... | false = go (suc i) j (weakenOrder osⱼ) γs

-- -- -- ... but this second "something" makes it slow. Why?
-- --       something-slow  : Nat × List (Arg Type × Nat)
-- --       something-slow = let asdf = go 0 0 [] Γ in (length asdf , asdf) where
-- --         go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat)
-- --         go _ _ _ [] = []
-- --         go i j osⱼ (γ ∷ γs) with length Γ - 1
-- --         ... | n with {-weaken (2 + j)-} L
-- --         ... | L' with {-weaken ((n - i) + 3 + j)-} γ
-- --         ... | γ' with (let w' = var₀ 0 -- (suc j)
-- --                        in let γ'[w'/L'] = γ' r[ w' / L ]
-- --                        in {-reorderVars osⱼ <$>-} γ'[w'/L'])
-- --         ... | γ'[w'/L'][reordered]
-- --         -- = let foo = go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs in (γ'[w'/L'][reordered] , i) ∷ foo
-- --          with (let γ≢l≡r = isNo $ var₀ (n - i) == l≡r
-- --                in let γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
-- --                in γ≢l≡r && γ'≠γ'[w'/L'][reordered])
-- --         ... | true = let foo = go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs in (γ'[w'/L'][reordered] , i) ∷ foo
-- --         ... | false = go (suc i) j (weakenOrder osⱼ) γs

-- --       something-slow₂  : Nat × List (Arg Type × Nat)
-- --       something-slow₂ = let asdf = go 0 0 [] Γ in (5 , asdf) where
-- --         go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat)
-- --         go _ _ _ [] = []
-- --         go i j osⱼ (γ ∷ γs) with length Γ - 1
-- --         ... | n with {-weaken (2 + j)-} L
-- --         ... | L' with {-weaken ((n - i) + 3 + j)-} γ
-- --         ... | γ' with (let w' = var₀ 0 -- (suc j)
-- --                        in let γ'[w'/L'] = γ' r[ w' / L ]
-- --                        in {-reorderVars osⱼ <$>-} γ'[w'/L'])
-- --         ... | γ'[w'/L'][reordered]
-- --         -- = let foo = go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs in (γ'[w'/L'][reordered] , i) ∷ foo
-- --          with (isNo $ γ' == γ' r[ var₀ 0 / L ])
-- --         {-
-- --          with (let γ≢l≡r = isNo $ var₀ (n - i) == l≡r
-- --                in let γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
-- --                in γ≢l≡r && γ'≠γ'[w'/L'][reordered])
-- --         -}
-- --         ... | true = let foo = go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs in (γ'[w'/L'][reordered] , i) ∷ foo
-- --         ... | false = go (suc i) j (weakenOrder osⱼ) γs

-- --       something-fast₃  : List (Arg Type × Nat) × List (Arg Type × Nat)
-- --       something-fast₃ = go 0 0 [] Γ where
-- --         go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat) × List (Arg Type × Nat)
-- --         go _ _ _ [] = [] , []
-- --         go i j osⱼ (γ ∷ γs) with length Γ - 1
-- --         ... | n with L
-- --         ... | L' with γ
-- --         ... | γ' with γ' r[ var₀ 0 / L' ]
-- --         ... | γ'[w'/L'][reordered]
-- --          with (isNo $ γ' == γ' r[ var₀ 0 / L ])
-- --         ... | true = let foo = go (suc i) (suc j) ((j + 3 + (length Γ - 1) - i , 0) ∷ weakenOrder osⱼ) γs in (snd foo , (γ'[w'/L'][reordered] , i) ∷ snd foo)
-- --         ... | false = go (suc i) j (weakenOrder osⱼ) γs

-- --       something-slow₃  : Nat × List (Arg Type × Nat)
-- --       something-slow₃ = let asdf = go 0 0 [] Γ in (5 , asdf) where
-- --         go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat)
-- --         go _ _ _ [] = []
-- --         go i j osⱼ (γ ∷ γs) with length Γ - 1
-- --         ... | n with L
-- --         ... | L' with γ
-- --         ... | γ' with γ' r[ var₀ 0 / L' ]
-- --         ... | γ'[w'/L'][reordered]
-- --          with (isNo $ γ' == γ' r[ var₀ 0 / L ])
-- --         ... | true = let foo = go (suc i) (suc j) ((j + 3 + (length Γ - 1) - i , 0) ∷ weakenOrder osⱼ) γs in (γ'[w'/L'][reordered] , i) ∷ foo
-- --         ... | false = go (suc i) j (weakenOrder osⱼ) γs

-- --       something-fast₄  : List (Arg Type × Nat) × List (Arg Type × Nat)
-- --       something-fast₄ = go 0 0 [] Γ where
-- --         go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat) × List (Arg Type × Nat)
-- --         go _ _ _ [] = [] , []
-- --         go i j osⱼ (γ ∷ γs)
-- --          with (isNo $ γ == γ r[ var₀ 0 / L ])
-- --         ... | true = let foo = go (suc i) (suc j) ((0 , 0) ∷ osⱼ) γs in (snd foo , (γ r[ var₀ 0 / L ] , i) ∷ snd foo)
-- --         ... | false = go (suc i) j (weakenOrder osⱼ) γs

-- --       something-slow₄  : Nat × List (Arg Type × Nat)
-- --       something-slow₄ = let asdf = go 0 0 [] Γ in (5 , asdf) where
-- --         go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat)
-- --         go _ _ _ [] = []
-- --         go i j osⱼ (γ ∷ γs)
-- --          with (isNo $ γ == γ r[ var₀ 0 / L ])
-- --         ... | true = let foo = go (suc i) (suc j) ((0 , 0) ∷ osⱼ) γs in (γ r[ var₀ 0 / L ] , i) ∷ foo
-- --         ... | false = go (suc i) j (weakenOrder osⱼ) γs

-- --       something-fast₅  : List (Arg Type × Nat) × List (Arg Type × Nat)
-- --       something-fast₅ = go Γ where
-- --         go : List (Arg Type) → List (Arg Type × Nat) × List (Arg Type × Nat)
-- --         go [] = [] , []
-- --         go (γ ∷ γs)
-- --          with (isNo $ γ == γ r[ var₀ 0 / L ])
-- --         ... | true = let foo = go γs in (snd foo , (γ r[ var₀ 0 / L ] , 0) ∷ snd foo)
-- --         ... | false = go γs

-- --       something-slow₅  : List (Arg Type × Nat) × List (Arg Type × Nat)
-- --       something-slow₅ = ([] , go Γ) where
-- --         go : List (Arg Type) → List (Arg Type × Nat)
-- --         go [] = []
-- --         go (γ ∷ γs)
-- --          with (isNo $ γ == γ r[ var₀ 0 / L ])
-- --         ... | true = let foo = go γs in (γ r[ var₀ 0 / L ] , 0) ∷ foo
-- --         ... | false = go γs

-- --       no-cps-𝐺[w/L]₃ : Type
-- --       no-cps-𝐺[w/L]₃ = helper something-fast₅
-- --         where
-- --         helper : _ × List (Arg Type × Nat) → Type
-- --         helper (_ , Γw) =
-- --           let |L| = length (fst <$> Γw)
-- --               os = go |L| 0 (snd <$> Γw) []
-- --               𝐺' = (weaken (3 + |L|) 𝐺) r[ var₀ (2 + |L|) / weaken (3 + |L|) L ]
-- --           in
-- --             {-reorderVars os-} 𝐺'
-- --           where
-- --           go : Nat → Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
-- --           go |L| _ [] ns = ns
-- --           go |L| j (i ∷ is) ns = go |L| (suc j) is $ (1 + |L| + 2 + (length Γ - 1) - i , 1 + (|L| - 1) - j) ∷ ns

-- --       something-fast₆  : List (Arg Type) × List (Arg Type)
-- --       something-fast₆ = go Γ where
-- --         go : List (Arg Type) → List (Arg Type) × List (Arg Type)
-- --         go [] = [] , []
-- --         go (γ ∷ γs)
-- --          with (isNo $ γ == γ r[ var₀ 0 / L ])
-- --         ... | true = let goo = go γs in snd goo , (γ r[ var₀ 0 / L ] ∷ snd goo)
-- --         ... | false = go γs

-- --       something-slow₆  : List (Arg Type) × List (Arg Type)
-- --       something-slow₆ = ([] , go Γ) where
-- --         go : List (Arg Type) → List (Arg Type)
-- --         go [] = []
-- --         go (γ ∷ γs)
-- --          with (isNo $ γ == γ r[ var₀ 0 / L ])
-- --         ... | true = let goo = go γs in γ r[ var₀ 0 / L ] ∷ goo
-- --         ... | false = go γs

-- --       no-cps-𝐺[w/L]₄ : Type
-- --       no-cps-𝐺[w/L]₄ = helper something-fast₆
-- --         where
-- --         helper : _ × List (Arg Type) → Type
-- --         helper (_ , Γw) =
-- --           let |L| = length (Γw)
-- --               𝐺' = (weaken (3 + |L|) 𝐺) r[ var₀ (2 + |L|) / weaken (3 + |L|) L ]
-- --           in
-- --             𝐺'

-- --       no-cps-𝐺[w/L]₂ : Type
-- --       no-cps-𝐺[w/L]₂ = helper something-slow₅
-- --         where
-- --         helper : _ × List (Arg Type × Nat) → Type
-- --         helper (_ , Γw) =
-- --           let |L| = length (fst <$> Γw)
-- --               os = go |L| 0 (snd <$> Γw) []
-- --               𝐺' = (weaken (3 + |L|) 𝐺) r[ var₀ (2 + |L|) / weaken (3 + |L|) L ]
-- --           in
-- --             reorderVars os 𝐺'
-- --           where
-- --           go : Nat → Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
-- --           go |L| _ [] ns = ns
-- --           go |L| j (i ∷ is) ns = go |L| (suc j) is $ (1 + |L| + 2 + (length Γ - 1) - i , 1 + (|L| - 1) - j) ∷ ns

-- --       no-cps-𝐺[w/L] : Type
-- --       no-cps-𝐺[w/L]
-- --        with something-fast₂
-- --       ... | (_ , Γw) =
-- --         let |L| = length (fst <$> Γw)
-- --             os = go |L| 0 (snd <$> Γw) []
-- --             𝐺' = (weaken (3 + |L|) 𝐺) r[ var₀ (2 + |L|) / weaken (3 + |L|) L ]
-- --         in
-- --           reorderVars os 𝐺'
-- --         where
-- --         go : Nat → Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
-- --         go |L| _ [] ns = ns
-- --         go |L| j (i ∷ is) ns = go |L| (suc j) is $ (1 + |L| + 2 + (length Γ - 1) - i , 1 + (|L| - 1) - j) ∷ ns

-- --     getRequest : Term → Term → TC Request
-- --     getRequest l≡r hole = do
-- --       L≡R ← inferType l≡r -|
-- --       L≡R-matched ← maybe (typeError (strErr "not an equality" ∷ termErr l≡r ∷ termErr L≡R ∷ [])) pure $
-- --         match 3 (def (quote _≡_) (hArg unknown ∷ (hArg (var₀ 0)) ∷ (vArg (var₀ 1)) ∷ (vArg (var₀ 2)) ∷ [])) L≡R -|
-- --       𝐺 ← inferFunRange hole -|
-- --       Γ ← getContext -|
-- --       case L≡R-matched of λ { (A ∷ L ∷ R ∷ []) →
-- --         pure $ record { l≡r = l≡r ; A = A ; L = L ; R = R ; Γ = reverse Γ ; 𝐺 = 𝐺 } }

-- --     macro
-- --       reright-debug : Term → Tactic
-- --       reright-debug l≡r hole =
-- --         q ← getRequest l≡r hole -|
-- --         let open Request q in
-- --         typeError ( strErr "reright-debug"     ∷
-- --                     strErr "\n𝐺[w/L]:"         ∷ termErr (`
-- --                       no-cps-𝐺[w/L]₄
-- --                       )               ∷
-- --                     [] )

-- --     tester : ∀ {a} → {A : Set a} → {x y : A} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {g : Set a → Set a} →
-- --              x ≡ y →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →

-- --              Set
-- --     tester x≡y = {!!} -- reright-debug x≡y {!!}

-- --   module big where
-- --     open import Prelude

-- --     open import Tactic.Reflection
-- --     open import Tactic.Reflection.Match
-- --     open import Tactic.Reflection.Replace
-- --     open import Tactic.Reflection.Quote

-- --     private
-- --       weakenOrder : List (Nat × Nat) → List (Nat × Nat)
-- --       weakenOrder [] = []
-- --       weakenOrder ((x , n) ∷ xs) = (suc x , suc n) ∷ weakenOrder xs

-- --       replaceVar : Nat → List (Nat × Nat) → Nat → Nat
-- --       replaceVar d [] x = x
-- --       replaceVar d ((x-d , n-d) ∷ xns) x with x == x-d + d
-- --       ... | yes _ = n-d + d
-- --       ... | no _ = replaceVar d xns x

-- --       reorderVars' : Nat → Nat → List (Nat × Nat) → Term → Term
-- --       reorderVars' 0 _ _ x = x
-- --       reorderVars' (suc n) d [] (var x args) = var x (fmap (reorderVars' n d []) <$> args)
-- --       reorderVars' (suc n) d ((x-d , n-d) ∷ xns) (var x args) with x == x-d + d
-- --       ... | yes _ = var (n-d + d) (fmap (reorderVars' n d xns) <$> args)
-- --       ... | no _ = reorderVars' (suc n) d xns (var x args)
-- --       reorderVars' (suc n) d xns (con c args) = con c ((fmap ∘ fmap) (reorderVars' n d xns) args)
-- --       reorderVars' (suc n) d xns (def f args) = def f (fmap (reorderVars' n d xns) <$> args)
-- --       reorderVars' (suc n) d xns (lam v t) = lam v (reorderVars' n (suc d) xns <$> t)
-- --       reorderVars' (suc n) d xns (pat-lam cs args) = pat-lam (fmap (reorderVars'InClause n d xns) cs) ((fmap ∘ fmap) (reorderVars' n d xns) args) where
-- --         reorderVars'InClause : Nat → Nat → List (Nat × Nat) → Clause → Clause -- TODO reorder patterns?
-- --         reorderVars'InClause n d xns (clause ps t) = (clause ps (reorderVars' n d xns t))
-- --         reorderVars'InClause n d xns (absurd-clause ps) = (absurd-clause ps)
-- --       reorderVars' (suc n) d xns (pi a b) = pi (reorderVars' n d xns <$> a) (reorderVars' n (suc d) xns <$> b)
-- --       reorderVars' (suc n) d xns (agda-sort (set t)) = agda-sort (set (reorderVars' n d xns t))
-- --       reorderVars' (suc n') d xns (agda-sort (lit n)) = agda-sort (lit n')
-- --       reorderVars' (suc n) d xns (agda-sort unknown) = agda-sort unknown
-- --       reorderVars' (suc n) d xns (lit l) = lit l
-- --       reorderVars' (suc n) d xns (meta x args) = meta x $ (fmap ∘ fmap) (reorderVars' n d xns) args
-- --       reorderVars' (suc n) d xns unknown = unknown

-- --       reorderVars : List (Nat × Nat) → Term → Term
-- --       reorderVars xs t = reorderVars' 99 0 xs t

-- --       record Request : Set where
-- --         field
-- --           l≡r : Term
-- --           A : Type
-- --           L R : Type
-- --           Γ : List (Arg Type)
-- --           𝐺 : Type

-- --   -- TODO: Using this first "something" makes it slow to evaluate ` 𝐺[w/L] ...

-- --         something-fast  : Nat × List (Arg Type × Nat)
-- --         something-fast = go 0 0 [] Γ where
-- --           go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → Nat × List (Arg Type × Nat)
-- --           go _ _ _ [] = 0 , []
-- --           go i j osⱼ (γ ∷ γs) with length Γ - 1
-- --           ... | n with weaken (2 + j) L
-- --           ... | L' with weaken ((n - i) + 3 + j) γ
-- --           ... | γ' with (let w' = var₀ (suc j)
-- --                          in let γ'[w'/L'] = γ' r[ w' / L' ]
-- --                          in reorderVars osⱼ <$> γ'[w'/L'])
-- --           ... | γ'[w'/L'][reordered] with (let γ≢l≡r = isNo $ var₀ (n - i) == l≡r
-- --                                            in let γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
-- --                                            in γ≢l≡r && γ'≠γ'[w'/L'][reordered])
-- --           ... | true = let foo = go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs in (suc (length (snd foo)) , (γ'[w'/L'][reordered] , i) ∷ snd foo)
-- --           ... | false = go (suc i) j (weakenOrder osⱼ) γs

-- --   -- ... but this second "something" makes it slow. Why?
-- --         something-slow  : Nat × List (Arg Type × Nat)
-- --         something-slow = let asdf = go 0 0 [] Γ in (length asdf , asdf) where
-- --           go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat)
-- --           go _ _ _ [] = []
-- --           go i j osⱼ (γ ∷ γs) with length Γ - 1
-- --           ... | n with weaken (2 + j) L
-- --           ... | L' with weaken ((n - i) + 3 + j) γ
-- --           ... | γ' with (let w' = var₀ (suc j)
-- --                          in let γ'[w'/L'] = γ' r[ w' / L' ]
-- --                          in reorderVars osⱼ <$> γ'[w'/L'])
-- --           ... | γ'[w'/L'][reordered] with (let γ≢l≡r = isNo $ var₀ (n - i) == l≡r
-- --                                            in let γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
-- --                                            in γ≢l≡r && γ'≠γ'[w'/L'][reordered])
-- --           ... | true = let foo = go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs in (γ'[w'/L'][reordered] , i) ∷ foo
-- --           ... | false = go (suc i) j (weakenOrder osⱼ) γs

-- --         no-cps-𝐺[w/L] : Type
-- --         no-cps-𝐺[w/L]
-- --          with something-fast
-- --         ... | (_ , Γw) =
-- --           let |L| = length (fst <$> Γw)
-- --               os = go |L| 0 (snd <$> Γw) []
-- --               𝐺' = (weaken (3 + |L|) 𝐺) r[ var₀ (2 + |L|) / weaken (3 + |L|) L ]
-- --           in
-- --             reorderVars os 𝐺'
-- --           where
-- --           go : Nat → Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
-- --           go |L| _ [] ns = ns
-- --           go |L| j (i ∷ is) ns = go |L| (suc j) is $ (1 + |L| + 2 + (length Γ - 1) - i , 1 + (|L| - 1) - j) ∷ ns


-- --         cps₀ : List (Arg Type × Nat) × Type
-- --         cps₀
-- --          with something-fast
-- --         ... | (_ , Γw)
-- --          with fst <$> Γw
-- --         ... | biggies
-- --          with length biggies
-- --         ... | |l| = Γw , 𝐺[w/L]
-- --           where
-- --           𝐺[w/L] : Type
-- --           𝐺[w/L] with 2 + |l| | 3 + |l|
-- --           ... | l | r =
-- --             let
-- --                 LL = 2 + |l|
-- --                 os = go 0 (snd <$> Γw) []
-- --                 𝐺' = (weaken (3 + |l|) 𝐺) r[ var₀ LL / weaken r L ]
-- --             in
-- --               reorderVars os 𝐺'
-- --             where
-- --             go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
-- --             go _ [] ns = ns
-- --             go j (i ∷ is) ns = go (suc j) is $ (1 + |l| + 2 + (length Γ - 1) - i , 1 + (|l| - 1) - j) ∷ ns

-- --         𝐺[w/L]-cps₁ : List (Arg Type × Nat) → Type
-- --         𝐺[w/L]-cps₁ [at×n]
-- --          with length [at×n]
-- --         ... | |l|
-- --          with 2 + |l| | 3 + |l|
-- --         ... | l | r
-- --          with [at×n]
-- --         ... | Γw =
-- --           let LL = 2 + |l|
-- --               os = go 0 (snd <$> Γw) []
-- --               𝐺' = (weaken (3 + |l|) 𝐺) r[ var₀ {-LL-} 0 / {-weaken r-} L ]
-- --           in
-- --             {-reorderVars os-} 𝐺'
-- --           where
-- --           go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
-- --           go _ [] ns = ns
-- --           go j (i ∷ is) ns = go (suc j) is $ (1 + |l| + 2 + (length Γ - 1) - i , 1 + (|l| - 1) - j) ∷ ns

-- --         cps₁ : List (Arg Type × Nat) × Type
-- --         cps₁ = go 0 0 Γ where
-- --           go : Nat → Nat → List (Arg Type) → List (Arg Type × Nat) × Type
-- --           go _ _ [] = [] , 𝐺[w/L]-cps₁ []
-- --           go i j (γ ∷ γs) with length Γ - 1
-- --           ... | n with weaken (2 + j) L
-- --           ... | L' with weaken ((n - i) + 3 + j) γ
-- --           ... | γ' with γ' -- (let w' = var₀ (suc j)
-- --                            --  in let γ'[w'/L'] = γ' r[ w' / L' ]
-- --                            --  in reorderVars osⱼ <$> γ'[w'/L'])
-- --           ... | γ'[w'/L'][reordered] with (let γ≢l≡r = isNo $ var₀ (n - i) == l≡r
-- --                                            in let γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
-- --                                            in γ≢l≡r && γ'≠γ'[w'/L'][reordered])
-- --           ... | true = let cps = (γ'[w'/L'][reordered] , i) ∷ fst (go (suc i) (suc j) γs)
-- --                        in
-- --                        cps , 𝐺[w/L]-cps₁ cps
-- --           ... | false = go (suc i) j γs
-- --   {-
-- --         cps₂ : List (Arg Type × Nat) × Type
-- --         cps₂ = {!!}
-- --   -}
-- --         Γ[w/L]₀ : List (Arg Type)
-- --         Γ[w/L]₀ = fst <$> (fst cps₀)

-- --         𝐺[w/L]₀ : Type
-- --         𝐺[w/L]₀ = snd cps₀

-- --         Γ[w/L]₁ : List (Arg Type)
-- --         Γ[w/L]₁ = fst <$> (fst cps₁)

-- --         𝐺[w/L]₁ : Type
-- --         𝐺[w/L]₁ = snd cps₁
-- --   {-
-- --         Γ[w/L]₂ : List (Arg Type)
-- --         Γ[w/L]₂ = fst <$> (fst cps₂)

-- --         𝐺[w/L]₂ : Type
-- --         𝐺[w/L]₂ = snd cps₂
-- --   -}
-- --       getRequest : Term → Term → TC Request
-- --       getRequest l≡r hole = do
-- --         L≡R ← inferType l≡r -|
-- --         L≡R-matched ← maybe (typeError (strErr "not an equality" ∷ termErr l≡r ∷ termErr L≡R ∷ [])) pure $
-- --           match 3 (def (quote _≡_) (hArg unknown ∷ (hArg (var₀ 0)) ∷ (vArg (var₀ 1)) ∷ (vArg (var₀ 2)) ∷ [])) L≡R -|
-- --         𝐺 ← inferFunRange hole -|
-- --         Γ ← getContext -|
-- --         case L≡R-matched of λ { (A ∷ L ∷ R ∷ []) →
-- --           pure $ record { l≡r = l≡r ; A = A ; L = L ; R = R ; Γ = reverse Γ ; 𝐺 = 𝐺 } }

-- --     𝐺! : Term
-- --     𝐺! = pi
-- --           (arg (arg-info visible relevant)
-- --            (pi (arg (arg-info visible relevant) (var 31 []))
-- --             (abs "_"
-- --              (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --               (abs "_"
-- --                (pi (arg (arg-info visible relevant) (var 33 []))
-- --                 (abs "_" (agda-sort (lit 0)))))))))
-- --           (abs "_"
-- --            (pi
-- --             (arg (arg-info visible relevant)
-- --              (pi (arg (arg-info visible relevant) (var 32 []))
-- --               (abs "_"
-- --                (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                 (abs "_"
-- --                  (pi (arg (arg-info visible relevant) (var 34 []))
-- --                   (abs "_" (agda-sort (lit 0)))))))))
-- --             (abs "_"
-- --              (pi
-- --               (arg (arg-info visible relevant)
-- --                (pi (arg (arg-info visible relevant) (var 33 []))
-- --                 (abs "_"
-- --                  (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                   (abs "_"
-- --                    (pi (arg (arg-info visible relevant) (var 35 []))
-- --                     (abs "_" (agda-sort (lit 0)))))))))
-- --               (abs "_"
-- --                (pi
-- --                 (arg (arg-info visible relevant)
-- --                  (pi (arg (arg-info visible relevant) (var 34 []))
-- --                   (abs "_"
-- --                    (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                     (abs "_"
-- --                      (pi (arg (arg-info visible relevant) (var 36 []))
-- --                       (abs "_" (agda-sort (lit 0)))))))))
-- --                 (abs "_"
-- --                  (pi
-- --                   (arg (arg-info visible relevant)
-- --                    (pi (arg (arg-info visible relevant) (var 35 []))
-- --                     (abs "_"
-- --                      (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                       (abs "_"
-- --                        (pi (arg (arg-info visible relevant) (var 37 []))
-- --                         (abs "_" (agda-sort (lit 0)))))))))
-- --                   (abs "_"
-- --                    (pi
-- --                     (arg (arg-info visible relevant)
-- --                      (pi (arg (arg-info visible relevant) (var 36 []))
-- --                       (abs "_"
-- --                        (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                         (abs "_"
-- --                          (pi (arg (arg-info visible relevant) (var 38 []))
-- --                           (abs "_" (agda-sort (lit 0)))))))))
-- --                     (abs "_"
-- --                      (pi
-- --                       (arg (arg-info visible relevant)
-- --                        (pi (arg (arg-info visible relevant) (var 37 []))
-- --                         (abs "_"
-- --                          (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                           (abs "_"
-- --                            (pi (arg (arg-info visible relevant) (var 39 []))
-- --                             (abs "_" (agda-sort (lit 0)))))))))
-- --                       (abs "_"
-- --                        (pi
-- --                         (arg (arg-info visible relevant)
-- --                          (pi (arg (arg-info visible relevant) (var 38 []))
-- --                           (abs "_"
-- --                            (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                             (abs "_"
-- --                              (pi (arg (arg-info visible relevant) (var 40 []))
-- --                               (abs "_" (agda-sort (lit 0)))))))))
-- --                         (abs "_"
-- --                          (pi
-- --                           (arg (arg-info visible relevant)
-- --                            (pi (arg (arg-info visible relevant) (var 39 []))
-- --                             (abs "_"
-- --                              (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                               (abs "_"
-- --                                (pi (arg (arg-info visible relevant) (var 41 []))
-- --                                 (abs "_" (agda-sort (lit 0)))))))))
-- --                           (abs "_"
-- --                            (pi
-- --                             (arg (arg-info visible relevant)
-- --                              (pi (arg (arg-info visible relevant) (var 40 []))
-- --                               (abs "_"
-- --                                (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                                 (abs "_"
-- --                                  (pi (arg (arg-info visible relevant) (var 42 []))
-- --                                   (abs "_" (agda-sort (lit 0)))))))))
-- --                             (abs "_"
-- --                              (pi
-- --                               (arg (arg-info visible relevant)
-- --                                (pi (arg (arg-info visible relevant) (var 41 []))
-- --                                 (abs "_"
-- --                                  (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                                   (abs "_"
-- --                                    (pi (arg (arg-info visible relevant) (var 43 []))
-- --                                     (abs "_" (agda-sort (lit 0)))))))))
-- --                               (abs "_"
-- --                                (pi
-- --                                 (arg (arg-info visible relevant)
-- --                                  (pi (arg (arg-info visible relevant) (var 42 []))
-- --                                   (abs "_"
-- --                                    (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                                     (abs "_"
-- --                                      (pi (arg (arg-info visible relevant) (var 44 []))
-- --                                       (abs "_" (agda-sort (lit 0)))))))))
-- --                                 (abs "_"
-- --                                  (pi
-- --                                   (arg (arg-info visible relevant)
-- --                                    (pi (arg (arg-info visible relevant) (var 43 []))
-- --                                     (abs "_"
-- --                                      (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                                       (abs "_"
-- --                                        (pi (arg (arg-info visible relevant) (var 45 []))
-- --                                         (abs "_" (agda-sort (lit 0)))))))))
-- --                                   (abs "_"
-- --                                    (pi
-- --                                     (arg (arg-info visible relevant)
-- --                                      (pi (arg (arg-info visible relevant) (var 44 []))
-- --                                       (abs "_"
-- --                                        (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                                         (abs "_"
-- --                                          (pi (arg (arg-info visible relevant) (var 46 []))
-- --                                           (abs "_" (agda-sort (lit 0)))))))))
-- --                                     (abs "_"
-- --                                      (pi
-- --                                       (arg (arg-info visible relevant)
-- --                                        (pi (arg (arg-info visible relevant) (var 45 []))
-- --                                         (abs "_"
-- --                                          (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                                           (abs "_"
-- --                                            (pi (arg (arg-info visible relevant) (var 47 []))
-- --                                             (abs "_" (agda-sort (lit 0)))))))))
-- --                                       (abs "_"
-- --                                        (pi
-- --                                         (arg (arg-info visible relevant)
-- --                                          (pi (arg (arg-info visible relevant) (var 46 []))
-- --                                           (abs "_"
-- --                                            (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                                             (abs "_"
-- --                                              (pi (arg (arg-info visible relevant) (var 48 []))
-- --                                               (abs "_" (agda-sort (lit 0)))))))))
-- --                                         (abs "_"
-- --                                          (pi
-- --                                           (arg (arg-info visible relevant)
-- --                                            (pi (arg (arg-info visible relevant) (var 47 []))
-- --                                             (abs "_"
-- --                                              (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                                               (abs "_"
-- --                                                (pi (arg (arg-info visible relevant) (var 49 []))
-- --                                                 (abs "_" (agda-sort (lit 0)))))))))
-- --                                           (abs "_"
-- --                                            (pi
-- --                                             (arg (arg-info visible relevant)
-- --                                              (pi (arg (arg-info visible relevant) (var 48 []))
-- --                                               (abs "_"
-- --                                                (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                                                 (abs "_"
-- --                                                  (pi (arg (arg-info visible relevant) (var 50 []))
-- --                                                   (abs "_" (agda-sort (lit 0)))))))))
-- --                                             (abs "_"
-- --                                              (pi
-- --                                               (arg (arg-info visible relevant)
-- --                                                (pi (arg (arg-info visible relevant) (var 49 []))
-- --                                                 (abs "_"
-- --                                                  (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                                                   (abs "_"
-- --                                                    (pi (arg (arg-info visible relevant) (var 51 []))
-- --                                                     (abs "_" (agda-sort (lit 0)))))))))
-- --                                               (abs "_"
-- --                                                (pi
-- --                                                 (arg (arg-info visible relevant)
-- --                                                  (pi (arg (arg-info visible relevant) (var 50 []))
-- --                                                   (abs "_"
-- --                                                    (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                                                     (abs "_"
-- --                                                      (pi (arg (arg-info visible relevant) (var 52 []))
-- --                                                       (abs "_" (agda-sort (lit 0)))))))))
-- --                                                 (abs "_"
-- --                                                  (pi
-- --                                                   (arg (arg-info visible relevant)
-- --                                                    (pi (arg (arg-info visible relevant) (var 51 []))
-- --                                                     (abs "_"
-- --                                                      (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                                                       (abs "_"
-- --                                                        (pi (arg (arg-info visible relevant) (var 53 []))
-- --                                                         (abs "_" (agda-sort (lit 0)))))))))
-- --                                                   (abs "_"
-- --                                                    (pi
-- --                                                     (arg (arg-info visible relevant)
-- --                                                      (pi (arg (arg-info visible relevant) (var 52 []))
-- --                                                       (abs "_"
-- --                                                        (pi
-- --                                                         (arg (arg-info visible relevant) (agda-sort (lit 1)))
-- --                                                         (abs "_"
-- --                                                          (pi (arg (arg-info visible relevant) (var 54 []))
-- --                                                           (abs "_" (agda-sort (lit 0)))))))))
-- --                                                     (abs "_"
-- --                                                      (pi
-- --                                                       (arg (arg-info visible relevant)
-- --                                                        (pi (arg (arg-info visible relevant) (var 53 []))
-- --                                                         (abs "_"
-- --                                                          (pi
-- --                                                           (arg (arg-info visible relevant)
-- --                                                            (agda-sort (lit 1)))
-- --                                                           (abs "_"
-- --                                                            (pi (arg (arg-info visible relevant) (var 55 []))
-- --                                                             (abs "_" (agda-sort (lit 0)))))))))
-- --                                                       (abs "_"
-- --                                                        (pi
-- --                                                         (arg (arg-info visible relevant)
-- --                                                          (pi (arg (arg-info visible relevant) (var 54 []))
-- --                                                           (abs "_"
-- --                                                            (pi
-- --                                                             (arg (arg-info visible relevant)
-- --                                                              (agda-sort (lit 1)))
-- --                                                             (abs "_"
-- --                                                              (pi (arg (arg-info visible relevant) (var 56 []))
-- --                                                               (abs "_" (agda-sort (lit 0)))))))))
-- --                                                         (abs "_"
-- --                                                          (pi
-- --                                                           (arg (arg-info visible relevant)
-- --                                                            (pi (arg (arg-info visible relevant) (var 55 []))
-- --                                                             (abs "_"
-- --                                                              (pi
-- --                                                               (arg (arg-info visible relevant)
-- --                                                                (agda-sort (lit 1)))
-- --                                                               (abs "_"
-- --                                                                (pi
-- --                                                                 (arg (arg-info visible relevant) (var 57 []))
-- --                                                                 (abs "_" (agda-sort (lit 0)))))))))
-- --                                                           (abs "_"
-- --                                                            (pi
-- --                                                             (arg (arg-info visible relevant)
-- --                                                              (pi (arg (arg-info visible relevant) (var 56 []))
-- --                                                               (abs "_"
-- --                                                                (pi
-- --                                                                 (arg (arg-info visible relevant)
-- --                                                                  (agda-sort (lit 1)))
-- --                                                                 (abs "_"
-- --                                                                  (pi
-- --                                                                   (arg (arg-info visible relevant)
-- --                                                                    (var 58 []))
-- --                                                                   (abs "_" (agda-sort (lit 0)))))))))
-- --                                                             (abs "_"
-- --                                                              (agda-sort
-- --                                                               (lit
-- --                                                                0)))))))))))))))))))))))))))))))))))))))))))))))))))))


-- --     macro
-- --       reright-debug : Term → Tactic
-- --       reright-debug l≡r hole =
-- --         q ← getRequest l≡r hole -|
-- --         let open Request q in
-- --         typeError ( strErr "reright-debug"     ∷
-- --                     --strErr "\nΓ[w/L]₀:"         ∷ termErr (` Γ[w/L]₀)               ∷
-- --                     --strErr "\n𝐺[w/L]₀:"         ∷ termErr (` 𝐺[w/L]₀)               ∷
-- --                     strErr "\nno-cps-𝐺[w/L]:"         ∷ termErr (` no-cps-𝐺[w/L])               ∷
-- --                     --strErr "\nΓ[w/L]₁:"         ∷ termErr (` Γ[w/L]₁)               ∷
-- --                     --strErr "\n𝐺[w/L]₁:"         ∷ termErr (` 𝐺[w/L]₁)               ∷
-- --                     --strErr "\n𝐺[w/L]₁*:"         ∷ termErr (` (𝐺[w/L]-cps₁ []))               ∷
-- --                     --strErr "\n𝐺*:"         ∷ termErr (` (𝐺! r[ unknown / var₀ 0 ]))               ∷
-- --                     --strErr "\n𝐺*:"         ∷ termErr (` (𝐺! r[ unknown / set! ]))               ∷

-- --                     --strErr "\nΓ[w/L]₂:"         ∷ termErr (` Γ[w/L]₂)               ∷
-- --                     --strErr "\n𝐺[w/L]₂:"         ∷ termErr (` 𝐺[w/L]₂)               ∷
-- --                     [] )

-- --     tester : ∀ {a} → {A : Set a} → {x y : A} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} → {f : Set a → Set a → Set a} →
-- --              {g : Set a → Set a} →
-- --   {-
-- --              Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a →
-- --              Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a →
-- --              Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a →
-- --              Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a →
-- --              Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a →
-- --              Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a →
-- --              Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a →
-- --   -}
-- --              x ≡ y →
-- --              {-
-- --              Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set →
-- --              Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set →
-- --              Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set →
-- --              Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set →
-- --              Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set →
-- --              Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set →
-- --              Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set →
-- --              -}
-- --              -- f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A →
-- --              -- g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A →
-- --              -- A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →
-- --              (A → Set₁ → A → Set) →

-- --              Set
-- --     tester x≡y = {!!} -- reright-debug x≡y {!!}

-- --     retest : 𝐺! ≡ 𝐺! r[ unknown / var₀ 0 ]
-- --     retest = refl

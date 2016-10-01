module Tactic.Reflection.Reright-Performance-2 where
  open import Prelude

  open import Tactic.Reflection
  open import Tactic.Reflection.Match
  open import Tactic.Reflection.Replace
  open import Tactic.Reflection.Quote

  private
    weakenOrder : List (Nat × Nat) → List (Nat × Nat)
    weakenOrder [] = []
    weakenOrder ((x , n) ∷ xs) = (suc x , suc n) ∷ weakenOrder xs

    replaceVar : Nat → List (Nat × Nat) → Nat → Nat
    replaceVar d [] x = x
    replaceVar d ((x-d , n-d) ∷ xns) x with x == x-d + d
    ... | yes _ = n-d + d
    ... | no _ = replaceVar d xns x

    reorderVars' : Nat → Nat → List (Nat × Nat) → Term → Term
    reorderVars' 0 _ _ x = x
    reorderVars' (suc n) d [] (var x args) = var x (fmap (reorderVars' n d []) <$> args)
    reorderVars' (suc n) d ((x-d , n-d) ∷ xns) (var x args) with x == x-d + d
    ... | yes _ = var (n-d + d) (fmap (reorderVars' n d xns) <$> args)
    ... | no _ = reorderVars' (suc n) d xns (var x args)
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

    reorderVars : List (Nat × Nat) → Term → Term
    reorderVars xs t = reorderVars' 99 0 xs t

    record Request : Set where
      field
        l≡r : Term
        A : Type
        L R : Type
        Γ : List (Arg Type)
        𝐺 : Type

-- TODO: Using this first "something" makes it slow to evaluate ` 𝐺[w/L] ...

      something-fast  : Nat × List (Arg Type × Nat)
      something-fast = go 0 0 Γ where
        go : Nat → Nat → List (Arg Type) → Nat × List (Arg Type × Nat)
        go _ _ [] = 0 , []
        go i j (γ ∷ γs) with length Γ - 1
        ... | n with weaken (2 + j) L
        ... | L' with weaken ((n - i) + 3 + j) γ
        ... | γ' with γ' -- (let w' = var₀ (suc j)
                         --  in let γ'[w'/L'] = γ' r[ w' / L' ]
                         --  in reorderVars osⱼ <$> γ'[w'/L'])
        ... | γ'[w'/L'][reordered] with (let γ≢l≡r = isNo $ var₀ (n - i) == l≡r
                                         in let γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
                                         in γ≢l≡r && γ'≠γ'[w'/L'][reordered])
        ... | true = let foo = go (suc i) (suc j) γs in (suc (length (snd foo)) , (γ'[w'/L'][reordered] , i) ∷ snd foo)
        ... | false = go (suc i) j γs

      something-slow  : Nat × List (Arg Type × Nat)
      something-slow = let asdf = go 0 0 Γ in (length asdf , asdf) where
        go : Nat → Nat → List (Arg Type) → List (Arg Type × Nat)
        go _ _ [] = []
        go i j (γ ∷ γs) with length Γ - 1
        ... | n with weaken (2 + j) L
        ... | L' with weaken ((n - i) + 3 + j) γ
        ... | γ' with isNo $ γ' == γ'
{-
        ... | γ' with (let γ≢l≡r = isNo $ var₀ (n - i) == l≡r
                       in let γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'
                       in γ≢l≡r && γ'≠γ'[w'/L'][reordered])
-}
        ... | true = let foo = go (suc i) (suc j) γs in (vArg unknown , i) ∷ foo
        ... | false = go (suc i) j γs

      cps₀ : List (Arg Type × Nat) × Type
      cps₀
       with something-fast
      ... | (_ , Γw)
       with fst <$> Γw
      ... | biggies
       with length biggies
      ... | |l| = Γw , 𝐺[w/L]
        where
        𝐺[w/L] : Type
        𝐺[w/L] with 2 + |l| | 3 + |l|
        ... | l | r =
          let
              LL = 2 + |l|
              os = go 0 (snd <$> Γw) []
              𝐺' = ({-weaken (3 + |l|)-} 𝐺) r[ var₀ LL / weaken r L ]
          in
            reorderVars os 𝐺'
          where
          go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
          go _ [] ns = ns
          go j (i ∷ is) ns = go (suc j) is $ (1 + |l| + 2 + (length Γ - 1) - i , 1 + (|l| - 1) - j) ∷ ns

      𝐺[w/L]-cps₁ : List (Arg Type × Nat) → Type
      𝐺[w/L]-cps₁ [at×n]
       with length [at×n]
      ... | |l|
       with 2 + |l| | 3 + |l|
      ... | l | r
       with [at×n]
      ... | Γw =
        let LL = 2 + |l|
            os = go 0 (snd <$> Γw) []
            𝐺' = (weaken (3 + |l|) 𝐺) r[ var₀ {-LL-} 0 / {-weaken r-} L ]
        in
          {-reorderVars os-} 𝐺'
        where
        go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
        go _ [] ns = ns
        go j (i ∷ is) ns = go (suc j) is $ (1 + |l| + 2 + (length Γ - 1) - i , 1 + (|l| - 1) - j) ∷ ns

      cps₁ : List (Arg Type × Nat) × Type
      cps₁ = go 0 0 Γ where
        go : Nat → Nat → List (Arg Type) → List (Arg Type × Nat) × Type
        go _ _ [] = [] , 𝐺[w/L]-cps₁ []
        go i j (γ ∷ γs) with length Γ - 1
        ... | n with weaken (2 + j) L
        ... | L' with weaken ((n - i) + 3 + j) γ
        ... | γ' with γ' -- (let w' = var₀ (suc j)
                         --  in let γ'[w'/L'] = γ' r[ w' / L' ]
                         --  in reorderVars osⱼ <$> γ'[w'/L'])
        ... | γ'[w'/L'][reordered] with (let γ≢l≡r = isNo $ var₀ (n - i) == l≡r
                                         in let γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
                                         in γ≢l≡r && γ'≠γ'[w'/L'][reordered])
        ... | true = let cps = (γ'[w'/L'][reordered] , i) ∷ fst (go (suc i) (suc j) γs)
                     in
                     cps , 𝐺[w/L]-cps₁ cps
        ... | false = go (suc i) j γs

      cps₂ : List (Arg Type × Nat) × Type
      cps₂ = ?

      Γ[w/L]₀ : List (Arg Type)
      Γ[w/L]₀ = fst <$> (fst cps₀)

      𝐺[w/L]₀ : Type
      𝐺[w/L]₀ = snd cps₀

      Γ[w/L]₁ : List (Arg Type)
      Γ[w/L]₁ = fst <$> (fst cps₁)

      𝐺[w/L]₁ : Type
      𝐺[w/L]₁ = snd cps₁

      Γ[w/L]₂ : List (Arg Type)
      Γ[w/L]₂ = fst <$> (fst cps₂)

      𝐺[w/L]₂ : Type
      𝐺[w/L]₂ = snd cps₂

    getRequest : Term → Term → TC Request
    getRequest l≡r hole = do
      L≡R ← inferType l≡r -|
      L≡R-matched ← maybe (typeError (strErr "not an equality" ∷ termErr l≡r ∷ termErr L≡R ∷ [])) pure $
        match 3 (def (quote _≡_) (hArg unknown ∷ (hArg (var₀ 0)) ∷ (vArg (var₀ 1)) ∷ (vArg (var₀ 2)) ∷ [])) L≡R -|
      𝐺 ← inferFunRange hole -|
      Γ ← getContext -|
      case L≡R-matched of λ { (A ∷ L ∷ R ∷ []) →
        pure $ record { l≡r = l≡r ; A = A ; L = L ; R = R ; Γ = reverse Γ ; 𝐺 = 𝐺 } }

  𝐺! : Term
  𝐺! = pi
        (arg (arg-info visible relevant)
         (pi (arg (arg-info visible relevant) (var 31 []))
          (abs "_"
           (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
            (abs "_"
             (pi (arg (arg-info visible relevant) (var 33 []))
              (abs "_" (agda-sort (lit 0)))))))))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (pi (arg (arg-info visible relevant) (var 32 []))
            (abs "_"
             (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
              (abs "_"
               (pi (arg (arg-info visible relevant) (var 34 []))
                (abs "_" (agda-sort (lit 0)))))))))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (pi (arg (arg-info visible relevant) (var 33 []))
              (abs "_"
               (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                (abs "_"
                 (pi (arg (arg-info visible relevant) (var 35 []))
                  (abs "_" (agda-sort (lit 0)))))))))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (pi (arg (arg-info visible relevant) (var 34 []))
                (abs "_"
                 (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                  (abs "_"
                   (pi (arg (arg-info visible relevant) (var 36 []))
                    (abs "_" (agda-sort (lit 0)))))))))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (pi (arg (arg-info visible relevant) (var 35 []))
                  (abs "_"
                   (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                    (abs "_"
                     (pi (arg (arg-info visible relevant) (var 37 []))
                      (abs "_" (agda-sort (lit 0)))))))))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (pi (arg (arg-info visible relevant) (var 36 []))
                    (abs "_"
                     (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                      (abs "_"
                       (pi (arg (arg-info visible relevant) (var 38 []))
                        (abs "_" (agda-sort (lit 0)))))))))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (pi (arg (arg-info visible relevant) (var 37 []))
                      (abs "_"
                       (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                        (abs "_"
                         (pi (arg (arg-info visible relevant) (var 39 []))
                          (abs "_" (agda-sort (lit 0)))))))))
                    (abs "_"
                     (pi
                      (arg (arg-info visible relevant)
                       (pi (arg (arg-info visible relevant) (var 38 []))
                        (abs "_"
                         (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                          (abs "_"
                           (pi (arg (arg-info visible relevant) (var 40 []))
                            (abs "_" (agda-sort (lit 0)))))))))
                      (abs "_"
                       (pi
                        (arg (arg-info visible relevant)
                         (pi (arg (arg-info visible relevant) (var 39 []))
                          (abs "_"
                           (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                            (abs "_"
                             (pi (arg (arg-info visible relevant) (var 41 []))
                              (abs "_" (agda-sort (lit 0)))))))))
                        (abs "_"
                         (pi
                          (arg (arg-info visible relevant)
                           (pi (arg (arg-info visible relevant) (var 40 []))
                            (abs "_"
                             (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                              (abs "_"
                               (pi (arg (arg-info visible relevant) (var 42 []))
                                (abs "_" (agda-sort (lit 0)))))))))
                          (abs "_"
                           (pi
                            (arg (arg-info visible relevant)
                             (pi (arg (arg-info visible relevant) (var 41 []))
                              (abs "_"
                               (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                                (abs "_"
                                 (pi (arg (arg-info visible relevant) (var 43 []))
                                  (abs "_" (agda-sort (lit 0)))))))))
                            (abs "_"
                             (pi
                              (arg (arg-info visible relevant)
                               (pi (arg (arg-info visible relevant) (var 42 []))
                                (abs "_"
                                 (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                                  (abs "_"
                                   (pi (arg (arg-info visible relevant) (var 44 []))
                                    (abs "_" (agda-sort (lit 0)))))))))
                              (abs "_"
                               (pi
                                (arg (arg-info visible relevant)
                                 (pi (arg (arg-info visible relevant) (var 43 []))
                                  (abs "_"
                                   (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                                    (abs "_"
                                     (pi (arg (arg-info visible relevant) (var 45 []))
                                      (abs "_" (agda-sort (lit 0)))))))))
                                (abs "_"
                                 (pi
                                  (arg (arg-info visible relevant)
                                   (pi (arg (arg-info visible relevant) (var 44 []))
                                    (abs "_"
                                     (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                                      (abs "_"
                                       (pi (arg (arg-info visible relevant) (var 46 []))
                                        (abs "_" (agda-sort (lit 0)))))))))
                                  (abs "_"
                                   (pi
                                    (arg (arg-info visible relevant)
                                     (pi (arg (arg-info visible relevant) (var 45 []))
                                      (abs "_"
                                       (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                                        (abs "_"
                                         (pi (arg (arg-info visible relevant) (var 47 []))
                                          (abs "_" (agda-sort (lit 0)))))))))
                                    (abs "_"
                                     (pi
                                      (arg (arg-info visible relevant)
                                       (pi (arg (arg-info visible relevant) (var 46 []))
                                        (abs "_"
                                         (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                                          (abs "_"
                                           (pi (arg (arg-info visible relevant) (var 48 []))
                                            (abs "_" (agda-sort (lit 0)))))))))
                                      (abs "_"
                                       (pi
                                        (arg (arg-info visible relevant)
                                         (pi (arg (arg-info visible relevant) (var 47 []))
                                          (abs "_"
                                           (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                                            (abs "_"
                                             (pi (arg (arg-info visible relevant) (var 49 []))
                                              (abs "_" (agda-sort (lit 0)))))))))
                                        (abs "_"
                                         (pi
                                          (arg (arg-info visible relevant)
                                           (pi (arg (arg-info visible relevant) (var 48 []))
                                            (abs "_"
                                             (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                                              (abs "_"
                                               (pi (arg (arg-info visible relevant) (var 50 []))
                                                (abs "_" (agda-sort (lit 0)))))))))
                                          (abs "_"
                                           (pi
                                            (arg (arg-info visible relevant)
                                             (pi (arg (arg-info visible relevant) (var 49 []))
                                              (abs "_"
                                               (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                                                (abs "_"
                                                 (pi (arg (arg-info visible relevant) (var 51 []))
                                                  (abs "_" (agda-sort (lit 0)))))))))
                                            (abs "_"
                                             (pi
                                              (arg (arg-info visible relevant)
                                               (pi (arg (arg-info visible relevant) (var 50 []))
                                                (abs "_"
                                                 (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                                                  (abs "_"
                                                   (pi (arg (arg-info visible relevant) (var 52 []))
                                                    (abs "_" (agda-sort (lit 0)))))))))
                                              (abs "_"
                                               (pi
                                                (arg (arg-info visible relevant)
                                                 (pi (arg (arg-info visible relevant) (var 51 []))
                                                  (abs "_"
                                                   (pi (arg (arg-info visible relevant) (agda-sort (lit 1)))
                                                    (abs "_"
                                                     (pi (arg (arg-info visible relevant) (var 53 []))
                                                      (abs "_" (agda-sort (lit 0)))))))))
                                                (abs "_"
                                                 (pi
                                                  (arg (arg-info visible relevant)
                                                   (pi (arg (arg-info visible relevant) (var 52 []))
                                                    (abs "_"
                                                     (pi
                                                      (arg (arg-info visible relevant) (agda-sort (lit 1)))
                                                      (abs "_"
                                                       (pi (arg (arg-info visible relevant) (var 54 []))
                                                        (abs "_" (agda-sort (lit 0)))))))))
                                                  (abs "_"
                                                   (pi
                                                    (arg (arg-info visible relevant)
                                                     (pi (arg (arg-info visible relevant) (var 53 []))
                                                      (abs "_"
                                                       (pi
                                                        (arg (arg-info visible relevant)
                                                         (agda-sort (lit 1)))
                                                        (abs "_"
                                                         (pi (arg (arg-info visible relevant) (var 55 []))
                                                          (abs "_" (agda-sort (lit 0)))))))))
                                                    (abs "_"
                                                     (pi
                                                      (arg (arg-info visible relevant)
                                                       (pi (arg (arg-info visible relevant) (var 54 []))
                                                        (abs "_"
                                                         (pi
                                                          (arg (arg-info visible relevant)
                                                           (agda-sort (lit 1)))
                                                          (abs "_"
                                                           (pi (arg (arg-info visible relevant) (var 56 []))
                                                            (abs "_" (agda-sort (lit 0)))))))))
                                                      (abs "_"
                                                       (pi
                                                        (arg (arg-info visible relevant)
                                                         (pi (arg (arg-info visible relevant) (var 55 []))
                                                          (abs "_"
                                                           (pi
                                                            (arg (arg-info visible relevant)
                                                             (agda-sort (lit 1)))
                                                            (abs "_"
                                                             (pi
                                                              (arg (arg-info visible relevant) (var 57 []))
                                                              (abs "_" (agda-sort (lit 0)))))))))
                                                        (abs "_"
                                                         (pi
                                                          (arg (arg-info visible relevant)
                                                           (pi (arg (arg-info visible relevant) (var 56 []))
                                                            (abs "_"
                                                             (pi
                                                              (arg (arg-info visible relevant)
                                                               (agda-sort (lit 1)))
                                                              (abs "_"
                                                               (pi
                                                                (arg (arg-info visible relevant)
                                                                 (var 58 []))
                                                                (abs "_" (agda-sort (lit 0)))))))))
                                                          (abs "_"
                                                           (agda-sort
                                                            (lit
                                                             0)))))))))))))))))))))))))))))))))))))))))))))))))))))


  macro
    reright-debug : Term → Tactic
    reright-debug l≡r hole =
      q ← getRequest l≡r hole -|
      --let open Request q in
      typeError ( strErr "reright-debug"     ∷
                  --strErr "\nΓ[w/L]₀:"         ∷ termErr (` Γ[w/L]₀)               ∷
                  --strErr "\n𝐺[w/L]₀:"         ∷ termErr (` 𝐺[w/L]₀)               ∷
                  --strErr "\nΓ[w/L]₁:"         ∷ termErr (` Γ[w/L]₁)               ∷
                  --strErr "\n𝐺[w/L]₁:"         ∷ termErr (` 𝐺[w/L]₁)               ∷
                  --strErr "\n𝐺[w/L]₁*:"         ∷ termErr (` (𝐺[w/L]-cps₁ []))               ∷
                  strErr "\n𝐺*:"         ∷ termErr (` (𝐺! r[ unknown / var₀ 0 ]))               ∷
                  --strErr "\n𝐺*:"         ∷ termErr (` (𝐺! r[ unknown / set! ]))               ∷

                  --strErr "\nΓ[w/L]₂:"         ∷ termErr (` Γ[w/L]₂)               ∷
                  --strErr "\n𝐺[w/L]₂:"         ∷ termErr (` 𝐺[w/L]₂)               ∷
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
{-
           Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a →
           Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a →
           Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a →
           Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a →
           Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a →
           Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a →
           Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a → Set a →
-}
           x ≡ y →
           {-
           Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set →
           Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set →
           Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set →
           Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set →
           Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set →
           Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set →
           Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set → Set →
           -}
           -- f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A → f A A →
           -- g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A → g A →
           -- A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A →
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

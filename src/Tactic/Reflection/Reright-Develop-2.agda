module Tactic.Reflection.Reright2 where
  open import Prelude

  open import Container.Traversable

  open import Tactic.Reflection
  open import Tactic.Reflection.Match
  open import Tactic.Reflection.Replace
  open import Tactic.Reflection.Quote

  private
    minBoundVar : Type → Nat
    minBoundVar x with reverse (freeVars x)
    ... | [] = 0
    ... | (v ∷ vs) = just (suc v)

    {- Request is a request for a reright in which
         * the reright is applied in context Γᶜ (inner-most first)
         * the last m terms of Γᶜ are module parameters (and therefore won't be rewritten or used in the definition of the helper function)
         * l≡r is a term (whose variables are relative to Γᶜ) whose type is _≡_ and whose meaning is equivalent to the argument to rewrite
         * A is the type of either side of l≡r
         * L and R are of type A and express that L is to be rewritten as R
         * 𝐺 is the goal (to be rewritten)
         * the variables in l≡r, A, L, R, and 𝐺 are relative to Γᶜ
    -}
    record Request : Set where
      field
        m : Nat
        l≡r : Term
        A : Type
        L R : Type
        Γᶜ : List (Arg Type)
        𝐺 : Type

      generalisable-terms : List (Arg Type)
      generalisable-terms = ?

      w-dependent-terms : List (Arg Type)
      w-dependent-terms = ?

      w : Arg Type
      w = ?

      w-independent-terms : List (Arg Type)
      w-independent-terms = ?

      w≡R : Arg Type
      w≡R = ?

      SOLVER : Arg Type
      SOLVER = ? where

{-
      [iᶜ∣iᶜ∈FVᴬ] : VarSet
      [iᶜ∣iᶜ∈FVᴬ] = maybe [] id $ freeDependencies Γᶜ A -- TODO this is a hack; I don't expect freeDependencies will return 'nothing', but if it does, I hope(!) the rest of the computation will fail

      [iᶜ∣iᶜ∉FVᴬ] : VarSet
      [iᶜ∣iᶜ∉FVᴬ] = filter (not ∘ flip elem [iᶜ∣iᶜ∈FVᴬ]) (from 0 for (length Γᶜ))
-}
     Γ-reright = reverse (outer-most terms from Γᶜ up to but not including the minBoundVar) ++
                 [ w ] ++
                 reverse (everything else in weakenFrom ? 1 Γᶜ with [ w / L ]) ++
                 [ w ≡ R ] ++
                 [ SOLVER ]

     SOLVER = everything





-- {-
--     test₁₃-helper : (β χ : Level) -- anything needed to define w
--                     {w : Set (β ⊔ χ)} -- w
--                     (a₀¹ a₀² : A₀) → w ≡ C lzero (β ⊔ χ) (A₁ a₀²) → w -- everything else in the problem with L replaced with w
--                     → w ≡ C lzero (β ⊔ χ) (A₁ a₀²) -- w ≡ R
--                     → (C lzero (β ⊔ χ) (A₁ a₀²) -- problem terms that had a replacement (not including the l≡r term), with [ R / L ]
--                        → Nat → Σ Level (λ γ → C lzero (β ⊔ χ) (A₁ a₀²) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))) -- solution's goal, with [ R / L ]
--                       ) -- solution
--                     → Nat → Σ Level (λ γ → w ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))) -- goal, with [ w / L ]
--     test₁₃-helper β χ {.(C lzero (χ ⊔ β) (A₁ a₀²))} a₀¹ a₀² z x refl f = f x

--       test-helper : -- anything needed to define w (that isn't in the module)
--                     {w : Set (β ⊔ χ)} -- w
--                     -- everything else in the problem (that isn't in the module) with L replaced with w
--                     → w ≡ C lzero (β ⊔ χ) (A₁ a₀²) -- w ≡ R
--                     → ( -- problem terms (that aren't in the module) that had a replacement (not including the l≡r term)
--                        Nat → Σ Level (λ γ → C lzero (β ⊔ χ) (A₁ a₀²) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹)))) -- solution's goal
--                     → Nat → Σ Level (λ γ → w ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))) --goal
--       test-helper {._} refl f = f


      {- γᶜ' is an element of Γᶜ in which
           * γᶜᵢ is the iᶜ-th element of Γᶜ, weakened by iᶜ, so that we can imagine each element is referenced from the top-level
           *
      -}
      record γᶜ' : Set where
        field
          iᶜ : Nat
          γᶜᵢ : Arg Type
          γᶜᵢ∈Γʳ : Bool -- problem terms that had a replacement (not including the l≡r term)
          γᶜᵢ[w/L] : Arg Type

      {-# TERMINATING #-}
      Γᶜ' : List γᶜ'
      Γᶜ' = go 0 Γᶜ where
        go : Nat → List (Arg Type) → List γᶜ'
        go iᶜ [] = []
        go iᶜ (γᶜᵢ ∷ Γᶜ) = γᶜᵢ' ∷ go (suc iᶜ) (weaken 1 Γᶜ) where
          γᶜᵢ' = record
            { iᶜ = iᶜ
            ; γᶜᵢ = γᶜᵢ
            ; γᶜᵢ∈Γʳ = let gᶜᵢ = unArg γᶜᵢ in (isNo $ weaken 1 gᶜᵢ == weaken 1 gᶜᵢ r[ unknown / L ])
                                              &&
                                              (isNo $ l≡r == var₀ iᶜ)
            }

      [iʷ∣γᶜᵢ∈Γʳ] : VarSet
      [iʷ∣γᶜᵢ∈Γʳ] = iʷ <$> filter γᶜᵢ∈Γʳ Γᶜ' where open γᶜ'

      [iʷ] : List Nat
      [iʷ] = iʷ <$> Γᶜ' where open γᶜ'

      subsetList : {A : Set} → List A → List Nat → Maybe (List A)
      subsetList xs is = traverse (index xs) is

      module _ where
        private
          Γʷ/ᶜ : Maybe (List (Arg Type))
          Γʷ/ᶜ = go [iʷ] Γᶜ where
            go : List Nat → List (Arg Type) → Maybe (List (Arg Type))
            go _ [] = just []
            go [] _ = nothing
            go (iʷ ∷ [iʷ]) (γᶜᵢ ∷ Γᶜ) = _∷_ <$> (strengthen (suc iʷ) $ reorderVars [iʷ] <$> γᶜᵢ) <*> (go [iʷ] Γᶜ)

        Γʷ/ᴬ = join $ subsetList <$> Γʷ/ᶜ <*> pure [iᶜ∣iᶜ∈FVᴬ]
        Γʷ/⁻ᴬ = join $ subsetList <$> Γʷ/ᶜ <*> pure [iᶜ∣iᶜ∉FVᴬ]

      module _ where
        private
          --Lʷ : Term
          Lʷ = reorderVars [iʷ] L

        --Γʷ : Maybe (List (Arg Type))
        -- Γʷ = caseF Γʷ' of _R[ var₀ (length [iᶜ∣iᶜ∉FVᴬ]) / Lʷ ] where
        Γʷ = _R[ var₀ (length [iᶜ∣iᶜ∉FVᴬ]) / Lʷ ] <$> Γʷ' where
          Γʷ' : Maybe (List (Arg Type))
          Γʷ' = _++_ <$> Γʷ/⁻ᴬ
                         <*> (_∷_ <$> (strengthen (suc (length [iᶜ∣iᶜ∉FVᴬ])) $ hArg $ reorderVars [iʷ] A)
                                       <*>
                                       Γʷ/ᴬ
                             )

        𝐺ʷ = reorderVars [iʷ] 𝐺 r[ var₀ (length [iᶜ∣iᶜ∉FVᴬ]) / Lʷ ]

      module _ where
        private
          Rʷ = reorderVars [iʷ] R

        gʳ : Maybe Type
        gʳ = join $ go <$> gʳ' <*> pure [iʷ∣γᶜᵢ∈Γʳ] <*> pure 𝐺ʷʳ where
          go : List (Arg Type) → List Nat → Type → Maybe Type
          go [] [] 𝐺 = just 𝐺
          go (γʷ ∷ Γʷ) (iʷ ∷ iʷs) 𝐺 = go Γʷ iʷs $ pi (weaken (1 + iʷ) γʷ) $ abs "_" $ weaken 1 𝐺 r[ var₀ 0 / var₀ $ weaken 1 iʷ ]
          go _ _ _ = nothing

          gʳ' : Maybe (List (Arg Type))
          gʳ' = join $ subsetList <$> (caseF Γʷ of _R[ Rʷ / var₀ (length [iᶜ∣iᶜ∉FVᴬ]) ])
                                      <*>
                                      pure [iʷ∣γᶜᵢ∈Γʳ]

          𝐺ʷʳ = 𝐺ʷ r[ Rʷ / var₀ (length [iᶜ∣iᶜ∉FVᴬ]) ]

        helper-type : Maybe Type
        helper-type = telPi <$> (_++_ <$> (reverse <$> Γʷ)
                                          <*>
                                          (_∷_ <$> (pure $ vArg (def₂ (quote _≡_) (var₀ (length [iᶜ∣iᶜ∉FVᴬ])) Rʷ))
                                                   <*>
                                                   ([_] ∘ vArg <$> (weaken 1 <$> gʳ))
                                          )
                                )
                                <*>
                                pure (weaken 2 𝐺ʷ)

      make-vars-from-args : List Nat → List (Arg Type) → Maybe (List (Arg Type))
      make-vars-from-args [] [] = pure []
      make-vars-from-args (i ∷ is) (x ∷ xs) = _∷_ <$> pure (var₀ i <$ x) <*> make-vars-from-args is xs
      make-vars-from-args _ _ = nothing

      defineHelper : Bool → Name → TC ⊤
      defineHelper debug n =
        maybe (typeError ( strErr "error constructing helper function type, patterns, or term" ∷
                           strErr "\nhelper-type:" ∷ termErr (maybe unknown id helper-type) ∷
                           strErr "\n`helper-type:" ∷ termErr (` helper-type) ∷
                           strErr "\nhelper-patterns:" ∷ termErr (` helper-patterns) ∷
                           strErr "\nhelper-term:" ∷ termErr (maybe unknown id helper-term) ∷
                           strErr "\ngʳ:" ∷ termErr (` gʳ) ∷
                           strErr "\nΓʷ:" ∷ termErr (` Γʷ) ∷
                           strErr "\n𝐺ʷ:" ∷ termErr (` 𝐺ʷ) ∷
                           strErr "\nl≡r:" ∷ termErr (` l≡r) ∷
                           strErr "\nA:" ∷ termErr (` A) ∷
                           strErr "\nL:" ∷ termErr (` L) ∷
                           strErr "\nR:" ∷ termErr (` R) ∷
                           strErr "\nΓᶜ:" ∷ termErr (` Γᶜ) ∷
                           strErr "\n𝐺:" ∷ termErr (` 𝐺) ∷
                           strErr "\nΓʷ/ᴬ" ∷ termErr (` Γʷ/ᴬ) ∷
                           strErr "\nΓʷ/⁻ᴬ" ∷ termErr (` Γʷ/⁻ᴬ) ∷
                           strErr "\n[iᶜ∣iᶜ∈FVᴬ]" ∷ termErr (` [iᶜ∣iᶜ∈FVᴬ]) ∷
                           strErr "\n[iᶜ∣iᶜ∉FVᴬ]" ∷ termErr (` [iᶜ∣iᶜ∉FVᴬ]) ∷
                           strErr "\n[iʷ]" ∷ termErr (` [iʷ]) ∷
                           [] ))
              (λ {(helper-type , helper-patterns , helper-term) →
                catchTC
                  (define (vArg n) helper-type [ clause helper-patterns helper-term ] ~|
                   if debug then typeError [] else return tt
                   )
                  (typeError ( strErr "error defining helper function" ∷
                               strErr "\nhelper-type:" ∷ termErr helper-type ∷
                               strErr "\n`helper-type:" ∷ termErr (` helper-type) ∷
                               strErr "\nhelper-patterns:" ∷ termErr (` helper-patterns) ∷
                               strErr "\nhelper-term:" ∷ termErr helper-term ∷
                               strErr "\n`helper-term:" ∷ termErr (` helper-term) ∷
                               strErr "\ngʳ:" ∷ termErr (` gʳ) ∷
                               strErr "\nΓʷ:" ∷ termErr (` Γʷ) ∷
                               strErr "\n𝐺ʷ:" ∷ termErr (` 𝐺ʷ) ∷
                               strErr "\nl≡r:" ∷ termErr (` l≡r) ∷
                               strErr "\nA:" ∷ termErr (` A) ∷
                               strErr "\nL:" ∷ termErr (` L) ∷
                               strErr "\nR:" ∷ termErr (` R) ∷
                               strErr "\nΓᶜ:" ∷ termErr (` Γᶜ) ∷
                               strErr "\n𝐺:" ∷ termErr (` 𝐺) ∷
                               strErr "\nΓʷ/ᴬ" ∷ termErr (` Γʷ/ᴬ) ∷
                               strErr "\nΓʷ/⁻ᴬ" ∷ termErr (` Γʷ/⁻ᴬ) ∷
                               strErr "\n[iᶜ∣iᶜ∈FVᴬ]" ∷ termErr (` [iᶜ∣iᶜ∈FVᴬ]) ∷
                               strErr "\n[iᶜ∣iᶜ∉FVᴬ]" ∷ termErr (` [iᶜ∣iᶜ∉FVᴬ]) ∷
                               strErr "\n[iʷ]" ∷ termErr (` [iʷ]) ∷
                               [] ))
                  })
              (_,_ <$> helper-type <*> (_,_ <$> helper-patterns <*> helper-term))
        where

        helper-patterns : Maybe (List (Arg Pattern))
        helper-patterns = (λ pa w p-a pr → pa ++ w ∷ (p-a ++ pr)) <$> (telePat ∘ reverse <$> Γʷ/ᴬ)
                                                                      <*> just (hArg dot)
                                                                      <*> (telePat ∘ reverse <$> Γʷ/⁻ᴬ)
                                                                      <*> pure (vArg (con₀ (quote refl)) ∷ [ vArg (var "_") ])

        helper-term : Maybe Term
        helper-term =
          γʷs ← join $ subsetList <$> Γʷ <*> pure [iʷ∣γᶜᵢ∈Γʳ] -|
          iʷs ← make-vars-from-args [iʷ∣γᶜᵢ∈Γʳ] γʷs -|
          pure (var 0 (reverse (weaken 1 iʷs)))

      callHelper : Name → Tactic
      callHelper n hole =
        maybe (typeError [ strErr "error constructing helper call" ])
              (unify hole)
              $ helper-call n
        where

        helper-call : Name → Maybe Term
        helper-call n = def n <$> (reverse <$> (_∷_ <$> pure (vArg l≡r) <*> Γʰ)) where
          Γʰ : Maybe $ List $ Arg Term
          Γʰ = (λ xs → take (length [iᶜ∣iᶜ∉FVᴬ]) xs ++ hArg unknown ∷ drop (length [iᶜ∣iᶜ∉FVᴬ]) xs) <$> (join $ make-vars-from-args <$> pure ([iᶜ∣iᶜ∉FVᴬ] ++ [iᶜ∣iᶜ∈FVᴬ]) <*> Γʰ') where
            Γʰ' : Maybe (List (Arg Type))
            Γʰ' = _++_ <$> subsetList Γᶜ [iᶜ∣iᶜ∉FVᴬ] <*> subsetList Γᶜ [iᶜ∣iᶜ∈FVᴬ]

    inferGoal : Term → TC Type
    inferGoal hole = unPi =<< forceFun =<< inferType hole where
      unPi : Type → TC Type
      unPi (pi _ (abs _ (meta x _))) = blockOnMeta! x
      unPi (pi _ (abs _ b)) = maybe (typeError (strErr "error strengthening" ∷ termErr b ∷ [])) pure $ strengthen 1 b
      unPi x = typeError (strErr "goal is not a pi type" ∷ termErr x ∷ [])

    getRequest : Nat → Term → Term → TC Request
    getRequest m l≡r hole = do
      L≡R ← inferType l≡r -|
      L≡R-matched ← maybe (typeError (strErr "not an equality" ∷ termErr l≡r ∷ termErr L≡R ∷ [])) pure $
        match 3 (def (quote _≡_) (hArg unknown ∷ (hArg (var₀ 0)) ∷ (vArg (var₀ 1)) ∷ (vArg (var₀ 2)) ∷ [])) L≡R -|
      𝐺 ← inferGoal hole -|
      Γᶜ ← getContext -|
      case L≡R-matched of λ { (A ∷ L ∷ R ∷ []) →
        pure $ record { m = m ; l≡r = l≡r ; A = A ; L = L ; R = R ; Γᶜ = (reverse (drop 6 (reverse Γᶜ))) ; 𝐺 = 𝐺 } }

  macro
    reright : Nat → Term → Tactic
    reright m l≡r hole =
      q ← getRequest m l≡r hole -|
      n ← freshName "reright" -|
      let open Request q in
      defineHelper false n ~|
      callHelper n hole

    reright' : Nat → Term → Tactic
    reright' m l≡r hole =
      q ← getRequest m l≡r hole -|
      n ← freshName "reright" -|
--      let open Request q in
      Request.defineHelper q true n ~|
      Request.callHelper q n hole

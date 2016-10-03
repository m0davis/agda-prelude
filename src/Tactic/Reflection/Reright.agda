module Tactic.Reflection.Reright where
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
-}
    reorderVars : List (Nat × Nat) → Term → Term
    reorderVars xs t = reorderVars' 99 0 xs t

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
      Γ[w/L]×indexes[Γ] = go 0 0 [] Γ where
        go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat)
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
            (γ'[w'/L'][reordered] , i) ∷ go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs
          else
            go (suc i) j (weakenOrder osⱼ) γs
      -}
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
              γ'[w'/L'][reordered] = reorderVars osⱼ <$> γ'[w'/L']
              γ≢l≡r = isNo $ var₀ (n - i) == l≡r
              γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
          in
          case γ≢l≡r && γ'≠γ'[w'/L'][reordered] of λ {
            true → (γ'[w'/L'][reordered] , i) ∷ go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs
          ; false → go (suc i) j (weakenOrder osⱼ) γs }
      -}

      {-
      Γ[w/L]×indexes[Γ]  : List (Arg Type × Nat)
      Γ[w/L]×indexes[Γ] = go 0 0 [] Γ where
        go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat)
        go _ _ _ [] = []
        go i j osⱼ (γ ∷ γs) with length Γ - 1
        ... | n with weaken (2 + j) L
        ... | L' with weaken ((n - i) + 3 + j) γ
        ... | γ' with (let w' = var₀ (suc j)
                       in let γ'[w'/L'] = γ' r[ w' / L' ]
                       in reorderVars osⱼ <$> γ'[w'/L'])
        ... | γ'[w'/L'][reordered] with (let γ≢l≡r = isNo $ var₀ (n - i) == l≡r
                                         in let γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
                                         in γ≢l≡r && γ'≠γ'[w'/L'][reordered])
        ... | true = (γ'[w'/L'][reordered] , i) ∷ go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs
        ... | false = go (suc i) j (weakenOrder osⱼ) γs

      Γ[w/L] : List (Arg Type)
      Γ[w/L] = fst <$> (Γ[w/L]×indexes[Γ])

      indexes[Γ] : List Nat
      indexes[Γ] = snd <$> (Γ[w/L]×indexes[Γ])

      ∣Γᴸ∣ = length Γ[w/L]
      -}

      Γ[w/L]×indexes[Γ]'  : Nat × List (Arg Type × Nat)
      Γ[w/L]×indexes[Γ]' = go 0 0 [] Γ where
        go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → Nat × List (Arg Type × Nat)
        go _ _ _ [] = 0 , []
        go i j osⱼ (γ ∷ γs) with length Γ - 1
        ... | n with weaken (2 + j) L
        ... | L' with weaken ((n - i) + 3 + j) γ
        ... | γ' with (let w' = var₀ (suc j)
                       in let γ'[w'/L'] = γ' r[ w' / L' ]
                       in reorderVars osⱼ <$> γ'[w'/L'])
        ... | γ'[w'/L'][reordered] with (let γ≢l≡r = isNo $ var₀ (n - i) == l≡r
                                         in let γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
                                         in γ≢l≡r && γ'≠γ'[w'/L'][reordered])
        ... | true = let foo = go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs in (suc (length (snd foo)) , (γ'[w'/L'][reordered] , i) ∷ snd foo)
        ... | false = go (suc i) j (weakenOrder osⱼ) γs

      Γ[w/L]×indexes[Γ] : List (Arg Type × Nat)
      Γ[w/L]×indexes[Γ] = snd Γ[w/L]×indexes[Γ]'
{-
      everything : List (Arg Type × Nat) × Type
      everything with Γ[w/L]×indexes[Γ]'
      ... | (|l| , Γw) = Γw , 𝐺[w/L]
        where
        𝐺[w/L] : Type
        𝐺[w/L] with 2 + |l| | 3 + |l|
        ... | l | r =
          let
              LL = length (fst <$> Γw) -- l
              os = go 0 (snd <$> Γw) []
              𝐺' = (weaken (3 + LL) 𝐺) r[ var₀ LL / weaken r L ]
                   --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / weaken (3 + ∣Γᴸ∣) L ]
                   --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / (weaken $! (3 + ∣Γᴸ∣)) L ]
                   --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / weaken 4 L ]
                   --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ 3 / weaken 4 L ]
                   --𝐺 r[ var₀ 0 / L ]
          in
            reorderVars os 𝐺'
          where
          go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
          go _ [] ns = ns
          go j (i ∷ is) ns = go (suc j) is $ (1 + |l| + 2 + (length Γ - 1) - i , 1 + (|l| - 1) - j) ∷ ns
-}
{-
      |l| = fst Γ[w/L]×indexes[Γ]'
      Γw = snd Γ[w/L]×indexes[Γ]'
      biggies = fst <$> Γw
      sizeofit = length biggies

      everything : List (Arg Type × Nat) × Type
      everything = Γw , 𝐺[w/L]
        where
        𝐺[w/L] : Type
        𝐺[w/L] with 2 + |l| | 3 + |l|
        ... | l | r =
          let
              LL = sizeofit -- length (fst <$> Γw) -- l
              os = go 0 (snd <$> Γw) []
              𝐺' = (weaken (3 + LL) 𝐺) r[ var₀ LL / weaken r L ]
                   --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / weaken (3 + ∣Γᴸ∣) L ]
                   --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / (weaken $! (3 + ∣Γᴸ∣)) L ]
                   --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / weaken 4 L ]
                   --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ 3 / weaken 4 L ]
                   --𝐺 r[ var₀ 0 / L ]
          in
            reorderVars os 𝐺'
          where
          go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
          go _ [] ns = ns
          go j (i ∷ is) ns = go (suc j) is $ (1 + |l| + 2 + (length Γ - 1) - i , 1 + (|l| - 1) - j) ∷ ns
-}

      {-
      something : Nat × List (Arg Type × Nat)
      something = (0 , go 0 0 [] Γ) where
          go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat)
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
              (γ'[w'/L'][reordered] , i) ∷ go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs
            else
              go (suc i) j (weakenOrder osⱼ) γs
      -}

-- TODO: Using this first "something" makes it fast to evaluate ` 𝐺[w/L] ...

      something-fast  : Nat × List (Arg Type × Nat)
      something-fast = go 0 0 [] Γ where
        go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → Nat × List (Arg Type × Nat)
        go _ _ _ [] = 0 , []
        go i j osⱼ (γ ∷ γs) with length Γ - 1
        ... | n with weaken (2 + j) L
        ... | L' with weaken ((n - i) + 3 + j) γ
        ... | γ' with (let w' = var₀ (suc j)
                       in let γ'[w'/L'] = γ' r[ w' / L' ]
                       in reorderVars osⱼ <$> γ'[w'/L'])
        ... | γ'[w'/L'][reordered] with (let γ≢l≡r = isNo $ var₀ (n - i) == l≡r
                                         in let γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
                                         in γ≢l≡r && γ'≠γ'[w'/L'][reordered])
        ... | true = let foo = go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs in (suc (length (snd foo)) , (γ'[w'/L'][reordered] , i) ∷ snd foo)
        ... | false = go (suc i) j (weakenOrder osⱼ) γs

-- ... but this second "something" makes it slow. Why?
      something-slow  : Nat × List (Arg Type × Nat)
      something-slow = let asdf = go 0 0 [] Γ in (length asdf , asdf) where
        go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat)
        go _ _ _ [] = []
        go i j osⱼ (γ ∷ γs) with length Γ - 1
        ... | n with weaken (2 + j) L
        ... | L' with weaken ((n - i) + 3 + j) γ
        ... | γ' with (let w' = var₀ (suc j)
                       in let γ'[w'/L'] = γ' r[ w' / L' ]
                       in reorderVars osⱼ <$> γ'[w'/L'])
        ... | γ'[w'/L'][reordered] with (let γ≢l≡r = isNo $ var₀ (n - i) == l≡r
                                         in let γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
                                         in γ≢l≡r && γ'≠γ'[w'/L'][reordered])
        ... | true = let foo = go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs in (γ'[w'/L'][reordered] , i) ∷ foo
        ... | false = go (suc i) j (weakenOrder osⱼ) γs

      everything : List (Arg Type × Nat) × Type × List (Arg Type)
      everything
       with something-slow
      ... | (_ , Γw)
       with fst <$> Γw
      ... | biggies
       with length biggies
      ... | |l| = Γw , 𝐺[w/L] , Γ[R/L]
        where

        Γ[R/L] : List (Arg Type)
        Γ[R/L] = go |l| 0 biggies where
  {-
        Γ[R/L] {-with length (snd Γ[w/L]×indexes[Γ]')
        ... | ∣Γᴸ∣-} = go 0 Γ[w/L] where
  -}
          go : Nat → Nat → List (Arg Type) → List (Arg Type)
          go _ _ [] = []
          go |l| i (γ ∷ γs) =
            -- γ is the index[γ]ᵗʰ element of Γ[w/L]
            let ∣Γᴸ∣ = |l|
                --∣Γᴸ∣ = length (snd things)
                --∣Γᴸ∣ = case things of λ { (_ , asdf) → length asdf }
                n = ∣Γᴸ∣ - 1
                γ' = weakenFrom i ∣Γᴸ∣ γ
                w' = var₀ (i + n + 2)
                R' = weaken (2 + ∣Γᴸ∣ + i) R
                γ'[R'/w'] = γ' r[ R' / w' ]
            in
              γ'[R'/w'] ∷ go |l| (suc i) γs

        𝐺[w/L] : Type
        𝐺[w/L] with 2 + |l| | 3 + |l|
        ... | l | r =
          let
              LL = 2 + |l|
                   -- length (fst <$> Γw) -- l
                   --length (fst <$> (snd Γ[w/L]×indexes[Γ]'))
              os = go 0 (snd <$> Γw) []
              𝐺' = (weaken (3 + |l|) 𝐺) r[ var₀ LL / weaken r L ]
                   --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / weaken (3 + ∣Γᴸ∣) L ]
                   --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / (weaken $! (3 + ∣Γᴸ∣)) L ]
                   --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / weaken 4 L ]
                   --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ 3 / weaken 4 L ]
                   --𝐺 r[ var₀ 0 / L ]
          in
            reorderVars os 𝐺'
          where
          go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
          go _ [] ns = ns
          go j (i ∷ is) ns = go (suc j) is $ (1 + |l| + 2 + (length Γ - 1) - i , 1 + (|l| - 1) - j) ∷ ns

      Γ[w/L] : List (Arg Type)
      Γ[w/L] = fst <$> (fst everything)

      indexes[Γ] : List Nat
      --indexes[Γ] = snd <$> (fst everything)
      indexes[Γ] with everything
      ... | (ind , _) = snd <$> ind

      ∣Γᴸ∣ : Nat
      ∣Γᴸ∣ with Γ[w/L]×indexes[Γ]'
      ... | things with things
      ... | (_ , stuff) with length stuff
      ... | l = l
      --∣Γᴸ∣ = length Γ[w/L]

      𝐺[w/L] : Type
      𝐺[w/L] = fst (snd everything)

      --postulate Γ[R/L] : List (Arg Type)
      Γ[R/L] : List (Arg Type)
      Γ[R/L] = snd (snd everything)

{-
      Γ[w/L]×indexes[Γ]  : List (Arg Type × Nat)
      Γ[w/L]×indexes[Γ] = go 0 0 [] Γ where
        go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → (Maybe (Maybe (Arg Type × Nat)) → Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat)
        go _ _ _ [] = []
        go i j osⱼ (γ ∷ γs) with length Γ - 1
        ... | n with weaken (2 + j) L
        ... | L' with weaken ((n - i) + 3 + j) γ
        ... | γ' with (let w' = var₀ (suc j)
                       in let γ'[w'/L'] = γ' r[ w' / L' ]
                       in reorderVars osⱼ <$> γ'[w'/L'])
        ... | γ'[w'/L'][reordered] with (let γ≢l≡r = isNo $ var₀ (n - i) == l≡r
                                         in let γ'≠γ'[w'/L'][reordered] = isNo $ γ' == γ'[w'/L'][reordered]
                                         in γ≢l≡r && γ'≠γ'[w'/L'][reordered])
        ... | true = (γ'[w'/L'][reordered] , i) ∷ go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs
        ... | false = go (suc i) j (weakenOrder osⱼ) γs

      𝐺[w/L] : Type
      𝐺[w/L] with 2 + ∣Γᴸ∣ | 3 + ∣Γᴸ∣
      ... | l | r =
        let os = go 0 indexes[Γ] []
            𝐺' = (weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ l / weaken r L ]
                 --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / weaken (3 + ∣Γᴸ∣) L ]
                 --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / (weaken $! (3 + ∣Γᴸ∣)) L ]
                 --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / weaken 4 L ]
                 --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ 3 / weaken 4 L ]
                 --𝐺 r[ var₀ 0 / L ]
        in
          {-reorderVars os-} 𝐺'
        where

        go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
        go _ [] ns = ns
        go j (i ∷ is) ns = go (suc j) is $ (1 + ∣Γᴸ∣ + 2 + (length Γ - 1) - i , 1 + (∣Γᴸ∣ - 1) - j) ∷ ns
-}



      {-
         <---------------------- helper-type------------------ ... -->
               <---- Γ[w/L] ----->   <------ Γ[R/L] ------->
         w w≡R γ₀ γ₁ ... γᵢ ... γₙ ( γ'₀ γ'₁ ... γ'ᵢ ... γ'ₙ )
         n = ∣Γᴸ∣ - 1 = length Γ[w/L] - 1
      -}
{-
      Γ[R/L] : List (Arg Type)
      Γ[R/L] = go 0 Γ[w/L] where
{-
      Γ[R/L] {-with length (snd Γ[w/L]×indexes[Γ]')
      ... | ∣Γᴸ∣-} = go 0 Γ[w/L] where
-}
        go : Nat → List (Arg Type) → List (Arg Type)
        go _ [] = []
        go i (γ ∷ γs) =
          -- γ is the index[γ]ᵗʰ element of Γ[w/L]
          let --∣Γᴸ∣ = length stuff
              --∣Γᴸ∣ = length (snd things)
              --∣Γᴸ∣ = case things of λ { (_ , asdf) → length asdf }
              n = ∣Γᴸ∣ - 1
              γ' = weakenFrom i ∣Γᴸ∣ γ
              w' = var₀ (i + n + 2)
              R' = weaken (2 + ∣Γᴸ∣ + i) R
              γ'[R'/w'] = γ' r[ R' / w' ]
          in
            γ'[R'/w'] ∷ go (suc i) γs
-}
      {-
         Γ             Γ[w/L]   Γ[R/L]
         0 ... n w w≡R 0 ... m (0 ... m → 𝐺[R/L]) → 𝐺[w/L]
      -}
      𝐺[R/L] : Type
      𝐺[R/L] with everything
      ... | things with things
      ... | (stuff , _) with length stuff
      ... | ∣Γᴸ∣ =
        let os = go 0 indexes[Γ] []
            𝐺' = weaken (2 * ∣Γᴸ∣ + 2) (𝐺 r[ R / L ])
        in
          reorderVars os 𝐺'
        where

        go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
        go _ [] ns = ns
        go j (i ∷ is) ns = go (suc j) is $ (2 * ∣Γᴸ∣ + 2 + (length Γ - 1) - i , (∣Γᴸ∣ - 1) - j) ∷ ns
{-
      𝐺[w/L] : Type
      𝐺[w/L] =
        let os = go 0 indexes[Γ] []
            𝐺' = --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / weaken (3 + ∣Γᴸ∣) L ]
                 --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / (weaken $! (3 + ∣Γᴸ∣)) L ]
                 --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / weaken 4 L ]
                 (weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ 3 / weaken 4 L ]
                 --𝐺 r[ var₀ 0 / L ]
        in
          {-reorderVars os-} 𝐺'
        where

        go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
        go _ [] ns = ns
        go j (i ∷ is) ns = go (suc j) is $ (1 + ∣Γᴸ∣ + 2 + (length Γ - 1) - i , 1 + (∣Γᴸ∣ - 1) - j) ∷ ns
-}
{-
      𝐺[w/L] : Type
      𝐺[w/L] with 2 + ∣Γᴸ∣ | 3 + ∣Γᴸ∣
      ... | l | r =
        let os = go 0 indexes[Γ] []
            𝐺' = (weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ l / weaken r L ]
                 --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / weaken (3 + ∣Γᴸ∣) L ]
                 --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / (weaken $! (3 + ∣Γᴸ∣)) L ]
                 --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ (2 + ∣Γᴸ∣) / weaken 4 L ]
                 --(weaken (3 + ∣Γᴸ∣) 𝐺) r[ var₀ 3 / weaken 4 L ]
                 --𝐺 r[ var₀ 0 / L ]
        in
          {-reorderVars os-} 𝐺'
        where

        go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
        go _ [] ns = ns
        go j (i ∷ is) ns = go (suc j) is $ (1 + ∣Γᴸ∣ + 2 + (length Γ - 1) - i , 1 + (∣Γᴸ∣ - 1) - j) ∷ ns
-}



{-
      [Γ[w/L]×indexes[Γ]]  : List (Arg Type × Nat)
      [Γ[w/L]×indexes[Γ]] = go 0 0 [] Γ where
        go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat)
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
            (γ'[w'/L'][reordered] , i) ∷ go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs
          else
            go (suc i) j (weakenOrder osⱼ) γs

      [Γ[w/L]] : List (Arg Type)
      [Γ[w/L]] = fst <$> [Γ[w/L]×indexes[Γ]]

      [indexes[Γ]] : List Nat
      [indexes[Γ]] = snd <$> [Γ[w/L]×indexes[Γ]]

      [|Γᴸ∣] : Nat
      [|Γᴸ∣] = length [Γ[w/L]]
{-
      [𝐺[w/L]] : Type
      [𝐺[w/L]] =
        let os = go 0 [indexes[Γ]] []
            𝐺' = (weaken (3 + [|Γᴸ∣]) 𝐺) r[ var₀ (2 + [|Γᴸ∣]) / weaken (3 + [|Γᴸ∣]) L ]
        in
          reorderVars os 𝐺'
        where

        go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
        go _ [] ns = ns
        go j (i ∷ is) ns = go (suc j) is $ (1 + [|Γᴸ∣] + 2 + (length Γ - 1) - i , 1 + ([|Γᴸ∣] - 1) - j) ∷ ns
-}
      [𝐺[w/L]] : Type
      [𝐺[w/L]] with [Γ[w/L]×indexes[Γ]]
      ... | [Γ[w/L]×indexes[Γ]] with fst <$> [Γ[w/L]×indexes[Γ]] | snd <$> [Γ[w/L]×indexes[Γ]]
      ... | [Γ[w/L]] | [indexes[Γ]] with length [Γ[w/L]]
      ... | [|Γᴸ∣] =
        let os = go 0 [indexes[Γ]] []
            𝐺' = (weaken (3 + [|Γᴸ∣]) 𝐺) r[ var₀ (2 + [|Γᴸ∣]) / weaken (3 + [|Γᴸ∣]) L ]
        in
          reorderVars os 𝐺'
        where

        go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
        go _ [] ns = ns
        go j (i ∷ is) ns = go (suc j) is $ (1 + [|Γᴸ∣] + 2 + (length Γ - 1) - i , 1 + ([|Γᴸ∣] - 1) - j) ∷ ns
-}

{-
      record ALLOFIT : Set where
        [Γ[w/L]×indexes[Γ]] : List (Arg Type × Nat)
        [Γ[w/L]×indexes[Γ]] = go 0 0 [] Γ where
          go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat)
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
              (γ'[w'/L'][reordered] , i) ∷ go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs
            else
              go (suc i) j (weakenOrder osⱼ) γs

        [Γ[w/L]] : List (Arg Type)
        [Γ[w/L]] = fst <$> [Γ[w/L]×indexes[Γ]]
{-
        [Γ[w/L]] : List (Arg Type)
        [Γ[w/L]] = fst <$> [Γ[w/L]×indexes[Γ]]
-}

        [indexes[Γ]] : List Nat
        [indexes[Γ]] = snd <$> [Γ[w/L]×indexes[Γ]]

        [|Γᴸ∣] : Nat
        [|Γᴸ∣] = length [Γ[w/L]]
  {-
        [𝐺[w/L]] : Type
        [𝐺[w/L]] =
          let os = go 0 [indexes[Γ]] []
              𝐺' = (weaken (3 + [|Γᴸ∣]) 𝐺) r[ var₀ (2 + [|Γᴸ∣]) / weaken (3 + [|Γᴸ∣]) L ]
          in
            reorderVars os 𝐺'
          where

          go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
          go _ [] ns = ns
          go j (i ∷ is) ns = go (suc j) is $ (1 + [|Γᴸ∣] + 2 + (length Γ - 1) - i , 1 + ([|Γᴸ∣] - 1) - j) ∷ ns
  -}
        [𝐺[w/L]] : Type
        [𝐺[w/L]] with [Γ[w/L]×indexes[Γ]]
        ... | [Γ[w/L]×indexes[Γ]] with fst <$> [Γ[w/L]×indexes[Γ]] | snd <$> [Γ[w/L]×indexes[Γ]]
        ... | [Γ[w/L]] | [indexes[Γ]] with length [Γ[w/L]]
        ... | [|Γᴸ∣] =
          let os = go 0 [indexes[Γ]] []
              𝐺' = (weaken (3 + [|Γᴸ∣]) 𝐺) r[ var₀ (2 + [|Γᴸ∣]) / weaken (3 + [|Γᴸ∣]) L ]
          in
            reorderVars os 𝐺'
          where

          go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
          go _ [] ns = ns
          go j (i ∷ is) ns = go (suc j) is $ (1 + [|Γᴸ∣] + 2 + (length Γ - 1) - i , 1 + ([|Γᴸ∣] - 1) - j) ∷ ns

      open ALLOFIT record {} public
-}

      record ALLOFIT : Set where
        inductive
        field
          [Γ[w/L]×indexes[Γ]] : List (Arg Type × Nat)
          [Γ[w/L]] : List (Arg Type)
          [indexes[Γ]] : List Nat
          [|Γᴸ∣] : Nat
          [𝐺[w/L]] : Type

      itsme : ALLOFIT
      ALLOFIT.[Γ[w/L]×indexes[Γ]] itsme = go 0 0 [] Γ where
          go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat)
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
              (γ'[w'/L'][reordered] , i) ∷ go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs
            else
              go (suc i) j (weakenOrder osⱼ) γs
      ALLOFIT.[Γ[w/L]] itsme = fst <$> ALLOFIT.[Γ[w/L]×indexes[Γ]] itsme
      ALLOFIT.[indexes[Γ]] itsme = snd <$> ALLOFIT.[Γ[w/L]×indexes[Γ]] itsme
      ALLOFIT.[|Γᴸ∣] itsme = length (ALLOFIT.[Γ[w/L]] itsme)
      ALLOFIT.[𝐺[w/L]] itsme
       with ALLOFIT.[Γ[w/L]×indexes[Γ]] itsme
      ... | [Γ[w/L]×indexes[Γ]]
       with fst <$> [Γ[w/L]×indexes[Γ]] | snd <$> [Γ[w/L]×indexes[Γ]]
      ... | [Γ[w/L]] | [indexes[Γ]]
       with length [Γ[w/L]]
      ... | [|Γᴸ∣] =
{-
      ALLOFIT.[𝐺[w/L]] itsme with ALLOFIT.[|Γᴸ∣] itsme
      ... | [|Γᴸ∣] =
-}
        --let os = go 0 (snd <$> [Γ[w/L]×indexes[Γ]]) []
        let os = go 0 [indexes[Γ]] []
            --[|Γᴸ∣] = ALLOFIT.[|Γᴸ∣] itsme
            𝐺' = (weaken (3 + [|Γᴸ∣]) 𝐺) r[ var₀ (2 + [|Γᴸ∣]) / weaken (3 + [|Γᴸ∣]) L ] --
        in
          reorderVars os 𝐺'
        where
        go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
        go _ [] ns = ns
        go j (i ∷ is) ns =
          --let [|Γᴸ∣] = ALLOFIT.[|Γᴸ∣] itsme
          --in
          go (suc j) is $ (1 + [|Γᴸ∣] + 2 + (length Γ - 1) - i , 1 + ([|Γᴸ∣] - 1) - j) ∷ ns

{-
        [Γ[w/L]×indexes[Γ]] : List (Arg Type × Nat)
        [Γ[w/L]×indexes[Γ]] = go 0 0 [] Γ where
          go : Nat → Nat → List (Nat × Nat) → List (Arg Type) → List (Arg Type × Nat)
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
              (γ'[w'/L'][reordered] , i) ∷ go (suc i) (suc j) ((j + 3 + n - i , 0) ∷ weakenOrder osⱼ) γs
            else
              go (suc i) j (weakenOrder osⱼ) γs

        [Γ[w/L]] : List (Arg Type)
        [Γ[w/L]] = fst <$> [Γ[w/L]×indexes[Γ]]
{-
        [Γ[w/L]] : List (Arg Type)
        [Γ[w/L]] = fst <$> [Γ[w/L]×indexes[Γ]]
-}

        [indexes[Γ]] : List Nat
        [indexes[Γ]] = snd <$> [Γ[w/L]×indexes[Γ]]

        [|Γᴸ∣] : Nat
        [|Γᴸ∣] = length [Γ[w/L]]
  {-
        [𝐺[w/L]] : Type
        [𝐺[w/L]] =
          let os = go 0 [indexes[Γ]] []
              𝐺' = (weaken (3 + [|Γᴸ∣]) 𝐺) r[ var₀ (2 + [|Γᴸ∣]) / weaken (3 + [|Γᴸ∣]) L ]
          in
            reorderVars os 𝐺'
          where

          go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
          go _ [] ns = ns
          go j (i ∷ is) ns = go (suc j) is $ (1 + [|Γᴸ∣] + 2 + (length Γ - 1) - i , 1 + ([|Γᴸ∣] - 1) - j) ∷ ns
  -}
        [𝐺[w/L]] : Type
        [𝐺[w/L]] with [Γ[w/L]×indexes[Γ]]
        ... | [Γ[w/L]×indexes[Γ]] with fst <$> [Γ[w/L]×indexes[Γ]] | snd <$> [Γ[w/L]×indexes[Γ]]
        ... | [Γ[w/L]] | [indexes[Γ]] with length [Γ[w/L]]
        ... | [|Γᴸ∣] =
          let os = go 0 [indexes[Γ]] []
              𝐺' = (weaken (3 + [|Γᴸ∣]) 𝐺) r[ var₀ (2 + [|Γᴸ∣]) / weaken (3 + [|Γᴸ∣]) L ]
          in
            reorderVars os 𝐺'
          where

          go : Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
          go _ [] ns = ns
          go j (i ∷ is) ns = go (suc j) is $ (1 + [|Γᴸ∣] + 2 + (length Γ - 1) - i , 1 + ([|Γᴸ∣] - 1) - j) ∷ ns
-}
      open ALLOFIT itsme public



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
                  strErr "\nlength Γ:"       ∷ termErr (` (length Γ))           ∷
                  strErr "\n𝐺:"              ∷ termErr (` 𝐺)                   ∷

                  --strErr "\nΓ[w/L]:"         ∷ termErr (` [Γ[w/L]])               ∷
                  --strErr "\nindexes[Γ]:"     ∷ termErr (` [indexes[Γ]])           ∷
                  --strErr "\n∣Γᴸ∣:"           ∷ termErr (` [|Γᴸ∣])                 ∷
                  --strErr "\n𝐺[w/L]:"         ∷ termErr (` [𝐺[w/L]])               ∷


                  strErr "\nΓ[w/L]:"         ∷ termErr (` Γ[w/L])               ∷
                  --strErr "\nindexes[Γ]:"     ∷ termErr (` indexes[Γ])           ∷
                  --strErr "\n∣Γᴸ∣:"           ∷ termErr (` ∣Γᴸ∣)                 ∷
                  strErr "\n𝐺[w/L]:"         ∷ termErr (` 𝐺[w/L])               ∷
                  strErr "\nΓ[R/L]:"         ∷ termErr (` Γ[R/L])               ∷


                  {-
                  strErr "\nΓ[w/L]:"         ∷ termErr (` Γ[w/L])               ∷
                  strErr "\nindexes[Γ]:"     ∷ termErr (` indexes[Γ])           ∷
                  strErr "\n∣Γᴸ∣:"           ∷ termErr (` ∣Γᴸ∣)                 ∷
                  strErr "\nΓ[R/L]:"         ∷ termErr (` Γ[R/L])               ∷
                  strErr "\n𝐺[R/L]:"         ∷ termErr (` 𝐺[R/L])               ∷
                  strErr "\n𝐺[w/L]:"         ∷ termErr (` 𝐺[w/L])               ∷
                  -}
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

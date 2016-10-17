--{-# OPTIONS --show-implicit #-}
module Reright where
  open import Prelude
  open import Tactic.Reflection.Reright
  open import Agda.Builtin.Reflection
  open import Tactic.Reflection
  open import Tactic.Reflection.Quote

  module Benchmarks where
    foo : (A : Set) (x y : A) (F : A → A → Set) →

          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →

          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →

          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →

          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →

          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →

          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
          (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →

          x ≡ y →

          F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y →

          Set
    foo A x y F
        _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _
        x≡y = reright-debug x≡y {!!}





-- -- --   macro
-- -- --     debug-rewrite : Name → Nat → Tactic
-- -- --     debug-rewrite function-name clause-index hole = do
-- -- --       function-clauses ← getClauses function-name -|
-- -- --       case index function-clauses clause-index of λ
-- -- --         { (just (clause _ (def rewrite-name _))) → do
-- -- --             rewrite-clauses ← getClauses rewrite-name -|
-- -- --             rewrite-type ← getType rewrite-name -|
-- -- --             typeError ( termErr (` function-clauses) ∷
-- -- --                         termErr (  rewrite-type) ∷
-- -- --                         termErr (` rewrite-type) ∷
-- -- --                         termErr (` rewrite-clauses) ∷
-- -- --                         [] )
-- -- --         ; _ → return _ -- typeError [ termErr (` function-clauses) ]
-- -- --         }

-- -- --   module S₀ where
-- -- --     -rewrite -rewrite' -reright' -reright :
-- -- --       {!!}

-- -- --     -rewrite = {!debug-rewrite -rewrite 0!}

-- -- --     -rewrite' = {!helper!} where
-- -- --       helper : {!!}
-- -- --       helper = {!!}

-- -- --     -reright' = {!helper!} where
-- -- --       helper : {!!}
-- -- --       helper = {!!}

-- -- --     -reright = {!reright ? ?!}

-- -- --   module S₁₋₀ where
-- -- --     postulate
-- -- --       L : Set
-- -- --       R : Set
-- -- --       L≡R : L ≡ R
-- -- --       F : (A : Set) (x y : A) → Set

-- -- --     -rewrite -rewrite' -reright' -reright :
-- -- --       (l : L) → F L l l

-- -- --     -rewrite l rewrite L≡R = {!debug-rewrite -rewrite 0!}

-- -- --     -rewrite' l = helper L L≡R l where
-- -- --       helper : (w : Set) (w₁ : w ≡ R) (l₁ : w) → F w l₁ l₁
-- -- --       helper ._ refl l = {!!}

-- -- --     -reright' l = helper L L≡R l {!!} where
-- -- --       helper : (w : Set) (w≡R : w ≡ R) →
-- -- --                (l' : w) →
-- -- --                ((l'' : R) →
-- -- --                 F R l'' l'') →
-- -- --                F w l' l'
-- -- --       helper ._ refl l' f = f l'

-- -- --     -reright l = reright L≡R {!!}

--   module S₁₋₁ where
--     -rewrite -rewrite' -reright' -reright :
--       (L : Set) (R : Set) (L≡R : L ≡ R) (G : L → Set) (l : L) → (Gl : G l) (F : (A : Set) (x y : A) → G l → Set) → F L l l Gl

--     -rewrite L R L≡R G l Gl F rewrite L≡R = {!debug-rewrite -rewrite 0!}

--     -rewrite' L R L≡R G l Gl F = {-helper-} {!!} where
--       helper : {!!}
--       helper = {!!}

--     -reright' L R L≡R G l Gl F = helper {_} L≡R G l Gl F {!!} where
--       helper : {w : Set} (w≡R : w ≡ R) →
--                (G' : w → Set)
--                (l' : w)
--                (Gl' : G' l')
--                (F' : (A : Set) (x y : A) → G' l' → Set) →
--                ((G'' : R → Set)
--                 (l'' : R)
--                 (Gl'' : G'' l'')
--                 (F'' : (A : Set) (x y : A) → G'' l'' → Set) →
--                 F'' R l'' l'' Gl'') →
--                F' w l' l' Gl'
--       helper {._} refl G' l' Gl' F' φ = φ G' l' Gl' F'

--     -reright L R L≡R G l Gl F = {!!} -- reright L≡R {!!}

-- {-
-- helper-type:
-- {A : Set} (z : A ≡ R) (f : (z₁ : A) → Set) (z₁ : A) (z₂ : f z₁)
-- (f₁ : (A₁ : Set) (x y : A₁) (z₃ : f z₁) → Set)
-- (f₂
--  : (f₃ : (z₃ : R) → Set) (z₃ : R) (z₄ : f₃ z₃)
--    (f₄ : (A₁ : Set) (x y : A₁) (z₅ : f₃ z₃) → Set) →
--    f₃ R z₄ z₄ z₃) →
-- f₁ A z₁ z₁ z₂
-- helper-patterns:
-- arg (arg-info hidden relevant) dot ∷
-- arg (arg-info visible relevant) (con (quote refl) []) ∷
-- arg (arg-info visible relevant) (var "_") ∷
-- arg (arg-info visible relevant) (var "_") ∷
-- arg (arg-info visible relevant) (var "_") ∷
-- arg (arg-info visible relevant) (var "_") ∷
-- arg (arg-info visible relevant) (var "_") ∷ []
-- helper-term:
-- var 0
-- (arg (arg-info visible relevant) (var 4 []) ∷
--  arg (arg-info visible relevant) (var 3 []) ∷
--  arg (arg-info visible relevant) (var 2 []) ∷
--  arg (arg-info visible relevant) (var 1 []) ∷ [])
-- helper-call-args:
-- arg (arg-info hidden relevant) unknown ∷
-- arg (arg-info visible relevant) (var 4 []) ∷
-- arg (arg-info visible relevant) (var 3 []) ∷
-- arg (arg-info visible relevant) (var 2 []) ∷
-- arg (arg-info visible relevant) (var 1 []) ∷
-- arg (arg-info visible relevant) (var 0 []) ∷ []
-- -}

-- -- --   module S₁₋₂ where
-- -- --     module _ (L : Set) (R : Set) (L≡R : L ≡ R) (G : L → Set) (l : L) (Gl : G l) (F : (A : Set) (x y : A) → G l → Set) where

-- -- --       -rewrite -rewrite' -reright :
-- -- --         F L l l Gl

-- -- --       -rewrite rewrite L≡R = {!debug-rewrite -rewrite 0!}

-- -- --       -rewrite' = {-helper-} {!!} where
-- -- --         helper : {!!}
-- -- --         helper = {!!}

-- -- --       -reright = helper L L≡R G l Gl F {!!} where
-- -- --         helper : (w : Set) (w≡R : w ≡ R) →
-- -- --                  (G' : w → Set) (l' : w) (Gl' : G' l') (F' : (A : Set) (x y : A) → G' l' → Set) →
-- -- --                  ((G'' : R → Set) (l'' : R) (Gl'' : G'' l'') (F'' : (A : Set) (x y : A) → G'' l'' → Set) →
-- -- --                   F'' R l'' l'' Gl'') →
-- -- --                  F' w l' l' Gl'
-- -- --         helper ._ refl G' l' Gl' F' φ = φ G' l' Gl' F'

-- -- --   module S₂ where
-- -- --     -rewrite -rewrite' -reright :
-- -- --       (A B : Set) → A ≡ B → A → B → A

-- -- --     -rewrite A B A≡B a b rewrite A≡B = {!debug-rewrite -rewrite 0!}

-- -- --     -rewrite' = {!!} where
-- -- --       helper : {!!}
-- -- --       helper = {!!}

-- -- --     -reright = {!!} where
-- -- --       helper : {!!}
-- -- --       helper = {!!}

-- -- --   module S₃ where
-- -- --     -rewrite -rewrite' -reright :
-- -- --       (A B : Set) (F : Set → Set) → F A → A ≡ B → B → A

-- -- --     -rewrite A B F fa A≡B b rewrite A≡B = {!debug-rewrite -rewrite 0!}

-- -- --     -rewrite' = {!!} where
-- -- --       helper : {!!}
-- -- --       helper = {!!}

-- -- --     -reright = {!!} where
-- -- --       helper : {!!}
-- -- --       helper = {!!}

-- -- --   module S₄ where
-- -- --     postulate
-- -- --       A₀ : Set
-- -- --       A₁ : A₀ → Set
-- -- --       C : (α : Level) (β : Level) → Set α → Set β

-- -- --     -rewrite -rewrite' -reright :
-- -- --       (β : Level)
-- -- --       (a₀¹ : A₀)
-- -- --       (χ : Level)
-- -- --       (a₀² : A₀)
-- -- --       (CA₁a₀¹≡CA₁a₀² : C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C lzero (β ⊔ χ) (A₁ a₀²))
-- -- --       (CA₁a₀¹ : C lzero (β ⊔ χ) (A₁ a₀¹)) →
-- -- --       Nat → Σ _ λ γ → C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))

-- -- --     -rewrite = {!debug-rewrite -rewrite 0!}

-- -- --     -- β a₀¹ χ a₀² CA₁a₀¹≡CA₁a₀² CA₁a₀¹ = test₁₃-helper β χ {_} a₀¹ a₀² CA₁a₀¹≡CA₁a₀² CA₁a₀¹ CA₁a₀¹≡CA₁a₀² {!!} -- reright' CA₁a₀¹≡CA₁a₀² {!!}

-- -- --     -rewrite' = {!!} where
-- -- --       helper : {!!}
-- -- --       helper = {!!}

-- -- --     -reright β a₀¹ χ a₀² CA₁a₀¹≡CA₁a₀² CA₁a₀¹ = helper (C lzero (β ⊔ χ) (A₁ a₀¹)) CA₁a₀¹≡CA₁a₀² CA₁a₀¹ {!!} where
-- -- --       helper : (w : Set (β ⊔ χ)) (w≡CA₁a₀² : w ≡ C lzero (β ⊔ χ) (A₁ a₀²)) →
-- -- --                (CA₁a₀¹' : w)
-- -- --                (φ : (CA₁a₀¹'' : C lzero (β ⊔ χ) (A₁ a₀²)) →
-- -- --                 Nat → Σ _ λ γ → C lzero (β ⊔ χ) (A₁ a₀²) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹)))
-- -- --                →
-- -- --                Nat → Σ _ λ γ → w ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))
-- -- --       helper ._ refl CA₁a₀¹' φ = φ CA₁a₀¹'

-- -- --   module M₁ (a : Level)
-- -- --             (A A' B B' : Set a)
-- -- --             {F : Set a → Set a}
-- -- --             {FA : F A}
-- -- --             (A≡B : A ≡ B)
-- -- --     where

-- -- --     -rewrite₁ -reright₁ : F A
-- -- --     -rewrite₁ rewrite A≡B = {!!}
-- -- --     -reright₁ = reright A≡B {!!}

-- -- --     -rewrite₂ : F A → F A
-- -- --     -rewrite₂ rewrite A≡B = {!!}

-- -- --     -rewrite₃ : F A → F A
-- -- --     -rewrite₃ fa rewrite A≡B = {!!}

-- -- --   module M₂
-- -- --     where
-- -- --     test : (a : Level)
-- -- --            (A A' B B' : Set a)
-- -- --            (F : Set a → Set a)
-- -- --            (FA : F A)
-- -- --            (A≡B : A ≡ B)
-- -- --            (A≡B' : A ≡ B)
-- -- --            → F A → F B
-- -- --     test a A A' B B' F FA A≡B A≡B' fa rewrite A≡B = {!!}
-- -- -- --    test a A A' B B' F FA A≡B fa = -- test-helper fa A≡B {!!}
-- -- -- --                                   test-helper' fa A≡B {!!}
-- -- --       where
-- -- --       test-helper' : {w : Set a} → F w → w ≡ B → (F B → F B) → F B
-- -- --       test-helper' {._} x refl y = y x

-- -- --   module M₃ where
-- -- --     -- 'reright' presents the user with changed context variabes, to mimic that done by 'rewrite'.
-- -- --     simple-reright-test₁-rewrite : (A B : Set) (F : Set → Set) → F A → A ≡ B → B → A
-- -- --     simple-reright-test₁-rewrite A B F FA A≡B b rewrite A≡B = {!!}

-- -- --     -- reverse(Γʷ/ᴬ) → {w : A} → reverse(Γʷ/⁻ᴬ)[w/L] → w ≡ R → gʳ → 𝐺ʷ
-- -- --     simple-reright-test₁-helper : {w : Set} (A B : Set) (F : Set → Set) → F w → w ≡ B → B → w ≡ B → (F B → B) → w
-- -- --     simple-reright-test₁-helper {._} _ _ _ z _ _ refl f₁ = f₁ z

-- -- --     simple-reright-test₁ : (A B : Set) (F : Set → Set) → F A → A ≡ B → B → A
-- -- --     simple-reright-test₁ A B F FA A≡B b = simple-reright-test₁-helper A B F FA A≡B b A≡B {!!} -- simple-reright-test₁-helper A B F FA A≡B b  {!!}

-- -- --     simple-reright-test₁-reright : (A B : Set) (F : Set → Set) → F A → A ≡ B → B → A
-- -- --     simple-reright-test₁-reright A B F FA A≡B b = {!!} -- reright A≡B $ λ (FB : F B) → b

-- -- --     -- the target of the reright (in this case x≡y₁) is excluded from the changed context variables
-- -- --     simple-reright-test₂-rewrite : {a : Level} {A : Set a} {x y : A} (x≡y₁ : x ≡ y) (x≡y₂ : x ≡ y) → y ≡ x
-- -- --     simple-reright-test₂-rewrite {y = y} x≡y₁ x≡y₂ rewrite x≡y₁ = {!!}

-- -- --     -- {a : Level} {A : Set a} {z z₁ : A} {z₁ = z₂ : A} (z₃ z₄ z₅ : z ≡ z₂) (f : (z₆ : z₂ ≡ z₂) → z₂ ≡ z₂) → z₂ ≡ z
-- -- --     simple-reright-test₂-helper : {a : Level} {A : Set a} {w : A} {x y : A} → w ≡ y → w ≡ y → w ≡ y → (y ≡ y → y ≡ y) → y ≡ w
-- -- --     simple-reright-test₂-helper {_} {_} {._} {_} {_} _ x refl f = f x

-- -- --     simple-reright-test₂ : {a : Level} {A : Set a} {x y : A} (x≡y₁ : x ≡ y) (x≡y₂ : x ≡ y) → y ≡ x
-- -- --     simple-reright-test₂ {a} {A} {x} {y} x≡y₁ x≡y₂ = simple-reright-test₂-helper {a} {A} {_} {x} {y} x≡y₁ x≡y₂ x≡y₁ {!!}

-- -- --     simple-reright-test₂-reright : {a : Level} {A : Set a} {x y : A} (x≡y₁ : x ≡ y) (x≡y₂ : x ≡ y) → y ≡ x
-- -- --     simple-reright-test₂-reright {y = y} x≡y₁ x≡y₂ = {!!} -- reright x≡y₁ λ (x≡y₂' : y ≡ y) → refl
-- -- --   {-
-- -- --     -- the visibility of context variables remains the same in their changed state
-- -- --     simple-reright-test₃ : {a : Level} {A : Set a} {x y : A} (x≡y₁ : x ≡ y) (x≡y₂ : x ≡ y) {x≡y₃ : x ≡ y} → y ≡ x
-- -- --     simple-reright-test₃ {y = y} x≡y₁ x≡y₂ {x≡y₃} = reright x≡y₁ λ (x≡y₂' : y ≡ y) {x≡y₃' : y ≡ y} → refl
-- -- --   -}
-- -- --     -- for some reason, when the first changed variable is hidden, it's impossible to bring it into scope
-- -- --     {- FAILS - results in unsolved metas
-- -- --       problematic-visibility : {a : Level} {A : Set a} {x y : A} (x≡y₁ : x ≡ y) {x≡y₃ : x ≡ y} → y ≡ x
-- -- --       problematic-visibility {y = y} x≡y₁ {x≡y₃} = reright x≡y₁ λ {x≡y₃' : y ≡ y} → refl
-- -- --     -}

-- -- --   module M₄ (A : Set) where
-- -- --     postulate R : A → Set

-- -- --     test : (x : A) → (y : A) → x ≡ y → R x → R x
-- -- -- --    test x y x≡y Rx rewrite x≡y = {!!}
-- -- --     test x y x≡y Rx = helper x≡y Rx {!!}
-- -- --       where
-- -- --         helper : {w : A} → w ≡ y → R w → (R y → R y) → R w
-- -- --         helper {._} refl Rx f = f Rx

-- -- --   module M₅ where
-- -- --     postulate
-- -- --       Set≡Set : Set ≡ Set
-- -- --       A₀ : Set
-- -- --       A₁ : A₀ → Set
-- -- --       A₂ : (a₀ : A₀) → A₁ a₀ → Set
-- -- --       A₃ : (a₀ : A₀) → (a₁ : A₁ a₀) → A₂ a₀ a₁ → Set
-- -- --       B₀ : Set
-- -- --       B₁ : B₀ → Set
-- -- --       B₂ : (b₀ : B₀) → B₁ b₀ → Set
-- -- --       B₃ : (b₀ : B₀) → (b₁ : B₁ b₀) → B₂ b₀ b₁ → Set
-- -- --       A₀≡B₀ : A₀ ≡ B₀
-- -- --       --A₀≡A₀ : A₀ ≡ A₀
-- -- --       F : Set → Set
-- -- --       C : (α : Level) (β : Level) → Set α → Set β
-- -- --       𝑨₀¹ : A₀
-- -- --       𝑨₀² : A₀
-- -- --       𝑨₀¹≡𝑨₀² : 𝑨₀¹ ≡ 𝑨₀²
-- -- --       𝑨₂𝑨₀²⋆ : (a₁𝑨₀² : A₁ 𝑨₀²) → A₂ 𝑨₀² a₁𝑨₀²
-- -- --       𝑩₀ : B₀
-- -- --       K₀ : A₀ → Set

-- -- --     simplest : A₀ ≡ B₀ → Set
-- -- --     simplest x = {!x!}
-- -- -- {-
-- -- --     test₀ : (b₀¹ b₀² : B₀) (b₀¹≡b₀² : b₀¹ ≡ b₀²) → Set
-- -- --     test₀ b₀¹ b₀² b₀¹≡b₀² with b₀¹≡b₀²
-- -- --     test₀ b₀¹ b₀² b₀¹≡b₀² | b₀¹≡b₀²-with = let b₀¹≡b₀²-let = b₀¹≡b₀²-with in reright b₀¹≡b₀²-let {!!}
-- -- -- -}
-- -- --     test₁'' : {X : Set} (x : X) → x ≡ x → Set
-- -- --     --test₁' a₀ = helper A₀≡B₀ a₀ {!!} -- reright' A₀≡B₀ ?
-- -- --     --test₁' a₀ rewrite A₀≡B₀ = {!!}
-- -- --     --test₁' a₀ rewrite A₀≡B₀ = {!!} -- reright A₀≡B₀ {!!}
-- -- --     test₁'' a₀ x≡x = {!!} -- reright x≡x {!!}
-- -- --       where
-- -- --       helper : {w : Set} (L≡R : w ≡ B₀) → (x : w) → (B₀ → a₀ ≡ a₀) → a₀ ≡ a₀
-- -- --       helper {._} refl x x₁ = x₁ x

-- -- --     postulate
-- -- --       a₀ : A₀
-- -- --       _≡'_ : ∀ {c} {C : Set c} (x : C) → C → Set c

-- -- --     A₀≡A₀ : A₀ ≡ A₀
-- -- --     A₀≡A₀ = refl

-- -- --     test₁' : a₀ ≡ a₀
-- -- --     --test₁' a₀ = helper A₀≡B₀ a₀ {!!} -- reright' A₀≡B₀ ?
-- -- --     --test₁' a₀ rewrite A₀≡B₀ = {!!}
-- -- --     --test₁' a₀ rewrite A₀≡B₀ = {!!} -- reright A₀≡B₀ {!!}
-- -- --     test₁' = {!!} -- reright A₀≡A₀ {!!}
-- -- --       where
-- -- --       helper : {w : Set} (L≡R : w ≡ B₀) → (x : w) → (B₀ → a₀ ≡ a₀) → a₀ ≡ a₀
-- -- --       helper {._} refl x x₁ = x₁ x

-- -- -- --     test₁ : ∀ (a₀ : A₀) → a₀ ≡ a₀
-- -- -- --     test₁ a₀ = id (reright A₀≡B₀ {!!})

-- -- -- -- --     test₂ : A₀ → B₀
-- -- -- -- --     test₂ a₀ = reright A₀≡B₀ (λ b₀ → 𝑩₀)

-- -- -- -- --     test₃ : A₀ → B₀
-- -- -- -- --     test₃ a₀ = reright Set≡Set (reright A₀≡B₀ (λ b₀ → 𝑩₀))

-- -- -- -- --     test₄ : A₀ → B₀
-- -- -- -- --     test₄ a₀ = reright Set≡Set (reright A₀≡B₀ (λ b₀ → reright A₀≡B₀ {!!}))

-- -- -- -- --     test₅ : A₀ → B₀
-- -- -- -- --     test₅ a₀ = reright Set≡Set 𝑩₀

-- -- -- -- --     test₆ : A₀ → B₀
-- -- -- -- --     test₆ a₀ = reright Set≡Set $ reright A₀≡B₀ $ {!!}

-- -- -- -- --     test₇ : ∀ {α : Level}
-- -- -- -- --             (a₀ : A₀)
-- -- -- -- --             {β : Level}
-- -- -- -- --             (X Y : Set (α ⊔ β))
-- -- -- -- --             → X ≡ Y
-- -- -- -- --             → Y ≡ X
-- -- -- -- --     test₇ {α} a₀ {β} X Y X≡Y = id (reright X≡Y {!!})

-- -- -- -- --     test₈ : (a₁𝑨₀¹ : A₁ 𝑨₀¹) → A₂ 𝑨₀¹ a₁𝑨₀¹
-- -- -- -- --     test₈ a₁𝑨₀¹ = reright 𝑨₀¹≡𝑨₀² (λ a₁𝑨₀² → {!!})

-- -- -- -- --     test₉ : (a₀¹ : A₀) (a₀² : A₀) (a₀¹≡a₀²-1 : a₀¹ ≡ a₀²) (a₁a₀¹ : A₁ a₀¹) (X : Set) (Y : Set) (a₀¹≡a₀²-2 : a₀¹ ≡ a₀²) → F (A₂ a₀¹ a₁a₀¹) → F (A₁ a₀¹) ≡ A₂ a₀¹ a₁a₀¹
-- -- -- -- --     test₉ a₀¹ a₀² a₀¹≡a₀²-1 a₁a₀¹ X Y a₀¹≡a₀²-2 = reright a₀¹≡a₀²-1 {!!}

-- -- -- -- --     module _ (A₂⋆ : (a₀ : A₀) (a₁a₀ : A₁ a₀) → A₂ a₀ a₁a₀) where
-- -- -- -- --       test₁₀ : (a₀ : A₀) (a₁a₀¹ : A₁ a₀) (a₁a₀² : A₁ a₀) (a₁a₀¹≡a₁a₀² : a₁a₀¹ ≡ a₁a₀²) → A₂ a₀ a₁a₀¹
-- -- -- -- --       test₁₀ a₀ a₁a₀¹ a₁a₀² a₁a₀¹≡a₁a₀² = reright a₁a₀¹≡a₁a₀² {!!}

-- -- -- -- --     test₁₁ : (a₀¹ : A₀) (a₀² : A₀) (FA₁a₀¹≡FA₁a₀² : F (A₁ a₀¹) ≡ F (A₁ a₀²)) → F (A₁ a₀¹) → F (A₁ a₀¹) ≡ F (F (A₁ a₀¹))
-- -- -- -- --     test₁₁ a₀¹ a₀² FA₁a₀¹≡FA₁a₀² = reright FA₁a₀¹≡FA₁a₀² {!!}

-- -- -- -- --     test₁₂ : (a₀¹ : A₀) (a₀² : A₀) (FA₁a₀¹≡FA₁a₀² : F (A₁ a₀¹) ≡ F (A₁ a₀²)) → F (A₁ a₀¹) → F (A₁ a₀¹) ≡ F (F (A₁ a₀¹))
-- -- -- -- --     test₁₂ a₀¹ a₀² FA₁a₀¹≡FA₁a₀² FA₁a₀¹ = reright FA₁a₀¹≡FA₁a₀² {!!}






-- -- -- -- -- {-
-- -- -- -- --     test₁₃-helper : (β χ : Level) -- anything needed to define w
-- -- -- -- --                     {w : Set (β ⊔ χ)} -- w
-- -- -- -- --                     (a₀¹ a₀² : A₀) → w ≡ C lzero (β ⊔ χ) (A₁ a₀²) → w -- everything else in the problem with L replaced with w
-- -- -- -- --                     → w ≡ C lzero (β ⊔ χ) (A₁ a₀²) -- w ≡ R
-- -- -- -- --                     → (C lzero (β ⊔ χ) (A₁ a₀²) -- problem terms that had a replacement (not including the l≡r term)
-- -- -- -- --                        → Nat → Σ Level (λ γ → C lzero (β ⊔ χ) (A₁ a₀²) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))) -- solution's goal
-- -- -- -- --                       ) -- solution
-- -- -- -- --                     → Nat → Σ Level (λ γ → w ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))) -- goal
-- -- -- -- --     test₁₃-helper β χ {.(C lzero (χ ⊔ β) (A₁ a₀²))} a₀¹ a₀² z x refl f = f x

-- -- -- -- --     test₁₃-helper' : (β : Level)
-- -- -- -- --                      (a₀¹ : A₀)
-- -- -- -- --                      (χ : Level) -- everything up till what we need to define w
-- -- -- -- --                      {w : Set (β ⊔ χ)}
-- -- -- -- --                      (a₀² : A₀)
-- -- -- -- --                      (CA₁a₀¹≡CA₁a₀² : w ≡ C lzero (β ⊔ χ) (A₁ a₀²)) →
-- -- -- -- --                      w
-- -- -- -- --                      (C lzero (β ⊔ χ) (A₁ a₀²)
-- -- -- -- --                       → Nat → Σ _ λ γ → C lzero (β ⊔ χ) (A₁ a₀²) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹)))
-- -- -- -- --                      → Nat → Σ _ λ γ → w ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))
-- -- -- -- --     test₁₃-helper β χ {.(C lzero (χ ⊔ β) (A₁ a₀²))} a₀¹ a₀² z x refl f = f x

-- -- -- -- --     test₁₃ : (β : Level)
-- -- -- -- --              (a₀¹ : A₀)
-- -- -- -- --              (χ : Level)
-- -- -- -- --              (a₀² : A₀)
-- -- -- -- --              (CA₁a₀¹≡CA₁a₀² : C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C lzero (β ⊔ χ) (A₁ a₀²)) →
-- -- -- -- --              C lzero (β ⊔ χ) (A₁ a₀¹)
-- -- -- -- --              → Nat → Σ _ λ γ → C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))
-- -- -- -- --     test₁₃ β a₀¹ χ a₀² CA₁a₀¹≡CA₁a₀² CA₁a₀¹ = test₁₃-helper β χ {_} a₀¹ a₀² CA₁a₀¹≡CA₁a₀² CA₁a₀¹ CA₁a₀¹≡CA₁a₀² {!!} -- reright' CA₁a₀¹≡CA₁a₀² {!!}

-- -- -- -- --     module M₁₃-1 (β : Level)
-- -- -- -- --                  (a₀¹ : A₀)
-- -- -- -- --                  (χ : Level)
-- -- -- -- --                  (a₀² : A₀)
-- -- -- -- --                  (CA₁a₀¹≡CA₁a₀² : C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C lzero (β ⊔ χ) (A₁ a₀²))
-- -- -- -- --                  (CA₁a₀¹ : C lzero (β ⊔ χ) (A₁ a₀¹))
-- -- -- -- --       where

-- -- -- -- --       test-helper : -- anything needed to define w (that isn't in the module)
-- -- -- -- --                     {w : Set (β ⊔ χ)} -- w
-- -- -- -- --                     -- everything else in the problem (that isn't in the module) with L replaced with w
-- -- -- -- --                     → w ≡ C lzero (β ⊔ χ) (A₁ a₀²) -- w ≡ R
-- -- -- -- --                     → ( -- problem terms (that aren't in the module) that had a replacement (not including the l≡r term)
-- -- -- -- --                        Nat → Σ Level (λ γ → C lzero (β ⊔ χ) (A₁ a₀²) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹)))) -- solution's goal
-- -- -- -- --                     → Nat → Σ Level (λ γ → w ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))) --goal
-- -- -- -- --       test-helper {._} refl f = f

-- -- -- -- --       test : Nat → Σ _ λ γ → C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))
-- -- -- -- --       test = test-helper {_} CA₁a₀¹≡CA₁a₀² {!!}

-- -- -- -- --       test-reright : Nat → Σ _ λ γ → C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))
-- -- -- -- --       test-reright = {!!} -- reright CA₁a₀¹≡CA₁a₀² ?
-- -- -- -- -- -}

-- -- -- -- -- --       test-rewrite : Nat → Σ _ λ γ → C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))
-- -- -- -- -- --       test-rewrite rewrite CA₁a₀¹≡CA₁a₀² = {!!}

-- -- -- -- -- --     module M₁₃-2 (β : Level)
-- -- -- -- -- --                  (a₀¹ : A₀)
-- -- -- -- -- --                  (χ : Level)
-- -- -- -- -- --                  (a₀² : A₀)
-- -- -- -- -- --                  (CA₁a₀¹≡CA₁a₀² : C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C lzero (β ⊔ χ) (A₁ a₀²))
-- -- -- -- -- --                  (CA₁a₀¹ : C lzero (β ⊔ χ) (A₁ a₀¹))
-- -- -- -- -- --       where
-- -- -- -- -- --       test-rewrite : Nat → Σ _ λ γ → C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))
-- -- -- -- -- --       test-rewrite rewrite CA₁a₀¹≡CA₁a₀² = {!!}

-- -- -- -- -- -- {-
-- -- -- -- -- --     test₁₃ : (β : Level)
-- -- -- -- -- --              (a₀¹ : A₀)
-- -- -- -- -- --              (χ : Level)
-- -- -- -- -- --              (a₀² : A₀)
-- -- -- -- -- --              (CA₁a₀¹≡CA₁a₀² : C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C lzero (β ⊔ χ) (A₁ a₀²)) →
-- -- -- -- -- --              C lzero (β ⊔ χ) (A₁ a₀¹)
-- -- -- -- -- --              → Nat → Σ _ λ γ → C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))
-- -- -- -- -- --     test₁₃ β a₀¹ χ a₀² CA₁a₀¹≡CA₁a₀² CA₁a₀¹ = reright CA₁a₀¹≡CA₁a₀² {!!}
-- -- -- -- -- -- -}
-- -- -- -- -- -- --     test₁₄ : (a₀ : A₀) (FFA₁a₀≡FA₁a₀ : F (F (A₁ a₀)) ≡ F (A₁ a₀)) → F (F (F (F (A₁ a₀))))
-- -- -- -- -- -- --     test₁₄ a₀ FFA₁a₀≡FA₁a₀ = reright FFA₁a₀≡FA₁a₀ (reright FFA₁a₀≡FA₁a₀ (reright FFA₁a₀≡FA₁a₀ {!!}))

-- -- -- -- -- -- --     test₁₅ : (a₀ : A₀) (FA₁a₀≡FFA₁a₀ : F (A₁ a₀) ≡ F (F (A₁ a₀))) → F (F (A₁ a₀))
-- -- -- -- -- -- --     test₁₅ a₀ FA₁a₀≡FFA₁a₀ = reright FA₁a₀≡FFA₁a₀ (reright FA₁a₀≡FFA₁a₀ {!!})

-- -- -- -- -- -- --     test₁₆ : (l : A₀ → Level → Level)
-- -- -- -- -- -- --              (β : Level)
-- -- -- -- -- -- --              (a₀² : A₀)
-- -- -- -- -- -- --              (a₀¹ : A₀)
-- -- -- -- -- -- --              (CA₁a₀¹≡CA₁a₀² : C lzero (l a₀¹ β) (A₁ a₀¹) ≡ C lzero (l a₀¹ β) (A₁ a₀²))
-- -- -- -- -- -- --              → C lzero (l a₀¹ β) (A₁ a₀¹)
-- -- -- -- -- -- --              → Σ _ λ γ → C lzero (l a₀¹ β) (A₁ a₀¹) ≡ C γ (l a₀¹ β) (C lzero γ (A₁ a₀¹))
-- -- -- -- -- -- --     test₁₆ l β a₀² a₀¹ CA₁a₀¹≡CA₁a₀² CA₁a₀¹ = reright CA₁a₀¹≡CA₁a₀² {!!}

-- -- -- -- -- -- --     test₁₇ : (a₀¹ : A₀)
-- -- -- -- -- -- --              (a₀² : A₀)
-- -- -- -- -- -- --              (K₀a₀¹ : K₀ a₀¹)
-- -- -- -- -- -- --              (a₀¹≡a₀² : a₀¹ ≡ a₀²)
-- -- -- -- -- -- --            → Set
-- -- -- -- -- -- --     test₁₇ a₀¹ a₀² K₀a₀¹ a₀¹≡a₀² = reright a₀¹≡a₀² {!!}

-- -- -- -- -- -- --     test₁₈ : (a₀¹ : A₀)
-- -- -- -- -- -- --              (a₀² : A₀)
-- -- -- -- -- -- --              (k₀a₀¹ : K₀ a₀¹)
-- -- -- -- -- -- --              (FK₀a₀¹ : F (K₀ a₀¹))
-- -- -- -- -- -- --              (K₀a₀¹≡K₀a₀² : K₀ a₀¹ ≡ K₀ a₀²)
-- -- -- -- -- -- --            → F (F (K₀ a₀¹)) ≡ F (K₀ a₀²)
-- -- -- -- -- -- --     test₁₈ a₀¹ a₀² k₀a₀¹ FK₀a₀¹ K₀a₀¹≡K₀a₀² = reright K₀a₀¹≡K₀a₀² {!!}

-- -- -- -- -- -- --     test₁₉ : ∀ {a₀¹ : A₀}
-- -- -- -- -- -- --                {a₀² : A₀}
-- -- -- -- -- -- --                {a₁a₀²-1 a₁a₀²-2 a₁a₀²-3 : A₁ a₀²}
-- -- -- -- -- -- --                {a₁a₀²-2=a₁a₀²-3 : A₂ a₀² a₁a₀²-2 ≡ A₂ a₀² a₁a₀²-3}
-- -- -- -- -- -- --                (R : ∀ (a₀²' : A₀) → A₂ a₀² a₁a₀²-1 ≡ A₂ a₀² a₁a₀²-2)
-- -- -- -- -- -- --                (X : A₂ a₀² a₁a₀²-2 ≡ A₂ a₀² a₁a₀²-3)
-- -- -- -- -- -- --                {ignore : Set}
-- -- -- -- -- -- --              → A₂ a₀² a₁a₀²-1 ≡ A₂ a₀² a₁a₀²-3
-- -- -- -- -- -- --     test₁₉ {a₀¹} {a₀²} {a₁a₀²-1} {a₁a₀²-2} {a₁a₀²-3} {a₁a₀²-2=a₁a₀²-3} R X = reright (R a₀¹) {!!}

-- -- -- -- -- -- --     {- FAILS (correctly, though perhaps without the most comprehensible of error messages)
-- -- -- -- -- -- --       test₂₀' : (f₁ : A₀) (f₂ : A₀) (A₀f₁≡A₀f₂ : A₁ f₁ ≡ A₁ f₂) (g₁ : A₁ f₁) → A₂ f₁ g₁
-- -- -- -- -- -- --       test₂₀' f₁ f₂ A₀f₁≡A₀f₂ g₁ rewrite A₀f₁≡A₀f₂ = {!!}

-- -- -- -- -- -- --       test₂₀ : (f₁ : A₀) (f₂ : A₀) (A₀f₁≡A₀f₂ : A₁ f₁ ≡ A₁ f₂) (g₁ : A₁ f₁) → A₂ f₁ g₁
-- -- -- -- -- -- --       test₂₀ f₁ f₂ A₀f₁≡A₀f₂ g₁ = reright A₀f₁≡A₀f₂ {!!}
-- -- -- -- -- -- --     -}

-- -- -- -- -- -- --     test₂₀ : ∀ {a b : Level} {A : Set a} {x y : A} (x≡y : x ≡ y) → Set
-- -- -- -- -- -- --     test₂₀ x≡y = reright x≡y {!!}

-- -- -- -- -- -- --     test₂₁ : ∀ {a b : Level} {A : Set a} {x y : A} (B : Set b) (x≡y : x ≡ y) → Set
-- -- -- -- -- -- --     test₂₁ B x≡y = reright x≡y {!!}

-- -- -- -- -- -- --     test₂₂ : ∀ {a : Level} {A : Set a} {B : Set} {x : B} {y : B} (x≡y : x ≡ y) → Set
-- -- -- -- -- -- --     test₂₂ x≡y = reright x≡y {!!}

-- -- -- -- -- -- --     module _ (l : Level) where
-- -- -- -- -- -- --       postulate P : Set

-- -- -- -- -- -- --       test₂₃ : (p : P)
-- -- -- -- -- -- --                (A : Set)
-- -- -- -- -- -- --                (x y : A)
-- -- -- -- -- -- --                (x≡y : x ≡ y)
-- -- -- -- -- -- --                → Set
-- -- -- -- -- -- --       test₂₃ _ _ _ _ x≡y = reright x≡y ?

-- -- -- -- -- -- --   module Test₂ where
-- -- -- -- -- -- --     record Map
-- -- -- -- -- -- --              {K : Set}
-- -- -- -- -- -- --              (V : K → Set)
-- -- -- -- -- -- --              (Carrier : Nat → Set) {{isDecEquivalence/K : Eq K}} {{isDecEquivalence/V : (k : K) → Eq (V k)}} : Set₁ where
-- -- -- -- -- -- --       field
-- -- -- -- -- -- --         ∅ : Carrier 0
-- -- -- -- -- -- --         _∉_ : ∀ {s} → K → Carrier s → Set
-- -- -- -- -- -- --         ∅-is-empty : ∀ {𝑘} {∅ : Carrier 0} → 𝑘 ∉ ∅

-- -- -- -- -- -- --       _∈_ : ∀ {s} → K → Carrier s → Set
-- -- -- -- -- -- --       _∈_ k m = ¬ k ∉ m

-- -- -- -- -- -- --       field
-- -- -- -- -- -- --         get : ∀ {k : K} {s} {m : Carrier s} → k ∈ m → V k
-- -- -- -- -- -- --         put : ∀ {k₀ : K} (v₀ : V k₀) {s₁} {m₁ : Carrier s₁} → k₀ ∉ m₁ → Σ _ λ (m₀ : Carrier (suc s₁)) → Σ _ λ (k₀∈m₀ : k₀ ∈ m₀) → get k₀∈m₀ ≡ v₀

-- -- -- -- -- -- --     postulate
-- -- -- -- -- -- --       A : Set

-- -- -- -- -- -- --     V : A → Set
-- -- -- -- -- -- --     V = λ _ → Nat

-- -- -- -- -- -- --     postulate
-- -- -- -- -- -- --       M : Nat → Set
-- -- -- -- -- -- --       isDecEquivalence/A : Eq A
-- -- -- -- -- -- --       isDecEquivalence/V : (a : A) → Eq (V a)

-- -- -- -- -- -- --     postulate
-- -- -- -- -- -- --       m : Map V M {{isDecEquivalence/A}} {{isDecEquivalence/V}}

-- -- -- -- -- -- --     open Map m

-- -- -- -- -- -- --     test₁ : (v : Nat) (k : A)
-- -- -- -- -- -- --       → (k∈putkv∅ : k ∈ (fst $ put {k₀ = k} v {m₁ = ∅} ∅-is-empty))
-- -- -- -- -- -- --       → Set
-- -- -- -- -- -- --     test₁ v k k∈putkv∅ = let p = (put {k₀ = k} v {m₁ = ∅} ∅-is-empty) in let r = sym (snd $ snd p) in reright r {!!}

-- -- -- -- -- -- -- {- expected.out
-- -- -- -- -- -- -- ?0 : b₀² ≡ b₀² → Set
-- -- -- -- -- -- -- ?1 : (b : B₀) → b ≡ b
-- -- -- -- -- -- -- ?2 : B₀ → B₀
-- -- -- -- -- -- -- ?3 : B₀ → B₀
-- -- -- -- -- -- -- ?4 : Y ≡ Y
-- -- -- -- -- -- -- ?5 : A₂ 𝑨₀² a₁𝑨₀²
-- -- -- -- -- -- -- ?6 : (a₁ : A₁ a₀²) → a₀² ≡ a₀² → F (A₂ a₀² a₁) → F (A₁ a₀²) ≡ A₂ a₀² a₁
-- -- -- -- -- -- -- ?7 : A₂ a₀ a₁a₀²
-- -- -- -- -- -- -- ?8 : F (A₁ a₀²) → F (A₁ a₀²) ≡ F (F (A₁ a₀²))
-- -- -- -- -- -- -- ?9 : F (A₁ a₀²) → F (A₁ a₀²) ≡ F (F (A₁ a₀²))
-- -- -- -- -- -- -- ?10 : C lzero (χ ⊔ β) (A₁ a₀²) →
-- -- -- -- -- -- -- Nat →
-- -- -- -- -- -- -- Σ Level
-- -- -- -- -- -- -- (λ γ → C lzero (χ ⊔ β) (A₁ a₀²) ≡ C γ (χ ⊔ β) (C lzero γ (A₁ a₀¹)))
-- -- -- -- -- -- -- ?11 : F (A₁ a₀)
-- -- -- -- -- -- -- ?12 : F (F (F (F (A₁ a₀))))
-- -- -- -- -- -- -- ?13 : C lzero (l a₀¹ β) (A₁ a₀²) →
-- -- -- -- -- -- -- Σ Level
-- -- -- -- -- -- -- (λ γ →
-- -- -- -- -- -- --    C lzero (l a₀¹ β) (A₁ a₀²) ≡ C γ (l a₀¹ β) (C lzero γ (A₁ a₀¹)))
-- -- -- -- -- -- -- ?14 : K₀ a₀² → Set
-- -- -- -- -- -- -- ?15 : K₀ a₀² → F (K₀ a₀²) → F (F (K₀ a₀²)) ≡ F (K₀ a₀²)
-- -- -- -- -- -- -- ?16 : (A₀ → A₂ a₀² a₁a₀²-2 ≡ A₂ a₀² a₁a₀²-2) →
-- -- -- -- -- -- -- A₂ a₀² a₁a₀²-2 ≡ A₂ a₀² a₁a₀²-3
-- -- -- -- -- -- -- ?17 : Set
-- -- -- -- -- -- -- ?18 : Set
-- -- -- -- -- -- -- ?19 : Set
-- -- -- -- -- -- -- ?20 : Set
-- -- -- -- -- -- -- ?21 : (k ∉ fst (put (get (fst (snd (put v ∅-is-empty)))) ∅-is-empty) →
-- -- -- -- -- -- --  ⊥) →
-- -- -- -- -- -- -- Set
-- -- -- -- -- -- -- -}

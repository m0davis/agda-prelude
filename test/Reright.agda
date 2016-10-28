--{-# OPTIONS --show-implicit #-}
module Reright where
  open import Prelude
  open import Tactic.Reright
  open import Agda.Builtin.Reflection
  open import Tactic.Reflection
  open import Tactic.Reflection.Quote

  module FailingCases where
    postulate
      A₀ : Set
      a₀ : A₀
      A₀≡A₀ : A₀ ≡ A₀

    test-rewrite : a₀ ≡ a₀
    test-rewrite rewrite A₀≡A₀ = {!!}

    test-reright : a₀ ≡ a₀
    test-reright = {!reright-debug A₀≡A₀ ?!}
    -- we should be checking that the left and right hand sides are equal and therefore do no rerighting

  {- In some of the modules below,
       -rewrite shows an example of rewrite (on the lhs)
       -reright' shows an example of the same but using a helper function
       -reright tests the use of the Tactic.Reright.reright macro, which creates and applies a helper function
  -}

  module S₁₋₀ where

    postulate

      L : Set
      R : Set
      L≡R : L ≡ R
      F : (A : Set) (x y : A) → Set

    -rewrite -reright' -reright :
      (l : L) → F L l l

    -rewrite l rewrite L≡R = {!debug-rewrite -rewrite 0!}

    -reright' l = helper L L≡R l {!!} where
      helper : (w : Set) (w≡R : w ≡ R) →
               (l' : w) →
               ((l'' : R) →
                F R l'' l'') →
               F w l' l'
      helper ._ refl l' f = f l'

    -reright l = reright L≡R {!!}

  module S₁₋₁ where

    -rewrite -reright' -reright :
      (L : Set) (R : Set) (L≡R : L ≡ R) (G : L → Set) (l : L) → (Gl : G l) (F : (A : Set) (x y : A) → G l → Set) → F L l l Gl

    -rewrite L R L≡R G l Gl F rewrite L≡R = {!!}

    -reright' L R L≡R G l Gl F = helper {_} L≡R G l Gl F {!!} where
      helper : {w : Set} (w≡R : w ≡ R) →
               (G' : w → Set)
               (l' : w)
               (Gl' : G' l')
               (F' : (A : Set) (x y : A) → G' l' → Set) →
               ((G'' : R → Set)
                (l'' : R)
                (Gl'' : G'' l'')
                (F'' : (A : Set) (x y : A) → G'' l'' → Set) →
                F'' R l'' l'' Gl'') →
               F' w l' l' Gl'
      helper {._} refl G' l' Gl' F' φ = φ G' l' Gl' F'

    -reright L R L≡R G l Gl F = reright L≡R {!!}

  module S₁₋₂ where

    module _ (L : Set) (R : Set) (L≡R : L ≡ R) (G : L → Set) (l : L) (Gl : G l) (F : (A : Set) (x y : A) → G l → Set) where

      -rewrite -reright' -reright :
        F L l l Gl

      -rewrite rewrite L≡R = {!!}

      -reright' = helper L L≡R G l Gl F {!!} where
        helper : (w : Set) (w≡R : w ≡ R) →
                 (G' : w → Set) (l' : w) (Gl' : G' l') (F' : (A : Set) (x y : A) → G' l' → Set) →
                 ((G'' : R → Set) (l'' : R) (Gl'' : G'' l'') (F'' : (A : Set) (x y : A) → G'' l'' → Set) →
                  F'' R l'' l'' Gl'') →
                 F' w l' l' Gl'
        helper ._ refl G' l' Gl' F' φ = φ G' l' Gl' F'

      -reright = reright L≡R {!!}

  module S₂ where
    -rewrite -reright :
      (A B : Set) → A ≡ B → A → B → A

    -rewrite A B A≡B a b rewrite A≡B = {!!}

    -reright A B A≡B a b = reright A≡B {!!} where

  module S₃ where
    -rewrite -reright :
      (A B : Set) (F : Set → Set) → F A → A ≡ B → B → A

    -rewrite A B F fa A≡B b rewrite A≡B = {!!}

    -reright A B F fa A≡B b = reright A≡B {!!}

  module S₄ where
    postulate
      A₀ : Set
      A₁ : A₀ → Set
      C : (α : Level) (β : Level) → Set α → Set β

    -rewrite -reright' -reright :
      (β : Level)
      (a₀¹ : A₀)
      (χ : Level)
      (a₀² : A₀)
      (CA₁a₀¹≡CA₁a₀² : C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C lzero (β ⊔ χ) (A₁ a₀²))
      (CA₁a₀¹ : C lzero (β ⊔ χ) (A₁ a₀¹)) →
      Nat → Σ _ λ γ → C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))

    -rewrite β a₀¹ χ a₀² CA₁a₀¹≡CA₁a₀² CA₁a₀¹ rewrite CA₁a₀¹≡CA₁a₀² = {!!}

    -reright' β a₀¹ χ a₀² CA₁a₀¹≡CA₁a₀² CA₁a₀¹ = helper (C lzero (β ⊔ χ) (A₁ a₀¹)) CA₁a₀¹≡CA₁a₀² CA₁a₀¹ {!!} where
      helper : (w : Set (β ⊔ χ)) (w≡CA₁a₀² : w ≡ C lzero (β ⊔ χ) (A₁ a₀²)) →
               (CA₁a₀¹' : w)
               (φ : (CA₁a₀¹'' : C lzero (β ⊔ χ) (A₁ a₀²)) →
                Nat → Σ _ λ γ → C lzero (β ⊔ χ) (A₁ a₀²) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹)))
               →
               Nat → Σ _ λ γ → w ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))
      helper ._ refl CA₁a₀¹' φ = φ CA₁a₀¹'

    -reright β a₀¹ χ a₀² CA₁a₀¹≡CA₁a₀² CA₁a₀¹ = reright CA₁a₀¹≡CA₁a₀² {!!}

  module S₅ where
    module _ (a : Level)
             (A A' B B' : Set a)
             {F : Set a → Set a}
             {FA : F A}
             (A≡B : A ≡ B)
      where

      -rewrite -reright : F A → F A

      -rewrite fa rewrite A≡B = {!!}

      -reright fa = reright A≡B {!!}

  module S₆ where
    module _ (A B : Set)
             (F : Set → Set)
             (FA : F A)
             (A≡B : A ≡ B)
      where

      -rewrite -reright : F A → F A

      -rewrite fa rewrite A≡B = {!!}

      -reright fa = reright A≡B {!!}

  module M₂
    where
    test : (a : Level)
           (A A' B B' : Set a)
           (F : Set a → Set a)
           (FA : F A)
           (A≡B : A ≡ B)
           (A≡B' : A ≡ B)
           → F A → F B
    test a A A' B B' F FA A≡B A≡B' fa = reright A≡B {!!}

  module M₃ where
    -- 'reright' presents the user with changed context variabes, to mimic that done by 'rewrite'.
    simple-reright-test₁-rewrite : (A B : Set) (F : Set → Set) → F A → A ≡ B → B → A
    simple-reright-test₁-rewrite A B F FA A≡B b rewrite A≡B = {!!}

    -- reverse(Γʷ/ᴬ) → {w : A} → reverse(Γʷ/⁻ᴬ)[w/L] → w ≡ R → gʳ → 𝐺ʷ
    simple-reright-test₁-helper : {w : Set} (A B : Set) (F : Set → Set) → F w → w ≡ B → B → w ≡ B → (F B → B) → w
    simple-reright-test₁-helper {._} _ _ _ z _ _ refl f₁ = f₁ z

    simple-reright-test₁ : (A B : Set) (F : Set → Set) → F A → A ≡ B → B → A
    simple-reright-test₁ A B F FA A≡B b = simple-reright-test₁-helper A B F FA A≡B b A≡B {!!} -- simple-reright-test₁-helper A B F FA A≡B b  {!!}

    simple-reright-test₁-reright : (A B : Set) (F : Set → Set) → F A → A ≡ B → B → A
    simple-reright-test₁-reright A B F FA A≡B b = {!!} -- reright A≡B $ λ (FB : F B) → b

    -- the target of the reright (in this case x≡y₁) is excluded from the changed context variables
    simple-reright-test₂-rewrite : {a : Level} {A : Set a} {x y : A} (x≡y₁ : x ≡ y) (x≡y₂ : x ≡ y) → y ≡ x
    simple-reright-test₂-rewrite {y = y} x≡y₁ x≡y₂ rewrite x≡y₁ = {!!}

    -- {a : Level} {A : Set a} {z z₁ : A} {z₁ = z₂ : A} (z₃ z₄ z₅ : z ≡ z₂) (f : (z₆ : z₂ ≡ z₂) → z₂ ≡ z₂) → z₂ ≡ z
    simple-reright-test₂-helper : {a : Level} {A : Set a} {w : A} {x y : A} → w ≡ y → w ≡ y → w ≡ y → (y ≡ y → y ≡ y) → y ≡ w
    simple-reright-test₂-helper {_} {_} {._} {_} {_} _ x refl f = f x

    simple-reright-test₂ : {a : Level} {A : Set a} {x y : A} (x≡y₁ : x ≡ y) (x≡y₂ : x ≡ y) → y ≡ x
    simple-reright-test₂ {a} {A} {x} {y} x≡y₁ x≡y₂ = simple-reright-test₂-helper {a} {A} {_} {x} {y} x≡y₁ x≡y₂ x≡y₁ {!!}

    simple-reright-test₂-reright : {a : Level} {A : Set a} {x y : A} (x≡y₁ : x ≡ y) (x≡y₂ : x ≡ y) → y ≡ x
    simple-reright-test₂-reright {y = y} x≡y₁ x≡y₂ = {!!} -- reright x≡y₁ λ (x≡y₂' : y ≡ y) → refl

    -- the visibility of context variables remains the same in their changed state
    simple-reright-test₃ : {a : Level} {A : Set a} {x y : A} (x≡y₁ : x ≡ y) (x≡y₂ : x ≡ y) {x≡y₃ : x ≡ y} → y ≡ x
    simple-reright-test₃ {y = y} x≡y₁ x≡y₂ {x≡y₃} = reright x≡y₁ λ (x≡y₂' : y ≡ y) {x≡y₃' : y ≡ y} → refl

    -- use pattern lambdas to bring hidden rewritten variables into scope
    visibility-test : {a : Level} {A : Set a} {x y : A} (x≡y₁ : x ≡ y) {x≡y₃ : x ≡ y} → y ≡ x
    visibility-test {y = y} x≡y₁ {x≡y₃} = reright x≡y₁ (λ { {x≡y₃'} → refl })

  module M₄ (A : Set) where
    postulate R : A → Set

    test : (x : A) → (y : A) → x ≡ y → R x → R x
    test x y x≡y Rx = reright x≡y {!!}

  module M₅ where
    postulate
      Set≡Set : Set ≡ Set
      A₀ : Set
      A₁ : A₀ → Set
      A₂ : (a₀ : A₀) → A₁ a₀ → Set
      A₃ : (a₀ : A₀) → (a₁ : A₁ a₀) → A₂ a₀ a₁ → Set
      B₀ : Set
      B₁ : B₀ → Set
      B₂ : (b₀ : B₀) → B₁ b₀ → Set
      B₃ : (b₀ : B₀) → (b₁ : B₁ b₀) → B₂ b₀ b₁ → Set
      A₀≡B₀ : A₀ ≡ B₀
      A₀≡A₀ : A₀ ≡ A₀
      F : Set → Set
      C : (α : Level) (β : Level) → Set α → Set β
      𝑨₀¹ : A₀
      𝑨₀² : A₀
      𝑨₀¹≡𝑨₀² : 𝑨₀¹ ≡ 𝑨₀²
      𝑨₂𝑨₀²⋆ : (a₁𝑨₀² : A₁ 𝑨₀²) → A₂ 𝑨₀² a₁𝑨₀²
      𝑩₀ : B₀
      K₀ : A₀ → Set

    simplest : A₀ ≡ B₀ → Set
    simplest x = reright x {!!}

    test₀ : (b₀¹ b₀² : B₀) (b₀¹≡b₀² : b₀¹ ≡ b₀²) → Set
    test₀ b₀¹ b₀² b₀¹≡b₀² with b₀¹≡b₀²
    test₀ b₀¹ b₀² b₀¹≡b₀² | b₀¹≡b₀²-with = let b₀¹≡b₀²-let = b₀¹≡b₀²-with in reright b₀¹≡b₀²-let {!!}

    test₁'' : {X : Set} (x : X) → x ≡ x → Set
    test₁'' a₀ x≡x = reright x≡x {!!}

    postulate
      a₀ : A₀
      _≡'_ : ∀ {c} {C : Set c} (x : C) → C → Set c

    test₁ : ∀ (a₀ : A₀) → a₀ ≡ a₀
    test₁ a₀ = id (reright A₀≡B₀ {!!})

    test₂ : A₀ → B₀
    test₂ a₀ = reright A₀≡B₀ (λ b₀ → 𝑩₀)

    test₃ : A₀ → B₀
    test₃ a₀ = reright Set≡Set (reright A₀≡B₀ (λ b₀ → 𝑩₀))

    test₄ : A₀ → B₀
    test₄ a₀ = reright Set≡Set (reright A₀≡B₀ (λ b₀ → reright A₀≡B₀ {!!}))

    test₅ : A₀ → B₀
    test₅ a₀ = reright Set≡Set 𝑩₀

    test₆ : A₀ → B₀
    test₆ a₀ = reright Set≡Set $ reright A₀≡B₀ $ {!!}

    test₇ : ∀ {α : Level}
            (a₀ : A₀)
            {β : Level}
            (X Y : Set (α ⊔ β))
            → X ≡ Y
            → Y ≡ X
    test₇ {α} a₀ {β} X Y X≡Y = id (reright X≡Y {!!})

    test₈ : (a₁𝑨₀¹ : A₁ 𝑨₀¹) → A₂ 𝑨₀¹ a₁𝑨₀¹
    test₈ a₁𝑨₀¹ = reright 𝑨₀¹≡𝑨₀² (λ a₁𝑨₀² → {!!})

    test₉ : (a₀¹ : A₀) (a₀² : A₀) (a₀¹≡a₀²-1 : a₀¹ ≡ a₀²) (a₁a₀¹ : A₁ a₀¹) (X : Set) (Y : Set) (a₀¹≡a₀²-2 : a₀¹ ≡ a₀²) → F (A₂ a₀¹ a₁a₀¹) → F (A₁ a₀¹) ≡ A₂ a₀¹ a₁a₀¹
    test₉ a₀¹ a₀² a₀¹≡a₀²-1 a₁a₀¹ X Y a₀¹≡a₀²-2 = reright a₀¹≡a₀²-1 {!!}

    module _ (A₂⋆ : (a₀ : A₀) (a₁a₀ : A₁ a₀) → A₂ a₀ a₁a₀) where
      test₁₀ : (a₀ : A₀) (a₁a₀¹ : A₁ a₀) (a₁a₀² : A₁ a₀) (a₁a₀¹≡a₁a₀² : a₁a₀¹ ≡ a₁a₀²) → A₂ a₀ a₁a₀¹
      test₁₀ a₀ a₁a₀¹ a₁a₀² a₁a₀¹≡a₁a₀² = reright a₁a₀¹≡a₁a₀² {!!}

    test₁₁ : (a₀¹ : A₀) (a₀² : A₀) (FA₁a₀¹≡FA₁a₀² : F (A₁ a₀¹) ≡ F (A₁ a₀²)) → F (A₁ a₀¹) → F (A₁ a₀¹) ≡ F (F (A₁ a₀¹))
    test₁₁ a₀¹ a₀² FA₁a₀¹≡FA₁a₀² = reright FA₁a₀¹≡FA₁a₀² {!!}

    test₁₂ : (a₀¹ : A₀) (a₀² : A₀) (FA₁a₀¹≡FA₁a₀² : F (A₁ a₀¹) ≡ F (A₁ a₀²)) → F (A₁ a₀¹) → F (A₁ a₀¹) ≡ F (F (A₁ a₀¹))
    test₁₂ a₀¹ a₀² FA₁a₀¹≡FA₁a₀² FA₁a₀¹ = reright FA₁a₀¹≡FA₁a₀² {!!}

    test₁₃ : (β : Level)
             (a₀¹ : A₀)
             (χ : Level)
             (a₀² : A₀)
             (CA₁a₀¹≡CA₁a₀² : C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C lzero (β ⊔ χ) (A₁ a₀²)) →
             C lzero (β ⊔ χ) (A₁ a₀¹)
             → Nat → Σ _ λ γ → C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))
    test₁₃ β a₀¹ χ a₀² CA₁a₀¹≡CA₁a₀² CA₁a₀¹ = reright CA₁a₀¹≡CA₁a₀² {!!}

    module M₁₃-1 (β : Level)
                 (a₀¹ : A₀)
                 (χ : Level)
                 (a₀² : A₀)
                 (CA₁a₀¹≡CA₁a₀² : C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C lzero (β ⊔ χ) (A₁ a₀²))
                 (CA₁a₀¹ : C lzero (β ⊔ χ) (A₁ a₀¹))
      where

      test-reright : Nat → Σ _ λ γ → C lzero (β ⊔ χ) (A₁ a₀¹) ≡ C γ (β ⊔ χ) (C lzero γ (A₁ a₀¹))
      test-reright = reright CA₁a₀¹≡CA₁a₀² {!!}

    test₁₄ : (a₀ : A₀) (FFA₁a₀≡FA₁a₀ : F (F (A₁ a₀)) ≡ F (A₁ a₀)) → F (F (F (F (A₁ a₀))))
    test₁₄ a₀ FFA₁a₀≡FA₁a₀ = reright FFA₁a₀≡FA₁a₀ (reright FFA₁a₀≡FA₁a₀ (reright FFA₁a₀≡FA₁a₀ {!!}))

    test₁₅ : (a₀ : A₀) (FA₁a₀≡FFA₁a₀ : F (A₁ a₀) ≡ F (F (A₁ a₀))) → F (F (A₁ a₀))
    test₁₅ a₀ FA₁a₀≡FFA₁a₀ = reright FA₁a₀≡FFA₁a₀ (reright FA₁a₀≡FFA₁a₀ {!!})

    test₁₆ : (l : A₀ → Level → Level)
             (β : Level)
             (a₀² : A₀)
             (a₀¹ : A₀)
             (CA₁a₀¹≡CA₁a₀² : C lzero (l a₀¹ β) (A₁ a₀¹) ≡ C lzero (l a₀¹ β) (A₁ a₀²))
             → C lzero (l a₀¹ β) (A₁ a₀¹)
             → Σ _ λ γ → C lzero (l a₀¹ β) (A₁ a₀¹) ≡ C γ (l a₀¹ β) (C lzero γ (A₁ a₀¹))
    test₁₆ l β a₀² a₀¹ CA₁a₀¹≡CA₁a₀² CA₁a₀¹ = reright CA₁a₀¹≡CA₁a₀² {!!}

    test₁₇ : (a₀¹ : A₀)
             (a₀² : A₀)
             (K₀a₀¹ : K₀ a₀¹)
             (a₀¹≡a₀² : a₀¹ ≡ a₀²)
           → Set
    test₁₇ a₀¹ a₀² K₀a₀¹ a₀¹≡a₀² = reright a₀¹≡a₀² {!!}

    test₁₈ : (a₀¹ : A₀)
             (a₀² : A₀)
             (k₀a₀¹ : K₀ a₀¹)
             (FK₀a₀¹ : F (K₀ a₀¹))
             (K₀a₀¹≡K₀a₀² : K₀ a₀¹ ≡ K₀ a₀²)
           → F (F (K₀ a₀¹)) ≡ F (K₀ a₀²)
    test₁₈ a₀¹ a₀² k₀a₀¹ FK₀a₀¹ K₀a₀¹≡K₀a₀² = reright K₀a₀¹≡K₀a₀² {!!}

    test₁₉ : ∀ {a₀¹ : A₀}
               {a₀² : A₀}
               {a₁a₀²-1 a₁a₀²-2 a₁a₀²-3 : A₁ a₀²}
               {a₁a₀²-2=a₁a₀²-3 : A₂ a₀² a₁a₀²-2 ≡ A₂ a₀² a₁a₀²-3}
               (R : ∀ (a₀²' : A₀) → A₂ a₀² a₁a₀²-1 ≡ A₂ a₀² a₁a₀²-2)
               (X : A₂ a₀² a₁a₀²-2 ≡ A₂ a₀² a₁a₀²-3)
               {ignore : Set}
             → A₂ a₀² a₁a₀²-1 ≡ A₂ a₀² a₁a₀²-3
    test₁₉ {a₀¹} {a₀²} {a₁a₀²-1} {a₁a₀²-2} {a₁a₀²-3} {a₁a₀²-2=a₁a₀²-3} R X = reright (R a₀¹) {!!}

    {- FAILS (correctly, though perhaps without the most comprehensible of error messages)
      test₂₀' : (f₁ : A₀) (f₂ : A₀) (A₀f₁≡A₀f₂ : A₁ f₁ ≡ A₁ f₂) (g₁ : A₁ f₁) → A₂ f₁ g₁
      test₂₀' f₁ f₂ A₀f₁≡A₀f₂ g₁ rewrite A₀f₁≡A₀f₂ = {!!}

      test₂₀ : (f₁ : A₀) (f₂ : A₀) (A₀f₁≡A₀f₂ : A₁ f₁ ≡ A₁ f₂) (g₁ : A₁ f₁) → A₂ f₁ g₁
      test₂₀ f₁ f₂ A₀f₁≡A₀f₂ g₁ = reright A₀f₁≡A₀f₂ {!!}
    -}

    test₂₀ : ∀ {a b : Level} {A : Set a} {x y : A} (x≡y : x ≡ y) → Set
    test₂₀ x≡y = reright x≡y {!!}

    test₂₁ : ∀ {a b : Level} {A : Set a} {x y : A} (B : Set b) (x≡y : x ≡ y) → Set
    test₂₁ B x≡y = reright x≡y {!!}

    test₂₂ : ∀ {a : Level} {A : Set a} {B : Set} {x : B} {y : B} (x≡y : x ≡ y) → Set
    test₂₂ x≡y = reright x≡y {!!}

    module _ (l : Level) where
      postulate P : Set

      test₂₃ : (p : P)
               (A : Set)
               (x y : A)
               (x≡y : x ≡ y)
               → Set
      test₂₃ _ _ _ _ x≡y = reright x≡y {!!}

  module Test₂ where
    record Map
             {K : Set}
             (V : K → Set)
             (Carrier : Nat → Set) {{isDecEquivalence/K : Eq K}} {{isDecEquivalence/V : (k : K) → Eq (V k)}} : Set₁ where
      field
        ∅ : Carrier 0
        _∉_ : ∀ {s} → K → Carrier s → Set
        ∅-is-empty : ∀ {𝑘} {∅ : Carrier 0} → 𝑘 ∉ ∅

      _∈_ : ∀ {s} → K → Carrier s → Set
      _∈_ k m = ¬ k ∉ m

      field
        get : ∀ {k : K} {s} {m : Carrier s} → k ∈ m → V k
        put : ∀ {k₀ : K} (v₀ : V k₀) {s₁} {m₁ : Carrier s₁} → k₀ ∉ m₁ → Σ _ λ (m₀ : Carrier (suc s₁)) → Σ _ λ (k₀∈m₀ : k₀ ∈ m₀) → get k₀∈m₀ ≡ v₀

    postulate
      A : Set

    V : A → Set
    V = λ _ → Nat

    postulate
      M : Nat → Set
      isDecEquivalence/A : Eq A
      isDecEquivalence/V : (a : A) → Eq (V a)

    postulate
      m : Map V M {{isDecEquivalence/A}} {{isDecEquivalence/V}}

    open Map m

    test₁ : (v : Nat) (k : A)
      → (k∈putkv∅ : k ∈ (fst $ put {k₀ = k} v {m₁ = ∅} ∅-is-empty))
      → Set
    test₁ v k k∈putkv∅ = let p = (put {k₀ = k} v {m₁ = ∅} ∅-is-empty) in let r = sym (snd $ snd p) in reright r {!!}

{- expected.out
?0 : b₀² ≡ b₀² → Set
?1 : (b : B₀) → b ≡ b
?2 : B₀ → B₀
?3 : B₀ → B₀
?4 : Y ≡ Y
?5 : A₂ 𝑨₀² a₁𝑨₀²
?6 : (a₁ : A₁ a₀²) → a₀² ≡ a₀² → F (A₂ a₀² a₁) → F (A₁ a₀²) ≡ A₂ a₀² a₁
?7 : A₂ a₀ a₁a₀²
?8 : F (A₁ a₀²) → F (A₁ a₀²) ≡ F (F (A₁ a₀²))
?9 : F (A₁ a₀²) → F (A₁ a₀²) ≡ F (F (A₁ a₀²))
?10 : C lzero (χ ⊔ β) (A₁ a₀²) →
Nat →
Σ Level
(λ γ → C lzero (χ ⊔ β) (A₁ a₀²) ≡ C γ (χ ⊔ β) (C lzero γ (A₁ a₀¹)))
?11 : F (A₁ a₀)
?12 : F (F (F (F (A₁ a₀))))
?13 : C lzero (l a₀¹ β) (A₁ a₀²) →
Σ Level
(λ γ →
   C lzero (l a₀¹ β) (A₁ a₀²) ≡ C γ (l a₀¹ β) (C lzero γ (A₁ a₀¹)))
?14 : K₀ a₀² → Set
?15 : K₀ a₀² → F (K₀ a₀²) → F (F (K₀ a₀²)) ≡ F (K₀ a₀²)
?16 : (A₀ → A₂ a₀² a₁a₀²-2 ≡ A₂ a₀² a₁a₀²-2) →
A₂ a₀² a₁a₀²-2 ≡ A₂ a₀² a₁a₀²-3
?17 : Set
?18 : Set
?19 : Set
?20 : Set
?21 : (k ∉ fst (put (get (fst (snd (put v ∅-is-empty)))) ∅-is-empty) →
 ⊥) →
Set
-}

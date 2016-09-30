{-# OPTIONS -v profile:10 #-}
-- compare agda issue 426
module Tactic.Reflection.Reright-Performance where
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat
  open import Agda.Builtin.List
  open import Agda.Builtin.Equality

  module before-and-after-vec-head where
    -- try putting the head element in the type, defaulting to 0

    infixr 0 case_of_
    case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
    case x of f = f x

    infixr 5 _∷_
    data H : Nat → Set where
      []  : H 0
      _∷_ : (x : Nat) → {x' : Nat} → (xs : H x') → H x

    headfn : Nat → Nat
    headfn n with n < 50
    ... | true = suc n
    ... | false = n

    compare-before-cons : {l : Nat} → (hs : H l) → H (case hs of λ {[] → 0 ; (n ∷ ns) → headfn n})
    compare-before-cons [] = []
    compare-before-cons {l} (n ∷ ns) = ifthenelse (n < 50) where
      ifthenelse : Bool → H (headfn n)
      ifthenelse true  = headfn n ∷ compare-before-cons ns -- TODO why does suc n not work here?
      ifthenelse false = headfn n ∷ compare-before-cons ns

    cons-before-compare : {l : Nat} → (hs : H l) → H (case hs of λ {[] → 0 ; (n ∷ ns) → headfn n})
    cons-before-compare [] = []
    cons-before-compare (n ∷ ns) = headfn n ∷ cons-before-compare ns where

    record ∃ {d} {D : Set d} (F : D → Set d) : Set d where
      constructor _,_
      field
        dom : D
        map : (x : D) → F x
      range : F dom
      range = map dom

    can : ∀ {d} {D : Set d} {F : D → Set d} → (e : ∃ F) → F (∃.dom e)
    can (d , m) = m d

    foo : Nat → {l : Nat} → H l → (∀ {l : Nat} → (hs : H l) → ∃ λ l' → H l') → Nat
    foo 0 [] _ = 0
    foo 0 (x ∷ xs) _ = x
    foo (suc n) xs f = -- foo n {!(λ xs' → (∃.map (f xs')) (∃.dom (f xs'))) xs!} f
                       foo n ((∃.map (f xs)) (∃.dom (f xs)) ) f
                       -- foo n (∃.map f xs) f
{-
    foo : Nat → {l : Nat} → H l → (∀ {l : Nat} → (hs : H l) → H (case hs of λ {[] → 0 ; (n ∷ ns) → headfn n})) → Nat
    foo 0 [] _ = 0
    foo 0 (x ∷ xs) _ = x
    foo (suc n) xs f = foo n (f xs) f
-}

    run-foo : ({l : Nat} → (hs : H l) → H (case hs of λ {[] → 0 ; (n ∷ ns) → headfn n})) → Nat
    run-foo = {!foo 100 (0 ∷ [])!} --

    compare-before-cons-is-fast : run-foo {!compare-before-cons!} ≡ 50
    compare-before-cons-is-fast = {!!} -- C-u C-u C-c C-,

    cons-before-compare-is-slow : run-foo {!cons-before-compare!} ≡ 50
    cons-before-compare-is-slow = {!refl!} -- C-u C-u C-c C-,

  module before-and-after-vec where

    infixr 5 _∷_
    data Vec {a} (A : Set a) : Nat → Set a where
      []  : Vec A zero
      _∷_ : {l : Nat} (x : A) (xs : Vec A l) → Vec A (suc l)

    -- check input constructor, then compare, then build output constructor
    compare-before-cons : {l : Nat} → Vec Nat l → Vec Nat l
    compare-before-cons [] = []
    compare-before-cons {l} (n ∷ ns) = ifthenelse (n < 50) where
      ifthenelse : Bool → Vec Nat l
      ifthenelse true = suc n ∷ compare-before-cons ns
      ifthenelse false = n ∷ compare-before-cons ns

    -- check input constructor, then build output constructor, then compare
    cons-before-compare : {l : Nat} → Vec Nat l → Vec Nat l
    cons-before-compare [] = []
    cons-before-compare (n ∷ ns) = (if n < 50 then suc n else n) ∷ cons-before-compare ns where
      if_then_else_ : Bool → Nat → Nat → Nat
      if true  then t else e = t
      if false then t else e = e

    infixr 0 case_of_
    case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
    case x of f = f x

    foo : Nat → {l : Nat} → Vec Nat l → (∀ {l : Nat} → Vec Nat l → Vec Nat l) → Nat
    foo 0 [] _ = 0
    foo 0 (x ∷ xs) _ = x
    --foo (suc n) xs f = foo n (f xs) f
    foo (suc n) xs f with f xs
    ... | [] = 0
    ... | (x' ∷ xs') with foo n (x' ∷ xs')
    ... | foo' = foo' f


    run-foo : (∀ {l : Nat} → Vec Nat l → Vec Nat l) → Nat
    run-foo = foo 100 (0 ∷ [])

    compare-before-cons-is-fast : run-foo compare-before-cons ≡ 50
    compare-before-cons-is-fast = {!!} -- C-u C-u C-c C-,

    cons-before-compare-is-slow : run-foo cons-before-compare ≡ 50
    cons-before-compare-is-slow = {!refl!} -- C-u C-u C-c C-,

  module before-and-after where
    compare-before-cons : List Nat → List Nat
    compare-before-cons [] = []
    compare-before-cons (n ∷ ns) = ifthenelse (n < 50) where
      ifthenelse : Bool → List Nat
      ifthenelse true = suc n ∷ compare-before-cons ns
      ifthenelse false = n ∷ compare-before-cons ns

    cons-before-compare : List Nat → List Nat
    cons-before-compare [] = []
    cons-before-compare (n ∷ ns) = (if n < 50 then suc n else n) ∷ cons-before-compare ns where
      if_then_else_ : Bool → Nat → Nat → Nat
      if true  then t else e = t
      if false then t else e = e

    infixr 0 case_of_
    case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
    case x of f = f x

    caseof-before : List Nat → List Nat
    caseof-before [] = []
    caseof-before (n ∷ ns) = case n < 50 of λ
      { true → suc n ∷ caseof-before ns
      ; false → n ∷ caseof-before ns
      }

    caseof-after : List Nat → List Nat
    caseof-after [] = []
    caseof-after (n ∷ ns) = (case (n < 50) of λ
      { true → suc n
      ; false → n
      }) ∷ caseof-after ns

    foo : Nat → List Nat → (List Nat → List Nat) → Nat
    foo 0 [] _ = 0
    foo 0 (x ∷ xs) _ = x
    foo (suc n) xs f = foo n (f xs) f

    run-foo : (List Nat → List Nat) → Nat
    run-foo = foo 100 (0 ∷ [])

    compare-before-cons-is-fast : run-foo compare-before-cons ≡ 50
    compare-before-cons-is-fast = {!!} -- C-u C-u C-c C-,

    cons-before-compare-is-slow : run-foo cons-before-compare ≡ 50
    cons-before-compare-is-slow = {!refl!} -- C-u C-u C-c C-,

    test-before : run-foo caseof-before ≡ 50
    test-before = {!!}

    test-after : run-foo caseof-after ≡ 50
    test-after = {!!}

    X = compare-before-cons -- cons-before-compare

    try-by-hand : foo 0 (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (X (0 ∷ [])))))))))))))))))))))))))))))))))))))))))) cons-before-compare ≡ 3
    try-by-hand = {!!}

  module slow-mod where
    mod : Nat -> Nat -> Nat
    mod 0       k = 0
    mod (suc n) k = ifthenelse (suc (mod n k) < k)
      where
      ifthenelse : Bool → Nat
      ifthenelse true  = suc (mod n k)
      ifthenelse false = 0

    test-mod : mod 100 10 ≡ 0
    test-mod = {!!}

  module fast-mod where
    mod : Nat -> Nat -> Nat
    mod 0       k = 0
    mod (suc n) k with suc (mod n k)
    ... | r with r < k
    ... | true = r
    ... | false = 0

    test-mod : mod 100 10 ≡ 0
    test-mod = {!refl!}

  module ulf-mod where
    case_of_ : {A B : Set} → A → (A → B) → B
    case_of_ x f = f x

    mod : Nat -> Nat -> Nat
    mod 0       k = 0
    mod (suc n) k =
      case suc (mod n k) of λ
        r → if r < k then r else 0
      where
        if_then_else_ : Bool → Nat → Nat → Nat
        if true  then t else e = t
        if false then t else e = e

    test-mod : mod 100 10 ≡ 0
    test-mod = {!refl!}

  {-
    foo 3 xs f
    foo 2 (f xs) f
    foo 1 (f (f xs)) f
    foo 0 (f (f (f xs))) f
    now try to pattern match on f (f (f xs)) as ([] vs (_ ∷ _))

    xs = 0 ∷ []

    f = compare-before-cons

    f (f (f (0 ∷ [])))
    f (f (ite 0 [] (0 < 50))))
    f (f (ite 0 [] true)))
    f (f (suc 0 ∷ f [])))
    f (ite (suc 0) (f []) (suc 0 < 50))
    f (ite (suc 0) (f []) true)
    f (suc (suc 0) ∷ f (f []))
    ite (suc (suc 0)) (f (f [])) (suc (suc 0) < 50)
    ite (suc (suc 0)) (f (f [])) true
    suc (suc (suc 0)) ∷ f (f (f []))
    -- we must evaluate all compares on the first element before reaching the cons
    -- i.e. n before before _∷_



    f = cons-before-compare

    f (f (f (0 ∷ [])))
    f (f (ite 0 [] (0 < 50) (suc 0) 0 ∷ f []))
          <----------- X₁ ---------->
    f (f (X₁ ∷ f []))
    f (ite X₁ (f []) (X₁ < 50) (suc X₁) X₁ ∷ f (f []))
       <-------------- X₂ --------------->
    f (X₂ ∷ f (f []))
    ite X₂ (f (f [])) (X₂ < 50) (suc X₂) X₂ ∷ f (f (f []))
    ANSWER: ite X₂ (f (f [])) (X₂ < 50) (suc X₂) X₂

    ... now need to evaluate X₂ to pattern match as (zero vs (suc _))
      X₂
      ite X₁ (f []) (X₁ < 50) (suc X₁) X₁
      ... now need to evaluate X₁
        X₁
        ite 0 [] (0 < 50) (suc 0) 0
        ite 0 [] true (suc 0) 0
        ANSWER: suc 0
      ite X₁ (f []) (suc 0 < 50) (suc X₁) X₁
      ite X₁ (f []) true (suc X₁) X₁
      ANSWER: suc X₁
      ... evaluate X₁ again
      ANSWER : suc (suc 0)
    ANSWER: ite X₂ (f (f [])) true (suc X₂) X₂ ∷ f (f (f []))
    suc X₂ ∷ f (f (f []))
    ... evaluate X₂ again



    f (f (ite 0 [] (0 < 50) (suc 0) 0 ∷ f []))

    f (f (ite 0 [] true (suc 0) 0 ∷ f []))
    f (f (suc 0 ∷ f []))

    f (f (ifthenelse 0 [] (0 < 50) ∷ f []))

    f = cons-before-compare
    f (f (if_then_else_ 0 [] (0 < 50) (suc 0) 0 ∷ cons-before-compare []))
    f (f (if_then_else_ 0 [] true (suc 0) 0 ∷ cons-before-compare []))
    f (f (suc 0 ∷ []))
    f (if_then_else_ (suc 0) [] (suc 0 < 50) (suc 0) ∷ cons-before-compare [])
  -}

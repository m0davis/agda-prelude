-- compare agda issue 426
module Tactic.Reflection.Reright-Performance where
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat
  open import Agda.Builtin.List
  open import Agda.Builtin.Equality

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

  foo : Nat → List Nat → (List Nat → List Nat) → Nat
  foo 0 [] _ = 0
  foo 0 (x ∷ xs) _ = x
  foo (suc n) xs f = foo n (f xs) f

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


    ? sharing









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

  run-foo : (List Nat → List Nat) → Nat
  run-foo = foo 100 (0 ∷ [])

  compare-before-cons-is-fast : run-foo compare-before-cons ≡ 50
  compare-before-cons-is-fast = {!!} -- C-u C-u C-c C-,

  cons-before-compare-is-slow : run-foo cons-before-compare ≡ 50
  cons-before-compare-is-slow = {!refl!} -- C-u C-u C-c C-,

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

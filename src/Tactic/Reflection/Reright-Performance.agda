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

  run-foo : (List Nat → List Nat) → Nat
  run-foo = foo 100 (0 ∷ [])

  compare-before-cons-is-fast : run-foo compare-before-cons ≡ 50
  compare-before-cons-is-fast = {!!} -- C-u C-u C-c C-,

  cons-before-compare-is-slow : run-foo cons-before-compare ≡ 50
  cons-before-compare-is-slow = {!!} -- C-u C-u C-c C-,

  mod : Nat -> Nat -> Nat
  mod 0       k = 0
  mod (suc n) k = ifthenelse (suc (mod n k) < k)
    where
    ifthenelse : Bool → Nat
    ifthenelse true  = suc (mod n k)
    ifthenelse false = 0

  test-mod : mod 100 10 ≡ 0
  test-mod = {!refl!}

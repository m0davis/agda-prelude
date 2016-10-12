module Tactic.Reflection.Reright-CPS-Memory where

open import Prelude.Decidable
open import Prelude.Equality
open import Prelude.Nat
open import Prelude.Bool
open import Prelude.Ord
open import Prelude.List
open import Prelude.Function
open import Prelude.Strict
open import Prelude.Product
open import Prelude.Sum

data Term : Set where
  pi : Term → Term → Term
  var : Nat → List Term → Term

mutual
  id-Term& : Term → {B : Set} → (Term → B) → B
  id-Term& (pi a b) f = id-Term& a λ a → id-Term& b λ b → f (pi a b)
  id-Term& (var n xs) f = id-ListTerm& xs λ xs → f (var n xs)

  id-ListTerm& : List Term → {B : Set} → (List Term → B) → B
  id-ListTerm& [] f = f []
  id-ListTerm& (x ∷ xs) f = id-Term& x λ x → id-ListTerm& xs λ xs → f (x ∷ xs)

mutual
  sucTerm : Term → Term
  sucTerm (pi t₁ t₂) = pi (sucTerm t₁) (sucTerm t₂)
  sucTerm (var n ts) = case n <? 0 of λ { true → var n (sucTerms ts) ; false → var (suc n) (sucTerms ts) }

  sucTerms : List Term → List Term
  sucTerms [] = []
  sucTerms (t ∷ ts) = sucTerm t ∷ sucTerms ts

pi-inj₁ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₁ ≡ t₁′
pi-inj₁ refl = refl

pi-inj₂ : ∀ {t₁ t₁′ t₂ t₂′} → pi t₁ t₂ ≡ pi t₁′ t₂′ → t₂ ≡ t₂′
pi-inj₂ refl = refl

var-inj₁ : ∀ {n n′ ts ts′} → var n ts ≡ var n′ ts′ → n ≡ n′
var-inj₁ refl = refl

var-inj₂ : ∀ {n n′ ts ts′} → var n ts ≡ var n′ ts′ → ts ≡ ts′
var-inj₂ refl = refl

mutual
  eqTerm : (x y : Term) → Dec (x ≡ y)
  eqTerm (pi t₁ t₂) (pi t₁′ t₂′) = decEq₂ pi-inj₁ pi-inj₂ (eqTerm t₁ t₁′) (eqTerm  t₂ t₂′)
  eqTerm (pi _ _) (var _ _) = no (λ ())
  eqTerm (var _ _) (pi _ _) = no (λ ())
  eqTerm (var n ts) (var n′ ts′) = decEq₂ var-inj₁ var-inj₂ (n == n′) (eqTerms ts ts′)

  eqTerms : (x y : List Term) → Dec (x ≡ y)
  eqTerms [] [] = yes refl
  eqTerms [] (_ ∷ _) = no (λ ())
  eqTerms (_ ∷ _) [] = no (λ ())
  eqTerms (t ∷ ts) (t′ ∷ ts′) = decEq₂ cons-inj-head cons-inj-tail (eqTerm t t′) (eqTerms ts ts′)

instance
  EqTerm : Eq Term
  _==_ {{EqTerm}} = eqTerm

{-# TERMINATING #-}
_r[_/_] : Term → Term → Term → Term
term r[ to / from ]
 with term == from
... | yes _ = to
... | no _
 with term
... | pi termₗ termᵣ = pi (termₗ r[ to / from ]) (termᵣ r[ sucTerm to / sucTerm from ])
... | var n terms = var n (map (_r[ to / from ]) terms)

deep-term : Term
deep-term = make-deep-term 100 where
  make-deep-term : Nat → Term
  make-deep-term 0 = var 0 []
  make-deep-term (suc d) = pi (make-deep-term d) (make-deep-term d)

wide-term : Term
wide-term = make-wide-term 1 where
  make-wide-term : Nat → Term
  make-wide-term 0 = var 0 []
  make-wide-term (suc n) = var n (make-wide-term n ∷ [])

c&r : List Term → List Term
c&r [] = []
c&r (t ∷ ts) =
  id-Term& (t r[ wide-term / var 0 [] ]) λ t' →
  if (isNo $ t == t') then
    t' ∷ c&r ts
  else
    c&r ts

length& : ∀ {a} {A : Set a} → List A → ∀ {b} {B : Set b} → (Nat → B) → B
length& {A = A} xs {B = B} f = helper 0 xs where
  helper : Nat → List A → B
  helper l [] = f l
  helper l (x ∷ xs) = helper (suc l) xs

test : c&r (deep-term ∷ []) ≡ []
test = {!!}

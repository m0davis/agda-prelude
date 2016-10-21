-- compare agda issue 426
module Tactic.Reright-2 where

open import Prelude.Memoization
open import Prelude

Natμ : (n : Nat) → Mem n
Natμ zero = putμ refl
Natμ (suc n) = -- putμ (cong suc refl) --
               case Natμ n of λ { (putμ n-refl) → putμ (cong suc n-refl) }

data Term : Set where
  pi : Term → Term → Term
  var : Nat → List Term → Term

mutual
  Termμ : (t : Term) → Mem t
  Termμ (pi a b) =
    case (Termμ a , Termμ b) of λ
    { (putμ a-refl , putμ b-refl) →
      putμ (cong₂ pi a-refl b-refl) }
  Termμ (var x ts) =
    case (Natμ x , ListTermμ ts) of λ
    { (putμ x-refl , putμ ts-refl) →
      putμ (cong₂ var x-refl ts-refl) }

  ListTermμ : (ts : List Term) → Mem ts
  ListTermμ [] = putμ refl
  ListTermμ (t ∷ ts) =
    case (Termμ t , ListTermμ ts) of λ
    { (putμ t-refl , putμ ts-refl) →
      putμ (cong₂ _∷_ t-refl ts-refl) }

ListTermNatμ : (tns : List (Term × Nat)) → Mem tns
ListTermNatμ [] = putμ refl
ListTermNatμ ((t , n) ∷ tns) =
  case (Termμ t , Natμ n , ListTermNatμ tns) of λ
  { (putμ t-refl , putμ n-refl , putμ tns-refl) →
    putμ (cong₂ _∷_ (cong₂ _,_ t-refl n-refl) tns-refl) }

wkNat : Nat → Nat → Nat → Nat
wkNat lo k n = if k <? lo then n else n + k

mutual
  wkTerm : Nat → Nat → Term → Term
  wkTerm lo k (pi a b) = pi (wkTerm lo k a) (wkTerm (suc lo) k b)
  wkTerm lo k (var n ts) = var (wkNat lo k n) (wkTerms lo k ts)

  wkTerms : Nat → Nat → List Term → List Term
  wkTerms lo k [] = []
  wkTerms lo k (t ∷ ts) = wkTerm lo k t ∷ wkTerms lo k ts

mutual
  sizeTerm : Term → Nat
  sizeTerm (pi a b) = suc (sizeTerm a + sizeTerm b)
  sizeTerm (var n ts) = suc (n + sizeTerms ts)

  sizeTerms : List Term → Nat
  sizeTerms [] = 0
  sizeTerms (t ∷ ts) = sizeTerm t + sizeTerms ts

sizeTermNats : List (Term × Nat) → Nat
sizeTermNats [] = 0
sizeTermNats ((t , n) ∷ tns) = suc (sizeTerm t + n + sizeTermNats tns)

wide-term : Term
wide-term = make-wide-term 10 where
  make-wide-term : Nat → Term
  make-wide-term 0 = var 0 []
  make-wide-term (suc n) = var n (make-wide-term n ∷ [])

deep-term : Term
deep-term = make-deep-term 5 where
  make-deep-term : Nat → Term
  make-deep-term 0 = wide-term
  make-deep-term (suc d) = pi (make-deep-term d) (make-deep-term d)

deep-terms : List Term
deep-terms = replicate 20 deep-term

before-operation : List Term → List (Term × Nat)
before-operation [] = []
before-operation (t ∷ ts) = (wkTerm 0 1 (wkTerm 0 1 (wkTerm 0 1 t)) , 0) ∷ before-operation ts

after-operation : Nat → List (Term × Nat) → List Nat
after-operation m tns = (λ { (_ , n) → m - n }) <$> tns

test-before : List Term → Nat
test-before tns =
  case ListTermNatμ (before-operation tns) of λ
  { (getμ befores) → sizeTermNats befores }

test-after : List Term → List Nat
test-after tns =
  case length tns of λ { l →
  case Natμ l of λ { (getμ l) →
  case before-operation tns of λ { befores →
  case ListTermNatμ befores of λ { (getμ befores) →
  after-operation l befores }}}}

test-area : Term × Term × Term × Term × Term
test-area = {!test-after deep-terms!} ,
            {!test-before deep-terms!} ,
            {!test-after input-terms!} ,
            {!test-before input-terms!} ,
            {!sizeTerms input-terms!}

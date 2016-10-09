-- compare agda issue 426
module Tactic.Reflection.Reright-Performance-BestExamples-ContinuationPassingStyle where

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
deep-term = make-deep-term 10 where
  make-deep-term : Nat → Term
  make-deep-term 0 = var 0 []
  make-deep-term (suc d) = pi (make-deep-term d) (make-deep-term d)

wide-term : Term
wide-term = make-wide-term 1 where
  make-wide-term : Nat → Term
  make-wide-term 0 = var 0 []
  make-wide-term (suc n) = var n (make-wide-term n ∷ [])

fast : Bool × List Term
fast = go (deep-term ∷ deep-term ∷ []) where
  go : List Term → Bool × List Term
  go [] = true , []
  go (t ∷ ts) = if (isNo $ t == t r[ wide-term / wide-term ]) then
                  true , t r[ wide-term / wide-term ] ∷ snd (go ts) -- `true ,_` acts as a delay
                else
                  go ts

slow : Bool × List Term
slow = true , go (deep-term ∷ deep-term ∷ []) where -- oops, this delays nothing!
  go : List Term → List Term
  go [] = []
  go (t ∷ ts) = if (isNo $ t == t r[ wide-term / wide-term ]) then
                  t r[ wide-term / wide-term ] ∷ go ts
                else
                  go ts

try : Bool × List Term → Term
try (_ , ts) = let l = length ts in deep-term r[ var l [] / var l [] ] -- pattern match strips the delays -- they will run if forced to! -- fortunately, length doesn't force them in "fast", b/c "fast" computed the list without delay (only the elements of the list have been delayed) -- otoh, "slow" delayed the entire computation; now when length is applied to the stripped computation, it must compute "go" before finding a list-like pattern match.

try-harder'' : Nat → Term
try-harder'' l = deep-term r[ var l [] / var l [] ]

try-harder' : Nat → List Term → Term
try-harder' l [] = try-harder'' l
try-harder' l (t ∷ ts) = try-harder' (suc l) ts

try-harder : Bool × List Term → Term
try-harder (_ , ts) = try-harder' 0 ts

cps-length : ∀ {a} {A : Set a} → List A → ∀ {b} {B : Set b} → (Nat → B) → B
cps-length {A = A} xs {B = B} f = helper 0 xs where
  helper : Nat → List A → B
  helper l [] = f l
  helper l (x ∷ xs) = helper (suc l) xs

try-cps : Bool × List Term → Term
try-cps bts = cps-length (snd bts) try-harder'' -- showing that we never needed to add that fake delay into slow

-- the difference between hell and help is that when you go through help you get to p. this ain't no help!
with-helP : Bool × List Term → Term
with-helP (_ , ts)
 with length ts
... | l = try-harder'' l

test-area : Term × Term × Term × Term × Term
test-area = {!try fast!} , -- fast
            {!try slow!} , -- slow
            {!try-harder slow!} , -- fast
            {!try-cps slow!} , -- fast
            {!with-helP slow!} -- slow

{- normalise: try fast
     try fast
     try (go (deep-term ∷ []))
     try (if (isNo $ deep-term == deep-term r[ wide-term / wide-term ]) then true , deep-term r[ wide-term / wide-term ] ∷ snd (go []) else go [])
     try (if false then true , deep-term r[ wide-term / wide-term ] ∷ snd (go []) else go [])
     try (go [])
     try (true , [])
     deep-term r[ var (length []) [] / var (length []) [] ]
-}
{- normalise: try slow
     try slow
     try (true , go (deep-term ∷ []))
     deep-term r[ var (length (go (deep-term ∷ []))) [] / var (length (go (deep-term ∷ []))) [] ]
-}
{- normalise: try-harder slow
     try-harder slow
     try-harder (true , go (non-matching-term ∷ matching-term ∷ []))
     try-harder' (go (non-matching-term ∷ matching-term ∷ []))
     try-harder' (if (isNo $ non-matching-term == non-matching-term r[ replacer-term / matcher-term ]) then non-matching-term r[ replacer-term / matcher-term ] ∷ go (matching-term ∷ []) else go (non-matching-term ∷ []))
     try-harder' 0 (if false then non-matching-term r[ replacer-term / matcher-term ] ∷ go (matching-term ∷ []) else go (matching-term ∷ []))
     try-harder' 0 (go (matching-term ∷ []))
     try-harder' 0 (if (isNo $ matching-term == matching-term r[ replacer-term / matcher-term ]) then matching-term r[ replacer-term / matcher-term ] ∷ go [] else go [])
     try-harder' 0 (if true then matching-term r[ replacer-term / matcher-term ] ∷ go [] else go [])
     try-harder' 0 (matching-term r[ replacer-term / matcher-term ] ∷ go [])
     try-harder' 0 (matching-term r[ replacer-term / matcher-term ] ∷ go [])
     try-harder' 0 (matching-term r[ replacer-term / matcher-term ] ∷ go [])
     try-harder' 1 (go [])
     try-harder' 1 []
     try-harder'' 1
     deep-term r[ var 1 [] / var 1 [] ]
-}

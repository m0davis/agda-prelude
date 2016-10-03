-- compare agda issue 426
module Tactic.Reflection.Reright-Performance where

module lifting-and-unlifting where
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat
  open import Agda.Builtin.List
  open import Agda.Builtin.Equality

  if_then_else_ : ∀ {a} {A : Set a} → Bool → A → A → A
  if true  then t else e = t
  if false then t else e = e

  [_$_]×_ : ∀ {a} {A : Set a} → (List A → List A) → List A → Nat → List A
  [ _ $ xs ]× 0 = xs
  [ f $ xs ]× suc n = [ f $ f xs ]× n

  unlifted-weaken : List Nat → List Nat
  unlifted-weaken [] = []
  unlifted-weaken (n ∷ ns) = (if n < 0 then n else suc n) ∷ unlifted-weaken ns

  test-unlifted-weaken : [ unlifted-weaken $ 0 ∷ [] ]× 100 ≡ 100 ∷ []
  test-unlifted-weaken = {!refl!} -- slow

  length : ∀ {a} {A : Set a} → List A → Nat
  length [] = 0
  length (_ ∷ xs) = suc (length xs)

  test-length-unlifted-weaken : length ([ unlifted-weaken $ [ 0 ∷_ $ [] ]× 1000 ]× 1000) ≡ 1000
  test-length-unlifted-weaken = refl

  lifted-weaken : List Nat → List Nat
  lifted-weaken [] = []
  lifted-weaken (n ∷ ns)
   with n < 0
  ... | true = n ∷ lifted-weaken ns
  ... | false = suc n ∷ lifted-weaken ns

  test-lifted-weaken : [ lifted-weaken $ 0 ∷ [] ]× 100 ≡ 100 ∷ []
  test-lifted-weaken = {!refl!} -- fast

  test-length-lifted-weaken : length ([ lifted-weaken $ [ 0 ∷_ $ [] ]× 100 ]× 1000) ≡ 100
  test-length-lifted-weaken = {!refl!} -- slow

  unlifted-mod : Nat -> Nat -> Nat
  unlifted-mod 0       k = 0
  unlifted-mod (suc n) k = if (suc (unlifted-mod n k) < k) then suc (unlifted-mod n k) else 0

  test-unlifted-mod : unlifted-mod 100 10 ≡ 0
  test-unlifted-mod = {!refl!} -- slow

  lifted-mod : Nat -> Nat -> Nat
  lifted-mod 0       k = 0
  lifted-mod (suc n) k
    with suc (lifted-mod n k)
  ... | r
    with r < k
  ... | true = r
  ... | false = 0

  test-lifted-mod : lifted-mod 100 10 ≡ 0
  test-lifted-mod = {!refl!} -- fast with --sharing, otherwise slow

  {-
     [ unlifted-weaken $ 0 ∷ [] ]× 3
     unlifted-weaken (unlifted-weaken (unlifted-weaken (0 ∷ [])))
     unlifted-weaken (unlifted-weaken ((if 0 < 0 then 0 else suc 0) ∷ unlifted-weaken []))
                                       <----------- n₁ ----------->   <------ ns₁ ----->
     unlifted-weaken (unlifted-weaken (             n₁              ∷         ns₁       ))

     unlifted-weaken ((if n₁ < 0 then n₁ else suc n₁) ∷ unlifted-weaken ns₁)
                      <------------- n₂ ------------>   <------- ns₂ ----->
     unlifted-weaken (               n₂               ∷          ns₂       )
     (if n₂ < 0 then n₂ else suc n₂) ∷ unlifted-weaken ns₂
     <--------------- n₃ ---------->   <------- ns₃ ----->
                      n₃             ∷ ns₃
     (if n₂ < 0 then n₂ else suc n₂) ∷ unlifted-weaken ns₂
         ? n₂ < 0
           (if n₁ < 0 then n₁ else suc n₁) < 0
               ? n₁ < 0
                 (if 0 < 0 then 0 else suc 0) < 0
                     ? 0 < 0
                     false
                     suc 0


           (if (if 0 < 0 then 0 else suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else suc (if 0 < 0 then 0 else suc 0)) < 0
               ?


  -}

  {-
     [ lifted-weaken $ 0 ∷ [] ]× 3
     lifted-weaken (lifted-weaken (lifted-weaken (0 ∷ [])))
                                   ? 0 < 0
                                     false
                                   suc 0 ∷ lifted-weaken []
     lifted-weaken (lifted-weaken (suc 0 ∷ lifted-weaken []))
                    ? suc 0 < 0
                      false
                    suc (suc 0) ∷ lifted-weaken (lifted-weaken [])
     lifted-weaken (suc (suc 0) ∷ lifted-weaken (lifted-weaken []))
     ? suc (suc 0) < 0
       false
     suc (suc (suc 0)) ∷ lifted-weaken (lifted-weaken (lifted-weaken []))
     suc (suc (suc 0)) ∷ lifted-weaken (lifted-weaken [])
     suc (suc (suc 0)) ∷ lifted-weaken []
     suc (suc (suc 0)) ∷ []
 -}

module continuation-passing where
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
                    true , t r[ wide-term / wide-term ] ∷ snd (go ts)
                  else
                    go ts

  slow : Bool × List Term
  slow = true , go (deep-term ∷ deep-term ∷ []) where
    go : List Term → List Term
    go [] = []
    go (t ∷ ts) = if (isNo $ t == t r[ wide-term / wide-term ]) then
                    t r[ wide-term / wide-term ] ∷ go ts
                  else
                    go ts

  try : Bool × List Term → Term
  try (_ , ts) = let l = length ts in deep-term r[ var l [] / var l [] ]

  try-harder'' : Nat → Term
  try-harder'' l = deep-term r[ var l [] / var l [] ]

  try-harder' : Nat → List Term → Term
  try-harder' l [] = try-harder'' l
  try-harder' l (t ∷ ts) = try-harder' (suc l) ts

  try-harder : Bool × List Term → Term
  try-harder (_ , ts) = try-harder' 0 ts

  test-area : Set × Set × Set
  test-area = {!try fast!} , {!try slow!} , {!try-harder slow!}

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

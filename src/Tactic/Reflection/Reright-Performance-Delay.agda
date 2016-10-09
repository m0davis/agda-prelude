{-# OPTIONS --copatterns #-}
module Tactic.Reflection.Reright-Performance-Delay where
  open import Prelude.Decidable
  open import Prelude.Equality
  open import Prelude.Nat
  open import Prelude.Bool
  open import Prelude.Ord
  open import Prelude.List
  open import Prelude.Function
  open import Prelude.Product
  open import Prelude.Sum
  open import Prelude renaming (force to force!)
  open import Agda.Builtin.Size

  mutual
    data Delay (i : Size) {𝑎} (𝐴 : Set 𝑎) : Set 𝑎 where
      now : (𝑎 : 𝐴) → Delay i 𝐴
      later : (𝑎′ : ∞Delay i 𝐴) → Delay i 𝐴

    record ∞Delay (i : Size) {𝑎} (𝐴 : Set 𝑎) : Set 𝑎 where
      coinductive
      field force : {j : Size< i} → Delay j 𝐴

  open ∞Delay public

  mutual
    _⟫=_ : ∀ {i a} {A B : Set a} → Delay i A → (A → Delay i B) → Delay i B
    now a ⟫= f = f a
    later a∞ ⟫= f = later (a∞ ∞⟫= f)

    _∞⟫=_ : ∀ {i a} {A B : Set a} → ∞Delay i A → (A → Delay i B) → ∞Delay i B
    force (a∞ ∞⟫= f) = force a∞ ⟫= f


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

  reverse& : ∀ {a} {A : Set a} → List A → ∀ {b} {B : Set b} → (List A → B) → B
  reverse& xs f = go xs [] f where
    go : ∀ {a} {A : Set a} → List A → List A → ∀ {b} {B : Set b} → (List A → B) → B
    go [] xs f = f xs
    go (m ∷ ms) xs f = go ms (m ∷ xs) f

  data Foo (i : Size) : Set where
    foo : Foo i

  size-test : ∀ {i} {j : Size< i} → Foo j → Foo i
  size-test f = f

  mutual
    ld2dl : ∀ {i} {j : Size< i} {a} → {A : Set a} → List (Delay j A) → Delay i (List A)
    ld2dl [] = now []
    ld2dl (now x ∷ xs) = {!!}
    ld2dl {i} {j} (later x ∷ xs) = {!(force x)!}

    _∷d_ : ∀ {i a} {A : Set a} → A → Delay i (List A) → Delay i (List A)
    x ∷d now xs = now (x ∷ xs)
    x ∷d later xs = x ∷∞ xs

    _∷∞_ : ∀ {i a} {A : Set a} → A → ∞Delay i (List A) → Delay i (List A)
    x ∷∞ xs = {!x ∷d force xs!}

    _∞∷∞_ : ∀ {i a} {A : Set a} → A → ∞Delay i (List A) → ∞Delay i (List A)
    x ∞∷∞ xs = {!!}

  -- ∞Delay i A → List (Delay i A) → Delay i (List A)

  {-# TERMINATING #-}
  mutual
    _rd[_/_] : ∀ {i} → Term → Term → Term → Delay i Term
    term rd[ to / from ]
     with term == from
    ... | yes _ = now to
    ... | no _
     with term
    ... | pi termₗ termᵣ =
      (termₗ rd[ to / from ]) ⟫= λ
      l → (termᵣ rd[ to / from ]) ⟫= λ
      r → now (pi l r)
    -- pi (termₗ rd[ to / from ]) (termᵣ rd[ sucTerm to / sucTerm from ])
    ... | var n terms =
      {!(map (_rd[ to / from ]) terms)!}
      -- now {!!} -- var n (map (_rd[ to / from ]) terms)

    --make-pi : ∀ {i} → Term → Term → Term → Term → ∞Delay i Term
    --make-pi from to termₗ termᵣ = record { force = now (pi {!!} {!!}) }

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
  test-area = {!try fast!} ,
              {!try slow!} ,
              {!try-harder slow!} ,
              {!try-cps slow!} ,
              {!with-helP slow!}

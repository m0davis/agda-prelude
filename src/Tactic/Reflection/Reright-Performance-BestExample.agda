-- compare agda issue 426
module Tactic.Reflection.Reright-Performance-BestExample where

open import Prelude

data Term : Set where
  set : Term
  pi : Term → Term → Term
  var : Nat → List Term → Term

mutual
  wkTermFrom : Nat → Nat → Term → Term
  wkTermFrom lo k set = set
  wkTermFrom lo k (pi a b) = pi (wkTermFrom lo k a) (wkTermFrom (suc lo) k b)
  wkTermFrom lo k (var x args) = case x <? lo of λ { true → var x (wkTermsFrom lo k args) ; false → var (x + k) (wkTermsFrom lo k args) }
                               --if x <? lo then var  x      (wkTerms args)
                               --           else var (x + k) (wkTerms args)
                               --var (if x <? lo then x else (x + k)) (wkTerms args)

  wkTermsFrom : Nat → Nat → List Term → List Term
  wkTermsFrom lo k [] = []
  wkTermsFrom lo k (t ∷ ts) = wkTermFrom lo k t ∷ wkTermsFrom lo k ts

wkTerm = wkTermFrom 0
wkTerms = wkTermsFrom 0

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
  eqTerm set set = yes refl
  eqTerm (pi t₁ t₂) (pi t₁′ t₂′) = decEq₂ pi-inj₁ pi-inj₂ (eqTerm t₁ t₁′) (eqTerm  t₂ t₂′)
  eqTerm (var n ts) (var n′ ts′) = decEq₂ var-inj₁ var-inj₂ (n == n′) (eqTerms ts ts′)
  eqTerm set (pi _ _) = no λ ()
  eqTerm set (var _ _) = no λ ()
  eqTerm (pi _ _) set = no λ ()
  eqTerm (pi _ _) (var _ _) = no λ ()
  eqTerm (var _ _) set = no λ ()
  eqTerm (var _ _) (pi _ _) = no λ ()

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
_r[_/_] = depth= 0 |_r[_/_] where
  depth=_|_r[_/_] : Nat → Term → Term → Term → Term
  depth= d | term r[ to / from ]
   with term == wkTerm d from
  ... | yes _ = wkTerm d to
  ... | no _
   with term
  ... | set = set
  ... | pi a b = pi (depth= d | a r[ to / from ]) (depth= suc d | b r[ to / from ])
  ... | var n terms = var n (map (depth= d |_r[ to / from ]) terms)

{-# TERMINATING #-}
_r[_/_]? : Term → Term → Term → Maybe Term
term r[ to / from ]?
 with term == from
... | yes _ = just to
... | no _
 with term
... | set = nothing
... | pi a b =
  case (a r[ to / from ]? , b r[ wkTerm 1 to / wkTerm 1 from ]?) of λ
  { (a' , b') → {!!} }
--pi (a [ to / from ]?) (b [ wkTerm to / wkTerm from ]?)
... | var n terms = {!!}

infixr 4 _`→_
_`→_ : Term → Term → Term
a `→ b = pi a b

pattern var₀ x = var x []
pattern var₁ x arg₁ = var x (arg₁ ∷ [])
pattern var₂ x arg₁ arg₂ = var x (arg₁ ∷ arg₂ ∷ [])

{- For the test below, we model the hole in the following function:

foo : (A : Set) (x y : A) (F : A → A → Set) (G : Set → Set)
      (f₁ f₂ ... fₗ : F x y) →
      (g₁ : G f₁)
      (g₂ : G f₂)
      ...
      (gₘ : G fₘ)
      → Set
foo A x y F G t₁ t₂ ... tₙ = ?

NB: m ≤ l, and n ≤ l + m, so l - m ≥ 0 and l + m - n ≥ 0.

We then construct a helper function that will allow us to rewrite x ≡ y. Here are some examples of what the helper function will look like:

Example 1. If n = l + m, the helper function will have the following type:

helper : (w : Set)
         (f₁ : F w y) (f₂ : F w y) ... (fₗ : F w y)
         (g₁ : G f₁)
         (g₂ : G f₂)
         ...
         (gₘ : G fₘ)
         (_ : ((f₁' : F y y) (f₂' : F y y) ... (fₗ' : F y y)
               (g₁' : G f₁') (g₂' : G f₂') ... (gₘ' : G fₘ')
               → set))
         → set

Example 2. If n = 0, the helper function will have the following type:

helper : (w : Set)
         (_ : ((f₁' : F y y) (f₂' : F y y) ... (fₗ' : F y y)
               (g₁' : G f₁') (g₂' : G f₂') ... (gₘ' : G fₘ')
               → set))
         (f₁ f₂ ... fₗ : F w y)
         (g₁ : G f₁)
         (g₂ : G f₂)
         ...
         (gₘ : G fₘ)
         → set
-}

-- make-model-of-hole m l-m l+m-n = (the context , the goal) at the hole of the function `foo` described above. `m` is the number of `g` terms; `l-m` is the number of additional `f` terms, and `l+m-n` are the number of `f` and `g` terms that wind-up in the goal.

-- m = m
-- l = l-m + m
-- n = l + m - l+m-n = l-m + m + m - l+m-n = l-m + 2 * m - l+m-n

-- the number of `f` terms in the context is `min l n`
-- the number of `g` terms in the context is `min m (n - l)`

-- correspondingly,
-- the number of `f` terms in the goal is l - min l n
-- the number of `g` terms in the goal is m - min m (n - l)


make-model-of-hole : Nat → Nat → Nat → List Term × Term
make-model-of-hole m l-m l+m-n = the-context , the-goal
  where

  l = l-m + m
  n = l-m + 2 * m - l+m-n

  context-#f = min l n
  context-#g = min m (n - l)
  goal-#f = l - context-#f
  goal-#g = m - context-#g

  -- this is like what would be returned by Agda.Builtin.Reflection.getContext
  the-context = prepend-initial-terms& λ Γ →
                prepend-f-terms& context-#f Γ λ Γ →
                prepend-g-terms& context-#g Γ λ Γ →
                Γ
    where

    prepend-initial-terms& : (List Term → List Term) → List Term
    prepend-initial-terms& cc =
      cc $ -- (G : Set → Set)
              (set `→ set) ∷
           -- (F : A → A → Set)
              (var₀ 2 `→ var₀ 3 `→ set) ∷
           -- (y : A)
              var₀ 1 ∷
           -- (x : A)
              var₀ 0 ∷
           -- (A : Set)
              set ∷
              []

    prepend-f-terms& : Nat → List Term → (List Term → List Term) → List Term
    prepend-f-terms& 0 Γ cc = cc Γ
    prepend-f-terms& (suc l') Γ cc =
      -- we are prepending the (l - l')ᵗʰ term of the form `F x y`
      -- the DeBruijn index (l - suc l') refers to the term `G` in `foo`
      -- so, the following indices refer to `F`, `y`, and `x`, respectively.
      let :F = l - l' -- = :G + 1 = (l - suc l') + 1
          :y = l - l' + 1 -- = :F + 1
          :x = l - l' + 2 -- = :y + 1
      in
      prepend-f-terms& l' (var₂ :F (var₀ :x) (var₀ :y) ∷ Γ) cc

    prepend-g-terms& : Nat → List Term → (List Term → List Term) → List Term
    prepend-g-terms& 0 Γ cc = cc Γ
    prepend-g-terms& (suc m') Γ cc =
      -- we are prepending the (m - m')ᵗʰ term of the form `G fᵢ`
      -- the DeBruijn index (m - suc m') refers to the term `fₗ` in `foo`
      -- so, the folowing indices refer to `G`, and `fₓ`.
      let :G = m - suc m' + l -- = :fₗ + l
          :fᵢ = l - 1 -- = :G - (m - m') =  m - suc m' + l - (m - m') = l - 1
      in
      prepend-g-terms& m' (var₁ :G (var₀ :fᵢ) ∷ Γ) cc

  -- this is like what would be returned by Agda.Builtin.Reflection.inferType hole
  the-goal = f-terms goal-#f (g-terms goal-#g set) where
    g-terms : Nat → Term → Term
    g-terms 0 goal = goal
    g-terms (suc m') goal =
      let :G =
          :fᵢ =
      in
      var₁ :G (var₀ :fᵢ) `→ goal
      --

--     let index-G =
--   g-terms 0 gs = -terms l gs

--   fg-terms 0

--   innermost-Γ
--    with l-m + m
--   ... | l = f-terms ++ g-terms where
--     f-terms = go l where
--       go 0 = []
--       go (suc l-1) =
--     let l = l-m - m in



--   outermost-Γ : List Term
--   outermost-Γ =

-- -- make-`Γ n = context with n terms on the lhs
-- make-`Γ : Nat → List Term
-- make-`Γ 0 = []
-- make-`Γ (suc n) = `Fxy ∷ wkTerms 1 (make-`Γ n)

-- make-`Γ₂ : Nat → List Term
-- make-`Γ₂ 0 = []
-- make-`Γ₂ (suc n) = wkTerm n `Fxy ∷ make-`Γ₂ n

-- test : Set
-- test = {!index (make-`Γ₂ 10000) 0!}
-- -- index (make-`Γ 1000) 300 -- 3 seconds ; 600 -- 13 seconds




-- -- make-`Goal (m - n) n = goal at "?" above,
-- make-`Goal : Nat → Nat → Term
-- make-`Goal 0         n = wkTerm n `Fxy
-- make-`Goal (suc m-n) n = wkTerm n `Fxy `→ wkTerm 1 (make-`Goal m-n n)

-- make-`Γ×`Goal : Nat → Nat → List Term × Term
-- make-`Γ×`Goal ∣Γ∣ ∣Goal∣₋₁ = make-`Γ ∣Γ∣ , make-`Goal ∣Goal∣₋₁ ∣Γ∣

-- `Γ×`Goal : List Term × Term
-- `Γ×`Goal = {!make-`Γ×`Goal 2 4!}

-- test-`Γ×`Goal :
--   make-`Γ×`Goal 2 4
--     ≡
--   (var 2 (var 1 [] ∷ var 0 [] ∷ []) ∷
--    var 3 (var 2 [] ∷ var 1 [] ∷ []) ∷ []
--    ,
--    pi (var 4 (var 3 [] ∷ var 2 [] ∷ []))
--       (pi (var 5 (var 4 [] ∷ var 3 [] ∷ []))
--           (pi (var 6 (var 5 [] ∷ var 4 [] ∷ []))
--               (pi (var 7 (var 6 [] ∷ var 5 [] ∷ []))
--                   (var 8 (var 7 [] ∷ var 6 [] ∷ []))))))
-- test-`Γ×`Goal = refl

-- `L : Term
-- `L = var₀ 1

-- `R : Term
-- `R = var₀ 0

-- Reordering = List (Nat × Nat)

-- Γ[w/L] : List Term → List Term
-- Γ[w/L] = go 0 where
--   go : Nat → List Term → List Term
--   go _ [] = []
--   go d (γ ∷ γs) = wkTerm (2 + d) γ r[ var₀ (suc d) / wkTerm (2 + d) `L ] ∷ go (suc d) γs

-- -- make-deep-and-wide-term : Nat → Nat → Term
-- -- make-deep-and-wide-term depth width = {!depth width!}

-- -- -- deep-term : Term
-- -- -- deep-term = make-deep-term 10 where
-- -- --   make-deep-term : Nat → Term
-- -- --   make-deep-term 0 = var 0 []
-- -- --   make-deep-term (suc d) = pi (make-deep-term d) (make-deep-term d)

-- -- -- wide-term : Term
-- -- -- wide-term = make-wide-term 1 where
-- -- --   make-wide-term : Nat → Term
-- -- --   make-wide-term 0 = var 0 []
-- -- --   make-wide-term (suc n) = var n (make-wide-term n ∷ [])

-- -- -- fast : Bool × List Term
-- -- -- fast = go (deep-term ∷ deep-term ∷ []) where
-- -- --   go : List Term → Bool × List Term
-- -- --   go [] = true , []
-- -- --   go (t ∷ ts) = if (isNo $ t == t r[ wide-term / wide-term ]) then
-- -- --                   true , t r[ wide-term / wide-term ] ∷ snd (go ts) -- `true ,_` acts as a delay
-- -- --                 else
-- -- --                   go ts

-- -- -- slow : Bool × List Term
-- -- -- slow = true , go (deep-term ∷ deep-term ∷ []) where -- oops, this delays nothing!
-- -- --   go : List Term → List Term
-- -- --   go [] = []
-- -- --   go (t ∷ ts) = if (isNo $ t == t r[ wide-term / wide-term ]) then
-- -- --                   t r[ wide-term / wide-term ] ∷ go ts
-- -- --                 else
-- -- --                   go ts

-- -- -- try : Bool × List Term → Term
-- -- -- try (_ , ts) = let l = length ts in deep-term r[ var l [] / var l [] ] -- pattern match strips the delays -- they will run if forced to! -- fortunately, length doesn't force them in "fast", b/c "fast" computed the list without delay (only the elements of the list have been delayed) -- otoh, "slow" delayed the entire computation; now when length is applied to the stripped computation, it must compute "go" before finding a list-like pattern match.

-- -- -- try-harder'' : Nat → Term
-- -- -- try-harder'' l = deep-term r[ var l [] / var l [] ]

-- -- -- try-harder' : Nat → List Term → Term
-- -- -- try-harder' l [] = try-harder'' l
-- -- -- try-harder' l (t ∷ ts) = try-harder' (suc l) ts

-- -- -- try-harder : Bool × List Term → Term
-- -- -- try-harder (_ , ts) = try-harder' 0 ts

-- -- -- cps-length : ∀ {a} {A : Set a} → List A → ∀ {b} {B : Set b} → (Nat → B) → B
-- -- -- cps-length {A = A} xs {B = B} f = helper 0 xs where
-- -- --   helper : Nat → List A → B
-- -- --   helper l [] = f l
-- -- --   helper l (x ∷ xs) = helper (suc l) xs

-- -- -- try-cps : Bool × List Term → Term
-- -- -- try-cps bts = cps-length (snd bts) try-harder'' -- showing that we never needed to add that fake delay into slow

-- -- -- -- the difference between hell and help is that when you go through help you get to p. this ain't no help!
-- -- -- with-helP : Bool × List Term → Term
-- -- -- with-helP (_ , ts)
-- -- --  with length ts
-- -- -- ... | l = try-harder'' l

-- -- -- test-area : Term × Term × Term × Term × Term
-- -- -- test-area = {!try fast!} , -- fast
-- -- --             {!try slow!} , -- slow
-- -- --             {!try-harder slow!} , -- fast
-- -- --             {!try-cps slow!} , -- fast
-- -- --             {!with-helP slow!} -- slow

-- -- -- {- normalise: try fast
-- -- --      try fast
-- -- --      try (go (deep-term ∷ []))
-- -- --      try (if (isNo $ deep-term == deep-term r[ wide-term / wide-term ]) then true , deep-term r[ wide-term / wide-term ] ∷ snd (go []) else go [])
-- -- --      try (if false then true , deep-term r[ wide-term / wide-term ] ∷ snd (go []) else go [])
-- -- --      try (go [])
-- -- --      try (true , [])
-- -- --      deep-term r[ var (length []) [] / var (length []) [] ]
-- -- -- -}
-- -- -- {- normalise: try slow
-- -- --      try slow
-- -- --      try (true , go (deep-term ∷ []))
-- -- --      deep-term r[ var (length (go (deep-term ∷ []))) [] / var (length (go (deep-term ∷ []))) [] ]
-- -- -- -}
-- -- -- {- normalise: try-harder slow
-- -- --      try-harder slow
-- -- --      try-harder (true , go (non-matching-term ∷ matching-term ∷ []))
-- -- --      try-harder' (go (non-matching-term ∷ matching-term ∷ []))
-- -- --      try-harder' (if (isNo $ non-matching-term == non-matching-term r[ replacer-term / matcher-term ]) then non-matching-term r[ replacer-term / matcher-term ] ∷ go (matching-term ∷ []) else go (non-matching-term ∷ []))
-- -- --      try-harder' 0 (if false then non-matching-term r[ replacer-term / matcher-term ] ∷ go (matching-term ∷ []) else go (matching-term ∷ []))
-- -- --      try-harder' 0 (go (matching-term ∷ []))
-- -- --      try-harder' 0 (if (isNo $ matching-term == matching-term r[ replacer-term / matcher-term ]) then matching-term r[ replacer-term / matcher-term ] ∷ go [] else go [])
-- -- --      try-harder' 0 (if true then matching-term r[ replacer-term / matcher-term ] ∷ go [] else go [])
-- -- --      try-harder' 0 (matching-term r[ replacer-term / matcher-term ] ∷ go [])
-- -- --      try-harder' 0 (matching-term r[ replacer-term / matcher-term ] ∷ go [])
-- -- --      try-harder' 0 (matching-term r[ replacer-term / matcher-term ] ∷ go [])
-- -- --      try-harder' 1 (go [])
-- -- --      try-harder' 1 []
-- -- --      try-harder'' 1
-- -- --      deep-term r[ var 1 [] / var 1 [] ]
-- -- -- -}

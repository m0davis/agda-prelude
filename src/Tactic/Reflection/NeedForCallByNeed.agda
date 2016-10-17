{-# OPTIONS --exact-split #-}

module Tactic.Reflection.NeedForCallByNeed where
{-
module Issue426 where

  open import Agda.Builtin.Nat
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Equality

  if_then_else : ∀ {a} {A : Set a} → Bool → A → A → A
  if true then t else e = t
  if false then t else e = e

  leq : Nat -> Nat -> Bool
  leq zero    _       = true
  leq (suc _) zero    = false
  leq (suc m) (suc n) = leq m n

  mod : Nat -> Nat -> Nat
  mod 0       k = 0
  mod (suc n) k = if leq (suc r) k then r else 0
    where r = suc (mod n k)

  test : mod 100 10 ≡ 0
  test = {!refl!}
-}
module Issue426-Revised where

  open import Agda.Primitive
  open import Agda.Builtin.Nat
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Equality

  -- Function
  case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  case x of f = f x

  -- Bool
  if_then_else : ∀ {a} {A : Set a} → Bool → A → A → A
  if true then t else e = t
  if false then t else e = e

  -- Product
  infixr 1 _,_
  data Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    _,_ : (x : A) (y : B x) → Σ A B

  infixr 3 _×_
  _×_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
  A × B = Σ A (λ _ → B)

  -- Memoization
  Mem : ∀ {a} {A : Set a} → A → Set a
  Mem x = Σ
            _      -- memoized value
            (_≡ x) -- proof of soundness

  -- needed by `leq` to prove its memoization is sound
  suc-proj : ∀ {m n} → m ≡ n → suc m ≡ suc n
  suc-proj refl = refl

  -- like the original `leq`, but memoizes its arguments' reductions
  leq : (m : Nat) -> (n : Nat) -> Bool × Mem m × Mem n
  leq zero    n       = true  , (zero    , refl) , (n    , refl)
  leq (suc m) zero    = false , ((suc m) , refl) , (zero , refl)
  leq (suc m) (suc n) =
    case leq m n of λ
    { (leq' , (m' , m'≡m) , (n' , n'≡n)) →
      leq' , (suc m' , suc-proj m'≡m) , (suc n' , suc-proj n'≡n) }

  mod : Nat -> Nat -> Nat
  mod 0       k = 0
  mod (suc n) k =
    -- use `leq`'s memoized reduction of `suc r` in the call to `if_then_else_`
    case leq (suc r) k of λ
    { (leq' , (suc r , _) , k) → if leq' then r else 0
    ; (_    , (zero , ()) , _)
      -- NB if we hadn't proved soundness, we'd have to deal with impossible cases
    }

    where r = suc (mod n k)

  test : mod 100 10 ≡ 0
  test = refl

{-
It's possible to memoize under call-by-name. This example follows the [above test case] (https://github.com/agda/agda/issues/426#issuecomment-129023260) and runs fast under --no-sharing.
-}


-- -- module WithoutCallByNeed where

-- --   open import Agda.Builtin.Nat
-- --   open import Agda.Builtin.Bool
-- --   open import Agda.Builtin.Equality

-- --   case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
-- --   case x of f = f x

-- --   max : Nat → Nat → Nat
-- --   max n m =
-- --     case n < m of λ
-- --     { true → m
-- --     ; false → n }
-- -- {-
-- --   max : Nat → Nat → Nat
-- --   max n m with n < m
-- --   ... | true = m
-- --   ... | false = n
-- -- -}
-- --   max42 : Nat → Nat
-- --   max42 = max 42

-- --   test : max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 100)))))))))))))))))))))))))))))) ≡ 100
-- --   test = refl

-- -- -- module WithCallByNeed where
-- -- -- {-
-- -- -- refl must check the structure of a Nat
-- -- -- so max42 must be sensitive to this
-- -- -- so max must be also
-- -- -- max calls _<_, which recursively checks the structure of its arguments
-- -- -- depending on the case of Bool returned by _<_, it returns one or the other of its arguments
-- -- -- so, the call to _<_ must preserve the destructuring done by it
-- -- -- -}

-- -- --   open import Agda.Builtin.Nat using (Nat; zero; suc)
-- -- --   open import Agda.Builtin.Bool using (Bool; false; true)
-- -- --   open import Agda.Builtin.Equality using (_≡_; refl)
-- -- --   open import Prelude.Product using (Σ; _,_; _×_)

-- -- --   case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
-- -- --   case x of f = f x

-- -- --   _<_ : Nat → Nat → Bool × Nat × Nat
-- -- --   m  < zero = false , m , zero
-- -- --   zero < (suc n) = true , zero , suc n
-- -- --   suc m < suc n =
-- -- --     case m < n of λ
-- -- --     { (result , m , n) →
-- -- --       result , suc m , suc n }

-- -- --   max : Nat → Nat → Nat
-- -- --   max n m =
-- -- --     case n < m of λ
-- -- --     { (true , n , m) → m
-- -- --     ; (false , n , m) → n }

-- -- --   max42 : Nat → Nat
-- -- --   max42 = max 42

-- -- --   test : max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 (max42 100)))))))))))))))))))))))))))))) ≡ 100
-- -- --   test = refl


-- -- -- module WithCallByNeed₂ where
-- -- --   open import Agda.Builtin.Nat using (Nat; zero; suc)
-- -- --   open import Agda.Builtin.Bool using (Bool; false; true)
-- -- --   open import Agda.Builtin.Equality using (_≡_; refl)
-- -- --   open import Prelude.Product using (Σ; _,_; _×_)

-- -- --   case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
-- -- --   case x of f = f x

-- -- --   -- _<_ : Nat → Nat × (Nat → Nat × Bool)
-- -- --   -- _<_ zero = zero , λ { zero → zero , false
-- -- --   --                     ; (suc x) → (suc x) , true}
-- -- --   -- _<_ x = {!!}

-- compare agda issue 426
module Tactic.Reflection.Reright-Performance-BestExamples-LambdaLift where

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

smarter : Nat → Nat
--smarter n = if n < 0 then 0 else suc n
smarter n with n < 0
... | true = 0
... | false = suc n

unlifted-weaken-smart : List Nat → List Nat
unlifted-weaken-smart [] = []
unlifted-weaken-smart (n ∷ ns) = smarter n ∷ unlifted-weaken-smart ns

test-unlifted-weaken : [ unlifted-weaken-smart $ 0 ∷ [] ]× 100 ≡ 100 ∷ []
test-unlifted-weaken = {!!} -- slow

case_of_ : ∀ {a} {A : Set a} {b} {B : Set b} → A → (A → B) → B
case_of_ x f = f x

open import Prelude.Product

<& : Nat → Nat → Nat → Nat × Bool
<& _ zero l = l , false
<& zero (suc n) = {!!}
<& (suc m) (suc n) = {!<& m n (suc m)!}

S : Nat → Nat
S n = case n < zero of λ
      { true  → zero
      ; false → suc n }

open import Agda.Builtin.Reflection

S0 : Nat
S0 = S 0

suc? : Nat → Bool
suc? zero = false
suc? (suc _) = true

test-sm : suc? (Nat.suc (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter 0))))))))))))))))))))))))))))))))) ≡ true
test-sm = {!refl!}

-- suc (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter (smarter 0)))))))))))))))))))))))))))))))) < 0

open import Prelude.Strict
a-suc : Nat
a-suc = Nat.suc $! (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S 0))))))))))))))))))))))))))))))))))))))

nat-cps : ∀ {b} {B : Set b} → Nat → (Nat → B) → B
nat-cps = helper 0 where
  helper : ∀ {b} {B : Set b} → Nat → Nat → (Nat → B) → B
  helper n' zero f = f n'
  helper n' (suc n) f = helper (suc n') n f

apply-cps : Nat → (Nat → Nat) → Nat → Nat
apply-cps zero f n = n
apply-cps (suc d) f n = nat-cps (f n) λ x → apply-cps d f x

test-cps-nat : apply-cps 500 S 0 ≡ 500
test-cps-nat = refl

test-S : suc? a-suc ≡ true
test-S = {!refl!}

bool-first-arg : Bool → Nat → Bool
bool-first-arg false _ = false
bool-first-arg true zero = true
bool-first-arg true (suc _) = true

test-b : bool-first-arg true a-suc ≡ true
test-b = {!refl!}

length& : ∀ {a} {A : Set a} → List A → ∀ {b} {B : Set b} → (Nat → B) → B
length& {A = A} xs {B = B} f = helper 0 xs where
  helper : Nat → List A → B
  helper l [] = f l
  helper l (x ∷ xs) = helper (suc l) xs

test-length& : length& (a-suc ∷ []) (_+ 0) ≡ 1
test-length& = refl

open import Prelude

-- {-
-- is-suc (Nat.suc (S (S (S 0)))) ≡ true

-- S (S (S 0))
-- case (S (S 0) < 0) of λ { true → zero ; false → suc (S (S 0)) }
-- (λ { true → zero ; false → suc (S (S 0)) }) (S (S 0) < 0)




-- -}

-- S! : Nat → Nat → Nat
-- S! 0 n = S n
-- S! (suc d) n with S! d n
-- ... | S!d = S S!d

-- test-S! : Nat
-- test-S! = {!S! 20 0!}

-- S!! : Nat → Nat → Nat
-- S!! 0 n = S n
-- S!! (suc d) n with S!! d n
-- ... | S!d with S!d < 0
-- ... | true = zero
-- ... | false = suc S!d

-- test-S!! : S!! 20 0 ≡ 21
-- test-S!! = {!refl!}


-- {-
-- S (S (S 0))
-- S (S (S 0)) | S (S 0)
-- S (S (S 0)) | S (S 0) | S 0
-- S (S (S 0)) | S (S 0) | S 0 | 0 < 0
-- S (S (S 0)) | S (S 0) | S 0 | false
-- S (S (S 0)) | S (S 0) | suc 0
-- S (S (S 0)) | S (suc 0)
-- S (S (S 0)) | S (suc 0) | suc 0 < 0
-- S (S (S 0)) | S (suc 0) | false
-- S (S (S 0)) | suc (suc 0)
-- S (suc (suc 0))












--  1. S (S (S 0)                       )
--  2. S (S (S 0)                       ) |  S (S 0)                       < 0
--  3. S (S (S 0)                       ) | (S (S 0) |   S 0          < 0) < 0
--  4. S (S (S 0)                       ) | (S (S 0) |  (S 0 | 0 < 0) < 0) < 0
--  5. S (S (S 0)                       ) | (S (S 0) |  (S 0 | false) < 0) < 0
--  6. S (S (S 0)                       ) | (S (S 0) |  suc 0         < 0) < 0
--  7. S (S (S 0)                       ) | (S (S 0) | false             ) < 0
--  8. S (S (S 0)                       ) |  suc (S 0)                     < 0
--  9. S (S (S 0)                       ) |  false
-- 10. suc (S (S 0)                     )
-- 11. suc (S (S 0) |   S 0          < 0)
-- 12. suc (S (S 0) |  (S 0 | 0 < 0) < 0)
-- 13. suc (S (S 0) |  (S 0 | false) < 0)
-- 14. suc (S (S 0) |  suc 0         < 0)
-- 15. suc (S (S 0) | false             )
-- 16. suc (suc (S 0)                   )
-- 17. suc (suc (S 0 | 0 < 0)           )
-- 18. suc (suc (S 0 | false)           )
-- 19. suc (suc (suc 0      )           )


-- Without sharing, I figure




-- S (S (S (S (S 0))))
-- S (S (S (S (S 0 | 0 < 0))))
-- S (S (S (S (S 0 | false))))
-- S (S (S (S (suc 0))))
-- S (S (S (S (suc 0) | suc 0 < 0)))
-- S (S (S (S (suc 0) | false)))
-- S (S (S (suc (suc 0))))
-- S (S (S (suc (suc 0)) | suc (suc 0) < 0))
-- S (S (S (suc (suc 0)) | false))

--  n = IGE0TS n = if n < 0 then 0 else suc n
-- T c t f
-- S n = T (n < 0) 0 (suc n)

-- S (S (S (S (S 0))))
-- T (S (S (S (S 0))) < 0) 0 (suc (S (S (S (S 0))))) | S (S (S (S 0))) < 0
-- T (S (S (S (S 0))) < 0) 0 (suc (S (S (S (S 0))))) | (T ((S (S (S 0))) < 0) 0 (suc (S (S (S 0))))) < 0
-- T (S (S (S (S 0))) < 0) 0 (suc (S (S (S (S 0))))) | (T ((S (S (S 0))) < 0) 0 (suc (S (S (S 0)))) | (S (S (S 0))) < 0) < 0
-- T (S (S (S (S 0))) < 0) 0 (suc (S (S (S (S 0))))) | (T ((S (S (S 0))) < 0) 0 (suc (S (S (S 0)))) | (T ((S (S 0)) < 0) 0 (suc (S (S 0)))) < 0) < 0

-- S (S (S 0))
-- T (S (S 0) < 0) 0 (suc (S (S 0)))
-- T (S (S 0) < 0) 0 (suc (S (S 0))) | S (S 0) < 0
-- T (S (S 0) < 0) 0 (suc (S (S 0))) | (T (S 0 < 0) 0 (suc (S 0))) < 0
-- T (S (S 0) < 0) 0 (suc (S (S 0))) | (T (S 0 < 0) 0 (suc (S 0)) | S 0 < 0) < 0
-- T (S (S 0) < 0) 0 (suc (S (S 0))) | (T (S 0 < 0) 0 (suc (S 0)) | T (0 < 0) 0 (suc 0) < 0) < 0
-- T (S (S 0) < 0) 0 (suc (S (S 0))) | (T (S 0 < 0) 0 (suc (S 0)) | (T (0 < 0) 0 (suc 0) | 0 < 0) < 0) < 0
-- T (S (S 0) < 0) 0 (suc (S (S 0))) | (T (S 0 < 0) 0 (suc (S 0)) | (T (0 < 0) 0 (suc 0) | false) < 0) < 0
-- T (S (S 0) < 0) 0 (suc (S (S 0))) | (T (S 0 < 0) 0 (suc (S 0)) | suc 0 < 0) < 0
-- T (S (S 0) < 0) 0 (suc (S (S 0))) | (T (S 0 < 0) 0 (suc (S 0)) | false) < 0
-- T (S (S 0) < 0) 0 (suc (S (S 0))) | suc (S 0) < 0
-- T (S (S 0) < 0) 0 (suc (S (S 0))) | false
-- suc (S (S 0))
-- suc (T (S 0 < 0) 0 (suc (S 0)))
-- suc (T (S 0 < 0) 0 (suc (S 0)) | S 0 < 0)






-- S (S (S (S (S 0))))
-- T (S (S (S (S 0))) < 0) 0 (suc (S (S (S (S 0))))) | S (S (S (S 0))) < 0
-- T (S (S (S (S 0))) < 0) 0 (suc (S (S (S (S 0))))) | (T ((S (S (S 0))) < 0) 0 (suc (S (S (S 0))))) < 0
-- T (S (S (S (S 0))) < 0) 0 (suc (S (S (S (S 0))))) | (T ((S (S (S 0))) < 0) 0 (suc (S (S (S 0)))) | (S (S (S 0))) < 0) < 0
-- T (S (S (S (S 0))) < 0) 0 (suc (S (S (S (S 0))))) | (T ((S (S (S 0))) < 0) 0 (suc (S (S (S 0)))) | (T ((S (S 0)) < 0) 0 (suc (S (S 0)))) < 0) < 0
-- T (S (S (S (S 0))) < 0) 0 (suc (S (S (S (S 0))))) | (T ((S (S (S 0))) < 0) 0 (suc (S (S (S 0)))) | (T ((S (S 0)) < 0) 0 (suc (S (S 0))) | ) < 0) < 0



-- S (S (S (S (S 0)))) | S (S (S (S 0))) < 0
-- S (S (S (S (S 0)))) | S (S (S (S 0))) < 0 | S (S (S 0)) < 0 | S (S 0) < 0 | S 0 < 0 | 0 < 0
-- S (S (S (S (S 0)))) | S (S (S (S 0))) < 0 | S (S (S 0)) < 0 | S (S 0) < 0 | S 0 < 0 | false
-- S (S (S (S (S 0)))) | S (S (S (S 0))) < 0 | S (S (S 0)) < 0 | S (S 0) < 0 | suc 0 < 0




-- S (S (S (S (S 0)))) | false
-- suc (S (S (S (S 0))))

-- S (S (S (S (S 0)))) | (S (S (S (S 0))) < 0 | S (S (S 0)) < 0)
-- S (S (S (S (S 0)))) | (S (S (S (S 0))) < 0 | (S (S (S 0)) < 0 | S (S 0) < 0))
-- S (S (S (S (S 0)))) | (S (S (S (S 0))) < 0 | (S (S (S 0)) < 0 | (S (S 0) < 0 | S 0 < 0)))
-- S (S (S (S (S 0)))) | (S (S (S (S 0))) < 0 | (S (S (S 0)) < 0 | (S (S 0) < 0 | (S 0 < 0 | 0 < 0))))
-- S (S (S (S (S 0)))) | (S (S (S (S 0))) < 0 | (S (S (S 0)) < 0 | (S (S 0) < 0 | (S 0 < 0 | false))))

-- -}





-- {- normalise: [ unlifted-weaken $ 0 ∷ [] ]× 4 ≡ 4 ∷ []

-- [ unlifted-weaken $ 0 ∷ [] ]× 4 ≡ 4 ∷ []
-- [ unlifted-weaken $ 0 ∷ [] ]× (suc 3) ≡ 4 ∷ []
-- [ unlifted-weaken $ unlifted-weaken (0 ∷ []) ]× 3 ≡ 4 ∷ []
-- [ unlifted-weaken $ unlifted-weaken (0 ∷ []) ]× (suc 2) ≡ 4 ∷ []
-- [ unlifted-weaken $ unlifted-weaken (unlifted-weaken (0 ∷ [])) ]× 2 ≡ 4 ∷ []
-- [ unlifted-weaken $ unlifted-weaken (unlifted-weaken (0 ∷ [])) ]× (suc 1) ≡ 4 ∷ []
-- [ unlifted-weaken $ unlifted-weaken (unlifted-weaken (unlifted-weaken (0 ∷ []))) ]× 1 ≡ 4 ∷ []
-- [ unlifted-weaken $ unlifted-weaken (unlifted-weaken (unlifted-weaken (0 ∷ []))) ]× (suc 0) ≡ 4 ∷ []
-- [ unlifted-weaken $ unlifted-weaken (unlifted-weaken (unlifted-weaken (unlifted-weaken (0 ∷ [])))) ]× 0 ≡ 4 ∷ []
-- unlifted-weaken (unlifted-weaken (unlifted-weaken (unlifted-weaken (0 ∷ [])))) ≡ 4 ∷ []
-- unlifted-weaken (unlifted-weaken (unlifted-weaken (if 0 < 0 then 0 else suc 0 ∷ unlifted-weaken []))) ≡ 4 ∷ []
-- unlifted-weaken (unlifted-weaken (if (if 0 < 0 then 0 else suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else (suc (if 0 < 0 then 0 else suc 0)))) ≡ 4 ∷ []
-- unlifted-weaken (if (if (if 0 < 0 then 0 else suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else (suc (if 0 < 0 then 0 else suc 0))) < 0 then (if (if 0 < 0 then 0 else suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else (suc (if 0 < 0 then 0 else suc 0))) else suc (if (if 0 < 0 then 0 else suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else (suc (if 0 < 0 then 0 else suc 0)))) ≡ 4 ∷ []
-- unlifted-weaken (if (if (if false then 0 else suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else (suc (if 0 < 0 then 0 else suc 0))) < 0 then (if (if 0 < 0 then 0 else suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else (suc (if 0 < 0 then 0 else suc 0))) else suc (if (if 0 < 0 then 0 else suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else (suc (if 0 < 0 then 0 else suc 0)))) ≡ 4 ∷ []
-- unlifted-weaken (if (if (                     suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else (suc (if 0 < 0 then 0 else suc 0))) < 0 then (if (if 0 < 0 then 0 else suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else (suc (if 0 < 0 then 0 else suc 0))) else suc (if (if 0 < 0 then 0 else suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else (suc (if 0 < 0 then 0 else suc 0)))) ≡ 4 ∷ []
-- unlifted-weaken (if (if                            false then (if 0 < 0 then 0 else suc 0) else (suc (if 0 < 0 then 0 else suc 0))) < 0 then (if (if 0 < 0 then 0 else suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else (suc (if 0 < 0 then 0 else suc 0))) else suc (if (if 0 < 0 then 0 else suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else (suc (if 0 < 0 then 0 else suc 0)))) ≡ 4 ∷ []
-- unlifted-weaken (if (                                                                           (suc (if 0 < 0 then 0 else suc 0))) < 0 then (if (if 0 < 0 then 0 else suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else (suc (if 0 < 0 then 0 else suc 0))) else suc (if (if 0 < 0 then 0 else suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else (suc (if 0 < 0 then 0 else suc 0)))) ≡ 4 ∷ []

-- -}

-- unlifted'-weaken : List Nat → List Nat
-- unlifted'-weaken [] = []
-- unlifted'-weaken (n ∷ ns)
--  with if n < 0 then n else suc n
-- ... | n' = n' ∷ unlifted-weaken ns

-- test-unlifted'-weaken : [ unlifted'-weaken $ 0 ∷ [] ]× 100 ≡ 100 ∷ []
-- test-unlifted'-weaken = {!refl!} -- slow

-- {- normalise: [ unlifted-weaken $ 0 ∷ [] ]× 4 ≡ 4 ∷ []

-- [ unlifted-weaken $ 0 ∷ [] ]× 4 ≡ 4 ∷ []
-- [ unlifted-weaken $ 0 ∷ [] ]× (suc 3) ≡ 4 ∷ []
-- [ unlifted-weaken $ unlifted-weaken (0 ∷ []) ]× 3 ≡ 4 ∷ []
-- [ unlifted-weaken $ unlifted-weaken (0 ∷ []) ]× (suc 2) ≡ 4 ∷ []
-- [ unlifted-weaken $ unlifted-weaken (unlifted-weaken (0 ∷ [])) ]× 2 ≡ 4 ∷ []
-- [ unlifted-weaken $ unlifted-weaken (unlifted-weaken (0 ∷ [])) ]× (suc 1) ≡ 4 ∷ []
-- [ unlifted-weaken $ unlifted-weaken (unlifted-weaken (unlifted-weaken (0 ∷ []))) ]× 1 ≡ 4 ∷ []
-- [ unlifted-weaken $ unlifted-weaken (unlifted-weaken (unlifted-weaken (0 ∷ []))) ]× (suc 0) ≡ 4 ∷ []
-- [ unlifted-weaken $ unlifted-weaken (unlifted-weaken (unlifted-weaken (unlifted-weaken (0 ∷ [])))) ]× 0 ≡ 4 ∷ []
-- unlifted-weaken (unlifted-weaken (unlifted-weaken (unlifted-weaken (0 ∷ [])))) ≡ 4 ∷ []
-- unlifted-weaken (unlifted-weaken (unlifted-weaken (unlifted-weaken (0 ∷ []) | if 0 < 0 then 0 else suc 0))) ≡ 4 ∷ []
-- unlifted-weaken (unlifted-weaken (unlifted-weaken (if 0 < 0 then 0 else suc 0 ∷ unlifted-weaken []))) ≡ 4 ∷ []
-- unlifted-weaken (unlifted-weaken (if (if 0 < 0 then 0 else suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else (suc (if 0 < 0 then 0 else suc 0)))) ≡ 4 ∷ []

-- -}


-- length : ∀ {a} {A : Set a} → List A → Nat
-- length [] = 0
-- length (_ ∷ xs) = suc (length xs)

-- test-length-unlifted-weaken : length ([ unlifted-weaken $ [ 0 ∷_ $ [] ]× 1000 ]× 1000) ≡ 1000
-- test-length-unlifted-weaken = {!refl!} -- fast (or anyway, O(n²)

-- lifted-weaken : List Nat → List Nat
-- lifted-weaken [] = []
-- lifted-weaken (n ∷ ns)
--  with n < 0
-- ... | true = n ∷ lifted-weaken ns
-- ... | false = suc n ∷ lifted-weaken ns

-- test-lifted-weaken : [ lifted-weaken $ 0 ∷ [] ]× 100 ≡ 100 ∷ []
-- test-lifted-weaken = {!refl!} -- fast

-- test-length-lifted-weaken : length ([ lifted-weaken $ [ 0 ∷_ $ [] ]× 100 ]× 1000) ≡ 100
-- test-length-lifted-weaken = {!refl!} -- slow

-- unlifted-mod : Nat -> Nat -> Nat
-- unlifted-mod 0       k = 0
-- unlifted-mod (suc n) k = if (suc (unlifted-mod n k) < k) then suc (unlifted-mod n k) else 0

-- test-unlifted-mod : unlifted-mod 100 10 ≡ 0
-- test-unlifted-mod = {!refl!} -- slow

-- lifted-mod : Nat -> Nat -> Nat
-- lifted-mod 0       k = 0
-- lifted-mod (suc n) k
--   with suc (lifted-mod n k)
-- ... | r
--   with r < k
-- ... | true = r
-- ... | false = 0

-- test-lifted-mod : lifted-mod 100 10 ≡ 0
-- test-lifted-mod = {!!} -- fast with --sharing, otherwise slow

-- id : ∀ {a} {A : Set a} → A → A
-- id x = x
-- {-# INLINE id #-}
-- {-
-- [_<_]& : Nat → Nat → (Bool → B) → B
-- [ _ < zero ]& f = f false
-- [ zero < suc n ]& f = f true
-- [ suc m < suc n ]& f = [ m < n ]& f

-- lifted-mod-cps : Nat -> Nat -> ∀ {b} {B : Set b} → (Nat → B) → B
-- lifted-mod-cps 0       k f = f 0
-- lifted-mod-cps (suc n) k f = [ suc (lifted-mod-cps n k id) < k ]& λ

-- lifted-mod-cps n k λ lm → let r = suc lm in
--   with suc ( id)
-- ... | r
--   with r < k
-- ... | true = f r
-- ... | false = f 0

-- test-lifted-mod-cps : lifted-mod-cps 100 10 id ≡ 0
-- test-lifted-mod-cps = {!refl!} -- fast with --sharing, otherwise slow
-- -}
-- {- normalise: lifted-mod 5 2; M = lifted-mod
--   M 5 2
--   M (suc 4) 2
--   M (suc 4) 2 | suc (M 4 2)
--   M (suc 4) 2 | suc (M 4 2) | suc (M 4 2)                                                                                                                                              < 2
--   M (suc 4) 2 | suc (M 4 2) | M 4 2                                                                                                                                                    < 1
--   M (suc 4) 2 | suc (M 4 2) |  M (suc 3) 2                                                                                                                                             < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2))                                                                                                                              < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | suc (M 3 2)                                                                                                            < 2) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | M 3 2                                                                                                                  < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | M (suc 2) 2                                                                                                            < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2))                                                                                            < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | suc (M 2 2)                                                                          < 2) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | M 2 2                                                                                < 1) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) |  M (suc 1) 2                                                                         < 1) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2))                                                          < 1) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | suc (M 1 2) < 2)                                        < 1) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | M 1 2                                              < 1) < 1) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | M (suc 0) 2                                        < 1) < 1) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | (M (suc 0) 2 | suc (M 0 2))                        < 1) < 1) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | (M (suc 0) 2 | suc (M 0 2) | suc (M 0 2)      < 2) < 1) < 1) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | (M (suc 0) 2 | suc (M 0 2) | M 0 2            < 1) < 1) < 1) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | (M (suc 0) 2 | suc (M 0 2) | 0                < 1) < 1) < 1) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | (M (suc 0) 2 | suc (M 0 2) | true                ) < 1) < 1) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | suc (M 0 2)                                        < 1) < 1) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | M 0 2                                              < 0) < 1) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | false                                                 ) < 1) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | 0                                                                                    < 1) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | true                                                                                    ) < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | suc (M 2 2)                                                                                                            < 1) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | M 2 2                                                                                                                  < 0) < 1
--   M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | false                                                                                                                     ) < 1
--   M (suc 4) 2 | suc (M 4 2) | 0                                                                                                                                                        < 1
--   -- on the above step, note that M (suc 3) 2 normalises to 0
--   M (suc 4) 2 | suc (M 4 2) | true
--   suc (M 4 2)
--   suc (M (suc 3) 2)
--   -- does --sharing speed the evaluation of the above step, noting that M (suc 3) 2 = 0?
--   -- if so, then we're done: M 5 2 = suc 0 = 1
--   -- otherwise, we'd continue laboriously...
--   suc (M (suc 3) 2 | suc (M 3 2)                                  )
--   suc (M (suc 3) 2 | suc (M 3 2) | suc (M 3 2)                 < 2)
--   suc (M (suc 3) 2 | suc (M 3 2) | M 3 2                       < 1)
--   suc (M (suc 3) 2 | suc (M 3 2) | M (suc 2) 2                 < 1)
--   suc (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2)) < 1)
--   -- ...etc...
--   1
-- -}

-- {-
--    [ unlifted-weaken $ 0 ∷ [] ]× 3
--    unlifted-weaken (unlifted-weaken (unlifted-weaken (0 ∷ [])))
--    unlifted-weaken (unlifted-weaken ((if 0 < 0 then 0 else suc 0) ∷ unlifted-weaken []))
--                                      <----------- n₁ ----------->   <------ ns₁ ----->
--    unlifted-weaken (unlifted-weaken (             n₁              ∷         ns₁       ))

--    unlifted-weaken ((if n₁ < 0 then n₁ else suc n₁) ∷ unlifted-weaken ns₁)
--                     <------------- n₂ ------------>   <------- ns₂ ----->
--    unlifted-weaken (               n₂               ∷          ns₂       )
--    (if n₂ < 0 then n₂ else suc n₂) ∷ unlifted-weaken ns₂
--    <--------------- n₃ ---------->   <------- ns₃ ----->
--                     n₃             ∷ ns₃
--    (if n₂ < 0 then n₂ else suc n₂) ∷ unlifted-weaken ns₂
--        ? n₂ < 0
--          (if n₁ < 0 then n₁ else suc n₁) < 0
--              ? n₁ < 0
--                (if 0 < 0 then 0 else suc 0) < 0
--                    ? 0 < 0
--                    false
--                    suc 0


--          (if (if 0 < 0 then 0 else suc 0) < 0 then (if 0 < 0 then 0 else suc 0) else suc (if 0 < 0 then 0 else suc 0)) < 0
--              ?
-- -}

-- {-
--    [ lifted-weaken $ 0 ∷ [] ]× 3
--    lifted-weaken (lifted-weaken (lifted-weaken (0 ∷ [])))
--                                  ? 0 < 0
--                                    false
--                                  suc 0 ∷ lifted-weaken []
--    lifted-weaken (lifted-weaken (suc 0 ∷ lifted-weaken []))
--                   ? suc 0 < 0
--                     false
--                   suc (suc 0) ∷ lifted-weaken (lifted-weaken [])
--    lifted-weaken (suc (suc 0) ∷ lifted-weaken (lifted-weaken []))
--    ? suc (suc 0) < 0
--      false
--    suc (suc (suc 0)) ∷ lifted-weaken (lifted-weaken (lifted-weaken []))
--    suc (suc (suc 0)) ∷ lifted-weaken (lifted-weaken [])
--    suc (suc (suc 0)) ∷ lifted-weaken []
--    suc (suc (suc 0)) ∷ []
-- -}

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

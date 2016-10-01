-- compare agda issue 426
module Tactic.Reflection.Reright-Performance where
  open import Agda.Builtin.Bool
  open import Agda.Builtin.Nat
  open import Agda.Builtin.List
  open import Agda.Builtin.Equality

  if_then_else_ : Bool → Nat → Nat → Nat
  if true  then t else e = t
  if false then t else e = e

  [_$_]×_ : (List Nat → List Nat) → List Nat → Nat → List Nat
  [ _ $ xs ]× 0 = xs
  [ f $ xs ]× (suc n) = [ f $ f xs ]× n

  unlifted-weaken : List Nat → List Nat
  unlifted-weaken [] = []
  unlifted-weaken (n ∷ ns) = (if n < 0 then n else suc n) ∷ unlifted-weaken ns

  test-unlifted-weaken : [ unlifted-weaken $ 0 ∷ [] ]× 100  ≡ 100 ∷ []
  test-unlifted-weaken = {!refl!} -- fast

  lifted-weaken : List Nat → List Nat
  lifted-weaken [] = []
  lifted-weaken (n ∷ ns)
   with n < 0
  ... | true = n ∷ lifted-weaken ns
  ... | false = suc n ∷ lifted-weaken ns

  test-lifted-weaken : [ lifted-weaken $ 0 ∷ [] ]× 100  ≡ 100 ∷ []
  test-lifted-weaken = {!refl!} -- slow

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

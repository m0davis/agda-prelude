-- compare agda issue 426
module Tactic.Reflection.Reright-Performance-BestExamples-SharingQuestion where

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- M n k = n modulo k
M : Nat -> Nat -> Nat
M 0       k = 0
M (suc n) k
  with suc (lifted-mod n k)
... | r
  with r < k
... | true = r
... | false = 0

test : M 100 10 ≡ 0
test = refl -- fast with --sharing, otherwise slow

{-
Why is test fast with --sharing and slow otherwise? To see this, let's normalise M 5 2 step-by-step:

M 5 2
M (suc 4) 2
M (suc 4) 2 | suc (M 4 2)
M (suc 4) 2 | suc (M 4 2) | suc (M 4 2) < 2
M (suc 4) 2 | suc (M 4 2) | M 4 2 < 1
M (suc 4) 2 | suc (M 4 2) | M (suc 3) 2 < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2)) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | suc (M 3 2) < 2) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | M 3 2 < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | M (suc 2) 2 < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2)) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | suc (M 2 2) < 2) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | M 2 2 < 1) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | M (suc 1) 2 < 1) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2)) < 1) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | suc (M 1 2) < 2) < 1) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | M 1 2 < 1) < 1) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | M (suc 0) 2 < 1) < 1) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | (M (suc 0) 2 | suc (M 0 2)) < 1) < 1) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | (M (suc 0) 2 | suc (M 0 2) | suc (M 0 2) < 2) < 1) < 1) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | (M (suc 0) 2 | suc (M 0 2) | M 0 2 < 1) < 1) < 1) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | (M (suc 0) 2 | suc (M 0 2) | 0 < 1) < 1) < 1) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | (M (suc 0) 2 | suc (M 0 2) | true) < 1) < 1) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | suc (M 0 2) < 1) < 1) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | M 0 2 < 0) < 1) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | (M (suc 1) 2 | suc (M 1 2) | false) < 1) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | 0 < 1) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2) | true) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | suc (M 2 2) < 1) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | M 2 2 < 0) < 1
M (suc 4) 2 | suc (M 4 2) | (M (suc 3) 2 | suc (M 3 2) | false) < 1
M (suc 4) 2 | suc (M 4 2) | 0 < 1
-- on the above step, note that M (suc 3) 2 normalises to 0
M (suc 4) 2 | suc (M 4 2) | true
suc (M 4 2)
suc (M (suc 3) 2)
-- does --sharing speed the evaluation of the above step, noting that M (suc 3) 2 = 0?
-- if so, then we're done: M 5 2 = suc 0 = 1
-- otherwise, we'd continue laboriously...
suc (M (suc 3) 2 | suc (M 3 2))
suc (M (suc 3) 2 | suc (M 3 2) | suc (M 3 2) < 2)
suc (M (suc 3) 2 | suc (M 3 2) | M 3 2 < 1)
suc (M (suc 3) 2 | suc (M 3 2) | M (suc 2) 2 < 1)
suc (M (suc 3) 2 | suc (M 3 2) | (M (suc 2) 2 | suc (M 2 2)) < 1)
-- ...etc...
1
-}

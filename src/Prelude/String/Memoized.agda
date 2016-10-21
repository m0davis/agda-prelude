
module Prelude.String.Memoized where

open import Prelude.Memoization
open import Prelude.Equality.Memoized
open import Prelude.Char
open import Prelude.Bool
open import Prelude.Product
open import Prelude.Decidable
open import Prelude.Equality.Unsafe

open import Agda.Builtin.String public

instance
  EqμString : Eqμ String
  _==μ_ {{EqμString}} x y with primStringEquality x y
  ... | true  = yes unsafeEqual , putμ refl , putμ refl
  ... | false = no  unsafeNotEqual , putμ refl , putμ refl

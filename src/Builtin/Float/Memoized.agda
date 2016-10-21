
module Builtin.Float.Memoized where

open import Prelude.Memoization
open import Prelude.Equality.Memoized
open import Prelude.Product
open import Prelude.Decidable
open import Prelude.Equality.Unsafe
open import Prelude

open import Agda.Builtin.Float public

instance
  EqμFloat : Eqμ Float
  _==μ_ {{EqμFloat}} x y with primFloatEquality x y
  ... | true  = yes unsafeEqual , putμ refl , putμ refl
  ... | false = no  unsafeNotEqual , putμ refl , putμ refl

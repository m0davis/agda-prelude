
module Prelude.Char.Memoized where

open import Prelude.Memoization
open import Prelude.Equality.Memoized
open import Prelude.Char
open import Prelude.Bool
open import Prelude.Product
open import Prelude.Decidable
open import Prelude.Equality.Unsafe

open import Agda.Builtin.Char public using (Char)

instance
  EqμChar : Eqμ Char
  _==μ_ {{EqμChar}} x y with eqChar x y
  ... | false = no  unsafeNotEqual , putμ refl , putμ refl
  ... | true  = yes unsafeEqual , putμ refl , putμ refl

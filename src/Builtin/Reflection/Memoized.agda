
module Builtin.Reflection.Memoized where

open import Prelude.Memoization
open import Prelude.Equality
open import Prelude.Equality.Memoized
open import Prelude.Product
open import Builtin.Reflection

instance
  EqμName : Eqμ Name
  _==μ_ {{EqμName}} x y = x == y , putμ refl , putμ refl

instance
  EqμMeta : Eqμ Meta
  _==μ_ {{EqμMeta}} x y = x == y , putμ refl , putμ refl

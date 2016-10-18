
module Prelude.Bool.Memoized where

open import Prelude.Memoization
open import Prelude.Product
open import Prelude.Equality

open import Prelude.Bool public

infixr 3 _&&μ_
infixr 2 _||μ_

_||μ_ : (l : Bool) → Bool → Bool × Mem l
true  ||μ _ = true , (true , refl)
false ||μ x = x , (false , refl)
{-# INLINE _||_ #-}

_&&μ_ : (l : Bool) → Bool → Bool × Mem l
true  &&μ x = x , (true , refl)
false &&μ _ = false , (false , refl)
{-# INLINE _&&_ #-}

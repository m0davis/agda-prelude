module Tactic.Reflection.AgdaIssue-loop-forever-2 where
  module loops-forever where
    open import Prelude

    {-# TERMINATING #-}
    bar : Set
    bar = bar

    postulate
      foo : Set → Nat

    qux : Nat
    qux = suc $ foo bar

  module terminates where
    open import Agda.Builtin.Nat
    open import Prelude using (_$_)

    {-# TERMINATING #-}
    bar : Set
    bar = bar

    postulate
      foo : Set → Nat

    qux : Nat
    qux = suc $ (foo bar)

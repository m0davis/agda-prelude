{-
Is there a way to do this? I'd like to write something like foo :: Term -> TC Term (in Haskell) and invoke it from Agda such that Agda "knows" what gets returned (in the same way that it knows the values of other builtin reflection functions). I don't think this is possible at the moment as the FFI only allows Agda to "call out", leaving the results of the call obscured behind a postulate.
-}

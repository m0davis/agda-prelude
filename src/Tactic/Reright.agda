
module Tactic.Reright where

open import Prelude

open import Tactic.Reflection
open import Tactic.Reflection.Match
open import Tactic.Reflection.Replace
open import Tactic.Reflection.Quote

open import Prelude.Memoization
open import Prelude.Equality.Memoized
open import Prelude.Nat.Memoized
open import Tactic.Reflection.Equality.Memoized

test-foo : List (Arg Term × Nat)
test-foo =
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 22
      (arg (arg-info visible relevant) (var 10 []) ∷
       arg (arg-info visible relevant) (var 23 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 23
        (arg (arg-info visible relevant) (var 11 []) ∷
         arg (arg-info visible relevant) (var 24 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 24
          (arg (arg-info visible relevant) (var 12 []) ∷
           arg (arg-info visible relevant) (var 25 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 25
            (arg (arg-info visible relevant) (var 13 []) ∷
             arg (arg-info visible relevant) (var 26 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 26
              (arg (arg-info visible relevant) (var 14 []) ∷
               arg (arg-info visible relevant) (var 27 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 27
                (arg (arg-info visible relevant) (var 15 []) ∷
                 arg (arg-info visible relevant) (var 28 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 28
                  (arg (arg-info visible relevant) (var 16 []) ∷
                   arg (arg-info visible relevant) (var 29 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 29
                    (arg (arg-info visible relevant) (var 17 []) ∷
                     arg (arg-info visible relevant) (var 30 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 30
                      (arg (arg-info visible relevant) (var 18 []) ∷
                       arg (arg-info visible relevant) (var 31 []) ∷ [])))
                    (abs "_"
                     (var 31
                      (arg (arg-info visible relevant) (var 19 []) ∷
                       arg (arg-info visible relevant) (var 32 []) ∷
                       []))))))))))))))))))))
   , 13)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 21
      (arg (arg-info visible relevant) (var 9 []) ∷
       arg (arg-info visible relevant) (var 22 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 22
        (arg (arg-info visible relevant) (var 10 []) ∷
         arg (arg-info visible relevant) (var 23 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 23
          (arg (arg-info visible relevant) (var 11 []) ∷
           arg (arg-info visible relevant) (var 24 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 24
            (arg (arg-info visible relevant) (var 12 []) ∷
             arg (arg-info visible relevant) (var 25 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 25
              (arg (arg-info visible relevant) (var 13 []) ∷
               arg (arg-info visible relevant) (var 26 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 26
                (arg (arg-info visible relevant) (var 14 []) ∷
                 arg (arg-info visible relevant) (var 27 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 27
                  (arg (arg-info visible relevant) (var 15 []) ∷
                   arg (arg-info visible relevant) (var 28 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 28
                    (arg (arg-info visible relevant) (var 16 []) ∷
                     arg (arg-info visible relevant) (var 29 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 29
                      (arg (arg-info visible relevant) (var 17 []) ∷
                       arg (arg-info visible relevant) (var 30 []) ∷ [])))
                    (abs "_"
                     (var 30
                      (arg (arg-info visible relevant) (var 18 []) ∷
                       arg (arg-info visible relevant) (var 31 []) ∷
                       []))))))))))))))))))))
   , 12)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 20
      (arg (arg-info visible relevant) (var 8 []) ∷
       arg (arg-info visible relevant) (var 21 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 21
        (arg (arg-info visible relevant) (var 9 []) ∷
         arg (arg-info visible relevant) (var 22 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 22
          (arg (arg-info visible relevant) (var 10 []) ∷
           arg (arg-info visible relevant) (var 23 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 23
            (arg (arg-info visible relevant) (var 11 []) ∷
             arg (arg-info visible relevant) (var 24 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 24
              (arg (arg-info visible relevant) (var 12 []) ∷
               arg (arg-info visible relevant) (var 25 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 25
                (arg (arg-info visible relevant) (var 13 []) ∷
                 arg (arg-info visible relevant) (var 26 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 26
                  (arg (arg-info visible relevant) (var 14 []) ∷
                   arg (arg-info visible relevant) (var 27 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 27
                    (arg (arg-info visible relevant) (var 15 []) ∷
                     arg (arg-info visible relevant) (var 28 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 28
                      (arg (arg-info visible relevant) (var 16 []) ∷
                       arg (arg-info visible relevant) (var 29 []) ∷ [])))
                    (abs "_"
                     (var 29
                      (arg (arg-info visible relevant) (var 17 []) ∷
                       arg (arg-info visible relevant) (var 30 []) ∷
                       []))))))))))))))))))))
   , 11)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 19
      (arg (arg-info visible relevant) (var 7 []) ∷
       arg (arg-info visible relevant) (var 20 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 20
        (arg (arg-info visible relevant) (var 8 []) ∷
         arg (arg-info visible relevant) (var 21 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 21
          (arg (arg-info visible relevant) (var 9 []) ∷
           arg (arg-info visible relevant) (var 22 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 22
            (arg (arg-info visible relevant) (var 10 []) ∷
             arg (arg-info visible relevant) (var 23 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 23
              (arg (arg-info visible relevant) (var 11 []) ∷
               arg (arg-info visible relevant) (var 24 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 24
                (arg (arg-info visible relevant) (var 12 []) ∷
                 arg (arg-info visible relevant) (var 25 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 25
                  (arg (arg-info visible relevant) (var 13 []) ∷
                   arg (arg-info visible relevant) (var 26 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 26
                    (arg (arg-info visible relevant) (var 14 []) ∷
                     arg (arg-info visible relevant) (var 27 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 27
                      (arg (arg-info visible relevant) (var 15 []) ∷
                       arg (arg-info visible relevant) (var 28 []) ∷ [])))
                    (abs "_"
                     (var 28
                      (arg (arg-info visible relevant) (var 16 []) ∷
                       arg (arg-info visible relevant) (var 29 []) ∷
                       []))))))))))))))))))))
   , 10)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 18
      (arg (arg-info visible relevant) (var 6 []) ∷
       arg (arg-info visible relevant) (var 19 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 19
        (arg (arg-info visible relevant) (var 7 []) ∷
         arg (arg-info visible relevant) (var 20 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 20
          (arg (arg-info visible relevant) (var 8 []) ∷
           arg (arg-info visible relevant) (var 21 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 21
            (arg (arg-info visible relevant) (var 9 []) ∷
             arg (arg-info visible relevant) (var 22 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 22
              (arg (arg-info visible relevant) (var 10 []) ∷
               arg (arg-info visible relevant) (var 23 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 23
                (arg (arg-info visible relevant) (var 11 []) ∷
                 arg (arg-info visible relevant) (var 24 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 24
                  (arg (arg-info visible relevant) (var 12 []) ∷
                   arg (arg-info visible relevant) (var 25 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 25
                    (arg (arg-info visible relevant) (var 13 []) ∷
                     arg (arg-info visible relevant) (var 26 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 26
                      (arg (arg-info visible relevant) (var 14 []) ∷
                       arg (arg-info visible relevant) (var 27 []) ∷ [])))
                    (abs "_"
                     (var 27
                      (arg (arg-info visible relevant) (var 15 []) ∷
                       arg (arg-info visible relevant) (var 28 []) ∷
                       []))))))))))))))))))))
   , 9)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 17
      (arg (arg-info visible relevant) (var 5 []) ∷
       arg (arg-info visible relevant) (var 18 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 18
        (arg (arg-info visible relevant) (var 6 []) ∷
         arg (arg-info visible relevant) (var 19 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 19
          (arg (arg-info visible relevant) (var 7 []) ∷
           arg (arg-info visible relevant) (var 20 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 20
            (arg (arg-info visible relevant) (var 8 []) ∷
             arg (arg-info visible relevant) (var 21 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 21
              (arg (arg-info visible relevant) (var 9 []) ∷
               arg (arg-info visible relevant) (var 22 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 22
                (arg (arg-info visible relevant) (var 10 []) ∷
                 arg (arg-info visible relevant) (var 23 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 23
                  (arg (arg-info visible relevant) (var 11 []) ∷
                   arg (arg-info visible relevant) (var 24 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 24
                    (arg (arg-info visible relevant) (var 12 []) ∷
                     arg (arg-info visible relevant) (var 25 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 25
                      (arg (arg-info visible relevant) (var 13 []) ∷
                       arg (arg-info visible relevant) (var 26 []) ∷ [])))
                    (abs "_"
                     (var 26
                      (arg (arg-info visible relevant) (var 14 []) ∷
                       arg (arg-info visible relevant) (var 27 []) ∷
                       []))))))))))))))))))))
   , 8)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 16
      (arg (arg-info visible relevant) (var 4 []) ∷
       arg (arg-info visible relevant) (var 17 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 17
        (arg (arg-info visible relevant) (var 5 []) ∷
         arg (arg-info visible relevant) (var 18 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 18
          (arg (arg-info visible relevant) (var 6 []) ∷
           arg (arg-info visible relevant) (var 19 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 19
            (arg (arg-info visible relevant) (var 7 []) ∷
             arg (arg-info visible relevant) (var 20 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 20
              (arg (arg-info visible relevant) (var 8 []) ∷
               arg (arg-info visible relevant) (var 21 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 21
                (arg (arg-info visible relevant) (var 9 []) ∷
                 arg (arg-info visible relevant) (var 22 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 22
                  (arg (arg-info visible relevant) (var 10 []) ∷
                   arg (arg-info visible relevant) (var 23 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 23
                    (arg (arg-info visible relevant) (var 11 []) ∷
                     arg (arg-info visible relevant) (var 24 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 24
                      (arg (arg-info visible relevant) (var 12 []) ∷
                       arg (arg-info visible relevant) (var 25 []) ∷ [])))
                    (abs "_"
                     (var 25
                      (arg (arg-info visible relevant) (var 13 []) ∷
                       arg (arg-info visible relevant) (var 26 []) ∷
                       []))))))))))))))))))))
   , 7)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 15
      (arg (arg-info visible relevant) (var 3 []) ∷
       arg (arg-info visible relevant) (var 16 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 16
        (arg (arg-info visible relevant) (var 4 []) ∷
         arg (arg-info visible relevant) (var 17 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 17
          (arg (arg-info visible relevant) (var 5 []) ∷
           arg (arg-info visible relevant) (var 18 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 18
            (arg (arg-info visible relevant) (var 6 []) ∷
             arg (arg-info visible relevant) (var 19 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 19
              (arg (arg-info visible relevant) (var 7 []) ∷
               arg (arg-info visible relevant) (var 20 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 20
                (arg (arg-info visible relevant) (var 8 []) ∷
                 arg (arg-info visible relevant) (var 21 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 21
                  (arg (arg-info visible relevant) (var 9 []) ∷
                   arg (arg-info visible relevant) (var 22 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 22
                    (arg (arg-info visible relevant) (var 10 []) ∷
                     arg (arg-info visible relevant) (var 23 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 23
                      (arg (arg-info visible relevant) (var 11 []) ∷
                       arg (arg-info visible relevant) (var 24 []) ∷ [])))
                    (abs "_"
                     (var 24
                      (arg (arg-info visible relevant) (var 12 []) ∷
                       arg (arg-info visible relevant) (var 25 []) ∷
                       []))))))))))))))))))))
   , 6)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 14
      (arg (arg-info visible relevant) (var 2 []) ∷
       arg (arg-info visible relevant) (var 15 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 15
        (arg (arg-info visible relevant) (var 3 []) ∷
         arg (arg-info visible relevant) (var 16 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 16
          (arg (arg-info visible relevant) (var 4 []) ∷
           arg (arg-info visible relevant) (var 17 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 17
            (arg (arg-info visible relevant) (var 5 []) ∷
             arg (arg-info visible relevant) (var 18 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 18
              (arg (arg-info visible relevant) (var 6 []) ∷
               arg (arg-info visible relevant) (var 19 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 19
                (arg (arg-info visible relevant) (var 7 []) ∷
                 arg (arg-info visible relevant) (var 20 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 20
                  (arg (arg-info visible relevant) (var 8 []) ∷
                   arg (arg-info visible relevant) (var 21 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 21
                    (arg (arg-info visible relevant) (var 9 []) ∷
                     arg (arg-info visible relevant) (var 22 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 22
                      (arg (arg-info visible relevant) (var 10 []) ∷
                       arg (arg-info visible relevant) (var 23 []) ∷ [])))
                    (abs "_"
                     (var 23
                      (arg (arg-info visible relevant) (var 11 []) ∷
                       arg (arg-info visible relevant) (var 24 []) ∷
                       []))))))))))))))))))))
   , 5)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 13
      (arg (arg-info visible relevant) (var 1 []) ∷
       arg (arg-info visible relevant) (var 14 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 14
        (arg (arg-info visible relevant) (var 2 []) ∷
         arg (arg-info visible relevant) (var 15 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 15
          (arg (arg-info visible relevant) (var 3 []) ∷
           arg (arg-info visible relevant) (var 16 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 16
            (arg (arg-info visible relevant) (var 4 []) ∷
             arg (arg-info visible relevant) (var 17 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 17
              (arg (arg-info visible relevant) (var 5 []) ∷
               arg (arg-info visible relevant) (var 18 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 18
                (arg (arg-info visible relevant) (var 6 []) ∷
                 arg (arg-info visible relevant) (var 19 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 19
                  (arg (arg-info visible relevant) (var 7 []) ∷
                   arg (arg-info visible relevant) (var 20 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 20
                    (arg (arg-info visible relevant) (var 8 []) ∷
                     arg (arg-info visible relevant) (var 21 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 21
                      (arg (arg-info visible relevant) (var 9 []) ∷
                       arg (arg-info visible relevant) (var 22 []) ∷ [])))
                    (abs "_"
                     (var 22
                      (arg (arg-info visible relevant) (var 10 []) ∷
                       arg (arg-info visible relevant) (var 23 []) ∷
                       []))))))))))))))))))))
   , 4)
  ∷ []

private

  module Debug-Size where

    SIZE : Set → Set
    SIZE A = A → Nat

    mutual
      size-Term : SIZE Term
      size-Term (var x args) = suc $′ size-ListArgTerm args + x
      size-Term (con c args) = suc $ size-ListArgTerm args
      size-Term (def f args) = suc $ size-ListArgTerm args
      size-Term (lam v t) = suc $ size-AbsTerm t
      size-Term (pat-lam cs args) = suc $ size-ListClause cs
      size-Term (pi a b) = suc (size-ArgTerm a + size-AbsTerm b)
      size-Term (agda-sort s) = suc $ size-Sort s
      size-Term (lit l) = 0
      size-Term (meta x args) = suc $ size-ListArgTerm args
      size-Term unknown = 0

      size-ArgTerm : SIZE (Arg Term)
      size-ArgTerm (arg i x) = suc $ size-Term x

      size-AbsTerm : SIZE (Abs Term)
      size-AbsTerm (abs s x) = suc $ size-Term x

      size-Clause : SIZE Clause
      size-Clause (clause ps t) = suc $ size-Term t
      size-Clause (absurd-clause ps) = 0

      size-ListClause : SIZE (List Clause)
      size-ListClause [] = 0
      size-ListClause (x ∷ xs) = suc $′ size-Clause x + size-ListClause xs

      size-Sort : SIZE Sort
      size-Sort (set t) = suc $ size-Term t
      size-Sort (lit n) = 0
      size-Sort unknown = 0

      size-ListArgTerm : SIZE (List (Arg Term))
      size-ListArgTerm [] = 0
      size-ListArgTerm (x ∷ xs) = suc $′ size-ArgTerm x + size-ListArgTerm xs

    size-ListArgTermNat : SIZE (List (Arg Term × Nat))
    size-ListArgTermNat [] = 0
    size-ListArgTermNat ((x , n) ∷ xs) = suc $′ size-ArgTerm x + size-ListArgTermNat xs + n

  open Debug-Size

private

  Reordering = List (Nat × Nat)

  weakenReordering : (os : Reordering) → Reordering
  weakenReordering [] = []
  weakenReordering ((x , n) ∷ xs) = (suc x , suc n) ∷ weakenReordering xs

  Reorderingμ : (os : Reordering) → Mem os
  Reorderingμ [] = putμ refl
  Reorderingμ ((from , to) ∷ oss)
   with Reorderingμ oss
  ... | putμ oss-refl = putμ (cong₂ _∷_ (cong₂ _,_ refl refl) oss-refl)

  Natμ : (n : Nat) → Mem n
  Natμ zero = putμ refl
  Natμ (suc n) = -- putμ (cong suc refl) --
                 case Natμ n of λ { (putμ n-refl) → putμ (cong suc n-refl) }

{-
  Termμ : (t : Term) → Mem t
  Termμ t with t ==μ t
  ... | (_ , t-refl , _) = t-refl
-}

  Natμ' : (n : Nat) → Nat
  Natμ' zero = zero
  Natμ' (suc n) = -- suc n
                  case Natμ' n of λ { n → suc n }

  mutual
    Termμ' : (t : Term) → Term
    Termμ' (var x args) =
      case Natμ' x , ListArgTermμ' args of λ
      { (x , args) → var x args }
    Termμ' (con c args) =
      case ListArgTermμ' args of λ
      { args → con c args }
    Termμ' (def f args) =
      case ListArgTermμ' args of λ
      { args → def f args }
    Termμ' (lam v t) =
      case AbsTermμ' t of λ
      { t → lam v t }
    Termμ' (pat-lam cs args) = pat-lam cs args
    Termμ' (pi a b) =
      case ArgTermμ' a , AbsTermμ' b of λ
      { (a , b) → pi a b }
    Termμ' (agda-sort s) =
      case Sortμ' s of λ
      { s → agda-sort s }
    Termμ' (lit l) = lit l
    Termμ' (meta x args) =
      case ListArgTermμ' args of λ
      { args → meta x args }
    Termμ' unknown = unknown

    Sortμ' : (s : Sort) → Sort
    Sortμ' (set t) =
      case Termμ' t of λ
      { t → set t }
    Sortμ' (lit n) = lit n
    Sortμ' unknown = unknown

    AbsTermμ' : (as : Abs Term) → Abs Term
    AbsTermμ' (abs s x) =
      case Termμ' x of λ
      { x → abs s x }

    ArgTermμ' : (at : Arg Term) → Arg Term
    ArgTermμ' (arg i x) =
      case Termμ' x of λ
      { x →
        arg i x }

    ListArgTermμ' : (ats : List (Arg Term)) → List (Arg Term)
    ListArgTermμ' [] = []
    ListArgTermμ' (at ∷ ats) =
      case ArgTermμ' at , ListArgTermμ' ats of λ
      { (at , ats) →
        at ∷ ats }

  ListArgTerm×Natμ' : (atns : List (Arg Term × Nat)) → List (Arg Term × Nat)
  ListArgTerm×Natμ' [] = []
  ListArgTerm×Natμ' ((at , n) ∷ atns) =
    case ArgTermμ' at , Natμ' n , ListArgTerm×Natμ' atns of λ
    { (at , n , atns) → (at , n) ∷ atns }

  mutual
    Termμ : (t : Term) → Mem t
    Termμ (var x args) =
      case Natμ x , ListArgTermμ args of λ
      { (putμ x-refl , putμ args-refl) →
        putμ (cong₂ var x-refl args-refl) }
    Termμ (con c args) =
      case ListArgTermμ args of λ
      { (putμ args-refl) →
        putμ (cong₂ con refl args-refl) }
    Termμ (def f args) =
      case ListArgTermμ args of λ
      { (putμ args-refl) →
        putμ (cong₂ def refl args-refl) }
    Termμ (lam v t) =
      case AbsTermμ t of λ
      { (putμ t-refl) →
        putμ (cong₂ lam refl t-refl) }
    Termμ (pat-lam cs args) = putμ refl
    Termμ (pi a b) =
      case ArgTermμ a , AbsTermμ b of λ
      { (putμ a-refl , putμ b-refl) →
        putμ (cong₂ pi a-refl b-refl) }
    Termμ (agda-sort s) =
      case Sortμ s of λ
      { (putμ s-refl) →
        putμ (cong agda-sort s-refl) }
    Termμ (lit l) = putμ refl
    Termμ (meta x args) =
      case ListArgTermμ args of λ
      { (putμ args-refl) →
        putμ (cong₂ meta refl args-refl) }
    Termμ unknown = putμ refl

    Sortμ : (s : Sort) → Mem s
    Sortμ (set t) =
      case Termμ t of λ
      { (putμ t-refl) →
        putμ (cong set t-refl) }
    Sortμ (lit n) = putμ refl
    Sortμ unknown = putμ refl

    AbsTermμ : (as : Abs Term) → Mem as
    AbsTermμ (abs s x) =
      case Termμ x of λ
      { (putμ x-refl) →
        putμ (cong₂ abs refl x-refl) }

    ArgTermμ : (at : Arg Term) → Mem at
    ArgTermμ (arg i x) =
      case Termμ x of λ
      { (putμ x-refl) →
        putμ (cong₂ arg refl x-refl) }

    ListArgTermμ : (ats : List (Arg Term)) → Mem ats
    ListArgTermμ [] = putμ refl
    ListArgTermμ (at ∷ ats) =
      case ArgTermμ at , ListArgTermμ ats of λ
      { (putμ at-refl , putμ ats-refl) →
        putμ (cong₂ _∷_ at-refl ats-refl) }

  ListArgTerm×Natμ : (atns : List (Arg Term × Nat)) → Mem atns
  ListArgTerm×Natμ [] = putμ refl
  ListArgTerm×Natμ ((at , n) ∷ atns) =
    case ArgTermμ at , Natμ n , ListArgTerm×Natμ atns of λ
    { (putμ at-refl , putμ n-refl , putμ atns-refl) →
      putμ (cong₂ _∷_ (cong₂ _,_ at-refl n-refl) atns-refl) }

  replaceVar : Nat → (os : Reordering) → (x : Nat) → Nat
  replaceVar d [] x = x
  replaceVar d ((x-d , n-d) ∷ xns) x = ifYes x == x-d + d then n-d + d else replaceVar d xns x

  {-# TERMINATING #-}
  reorderVars : Reordering → Term → Term
  reorderVars os t = go 0 os t

    where

    go : Nat → (xns : Reordering) → (t' : Term) → Term
    go d xns (var x args) = var (replaceVar d xns x) (fmap (go d xns) <$> args)
    go d xns (con c args) = con c ((fmap ∘ fmap) (go d xns) args)
    go d xns (def f args) = def f (fmap (go d xns) <$> args)
    go d xns (lam v t) = lam v (go (suc d) xns <$> t)
    go d xns (pat-lam cs args) = pat-lam (fmap (reorderVarsInClause d xns) cs) ((fmap ∘ fmap) (go d xns) args) where
      reorderVarsInClause : Nat → Reordering → Clause → Clause -- TODO reorder patterns?
      reorderVarsInClause d xns (clause ps t) = clause ps (go d xns t)
      reorderVarsInClause d xns (absurd-clause ps) = absurd-clause ps
    go d xns (pi a b) = pi (go d xns <$> a) (go (suc d) xns <$> b)
    go d xns (agda-sort (set t)) = agda-sort (set (go d xns t))
    go d xns (agda-sort (lit n)) = agda-sort (lit n)
    go d xns (agda-sort unknown) = agda-sort unknown
    go d xns (lit l) = lit l
    go d xns (meta x args) = meta x $ (fmap ∘ fmap) (go d xns) args
    go d xns unknown = unknown

  {-
                         <------- helper-type--------- ... -->
     <------- Γ ------->        <------ Γ[w/L] ------>
     γ₀ γ₁ ... γᵢ ... γₙ w w≡R γ'₀ γ'₁ ... γ'ⱼ ... γ'ₘ

     γ' = γ'ⱼ
  -}

  {-
                           <------- helper-type--------- ... -->
     <------- Γ --------->       <------ Γ[w/L] ------>
     γₙ γₙ₋₁ ... γᵢ ... γ₀ w w≡R γ'₀ γ'₁ ... γ'ⱼ ... γ'ₘ

     γ' = γ'ⱼ
  -}

  {-
                         <-------- helper-type---------- ... -->
     <------- Γ ------->        <------- Γ[w/L] ------->
     γ₀ γ₁ ... γᵢ ... γₙ w w≡R γ'ₘ γ'ₘ₋₁ ... γ'ⱼ ... γ'₀

     γ' = γ'ⱼ
  -}

  Γ[w/L]×indexes[Γ]&  : (l≡r : Term) → (L : Type) → (Γ : List (Arg Type)) (∣Γ∣ : Nat) → List (Arg Type × Nat)
  Γ[w/L]×indexes[Γ]& l≡r L Γ ∣Γ∣ =
    go 0 0 [] Γ []

    where

    go : Nat → Nat → (osⱼ : Reordering) → (γs : List (Arg Type)) → List (Arg Type × Nat) → List (Arg Type × Nat)
    go _ _ _   []       cc = cc
    go i j osⱼ (γ ∷ γs) cc =
      let n = ∣Γ∣ - 1
          γ≢l≡r = isNo $ var₀ (n - i) == l≡r
          w' = var₀ (suc j)
      in
      case ArgTermμ (weaken ((n - i) + 3 + j) γ) of λ { (getμ γ') →
      case Termμ (weaken (2 + j) L) of λ { (getμ L') →
      case ArgTermμ (γ' r[ w' / L' ]) of λ { (getμ γ'[w'/L']) →
      let γ'[w'/L'][reordered] = reorderVars osⱼ <$> γ'[w'/L']
          γ≢l≡r&&γ'≠γ'[w'/L'][reordered] : Maybe (Arg Type)
          γ≢l≡r&&γ'≠γ'[w'/L'][reordered] =
            if γ≢l≡r then
              case γ' ==μ γ'[w'/L'][reordered] of (λ
              { (yes _ , _) → nothing
              ; (no _ , _ , getμ γ'[w'/L'][reordered]) → just γ'[w'/L'][reordered] })
            else
              nothing
      in
      case γ≢l≡r&&γ'≠γ'[w'/L'][reordered] of λ
      { (just γ'[w'/L'][reordered]) →
        case Reorderingμ ((j + 3 + n - i , 0) ∷ weakenReordering osⱼ) of λ
        { (getμ osⱼ') →
          go (suc i) (suc j) osⱼ' γs ((γ'[w'/L'][reordered] , i) ∷ cc) }
      ; nothing →
        go (suc i) j osⱼ γs cc }}}}
{-
      let n = ∣Γ∣ - 1
          γ≢l≡r = isNo $ var₀ (n - i) == l≡r
          L' = weaken (2 + j) L
          γ' = weaken ((n - i) + 3 + j) γ
          w' = var₀ (suc j)
          γ'[w'/L'] = γ' r[ w' / L' ]
          γ'[w'/L'][reordered] = reorderVars osⱼ <$> γ'[w'/L']
          γ≢l≡r&&γ'≠γ'[w'/L'][reordered] : Maybe (Arg Type)
          γ≢l≡r&&γ'≠γ'[w'/L'][reordered] =
            if γ≢l≡r then
              case γ' ==μ γ'[w'/L'][reordered] of (λ
              { (yes _ , _) → nothing
              ; (no _ , _ , getμ γ'[w'/L'][reordered]) → just γ'[w'/L'][reordered] })
            else
              nothing
      in
      case γ≢l≡r&&γ'≠γ'[w'/L'][reordered] of λ
      { (just γ'[w'/L'][reordered]) →
        case Reorderingμ ((j + 3 + n - i , 0) ∷ weakenReordering osⱼ) of λ
        { (getμ osⱼ') →
          go (suc i) (suc j) osⱼ' γs ((γ'[w'/L'][reordered] , i) ∷ cc) }
      ; nothing →
        go (suc i) j osⱼ γs cc }
-}
  Γ[w/L]& : List (Arg Type × Nat) → List (Arg Type)
  Γ[w/L]& Γ[w/L]×indexes[Γ] = fst <$> Γ[w/L]×indexes[Γ]

  indexes[Γ]& : List (Arg Type × Nat) → List Nat
  indexes[Γ]& Γ[w/L]×indexes[Γ] = snd <$> Γ[w/L]×indexes[Γ]

  {-
     <---------------------- helper-type--------------------- -->
           <---- Γ[w/L] ----->   <------ Γ[R/L] ------->
     w w≡R γ₀ γ₁ ... γᵢ ... γₙ ( γ'₀ γ'₁ ... γ'ᵢ ... γ'ₙ ) 𝐺[w/L]
     n = ∣Γᴸ∣ - 1 = length Γ[w/L] - 1
  -}
  Γ[R/L]& : (R : Type) → (Γ[w/L] : List (Arg Type)) (∣Γᴸ| : Nat) → List (Arg Type)
  Γ[R/L]& R Γ[w/L] ∣Γᴸ∣ = go 0 Γ[w/L] [] where
    go : Nat → List (Arg Type) → List (Arg Type) → List (Arg Type)
    go _ [] cc = cc
    go i (γ ∷ γs) cc =
      -- γ is the index[γ]ᵗʰ element of Γ[w/L]
      let n  = ∣Γᴸ∣ - 1
          γ' = weakenFrom (n - i) ∣Γᴸ∣ γ
          w' = var₀ (2 * n - i + 2)
          R' = weaken (2 + ∣Γᴸ∣ + (n - i)) R
          γ'[R'/w'] = γ' r[ R' / w' ]
      in
        go (suc i) γs (γ'[R'/w'] ∷ cc)

  {-
     Γ             Γ[w/L]   Γ[R/L]
     0 ... n w w≡R 0 ... m (0 ... m → 𝐺[R/L]) → 𝐺[w/L]
  -}
  𝐺[R/L]-Reordering& : (∣Γ∣ : Nat) → (indexes[Γ] : List Nat) (∣Γᴸ∣ : Nat) →
                       Reordering
  𝐺[R/L]-Reordering& ∣Γ∣ indexes[Γ] ∣Γᴸ∣ =
    go 0 indexes[Γ] []
    where
    go : Nat → List Nat → Reordering → Reordering
    go _ []       cc = cc
    go j (i ∷ is) cc = go (suc j) is ((2 * ∣Γᴸ∣ + 2 + (∣Γ∣ - 1) - i , j) ∷ cc)

  𝐺[R/L]& : (𝐺 : Type) (R : Type) (L : Type) (os : Reordering) (∣Γᴸ∣ : Nat) →
            Type
  𝐺[R/L]& 𝐺 R L os ∣Γᴸ∣ =
    case Termμ (𝐺 r[ R / L ]) of λ { (getμ 𝐺r[R/L]) →
    case Termμ (weaken (2 * ∣Γᴸ∣ + 2) 𝐺r[R/L]) of λ { (getμ wk𝐺r[R/L]) →
    reorderVars os wk𝐺r[R/L] }}
    --reorderVars os (weaken (2 * ∣Γᴸ∣ + 2) (𝐺 r[ R / L ]))

  𝐺[w/L]-Reordering& : (∣Γ∣ : Nat) → (indexes[Γ] : List Nat) (∣Γᴸ∣ : Nat) →
                       Reordering
  𝐺[w/L]-Reordering& ∣Γ∣ indexes[Γ] ∣Γᴸ∣ =
    go 0 indexes[Γ] []
    where
    go : Nat → List Nat → Reordering → Reordering
    go _ []       cc = cc
    go j (i ∷ is) cc = go (suc j) is ((1 + ∣Γᴸ∣ + 2 + (∣Γ∣ - 1) - i , 1 + j) ∷ cc)

  𝐺[w/L]& : (𝐺 : Type) (L : Type) (os : Reordering) (∣Γᴸ∣ : Nat) →
            Type
  𝐺[w/L]& 𝐺 L os ∣Γᴸ∣ =
    case Termμ (weaken (3 + ∣Γᴸ∣) L) of λ { (getμ L') →
    case Termμ (var₀ (2 + ∣Γᴸ∣)) of λ { (getμ w') →
    case Termμ (weaken (3 + ∣Γᴸ∣) 𝐺) of λ { (getμ 𝐺') →
    case Termμ (𝐺' r[ w' / L' ]) of λ { (getμ 𝐺'r[w'/L']) →
    reorderVars os 𝐺'r[w'/L'] }}}}
    --reorderVars os (weaken (3 + ∣Γᴸ∣) 𝐺 r[ var₀ (2 + ∣Γᴸ∣) / weaken (3 + ∣Γᴸ∣) L ])

  w& : (A : Type) → Arg Type
  w& A = hArg A

  w≡R& : (R : Type) → Arg Type
  w≡R& R = vArg (def₂ (quote _≡_) (var₀ 0) (weaken 1 R))

  record Request : Set where
    field
      l≡r : Term
      A : Type
      L : Term
      R : Term
      Γ : List (Arg Type)
      𝐺 : Type

  getRequest : Term → Term → TC Request
  getRequest l≡r hole = do
    L≡R ← inferType l≡r -|
    L≡R-matched ← maybe (typeError (strErr "not an equality" ∷ termErr l≡r ∷ termErr L≡R ∷ [])) pure $
      match 3 (def (quote _≡_) (hArg unknown ∷ (hArg (var₀ 0)) ∷ (vArg (var₀ 1)) ∷ (vArg (var₀ 2)) ∷ [])) L≡R -|
    𝐺 ← inferFunRange hole -|
    Γ ← getContext -|
    case L≡R-matched of λ { (A ∷ L ∷ R ∷ []) →
    case Termμ A , Termμ L , Termμ R of λ { (getμ A , getμ L , getμ R) →
    case ListArgTermμ (reverse Γ) of λ { (getμ reverse-Γ) →
    pure $ record { l≡r = l≡r ; A = A ; L = L ; R = R ; Γ = reverse-Γ ; 𝐺 = 𝐺 } } } }

  record Response : Set where
    no-eta-equality
    field
      l≡r : Term
      w : Arg Type
      w≡R : Arg Type
      Γ[w/L] Γ[R/L] : List (Arg Type)
      𝐺[R/L] 𝐺[w/L] : Type
      Γ[w/L]×indexes[Γ] : List (Arg Type × Nat)
      ∣Γ∣ : Nat

    helper-type : Type
    helper-type = --telPi ((w ∷ w≡R ∷ reverse Γ[w/L]) ++ [ vArg (telPi Γ[R/L] 𝐺[R/L]) ]) 𝐺[w/L]
                  telPi (w ∷ w≡R ∷ reverse Γ[w/L]) (telPi [ vArg (telPi Γ[R/L] 𝐺[R/L]) ] 𝐺[w/L])

    helper-patterns : List (Arg Pattern)
    helper-patterns = (hArg dot ∷ vArg (con₀ (quote refl)) ∷ telePat Γ[w/L]) ++ [ vArg (var "_") ]

    helper-term : Term
    helper-term = var 0 (weaken 1 (teleArgs Γ[w/L]))

    helper-call-args : List (Arg Term)
    helper-call-args = hArg unknown ∷ vArg l≡r ∷ helper-call-args' where
      helper-call-args' : List (Arg Term)
      helper-call-args' = (λ { (γ[w/L] , index[γ]) → var₀ (∣Γ∣ - index[γ] - 1) <$ γ[w/L] }) <$> reverse Γ[w/L]×indexes[Γ]

    stupid-test : List (Arg Term)
    stupid-test = (λ { (γ[w/L] , index[γ]) → var₀ (∣Γ∣ - index[γ] - 1) <$ γ[w/L] }) <$> Γ[w/L]×indexes[Γ]

    dumb-test : List Nat
    dumb-test = (λ { (γ[w/L] , index[γ]) → ∣Γ∣ - index[γ] }) <$> Γ[w/L]×indexes[Γ]

  Responseμ : (r : Response) → Mem r
  Responseμ record { l≡r = l≡r ; w = w ; w≡R = w≡R ; Γ[w/L] = Γ[w/L] ; Γ[R/L] = Γ[R/L] ; 𝐺[R/L] = 𝐺[R/L] ; 𝐺[w/L] = 𝐺[w/L] ; Γ[w/L]×indexes[Γ] = Γ[w/L]×indexes[Γ] ; ∣Γ∣ = ∣Γ∣ } =
    putμ refl

  getResponse : Request → Response
  getResponse q =
    let open Request q
    in
    case length Γ                                of λ   { ∣Γ∣ →
    case Natμ ∣Γ∣                                of λ   { (getμ ∣Γ∣) →
    case Γ[w/L]×indexes[Γ]& l≡r L Γ ∣Γ∣          of λ  { Γ[w/L]×indexes[Γ] →
    --case test-foo                                of λ   { Γ[w/L]×indexes[Γ] →
    case ListArgTerm×Natμ Γ[w/L]×indexes[Γ]      of λ   { (getμ Γ[w/L]×indexes[Γ]) →
    --case ListArgTerm×Natμ' Γ[w/L]×indexes[Γ]      of λ   { Γ[w/L]×indexes[Γ] →
    case length Γ[w/L]×indexes[Γ]                of λ  { ∣Γᴸ∣ →
    case Natμ ∣Γᴸ∣                               of λ  { (getμ ∣Γᴸ∣) →
    case indexes[Γ]& Γ[w/L]×indexes[Γ]           of λ { indexes[Γ] →
    case Γ[w/L]& Γ[w/L]×indexes[Γ]               of λ { Γ[w/L] →
    --case ListArgTermμ Γ[w/L]                     of   λ { (getμ Γ[w/L]) →
    case Γ[R/L]& R Γ[w/L] ∣Γᴸ∣                   of λ { Γ[R/L] →
    --case ListArgTermμ Γ[R/L]                     of λ { (getμ Γ[R/L]) →
    case 𝐺[R/L]-Reordering& ∣Γ∣ indexes[Γ] ∣Γᴸ∣  of λ { 𝐺[R/L]-Reordering →
    case Reorderingμ 𝐺[R/L]-Reordering           of λ { (getμ 𝐺[R/L]-Reordering) →
    case 𝐺[R/L]& 𝐺 R L 𝐺[R/L]-Reordering ∣Γᴸ∣   of λ { 𝐺[R/L] →
    --case Termμ 𝐺[R/L]                            of  λ { (getμ 𝐺[R/L]) →
    case 𝐺[w/L]-Reordering& ∣Γ∣ indexes[Γ] ∣Γᴸ∣  of λ { 𝐺[w/L]-Reordering →
    case Reorderingμ 𝐺[w/L]-Reordering           of λ { (getμ 𝐺[w/L]-Reordering) →
    case 𝐺[w/L]& 𝐺 L 𝐺[w/L]-Reordering ∣Γᴸ∣      of λ { 𝐺[w/L] →
    --case Termμ 𝐺[w/L]                            of λ { (getμ 𝐺[w/L]) →
       record
       { l≡r = l≡r
       ; w = case w& A of id
       ; w≡R = case w≡R& R of id
       ; Γ[w/L] = Γ[w/L]
       ; Γ[R/L] = Γ[R/L]
       ; 𝐺[R/L] = 𝐺[R/L]
       ; 𝐺[w/L] = 𝐺[w/L]
       ; Γ[w/L]×indexes[Γ] = Γ[w/L]×indexes[Γ]
       ; ∣Γ∣ = ∣Γ∣ } }}}}}}}}}}}}}}}

  getResponse-foo : Request → Response
  getResponse-foo q =
    let open Request q
    in
    case length Γ                                of λ   { ∣Γ∣ →
    case Natμ ∣Γ∣                                of λ   { (getμ ∣Γ∣) →
    --case Γ[w/L]×indexes[Γ]& l≡r L Γ ∣Γ∣          of λ  { Γ[w/L]×indexes[Γ] →
    case test-foo                                of λ   { Γ[w/L]×indexes[Γ] →
    case ListArgTerm×Natμ Γ[w/L]×indexes[Γ]      of λ   { (getμ Γ[w/L]×indexes[Γ]) →
    --case ListArgTerm×Natμ' Γ[w/L]×indexes[Γ]      of λ   { Γ[w/L]×indexes[Γ] →
    case length Γ[w/L]×indexes[Γ]                of λ  { ∣Γᴸ∣ →
    case Natμ ∣Γᴸ∣                               of λ  { (getμ ∣Γᴸ∣) →
    case indexes[Γ]& Γ[w/L]×indexes[Γ]           of λ { indexes[Γ] →
    case Γ[w/L]& Γ[w/L]×indexes[Γ]               of λ { Γ[w/L] →
    --case ListArgTermμ Γ[w/L]                     of   λ { (getμ Γ[w/L]) →
    case Γ[R/L]& R Γ[w/L] ∣Γᴸ∣                   of λ { Γ[R/L] →
    --case ListArgTermμ Γ[R/L]                     of λ { (getμ Γ[R/L]) →
    case 𝐺[R/L]-Reordering& ∣Γ∣ indexes[Γ] ∣Γᴸ∣  of λ { 𝐺[R/L]-Reordering →
    case Reorderingμ 𝐺[R/L]-Reordering           of λ { (getμ 𝐺[R/L]-Reordering) →
    case 𝐺[R/L]& 𝐺 R L 𝐺[R/L]-Reordering ∣Γᴸ∣   of λ { 𝐺[R/L] →
    --case Termμ 𝐺[R/L]                            of  λ { (getμ 𝐺[R/L]) →
    case 𝐺[w/L]-Reordering& ∣Γ∣ indexes[Γ] ∣Γᴸ∣  of λ { 𝐺[w/L]-Reordering →
    case Reorderingμ 𝐺[w/L]-Reordering           of λ { (getμ 𝐺[w/L]-Reordering) →
    case 𝐺[w/L]& 𝐺 L 𝐺[w/L]-Reordering ∣Γᴸ∣      of λ { 𝐺[w/L] →
    --case Termμ 𝐺[w/L]                            of λ { (getμ 𝐺[w/L]) →
       record
       { l≡r = l≡r
       ; w = case w& A of id
       ; w≡R = case w≡R& R of id
       ; Γ[w/L] = Γ[w/L]
       ; Γ[R/L] = Γ[R/L]
       ; 𝐺[R/L] = 𝐺[R/L]
       ; 𝐺[w/L] = 𝐺[w/L]
       ; Γ[w/L]×indexes[Γ] = Γ[w/L]×indexes[Γ]
       ; ∣Γ∣ = ∣Γ∣ } }}}}}}}}}}}}}}}

macro

  reright : Term → Tactic
  reright l≡r hole =
    q ← getRequest l≡r hole -|
    n ← freshName "reright" -|
    --let open Response (getResponse q) in
    case getResponse q of λ
    { r →
      let open Response r in
      catchTC (typeError [ strErr "error defining helper function" ]) (define (vArg n) helper-type [ clause helper-patterns helper-term ]) ~|
      unify hole (def n helper-call-args) }

macro
  reright-debug-foo-before : Term → Tactic
  reright-debug-foo-before l≡r hole =
    q ← getRequest l≡r hole -|
    let open Request q in
    case Responseμ (getResponse-foo q) of λ { (getμ r) →
    let open Response r in
    typeError ( strErr "reright-debug"            ∷ termErr (` (size-ListArgTermNat Γ[w/L]×indexes[Γ]))                 ∷
                [] ) }

  reright-debug-reg-before : Term → Tactic
  reright-debug-reg-before l≡r hole =
    q ← getRequest l≡r hole -|
    let open Request q in
    case Responseμ (getResponse q) of λ { (getμ r) →
    let open Response r in
    typeError ( strErr "reright-debug"            ∷ termErr (` (size-ListArgTermNat Γ[w/L]×indexes[Γ]))                 ∷
                [] ) }

  reright-debug-foo-after : Term → Tactic
  reright-debug-foo-after l≡r hole =
    q ← getRequest l≡r hole -|
    let open Request q in
    case Responseμ (getResponse-foo q) of λ { (getμ r) →
    let open Response r in
    typeError ( strErr "reright-debug"            ∷ termErr (` dumb-test)                  ∷
                [] ) }

  reright-debug-reg-after : Term → Tactic
  reright-debug-reg-after l≡r hole =
    q ← getRequest l≡r hole -|
    let open Request q in
    case Responseμ (getResponse q) of λ { (getμ r) →
    let open Response r in
    typeError ( strErr "reright-debug"            ∷ termErr (` dumb-test)                  ∷
                [] ) }


module Benchmarks where
  FOO : Set₁
  FOO = (A : Set) (x y : A) (F : A → A → Set) →

        (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
        (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
        (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
        (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
        (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
        (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
        (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
        (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
        (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →
        (_ : F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y) →

        x ≡ y →

        F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y → F x y →

        Set

  foo : FOO
  foo A x y F
      _ _ _ _ _ _ _ _ _ _
      x≡y = reright-debug-reg-after x≡y {!!}
      -- using full Natμ
      -- Typing.CheckRHS
      -- reright-debug-reg-after               11,869ms
      -- reright-debug-reg-before              2,796ms
      -- reright-debug-foo-before              1,746ms
      -- reright-debug-foo-after               2,240ms

{-
macro
  reright-debug : Term → Tactic
  reright-debug l≡r hole =
    q ← getRequest l≡r hole -|
    let open Request q in
    typeError ( strErr "reright-debug"          ∷
                strErr "\nl≡r:"                 ∷ termErr (` (Request.l≡r q))      ∷
                strErr "\nA:"                   ∷ termErr (` A)                    ∷
                strErr "\nL:"                   ∷ termErr (` L)                    ∷
                strErr "\nR:"                   ∷ termErr (` R)                    ∷
                strErr "\nΓ:"                   ∷ termErr (` Γ)                    ∷
                strErr "\nlength Γ:"            ∷ termErr (` (length Γ))           ∷
                strErr "\n𝐺:"                   ∷ termErr (` 𝐺)                   ∷
                strErr "\nΓ[w/L]×indexes[Γ]:"   ∷ termErr (` Γ[w/L]×indexes[Γ])    ∷
                strErr "\nΓ[w/L]:"              ∷ termErr (` Γ[w/L])               ∷
                strErr "\nindexes[Γ]:"          ∷ termErr (` indexes[Γ])           ∷
                strErr "\nΓ[R/L]:"              ∷ termErr (` Γ[R/L])               ∷
                strErr "\n𝐺[R/L]:"              ∷ termErr (` 𝐺[R/L])               ∷
                strErr "\nRE𝐺[R/L]:"            ∷ termErr (` reorderings-𝐺[R/L])   ∷
                strErr "\n𝐺[w/L]:"              ∷ termErr (` 𝐺[w/L])               ∷
                strErr "\nw:"                   ∷ termErr (` w)                    ∷
                strErr "\nw≡R:"                 ∷ termErr (` w≡R)                  ∷
                strErr "helper-type:"           ∷ termErr helper-type              ∷
                strErr "helper-patterns:"       ∷ termErr (` helper-patterns)      ∷
                strErr "helper-term:"           ∷ termErr (` helper-term)          ∷
                strErr "helper-call-args:"      ∷ termErr (` helper-call-args)     ∷
                [] )

  reright : Term → Tactic
  reright l≡r hole =
    q ← getRequest l≡r hole -|
    n ← freshName "reright" -|
    let open Request q in
    catchTC (typeError [ strErr "error defining helper function" ]) (define (vArg n) helper-type [ clause helper-patterns helper-term ]) ~|
    unify hole (def n helper-call-args)
-}


module Tactic.Reright-1 where

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

  Γ[w/L]×indexes[Γ]&'  : (l≡r : Term) → (L : Type) → (Γ : List (Arg Type)) (∣Γ∣ : Nat) → List (Arg Type × Nat)
  Γ[w/L]×indexes[Γ]&' l≡r L [] ∣Γ∣ = []
  Γ[w/L]×indexes[Γ]&' l≡r L (γ ∷ γs) ∣Γ∣ =
    (weaken 1 (weaken 1 (weaken 1 γ)) , 0) ∷ Γ[w/L]×indexes[Γ]&' l≡r L γs ∣Γ∣

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
      let γ'[w'/L'][reordered] = {-reorderVars osⱼ <$>-} γ'[w'/L']
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
    field
      Γ[w/L]×indexes[Γ] : List (Arg Type × Nat)
      ∣Γ∣ : Nat

    dumb-test : List Nat
    dumb-test = (λ { (γ[w/L] , index[γ]) → ∣Γ∣ - index[γ] }) <$> Γ[w/L]×indexes[Γ]

  Responseμ : (r : Response) → Mem r
  Responseμ record { Γ[w/L]×indexes[Γ] = Γ[w/L]×indexes[Γ] ; ∣Γ∣ = ∣Γ∣ } = putμ refl

  getResponse : Request → Response
  getResponse q =
    let open Request q
    in
    case length Γ                                of λ   { ∣Γ∣ →
    case Natμ ∣Γ∣                                of λ   { (getμ ∣Γ∣) →
    case Γ[w/L]×indexes[Γ]& l≡r L Γ ∣Γ∣          of λ  { Γ[w/L]×indexes[Γ] →
    case ListArgTerm×Natμ Γ[w/L]×indexes[Γ]      of λ   { (getμ Γ[w/L]×indexes[Γ]) →
       record
       { Γ[w/L]×indexes[Γ] = Γ[w/L]×indexes[Γ]
       ; ∣Γ∣ = ∣Γ∣ } }}}}

  getResponse' : Request → Response
  getResponse' q =
    let open Request q
    in
    case length Γ                                of λ   { ∣Γ∣ →
    case Natμ ∣Γ∣                                of λ   { (getμ ∣Γ∣) →
    case Γ[w/L]×indexes[Γ]&' l≡r L Γ ∣Γ∣          of λ  { Γ[w/L]×indexes[Γ] →
    case ListArgTerm×Natμ Γ[w/L]×indexes[Γ]      of λ   { (getμ Γ[w/L]×indexes[Γ]) →
       record
       { Γ[w/L]×indexes[Γ] = Γ[w/L]×indexes[Γ]
       ; ∣Γ∣ = ∣Γ∣ } }}}}

  getResponse-foo : Request → Response
  getResponse-foo q =
    let open Request q
    in
    case length Γ                                of λ   { ∣Γ∣ →
    case Natμ ∣Γ∣                                of λ   { (getμ ∣Γ∣) →
    case test-foo                                of λ   { Γ[w/L]×indexes[Γ] →
    case ListArgTerm×Natμ Γ[w/L]×indexes[Γ]      of λ   { (getμ Γ[w/L]×indexes[Γ]) →
       record
       { Γ[w/L]×indexes[Γ] = Γ[w/L]×indexes[Γ]
       ; ∣Γ∣ = ∣Γ∣ } }}}}

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

  reright-debug-reg'-before : Term → Tactic
  reright-debug-reg'-before l≡r hole =
    q ← getRequest l≡r hole -|
    let open Request q in
    case Responseμ (getResponse' q) of λ { (getμ r) →
    let open Response r in
    typeError ( strErr "reright-debug"            ∷ termErr (` (size-ListArgTermNat Γ[w/L]×indexes[Γ]))                  ∷
                [] ) }

  reright-debug-reg'-after : Term → Tactic
  reright-debug-reg'-after l≡r hole =
    q ← getRequest l≡r hole -|
    let open Request q in
    case Responseμ (getResponse' q) of λ { (getμ r) →
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
      x≡y = reright-debug-reg'-after x≡y {!!}
      -- using full Natμ
      -- Typing.CheckRHS
      -- reright-debug-reg-after               11,869ms
      -- reright-debug-reg-before              2,796ms
      -- reright-debug-foo-before              1,746ms
      -- reright-debug-foo-after               2,240ms

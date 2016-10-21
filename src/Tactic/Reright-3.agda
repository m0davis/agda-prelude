
module Tactic.Reright-3 where

open import Prelude

open import Tactic.Reflection
open import Tactic.Reflection.Match
open import Tactic.Reflection.Replace
open import Tactic.Reflection.Quote

open import Prelude.Memoization
open import Prelude.Equality.Memoized
open import Prelude.Nat.Memoized
open import Tactic.Reflection.Equality.Memoized

the-Γ : List (Arg Type)
the-Γ =
  arg (arg-info visible relevant)
  (def (quote _≡_)
   (arg (arg-info hidden relevant) (def (quote lzero) []) ∷
    arg (arg-info hidden relevant) (var 13 []) ∷
    arg (arg-info visible relevant) (var 12 []) ∷
    arg (arg-info visible relevant) (var 11 []) ∷ []))
  ∷
  arg (arg-info visible relevant)
  (pi
   (arg (arg-info visible relevant)
    (var 9
     (arg (arg-info visible relevant) (var 11 []) ∷
      arg (arg-info visible relevant) (var 10 []) ∷ [])))
   (abs "_"
    (pi
     (arg (arg-info visible relevant)
      (var 10
       (arg (arg-info visible relevant) (var 12 []) ∷
        arg (arg-info visible relevant) (var 11 []) ∷ [])))
     (abs "_"
      (pi
       (arg (arg-info visible relevant)
        (var 11
         (arg (arg-info visible relevant) (var 13 []) ∷
          arg (arg-info visible relevant) (var 12 []) ∷ [])))
       (abs "_"
        (pi
         (arg (arg-info visible relevant)
          (var 12
           (arg (arg-info visible relevant) (var 14 []) ∷
            arg (arg-info visible relevant) (var 13 []) ∷ [])))
         (abs "_"
          (pi
           (arg (arg-info visible relevant)
            (var 13
             (arg (arg-info visible relevant) (var 15 []) ∷
              arg (arg-info visible relevant) (var 14 []) ∷ [])))
           (abs "_"
            (pi
             (arg (arg-info visible relevant)
              (var 14
               (arg (arg-info visible relevant) (var 16 []) ∷
                arg (arg-info visible relevant) (var 15 []) ∷ [])))
             (abs "_"
              (pi
               (arg (arg-info visible relevant)
                (var 15
                 (arg (arg-info visible relevant) (var 17 []) ∷
                  arg (arg-info visible relevant) (var 16 []) ∷ [])))
               (abs "_"
                (pi
                 (arg (arg-info visible relevant)
                  (var 16
                   (arg (arg-info visible relevant) (var 18 []) ∷
                    arg (arg-info visible relevant) (var 17 []) ∷ [])))
                 (abs "_"
                  (pi
                   (arg (arg-info visible relevant)
                    (var 17
                     (arg (arg-info visible relevant) (var 19 []) ∷
                      arg (arg-info visible relevant) (var 18 []) ∷ [])))
                   (abs "_"
                    (var 18
                     (arg (arg-info visible relevant) (var 20 []) ∷
                      arg (arg-info visible relevant) (var 19 []) ∷
                      []))))))))))))))))))))
  ∷
  arg (arg-info visible relevant)
  (pi
   (arg (arg-info visible relevant)
    (var 8
     (arg (arg-info visible relevant) (var 10 []) ∷
      arg (arg-info visible relevant) (var 9 []) ∷ [])))
   (abs "_"
    (pi
     (arg (arg-info visible relevant)
      (var 9
       (arg (arg-info visible relevant) (var 11 []) ∷
        arg (arg-info visible relevant) (var 10 []) ∷ [])))
     (abs "_"
      (pi
       (arg (arg-info visible relevant)
        (var 10
         (arg (arg-info visible relevant) (var 12 []) ∷
          arg (arg-info visible relevant) (var 11 []) ∷ [])))
       (abs "_"
        (pi
         (arg (arg-info visible relevant)
          (var 11
           (arg (arg-info visible relevant) (var 13 []) ∷
            arg (arg-info visible relevant) (var 12 []) ∷ [])))
         (abs "_"
          (pi
           (arg (arg-info visible relevant)
            (var 12
             (arg (arg-info visible relevant) (var 14 []) ∷
              arg (arg-info visible relevant) (var 13 []) ∷ [])))
           (abs "_"
            (pi
             (arg (arg-info visible relevant)
              (var 13
               (arg (arg-info visible relevant) (var 15 []) ∷
                arg (arg-info visible relevant) (var 14 []) ∷ [])))
             (abs "_"
              (pi
               (arg (arg-info visible relevant)
                (var 14
                 (arg (arg-info visible relevant) (var 16 []) ∷
                  arg (arg-info visible relevant) (var 15 []) ∷ [])))
               (abs "_"
                (pi
                 (arg (arg-info visible relevant)
                  (var 15
                   (arg (arg-info visible relevant) (var 17 []) ∷
                    arg (arg-info visible relevant) (var 16 []) ∷ [])))
                 (abs "_"
                  (pi
                   (arg (arg-info visible relevant)
                    (var 16
                     (arg (arg-info visible relevant) (var 18 []) ∷
                      arg (arg-info visible relevant) (var 17 []) ∷ [])))
                   (abs "_"
                    (var 17
                     (arg (arg-info visible relevant) (var 19 []) ∷
                      arg (arg-info visible relevant) (var 18 []) ∷
                      []))))))))))))))))))))
  ∷
  arg (arg-info visible relevant)
  (pi
   (arg (arg-info visible relevant)
    (var 7
     (arg (arg-info visible relevant) (var 9 []) ∷
      arg (arg-info visible relevant) (var 8 []) ∷ [])))
   (abs "_"
    (pi
     (arg (arg-info visible relevant)
      (var 8
       (arg (arg-info visible relevant) (var 10 []) ∷
        arg (arg-info visible relevant) (var 9 []) ∷ [])))
     (abs "_"
      (pi
       (arg (arg-info visible relevant)
        (var 9
         (arg (arg-info visible relevant) (var 11 []) ∷
          arg (arg-info visible relevant) (var 10 []) ∷ [])))
       (abs "_"
        (pi
         (arg (arg-info visible relevant)
          (var 10
           (arg (arg-info visible relevant) (var 12 []) ∷
            arg (arg-info visible relevant) (var 11 []) ∷ [])))
         (abs "_"
          (pi
           (arg (arg-info visible relevant)
            (var 11
             (arg (arg-info visible relevant) (var 13 []) ∷
              arg (arg-info visible relevant) (var 12 []) ∷ [])))
           (abs "_"
            (pi
             (arg (arg-info visible relevant)
              (var 12
               (arg (arg-info visible relevant) (var 14 []) ∷
                arg (arg-info visible relevant) (var 13 []) ∷ [])))
             (abs "_"
              (pi
               (arg (arg-info visible relevant)
                (var 13
                 (arg (arg-info visible relevant) (var 15 []) ∷
                  arg (arg-info visible relevant) (var 14 []) ∷ [])))
               (abs "_"
                (pi
                 (arg (arg-info visible relevant)
                  (var 14
                   (arg (arg-info visible relevant) (var 16 []) ∷
                    arg (arg-info visible relevant) (var 15 []) ∷ [])))
                 (abs "_"
                  (pi
                   (arg (arg-info visible relevant)
                    (var 15
                     (arg (arg-info visible relevant) (var 17 []) ∷
                      arg (arg-info visible relevant) (var 16 []) ∷ [])))
                   (abs "_"
                    (var 16
                     (arg (arg-info visible relevant) (var 18 []) ∷
                      arg (arg-info visible relevant) (var 17 []) ∷
                      []))))))))))))))))))))
  ∷
  arg (arg-info visible relevant)
  (pi
   (arg (arg-info visible relevant)
    (var 6
     (arg (arg-info visible relevant) (var 8 []) ∷
      arg (arg-info visible relevant) (var 7 []) ∷ [])))
   (abs "_"
    (pi
     (arg (arg-info visible relevant)
      (var 7
       (arg (arg-info visible relevant) (var 9 []) ∷
        arg (arg-info visible relevant) (var 8 []) ∷ [])))
     (abs "_"
      (pi
       (arg (arg-info visible relevant)
        (var 8
         (arg (arg-info visible relevant) (var 10 []) ∷
          arg (arg-info visible relevant) (var 9 []) ∷ [])))
       (abs "_"
        (pi
         (arg (arg-info visible relevant)
          (var 9
           (arg (arg-info visible relevant) (var 11 []) ∷
            arg (arg-info visible relevant) (var 10 []) ∷ [])))
         (abs "_"
          (pi
           (arg (arg-info visible relevant)
            (var 10
             (arg (arg-info visible relevant) (var 12 []) ∷
              arg (arg-info visible relevant) (var 11 []) ∷ [])))
           (abs "_"
            (pi
             (arg (arg-info visible relevant)
              (var 11
               (arg (arg-info visible relevant) (var 13 []) ∷
                arg (arg-info visible relevant) (var 12 []) ∷ [])))
             (abs "_"
              (pi
               (arg (arg-info visible relevant)
                (var 12
                 (arg (arg-info visible relevant) (var 14 []) ∷
                  arg (arg-info visible relevant) (var 13 []) ∷ [])))
               (abs "_"
                (pi
                 (arg (arg-info visible relevant)
                  (var 13
                   (arg (arg-info visible relevant) (var 15 []) ∷
                    arg (arg-info visible relevant) (var 14 []) ∷ [])))
                 (abs "_"
                  (pi
                   (arg (arg-info visible relevant)
                    (var 14
                     (arg (arg-info visible relevant) (var 16 []) ∷
                      arg (arg-info visible relevant) (var 15 []) ∷ [])))
                   (abs "_"
                    (var 15
                     (arg (arg-info visible relevant) (var 17 []) ∷
                      arg (arg-info visible relevant) (var 16 []) ∷
                      []))))))))))))))))))))
  ∷
  arg (arg-info visible relevant)
  (pi
   (arg (arg-info visible relevant)
    (var 5
     (arg (arg-info visible relevant) (var 7 []) ∷
      arg (arg-info visible relevant) (var 6 []) ∷ [])))
   (abs "_"
    (pi
     (arg (arg-info visible relevant)
      (var 6
       (arg (arg-info visible relevant) (var 8 []) ∷
        arg (arg-info visible relevant) (var 7 []) ∷ [])))
     (abs "_"
      (pi
       (arg (arg-info visible relevant)
        (var 7
         (arg (arg-info visible relevant) (var 9 []) ∷
          arg (arg-info visible relevant) (var 8 []) ∷ [])))
       (abs "_"
        (pi
         (arg (arg-info visible relevant)
          (var 8
           (arg (arg-info visible relevant) (var 10 []) ∷
            arg (arg-info visible relevant) (var 9 []) ∷ [])))
         (abs "_"
          (pi
           (arg (arg-info visible relevant)
            (var 9
             (arg (arg-info visible relevant) (var 11 []) ∷
              arg (arg-info visible relevant) (var 10 []) ∷ [])))
           (abs "_"
            (pi
             (arg (arg-info visible relevant)
              (var 10
               (arg (arg-info visible relevant) (var 12 []) ∷
                arg (arg-info visible relevant) (var 11 []) ∷ [])))
             (abs "_"
              (pi
               (arg (arg-info visible relevant)
                (var 11
                 (arg (arg-info visible relevant) (var 13 []) ∷
                  arg (arg-info visible relevant) (var 12 []) ∷ [])))
               (abs "_"
                (pi
                 (arg (arg-info visible relevant)
                  (var 12
                   (arg (arg-info visible relevant) (var 14 []) ∷
                    arg (arg-info visible relevant) (var 13 []) ∷ [])))
                 (abs "_"
                  (pi
                   (arg (arg-info visible relevant)
                    (var 13
                     (arg (arg-info visible relevant) (var 15 []) ∷
                      arg (arg-info visible relevant) (var 14 []) ∷ [])))
                   (abs "_"
                    (var 14
                     (arg (arg-info visible relevant) (var 16 []) ∷
                      arg (arg-info visible relevant) (var 15 []) ∷
                      []))))))))))))))))))))
  ∷
  arg (arg-info visible relevant)
  (pi
   (arg (arg-info visible relevant)
    (var 4
     (arg (arg-info visible relevant) (var 6 []) ∷
      arg (arg-info visible relevant) (var 5 []) ∷ [])))
   (abs "_"
    (pi
     (arg (arg-info visible relevant)
      (var 5
       (arg (arg-info visible relevant) (var 7 []) ∷
        arg (arg-info visible relevant) (var 6 []) ∷ [])))
     (abs "_"
      (pi
       (arg (arg-info visible relevant)
        (var 6
         (arg (arg-info visible relevant) (var 8 []) ∷
          arg (arg-info visible relevant) (var 7 []) ∷ [])))
       (abs "_"
        (pi
         (arg (arg-info visible relevant)
          (var 7
           (arg (arg-info visible relevant) (var 9 []) ∷
            arg (arg-info visible relevant) (var 8 []) ∷ [])))
         (abs "_"
          (pi
           (arg (arg-info visible relevant)
            (var 8
             (arg (arg-info visible relevant) (var 10 []) ∷
              arg (arg-info visible relevant) (var 9 []) ∷ [])))
           (abs "_"
            (pi
             (arg (arg-info visible relevant)
              (var 9
               (arg (arg-info visible relevant) (var 11 []) ∷
                arg (arg-info visible relevant) (var 10 []) ∷ [])))
             (abs "_"
              (pi
               (arg (arg-info visible relevant)
                (var 10
                 (arg (arg-info visible relevant) (var 12 []) ∷
                  arg (arg-info visible relevant) (var 11 []) ∷ [])))
               (abs "_"
                (pi
                 (arg (arg-info visible relevant)
                  (var 11
                   (arg (arg-info visible relevant) (var 13 []) ∷
                    arg (arg-info visible relevant) (var 12 []) ∷ [])))
                 (abs "_"
                  (pi
                   (arg (arg-info visible relevant)
                    (var 12
                     (arg (arg-info visible relevant) (var 14 []) ∷
                      arg (arg-info visible relevant) (var 13 []) ∷ [])))
                   (abs "_"
                    (var 13
                     (arg (arg-info visible relevant) (var 15 []) ∷
                      arg (arg-info visible relevant) (var 14 []) ∷
                      []))))))))))))))))))))
  ∷
  arg (arg-info visible relevant)
  (pi
   (arg (arg-info visible relevant)
    (var 3
     (arg (arg-info visible relevant) (var 5 []) ∷
      arg (arg-info visible relevant) (var 4 []) ∷ [])))
   (abs "_"
    (pi
     (arg (arg-info visible relevant)
      (var 4
       (arg (arg-info visible relevant) (var 6 []) ∷
        arg (arg-info visible relevant) (var 5 []) ∷ [])))
     (abs "_"
      (pi
       (arg (arg-info visible relevant)
        (var 5
         (arg (arg-info visible relevant) (var 7 []) ∷
          arg (arg-info visible relevant) (var 6 []) ∷ [])))
       (abs "_"
        (pi
         (arg (arg-info visible relevant)
          (var 6
           (arg (arg-info visible relevant) (var 8 []) ∷
            arg (arg-info visible relevant) (var 7 []) ∷ [])))
         (abs "_"
          (pi
           (arg (arg-info visible relevant)
            (var 7
             (arg (arg-info visible relevant) (var 9 []) ∷
              arg (arg-info visible relevant) (var 8 []) ∷ [])))
           (abs "_"
            (pi
             (arg (arg-info visible relevant)
              (var 8
               (arg (arg-info visible relevant) (var 10 []) ∷
                arg (arg-info visible relevant) (var 9 []) ∷ [])))
             (abs "_"
              (pi
               (arg (arg-info visible relevant)
                (var 9
                 (arg (arg-info visible relevant) (var 11 []) ∷
                  arg (arg-info visible relevant) (var 10 []) ∷ [])))
               (abs "_"
                (pi
                 (arg (arg-info visible relevant)
                  (var 10
                   (arg (arg-info visible relevant) (var 12 []) ∷
                    arg (arg-info visible relevant) (var 11 []) ∷ [])))
                 (abs "_"
                  (pi
                   (arg (arg-info visible relevant)
                    (var 11
                     (arg (arg-info visible relevant) (var 13 []) ∷
                      arg (arg-info visible relevant) (var 12 []) ∷ [])))
                   (abs "_"
                    (var 12
                     (arg (arg-info visible relevant) (var 14 []) ∷
                      arg (arg-info visible relevant) (var 13 []) ∷
                      []))))))))))))))))))))
  ∷
  arg (arg-info visible relevant)
  (pi
   (arg (arg-info visible relevant)
    (var 2
     (arg (arg-info visible relevant) (var 4 []) ∷
      arg (arg-info visible relevant) (var 3 []) ∷ [])))
   (abs "_"
    (pi
     (arg (arg-info visible relevant)
      (var 3
       (arg (arg-info visible relevant) (var 5 []) ∷
        arg (arg-info visible relevant) (var 4 []) ∷ [])))
     (abs "_"
      (pi
       (arg (arg-info visible relevant)
        (var 4
         (arg (arg-info visible relevant) (var 6 []) ∷
          arg (arg-info visible relevant) (var 5 []) ∷ [])))
       (abs "_"
        (pi
         (arg (arg-info visible relevant)
          (var 5
           (arg (arg-info visible relevant) (var 7 []) ∷
            arg (arg-info visible relevant) (var 6 []) ∷ [])))
         (abs "_"
          (pi
           (arg (arg-info visible relevant)
            (var 6
             (arg (arg-info visible relevant) (var 8 []) ∷
              arg (arg-info visible relevant) (var 7 []) ∷ [])))
           (abs "_"
            (pi
             (arg (arg-info visible relevant)
              (var 7
               (arg (arg-info visible relevant) (var 9 []) ∷
                arg (arg-info visible relevant) (var 8 []) ∷ [])))
             (abs "_"
              (pi
               (arg (arg-info visible relevant)
                (var 8
                 (arg (arg-info visible relevant) (var 10 []) ∷
                  arg (arg-info visible relevant) (var 9 []) ∷ [])))
               (abs "_"
                (pi
                 (arg (arg-info visible relevant)
                  (var 9
                   (arg (arg-info visible relevant) (var 11 []) ∷
                    arg (arg-info visible relevant) (var 10 []) ∷ [])))
                 (abs "_"
                  (pi
                   (arg (arg-info visible relevant)
                    (var 10
                     (arg (arg-info visible relevant) (var 12 []) ∷
                      arg (arg-info visible relevant) (var 11 []) ∷ [])))
                   (abs "_"
                    (var 11
                     (arg (arg-info visible relevant) (var 13 []) ∷
                      arg (arg-info visible relevant) (var 12 []) ∷
                      []))))))))))))))))))))
  ∷
  arg (arg-info visible relevant)
  (pi
   (arg (arg-info visible relevant)
    (var 1
     (arg (arg-info visible relevant) (var 3 []) ∷
      arg (arg-info visible relevant) (var 2 []) ∷ [])))
   (abs "_"
    (pi
     (arg (arg-info visible relevant)
      (var 2
       (arg (arg-info visible relevant) (var 4 []) ∷
        arg (arg-info visible relevant) (var 3 []) ∷ [])))
     (abs "_"
      (pi
       (arg (arg-info visible relevant)
        (var 3
         (arg (arg-info visible relevant) (var 5 []) ∷
          arg (arg-info visible relevant) (var 4 []) ∷ [])))
       (abs "_"
        (pi
         (arg (arg-info visible relevant)
          (var 4
           (arg (arg-info visible relevant) (var 6 []) ∷
            arg (arg-info visible relevant) (var 5 []) ∷ [])))
         (abs "_"
          (pi
           (arg (arg-info visible relevant)
            (var 5
             (arg (arg-info visible relevant) (var 7 []) ∷
              arg (arg-info visible relevant) (var 6 []) ∷ [])))
           (abs "_"
            (pi
             (arg (arg-info visible relevant)
              (var 6
               (arg (arg-info visible relevant) (var 8 []) ∷
                arg (arg-info visible relevant) (var 7 []) ∷ [])))
             (abs "_"
              (pi
               (arg (arg-info visible relevant)
                (var 7
                 (arg (arg-info visible relevant) (var 9 []) ∷
                  arg (arg-info visible relevant) (var 8 []) ∷ [])))
               (abs "_"
                (pi
                 (arg (arg-info visible relevant)
                  (var 8
                   (arg (arg-info visible relevant) (var 10 []) ∷
                    arg (arg-info visible relevant) (var 9 []) ∷ [])))
                 (abs "_"
                  (pi
                   (arg (arg-info visible relevant)
                    (var 9
                     (arg (arg-info visible relevant) (var 11 []) ∷
                      arg (arg-info visible relevant) (var 10 []) ∷ [])))
                   (abs "_"
                    (var 10
                     (arg (arg-info visible relevant) (var 12 []) ∷
                      arg (arg-info visible relevant) (var 11 []) ∷
                      []))))))))))))))))))))
  ∷
  arg (arg-info visible relevant)
  (pi
   (arg (arg-info visible relevant)
    (var 0
     (arg (arg-info visible relevant) (var 2 []) ∷
      arg (arg-info visible relevant) (var 1 []) ∷ [])))
   (abs "_"
    (pi
     (arg (arg-info visible relevant)
      (var 1
       (arg (arg-info visible relevant) (var 3 []) ∷
        arg (arg-info visible relevant) (var 2 []) ∷ [])))
     (abs "_"
      (pi
       (arg (arg-info visible relevant)
        (var 2
         (arg (arg-info visible relevant) (var 4 []) ∷
          arg (arg-info visible relevant) (var 3 []) ∷ [])))
       (abs "_"
        (pi
         (arg (arg-info visible relevant)
          (var 3
           (arg (arg-info visible relevant) (var 5 []) ∷
            arg (arg-info visible relevant) (var 4 []) ∷ [])))
         (abs "_"
          (pi
           (arg (arg-info visible relevant)
            (var 4
             (arg (arg-info visible relevant) (var 6 []) ∷
              arg (arg-info visible relevant) (var 5 []) ∷ [])))
           (abs "_"
            (pi
             (arg (arg-info visible relevant)
              (var 5
               (arg (arg-info visible relevant) (var 7 []) ∷
                arg (arg-info visible relevant) (var 6 []) ∷ [])))
             (abs "_"
              (pi
               (arg (arg-info visible relevant)
                (var 6
                 (arg (arg-info visible relevant) (var 8 []) ∷
                  arg (arg-info visible relevant) (var 7 []) ∷ [])))
               (abs "_"
                (pi
                 (arg (arg-info visible relevant)
                  (var 7
                   (arg (arg-info visible relevant) (var 9 []) ∷
                    arg (arg-info visible relevant) (var 8 []) ∷ [])))
                 (abs "_"
                  (pi
                   (arg (arg-info visible relevant)
                    (var 8
                     (arg (arg-info visible relevant) (var 10 []) ∷
                      arg (arg-info visible relevant) (var 9 []) ∷ [])))
                   (abs "_"
                    (var 9
                     (arg (arg-info visible relevant) (var 11 []) ∷
                      arg (arg-info visible relevant) (var 10 []) ∷
                      []))))))))))))))))))))
  ∷
  arg (arg-info visible relevant)
  (pi (arg (arg-info visible relevant) (var 2 []))
   (abs "_"
    (pi (arg (arg-info visible relevant) (var 3 []))
     (abs "_" (agda-sort (lit 0))))))
  ∷
  arg (arg-info visible relevant) (var 1 []) ∷
  arg (arg-info visible relevant) (var 0 []) ∷
  arg (arg-info visible relevant) (agda-sort (lit 0)) ∷ []

test-foo : List (Arg Term × Nat)
test-foo =
  (arg (arg-info visible relevant) (agda-sort (lit 0)) , 0) ∷
  (arg (arg-info visible relevant) (var 3 []) , 0) ∷
  (arg (arg-info visible relevant) (var 4 []) , 0) ∷
  (arg (arg-info visible relevant)
   (pi (arg (arg-info visible relevant) (var 5 []))
    (abs "_"
     (pi (arg (arg-info visible relevant) (var 6 []))
      (abs "_" (agda-sort (lit 0))))))
   , 0)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 3
      (arg (arg-info visible relevant) (var 5 []) ∷
       arg (arg-info visible relevant) (var 4 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 4
        (arg (arg-info visible relevant) (var 6 []) ∷
         arg (arg-info visible relevant) (var 5 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 5
          (arg (arg-info visible relevant) (var 7 []) ∷
           arg (arg-info visible relevant) (var 6 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 6
            (arg (arg-info visible relevant) (var 8 []) ∷
             arg (arg-info visible relevant) (var 7 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 7
              (arg (arg-info visible relevant) (var 9 []) ∷
               arg (arg-info visible relevant) (var 8 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 8
                (arg (arg-info visible relevant) (var 10 []) ∷
                 arg (arg-info visible relevant) (var 9 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 9
                  (arg (arg-info visible relevant) (var 11 []) ∷
                   arg (arg-info visible relevant) (var 10 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 10
                    (arg (arg-info visible relevant) (var 12 []) ∷
                     arg (arg-info visible relevant) (var 11 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 11
                      (arg (arg-info visible relevant) (var 13 []) ∷
                       arg (arg-info visible relevant) (var 12 []) ∷ [])))
                    (abs "_"
                     (var 12
                      (arg (arg-info visible relevant) (var 14 []) ∷
                       arg (arg-info visible relevant) (var 13 []) ∷
                       []))))))))))))))))))))
   , 0)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 4
      (arg (arg-info visible relevant) (var 6 []) ∷
       arg (arg-info visible relevant) (var 5 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 5
        (arg (arg-info visible relevant) (var 7 []) ∷
         arg (arg-info visible relevant) (var 6 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 6
          (arg (arg-info visible relevant) (var 8 []) ∷
           arg (arg-info visible relevant) (var 7 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 7
            (arg (arg-info visible relevant) (var 9 []) ∷
             arg (arg-info visible relevant) (var 8 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 8
              (arg (arg-info visible relevant) (var 10 []) ∷
               arg (arg-info visible relevant) (var 9 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 9
                (arg (arg-info visible relevant) (var 11 []) ∷
                 arg (arg-info visible relevant) (var 10 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 10
                  (arg (arg-info visible relevant) (var 12 []) ∷
                   arg (arg-info visible relevant) (var 11 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 11
                    (arg (arg-info visible relevant) (var 13 []) ∷
                     arg (arg-info visible relevant) (var 12 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 12
                      (arg (arg-info visible relevant) (var 14 []) ∷
                       arg (arg-info visible relevant) (var 13 []) ∷ [])))
                    (abs "_"
                     (var 13
                      (arg (arg-info visible relevant) (var 15 []) ∷
                       arg (arg-info visible relevant) (var 14 []) ∷
                       []))))))))))))))))))))
   , 0)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 5
      (arg (arg-info visible relevant) (var 7 []) ∷
       arg (arg-info visible relevant) (var 6 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 6
        (arg (arg-info visible relevant) (var 8 []) ∷
         arg (arg-info visible relevant) (var 7 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 7
          (arg (arg-info visible relevant) (var 9 []) ∷
           arg (arg-info visible relevant) (var 8 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 8
            (arg (arg-info visible relevant) (var 10 []) ∷
             arg (arg-info visible relevant) (var 9 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 9
              (arg (arg-info visible relevant) (var 11 []) ∷
               arg (arg-info visible relevant) (var 10 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 10
                (arg (arg-info visible relevant) (var 12 []) ∷
                 arg (arg-info visible relevant) (var 11 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 11
                  (arg (arg-info visible relevant) (var 13 []) ∷
                   arg (arg-info visible relevant) (var 12 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 12
                    (arg (arg-info visible relevant) (var 14 []) ∷
                     arg (arg-info visible relevant) (var 13 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 13
                      (arg (arg-info visible relevant) (var 15 []) ∷
                       arg (arg-info visible relevant) (var 14 []) ∷ [])))
                    (abs "_"
                     (var 14
                      (arg (arg-info visible relevant) (var 16 []) ∷
                       arg (arg-info visible relevant) (var 15 []) ∷
                       []))))))))))))))))))))
   , 0)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 6
      (arg (arg-info visible relevant) (var 8 []) ∷
       arg (arg-info visible relevant) (var 7 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 7
        (arg (arg-info visible relevant) (var 9 []) ∷
         arg (arg-info visible relevant) (var 8 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 8
          (arg (arg-info visible relevant) (var 10 []) ∷
           arg (arg-info visible relevant) (var 9 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 9
            (arg (arg-info visible relevant) (var 11 []) ∷
             arg (arg-info visible relevant) (var 10 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 10
              (arg (arg-info visible relevant) (var 12 []) ∷
               arg (arg-info visible relevant) (var 11 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 11
                (arg (arg-info visible relevant) (var 13 []) ∷
                 arg (arg-info visible relevant) (var 12 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 12
                  (arg (arg-info visible relevant) (var 14 []) ∷
                   arg (arg-info visible relevant) (var 13 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 13
                    (arg (arg-info visible relevant) (var 15 []) ∷
                     arg (arg-info visible relevant) (var 14 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 14
                      (arg (arg-info visible relevant) (var 16 []) ∷
                       arg (arg-info visible relevant) (var 15 []) ∷ [])))
                    (abs "_"
                     (var 15
                      (arg (arg-info visible relevant) (var 17 []) ∷
                       arg (arg-info visible relevant) (var 16 []) ∷
                       []))))))))))))))))))))
   , 0)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 7
      (arg (arg-info visible relevant) (var 9 []) ∷
       arg (arg-info visible relevant) (var 8 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 8
        (arg (arg-info visible relevant) (var 10 []) ∷
         arg (arg-info visible relevant) (var 9 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 9
          (arg (arg-info visible relevant) (var 11 []) ∷
           arg (arg-info visible relevant) (var 10 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 10
            (arg (arg-info visible relevant) (var 12 []) ∷
             arg (arg-info visible relevant) (var 11 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 11
              (arg (arg-info visible relevant) (var 13 []) ∷
               arg (arg-info visible relevant) (var 12 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 12
                (arg (arg-info visible relevant) (var 14 []) ∷
                 arg (arg-info visible relevant) (var 13 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 13
                  (arg (arg-info visible relevant) (var 15 []) ∷
                   arg (arg-info visible relevant) (var 14 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 14
                    (arg (arg-info visible relevant) (var 16 []) ∷
                     arg (arg-info visible relevant) (var 15 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 15
                      (arg (arg-info visible relevant) (var 17 []) ∷
                       arg (arg-info visible relevant) (var 16 []) ∷ [])))
                    (abs "_"
                     (var 16
                      (arg (arg-info visible relevant) (var 18 []) ∷
                       arg (arg-info visible relevant) (var 17 []) ∷
                       []))))))))))))))))))))
   , 0)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 8
      (arg (arg-info visible relevant) (var 10 []) ∷
       arg (arg-info visible relevant) (var 9 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 9
        (arg (arg-info visible relevant) (var 11 []) ∷
         arg (arg-info visible relevant) (var 10 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 10
          (arg (arg-info visible relevant) (var 12 []) ∷
           arg (arg-info visible relevant) (var 11 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 11
            (arg (arg-info visible relevant) (var 13 []) ∷
             arg (arg-info visible relevant) (var 12 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 12
              (arg (arg-info visible relevant) (var 14 []) ∷
               arg (arg-info visible relevant) (var 13 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 13
                (arg (arg-info visible relevant) (var 15 []) ∷
                 arg (arg-info visible relevant) (var 14 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 14
                  (arg (arg-info visible relevant) (var 16 []) ∷
                   arg (arg-info visible relevant) (var 15 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 15
                    (arg (arg-info visible relevant) (var 17 []) ∷
                     arg (arg-info visible relevant) (var 16 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 16
                      (arg (arg-info visible relevant) (var 18 []) ∷
                       arg (arg-info visible relevant) (var 17 []) ∷ [])))
                    (abs "_"
                     (var 17
                      (arg (arg-info visible relevant) (var 19 []) ∷
                       arg (arg-info visible relevant) (var 18 []) ∷
                       []))))))))))))))))))))
   , 0)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 9
      (arg (arg-info visible relevant) (var 11 []) ∷
       arg (arg-info visible relevant) (var 10 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 10
        (arg (arg-info visible relevant) (var 12 []) ∷
         arg (arg-info visible relevant) (var 11 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 11
          (arg (arg-info visible relevant) (var 13 []) ∷
           arg (arg-info visible relevant) (var 12 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 12
            (arg (arg-info visible relevant) (var 14 []) ∷
             arg (arg-info visible relevant) (var 13 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 13
              (arg (arg-info visible relevant) (var 15 []) ∷
               arg (arg-info visible relevant) (var 14 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 14
                (arg (arg-info visible relevant) (var 16 []) ∷
                 arg (arg-info visible relevant) (var 15 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 15
                  (arg (arg-info visible relevant) (var 17 []) ∷
                   arg (arg-info visible relevant) (var 16 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 16
                    (arg (arg-info visible relevant) (var 18 []) ∷
                     arg (arg-info visible relevant) (var 17 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 17
                      (arg (arg-info visible relevant) (var 19 []) ∷
                       arg (arg-info visible relevant) (var 18 []) ∷ [])))
                    (abs "_"
                     (var 18
                      (arg (arg-info visible relevant) (var 20 []) ∷
                       arg (arg-info visible relevant) (var 19 []) ∷
                       []))))))))))))))))))))
   , 0)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 10
      (arg (arg-info visible relevant) (var 12 []) ∷
       arg (arg-info visible relevant) (var 11 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 11
        (arg (arg-info visible relevant) (var 13 []) ∷
         arg (arg-info visible relevant) (var 12 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 12
          (arg (arg-info visible relevant) (var 14 []) ∷
           arg (arg-info visible relevant) (var 13 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 13
            (arg (arg-info visible relevant) (var 15 []) ∷
             arg (arg-info visible relevant) (var 14 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 14
              (arg (arg-info visible relevant) (var 16 []) ∷
               arg (arg-info visible relevant) (var 15 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 15
                (arg (arg-info visible relevant) (var 17 []) ∷
                 arg (arg-info visible relevant) (var 16 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 16
                  (arg (arg-info visible relevant) (var 18 []) ∷
                   arg (arg-info visible relevant) (var 17 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 17
                    (arg (arg-info visible relevant) (var 19 []) ∷
                     arg (arg-info visible relevant) (var 18 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 18
                      (arg (arg-info visible relevant) (var 20 []) ∷
                       arg (arg-info visible relevant) (var 19 []) ∷ [])))
                    (abs "_"
                     (var 19
                      (arg (arg-info visible relevant) (var 21 []) ∷
                       arg (arg-info visible relevant) (var 20 []) ∷
                       []))))))))))))))))))))
   , 0)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 11
      (arg (arg-info visible relevant) (var 13 []) ∷
       arg (arg-info visible relevant) (var 12 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 12
        (arg (arg-info visible relevant) (var 14 []) ∷
         arg (arg-info visible relevant) (var 13 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 13
          (arg (arg-info visible relevant) (var 15 []) ∷
           arg (arg-info visible relevant) (var 14 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 14
            (arg (arg-info visible relevant) (var 16 []) ∷
             arg (arg-info visible relevant) (var 15 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 15
              (arg (arg-info visible relevant) (var 17 []) ∷
               arg (arg-info visible relevant) (var 16 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 16
                (arg (arg-info visible relevant) (var 18 []) ∷
                 arg (arg-info visible relevant) (var 17 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 17
                  (arg (arg-info visible relevant) (var 19 []) ∷
                   arg (arg-info visible relevant) (var 18 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 18
                    (arg (arg-info visible relevant) (var 20 []) ∷
                     arg (arg-info visible relevant) (var 19 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 19
                      (arg (arg-info visible relevant) (var 21 []) ∷
                       arg (arg-info visible relevant) (var 20 []) ∷ [])))
                    (abs "_"
                     (var 20
                      (arg (arg-info visible relevant) (var 22 []) ∷
                       arg (arg-info visible relevant) (var 21 []) ∷
                       []))))))))))))))))))))
   , 0)
  ∷
  (arg (arg-info visible relevant)
   (pi
    (arg (arg-info visible relevant)
     (var 12
      (arg (arg-info visible relevant) (var 14 []) ∷
       arg (arg-info visible relevant) (var 13 []) ∷ [])))
    (abs "_"
     (pi
      (arg (arg-info visible relevant)
       (var 13
        (arg (arg-info visible relevant) (var 15 []) ∷
         arg (arg-info visible relevant) (var 14 []) ∷ [])))
      (abs "_"
       (pi
        (arg (arg-info visible relevant)
         (var 14
          (arg (arg-info visible relevant) (var 16 []) ∷
           arg (arg-info visible relevant) (var 15 []) ∷ [])))
        (abs "_"
         (pi
          (arg (arg-info visible relevant)
           (var 15
            (arg (arg-info visible relevant) (var 17 []) ∷
             arg (arg-info visible relevant) (var 16 []) ∷ [])))
          (abs "_"
           (pi
            (arg (arg-info visible relevant)
             (var 16
              (arg (arg-info visible relevant) (var 18 []) ∷
               arg (arg-info visible relevant) (var 17 []) ∷ [])))
            (abs "_"
             (pi
              (arg (arg-info visible relevant)
               (var 17
                (arg (arg-info visible relevant) (var 19 []) ∷
                 arg (arg-info visible relevant) (var 18 []) ∷ [])))
              (abs "_"
               (pi
                (arg (arg-info visible relevant)
                 (var 18
                  (arg (arg-info visible relevant) (var 20 []) ∷
                   arg (arg-info visible relevant) (var 19 []) ∷ [])))
                (abs "_"
                 (pi
                  (arg (arg-info visible relevant)
                   (var 19
                    (arg (arg-info visible relevant) (var 21 []) ∷
                     arg (arg-info visible relevant) (var 20 []) ∷ [])))
                  (abs "_"
                   (pi
                    (arg (arg-info visible relevant)
                     (var 20
                      (arg (arg-info visible relevant) (var 22 []) ∷
                       arg (arg-info visible relevant) (var 21 []) ∷ [])))
                    (abs "_"
                     (var 21
                      (arg (arg-info visible relevant) (var 23 []) ∷
                       arg (arg-info visible relevant) (var 22 []) ∷
                       []))))))))))))))))))))
   , 0)
  ∷
  (arg (arg-info visible relevant)
   (def (quote _≡_)
    (arg (arg-info hidden relevant) (def (quote lzero) []) ∷
     arg (arg-info hidden relevant) (var 16 []) ∷
     arg (arg-info visible relevant) (var 15 []) ∷
     arg (arg-info visible relevant) (var 14 []) ∷ []))
   , 0)
  ∷ []

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

before-operation : List (Arg Type) → List (Arg Type × Nat)
before-operation [] = []
before-operation (γ ∷ γs) =
  (weaken 1 (weaken 1 (weaken 1 γ)) , 0) ∷ before-operation γs

getRequest : List (Arg Type)
getRequest =
  case ListArgTermμ the-Γ of λ { (getμ Γ) →
  Γ }

record Response : Set where
  field
    Γ[w/L]×indexes[Γ] : List (Arg Type × Nat)
    ∣Γ∣ : Nat

  after-operation : List Nat
  after-operation = (λ { (γ[w/L] , index[γ]) → ∣Γ∣ - index[γ] }) <$> Γ[w/L]×indexes[Γ]

Responseμ : (r : Response) → Mem r
Responseμ record { Γ[w/L]×indexes[Γ] = Γ[w/L]×indexes[Γ] ; ∣Γ∣ = ∣Γ∣ } = putμ refl

getResponse-reg : List (Arg Type) → Response
getResponse-reg q =
  case length q                                of λ   { ∣Γ∣ →
  case Natμ ∣Γ∣                                of λ   { (getμ ∣Γ∣) →
  case before-operation q                      of λ   { Γ[w/L]×indexes[Γ] →
  case ListArgTerm×Natμ Γ[w/L]×indexes[Γ]      of λ   { (getμ Γ[w/L]×indexes[Γ]) →
     record
     { Γ[w/L]×indexes[Γ] = Γ[w/L]×indexes[Γ]
     ; ∣Γ∣ = ∣Γ∣ } }}}}

getResponse-foo : List (Arg Type) → Response
getResponse-foo q =
  case length q                                of λ   { ∣Γ∣ →
  case Natμ ∣Γ∣                                of λ   { (getμ ∣Γ∣) →
  case test-foo                                of λ   { Γ[w/L]×indexes[Γ] →
  case ListArgTerm×Natμ Γ[w/L]×indexes[Γ]      of λ   { (getμ Γ[w/L]×indexes[Γ]) →
     record
     { Γ[w/L]×indexes[Γ] = Γ[w/L]×indexes[Γ]
     ; ∣Γ∣ = ∣Γ∣ } }}}}

macro
  reright-debug-show-before : Tactic
  reright-debug-show-before hole =
    case Responseμ (getResponse-reg getRequest) of λ { (getμ r) →
    let open Response r in
    typeError ( strErr "reright-debug"            ∷ termErr (` (Γ[w/L]×indexes[Γ]))                 ∷
                [] ) }

pure-reg-after : List Nat
pure-reg-after =
  case getRequest of λ { q →
  case Responseμ (getResponse-reg q) of λ { (getμ r) →
  let open Response r in
  after-operation } }

pure-reg-before : Nat
pure-reg-before =
  case getRequest of λ { q →
  case Responseμ (getResponse-reg q) of λ { (getμ r) →
  let open Response r in
  size-ListArgTermNat Γ[w/L]×indexes[Γ] } }

pure-foo-after : List Nat
pure-foo-after =
  case getRequest of λ { q →
  case Responseμ (getResponse-foo q) of λ { (getμ r) →
  let open Response r in
  after-operation } }

pure-foo-before : Nat
pure-foo-before =
  case getRequest of λ { q →
  case Responseμ (getResponse-foo q) of λ { (getμ r) →
  let open Response r in
  size-ListArgTermNat Γ[w/L]×indexes[Γ] } }

--benchmark-pure-foo-before : Nat
--benchmark-pure-foo-before = unquote (λ hole → unify hole (` pure-foo-before))

--benchmark-pure-foo-after : List Nat
--benchmark-pure-foo-after = unquote (λ hole → unify hole (` pure-foo-after))

--benchmark-pure-reg-before : Nat
--benchmark-pure-reg-before = unquote (λ hole → unify hole (` pure-reg-before))

--benchmark-pure-reg-after : List Nat
--benchmark-pure-reg-after = unquote (λ hole → unify hole (` pure-reg-after))

foo : Set × Set × Set × Set
foo = {!pure-foo-before!} ,
      {!pure-foo-after!} ,
      {!pure-reg-before!} ,
      {!pure-reg-after!}

      -- using full Natμ
      -- Typing.CheckRHS
      -- reright-debug-reg-after               11,869ms
      -- reright-debug-reg-before              2,796ms
      -- reright-debug-foo-before              1,746ms
      -- reright-debug-foo-after               2,240ms

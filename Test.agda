module Test where

open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Tactics.Nat.Semiring using (solve-goal)

shuffle-test : (a b : ℕ) → a + b + 1 ≡ b + (a + 1)
shuffle-test a b = quoteGoal g in (unquote (solve-goal g))

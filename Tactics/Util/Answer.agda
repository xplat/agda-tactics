{-# OPTIONS --universe-polymorphism #-}
module Tactics.Util.Answer where

open import Function using (Fun₁; _∘_; _∘′_; flip)
open import Data.String using (String)
open import Data.List using (List; map)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Category.Functor using (RawFunctor; module RawFunctor)
open import Category.Applicative using (RawApplicative; module RawApplicative)
open import Category.Monad using (RawMonad; module RawMonad)
open import Reflection

-- for the user's information when something goes wrong
data Obstruction : Set where
  term : Term → Obstruction
  arg : Arg Term → Obstruction
  el-arg : Arg Type → Obstruction
  el : Type → Obstruction
  sort : Sort → Obstruction

data Answer {a} (A : Set a) : Set a where
  ok : (r : A) → Answer A
  ko : (msg : String) → (os : List Obstruction) → Answer A

RawIsOK : ∀ {a} {A : Set a} (ans : Answer A) → Set
RawIsOK (ok r) = ⊤
RawIsOK _ = ⊥

record IsOK {a} {A : Set a} (ans : Answer A) : Set a where
  constructor isOK
  field cheap&easy : RawIsOK ans
  witness : A
  witness with ans | cheap&easy
  witness | ok r | _ = r
  witness | ko _ _ | ()

mapA : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Answer A → Answer B
mapA f (ok x) = ok (f x)
mapA f (ko msg os) = ko msg os

_>>=_ : ∀ {a b} {A : Set a} {B : Set b} → Answer A → (A → Answer B) → Answer B
(ok x) >>= f = f x
(ko msg os) >>= f = ko msg os

-- XXX should this be the order of effects?
infixl 10 _⊛_
_⊛_ : ∀ {a b} {A : Set a} {B : Set b} → Answer (A → B) → Answer A → Answer B
(ok f) ⊛ (ok x) = ok (f x)
(ok f) ⊛ (ko msg os) = ko msg os
(ko msg os) ⊛ _ = ko msg os

AnswerT : ∀ {ℓ} → Fun₁ (Fun₁ (Set ℓ))
AnswerT = flip _∘′_ Answer

AnswerTFunctor : ∀ {ℓ} {F : Fun₁ (Set ℓ)} → RawFunctor F → RawFunctor (AnswerT F)
AnswerTFunctor Fun = record { _<$>_ = (RawFunctor._<$>_ Fun) ∘ mapA }

AnswerTApplicative : ∀ {ℓ} {F : Fun₁ (Set ℓ)} → RawApplicative F → RawApplicative (AnswerT F)
AnswerTApplicative App = record
  { pure = RawApplicative.pure App ∘ ok
  ; _⊛_ = RawApplicative._⊛_ App ∘ RawFunctor._<$>_ (RawApplicative.rawFunctor App) _⊛_
  }

AnswerTMonad : ∀ {ℓ} {M : Fun₁ (Set ℓ)} → RawMonad M → RawMonad (AnswerT M)
AnswerTMonad {ℓ} {M} Mon = record
  { return = returnM ∘ ok
  ; _>>=_ = λ m k → m >>=M (λ { (ok r) → k r
                              ; (ko msg os) → returnM (ko msg os)})
  }
  where
  open RawMonad Mon using () renaming (_>>=_ to _>>=M_; return to returnM)

module AnswerTKit {ℓ} {M : Fun₁ (Set ℓ)} (Mon : RawMonad M) where
  AnswerM = AnswerT M

  private module Monad = RawMonad (AnswerTMonad Mon)
  open Monad public using (_>>=_)

  private module Applicative = RawApplicative (AnswerTApplicative (RawMonad.rawIApplicative Mon))
  open Applicative public using (_⊛_) renaming (pure to pureA)

  private module Functor = RawFunctor (AnswerTFunctor (RawApplicative.rawFunctor (RawMonad.rawIApplicative Mon)))
  open Functor public using () renaming (_<$>_ to mapA)

  open RawMonad Mon public using () renaming (return to A^_)

  -- convenience
  tko : ∀ {A : Set ℓ} msg → (os : List Term) → AnswerT M A
  tko msg os = A^ ko msg (map term os)
  ako : ∀ {A : Set ℓ} msg → (os : List (Arg Term)) → AnswerT M A
  ako msg os = A^ ko msg (map arg os)
  pko : ∀ {A : Set ℓ} msg → (os : List (Arg Type)) → AnswerT M A
  pko msg os = A^ ko msg (map el-arg os)
  eko : ∀ {A : Set ℓ} msg → (os : List Type) → AnswerT M A
  eko msg os = A^ ko msg (map el os)
  sko : ∀ {A : Set ℓ} msg → (os : List Sort) → AnswerT M A
  sko msg os = A^ ko msg (map sort os)

-- convenience
tko : ∀ {a} {A : Set a} msg → (os : List Term) → Answer A
tko msg os = ko msg (map term os)
ako : ∀ {a} {A : Set a} msg → (os : List (Arg Term)) → Answer A
ako msg os = ko msg (map arg os)
pko : ∀ {a} {A : Set a} msg → (os : List (Arg Type)) → Answer A
pko msg os = ko msg (map el-arg os)
eko : ∀ {a} {A : Set a} msg → (os : List Type) → Answer A
eko msg os = ko msg (map el os)
sko : ∀ {a} {A : Set a} msg → (os : List Sort) → Answer A
sko msg os = ko msg (map sort os)

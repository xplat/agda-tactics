{-# OPTIONS --universe-polymorphism #-}
module Tactics.Nat.Semiring where

-- SECTION : importing the entire standard library and then some

open import Function using (id; _∘_; type-signature; flip)
open import Data.Nat using (_+_; _*_; ℕ; zero; suc; _≤_; _⊔_; decTotalOrder) renaming (_≟_ to _≟-ℕ_)
open import Data.Nat.Properties using (module SemiringSolver; m≤m⊔n; ⊔-⊓-0-isCommutativeSemiringWithoutOne)
open import Algebra.Structures using (module IsCommutativeSemiringWithoutOne)
import Algebra.RingSolver as RSg
open import Relation.Binary.PropositionalEquality
open import Relation.Binary using (module DecTotalOrder; Decidable)
open import Data.Fin using (Fin; fromℕ; fromℕ≤; inject₁)
open import Data.Vec using (_∷_; []; Vec; _[_]=_; here; there; reverse)
open import Data.List using (_∷_; []; List; gfilter; [_]) renaming (map to mapL)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥-elim)
import Relation.Nullary.Decidable as Dec
open import Reflection
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; uncurry; ∃; proj₁; proj₂; ,_; Σ) renaming (map to mapΣ)
open import Data.Vec.N-ary using (N-ary-level; curryⁿ; Eqʰ; Eqʰ-to-Eq; uncurry-∀ⁿ; _$ⁿ_; left-inverse)
open import Function.Equivalence using (module Equivalence)
open import Function.Equality using (_⟨$⟩_)

open import Data.String using (String)
open import Category.Monad.State

open import Tactics.Util.Answer as Ans using (Answer; AnswerT; module AnswerTKit; ko; IsOK)

KnownClumps = ∃ (Vec Term)
open AnswerTKit (StateMonad KnownClumps)

open SemiringSolver
open DecTotalOrder decTotalOrder using () renaming (trans to ≤-trans)

q+ = quote _+_
q≡ = quote _≡_
q* = quote _*_
qN = quote ℕ
qS = quote suc
qZ = quote zero

-- SECTION : Building polynomials and equations

record OpenPolynomial : Set where
  field
    bound : ℕ
    close : ∀ n → (bound ≤ n) → Polynomial n

private
  -- XXX why isn't this in Data.Nat.Properties?
  n≤m⊔n : ∀ m n → n ≤ m ⊔ n
  n≤m⊔n m n = subst (_≤_ n) (+-comm _ m) (m≤m⊔n _ _)
    where
    open IsCommutativeSemiringWithoutOne ⊔-⊓-0-isCommutativeSemiringWithoutOne

_o+_ : OpenPolynomial → OpenPolynomial → OpenPolynomial
f o+ g = record
  { bound = bound f ⊔ bound g
  ; close = λ n high → close f n (≤-trans (m≤m⊔n (bound f) (bound g)) high)
                    :+ close g n (≤-trans (n≤m⊔n (bound f) (bound g)) high)
  }
  where open OpenPolynomial

_o*_ : OpenPolynomial → OpenPolynomial → OpenPolynomial
f o* g = record
  { bound = bound f ⊔ bound g
  ; close = λ n high → close f n (≤-trans (m≤m⊔n (bound f) (bound g)) high)
                    :* close g n (≤-trans (n≤m⊔n (bound f) (bound g)) high)
  }
  where open OpenPolynomial

ocon : ℕ → OpenPolynomial
ocon n = record { bound = 0; close = λ _ _ → con n }

ovar : ℕ → OpenPolynomial
ovar n = record { bound = suc n; close = λ _ high → var (fromℕ≤ high) }

record ClosedEquation : Set where
  field
    depth : ℕ
    lhs : Polynomial depth
    rhs : Polynomial depth
    env : Vec Term depth

record OpenEquation : Set where
  constructor _o≡_
  field
    lhs rhs : OpenPolynomial

  private module l = OpenPolynomial lhs
  private module r = OpenPolynomial rhs

  bound = l.bound ⊔ r.bound

  close : KnownClumps → Answer ClosedEquation
  close (n , e) with n ≟-ℕ bound
  close (n , e) | no _ = Ans.ko "INCONCEIVABLE: variable numbering mismatch" []
  close (.bound , e) | yes refl = Ans.ok (record
    { depth = bound
    ; lhs = l.close bound (m≤m⊔n l.bound r.bound)
    ; rhs = r.close bound (n≤m⊔n l.bound r.bound)
    ; env = reverse e
    })

-- SECTION : helpers for Fin and Vec

private
  push : ∀ {a} {A : Set a} (_=?_ : Decidable (_≡_ {A = A})) → 
       ∀ {n} {x q} {xs : Vec A n} → (q ≢ x)
       → Σ[ i ∶ Fin (suc n) ] (x ∷ xs [ i ]= q)
       → Σ[ i ∶ Fin n ] (xs [ i ]= q)
  push _=?_ ne (._        , here) = ⊥-elim (ne refl)
  push _=?_ ne (Fin.suc i , there xs[i]=x) = i , xs[i]=x

locate : ∀ {a} {A : Set a} (_=?_ : Decidable (_≡_ {A = A})) →
         ∀ {n} (xs : Vec A n) → (q : A)  → Dec (Σ[ i ∶ Fin n ] (xs [ i ]= q))
locate _ [] q = no because
  where
  because : ¬ (Σ[ i ∶ Fin zero ] ([] [ i ]= q))
  because (() , _)
locate _=?_ ( x ∷ xs) q with q =? x
locate _=?_ (.q ∷ xs) q | yes refl = yes (Fin.zero , here)
locate _=?_ ( x ∷ xs) q | no ¬p = Dec.map′ (mapΣ Fin.suc there) (push _=?_ ¬p) (locate _=?_ xs q)

complement : ∀ {n} (i : Fin n) → ℕ
complement {suc n} Data.Fin.zero = n
complement (Data.Fin.suc i) = complement i

-- SECTION : Reinterpreting terms as polynomials and equations

explicits : ∀ {X} → List (Arg X) → List X
explicits {X} = gfilter isExplicit
  where
  isExplicit : Arg X → Maybe X
  isExplicit (arg visible r x) = just x
  isExplicit (arg hidden r x) = nothing
  isExplicit (arg instance r x) = nothing

find-var : Term → AnswerM ℕ
find-var t (n , ts) with locate _≟_ ts t
find-var t (n , ts) | yes (i , pf) = Ans.ok (complement i) , n , ts
find-var t (n , ts) | no ¬p = Ans.ok n , suc n , t ∷ ts

carry-in : ℕ → AnswerM OpenPolynomial → AnswerM OpenPolynomial
carry-in zero = id
carry-in (suc k) = mapA (λ x → ocon (suc k) o+ x)

mutual
  two-args : ℕ → List (Arg Term) → AnswerM (OpenPolynomial × OpenPolynomial)
  two-args k [] = tko "no args, need 2" []
  two-args k (arg visible r a ∷ []) = ako "1 arg, need 2" [ arg visible r a ]
  two-args k (arg visible _ a ∷ arg visible _ b ∷ []) = mapA _,_ (interpret-expr k a) ⊛ interpret-expr 0 b
  two-args k as = ako "need 2 args, found something else" as

  interpret-suc' : ℕ → Arg Term → AnswerM OpenPolynomial
  interpret-suc' k (arg visible r x) = interpret-expr (suc k) x
  interpret-suc' k (arg hidden r x) = ako "suc with implicit arg" [ arg hidden r x ]
  interpret-suc' k (arg instance r x) = ako "suc with instance arg" [ arg instance r x ]

  interpret-suc : ℕ → List (Arg Term) → AnswerM OpenPolynomial
  interpret-suc k [] = tko "suc without args" []
  interpret-suc k (x ∷ []) = interpret-suc' k x
  interpret-suc k (x ∷ x' ∷ xs) = ako "suc with two args" (x ∷ x' ∷ xs)

  interpret-expr : ℕ → Term → AnswerM OpenPolynomial
  interpret-expr k (con c args) with c ≟-Name qZ
  interpret-expr k (con c []) | yes p = pureA (ocon k)
  interpret-expr k (con c as) | yes p = tko "zero with args" [ con c as ]
  interpret-expr k (con c args) | no _ with c ≟-Name qS
  interpret-expr k (con c args) | no _ | yes _ = interpret-suc k args
  interpret-expr k (con c args) | no _ | no _ = tko "IMPROBABLE: unknown constructor" [ con c args ]
  interpret-expr k (def f args) with f ≟-Name q+
  interpret-expr k (def f args) | yes _ = mapA (uncurry _o+_) (two-args k args)
  interpret-expr k (def f args) | no _ with f ≟-Name q*
  interpret-expr k (def f args) | no _ | yes _ = carry-in k (mapA (uncurry _o*_) (two-args 0 args))
  interpret-expr k (def f args) | no _ | no _ = carry-in k (mapA ovar (find-var (def f args)))
  interpret-expr k t = carry-in k (mapA ovar (find-var t))


interpret-eq : List Term → AnswerM OpenEquation
interpret-eq [] = A^ ko "no args to ≡" []
interpret-eq (x ∷ []) = tko "one arg to ≡" [ x ]
interpret-eq (x ∷ y ∷ []) = mapA _o≡_ (interpret-expr 0 x) ⊛ interpret-expr 0 y
interpret-eq (x ∷ y ∷ z ∷ ws) = tko "3 or more args to ≡" (x ∷ y ∷ z ∷ ws)

strengthA : ∀ {a b} {A : Set a} {B : Set b} → (Answer A × B) → Answer (A × B)
strengthA (Ans.ok a , b) = Ans.ok (a , b)
strengthA (ko msg os , b) = ko msg os

interpret-top : Term → Answer ClosedEquation
interpret-top (def f args) with f ≟-Name q≡ | explicits args
... | yes p | eargs = flip Ans._>>=_ 
                           (uncurry OpenEquation.close)
                           (strengthA (interpret-eq eargs (, [])))
... | no ¬p | _ = Ans.tko "not an equation" [ def f args ]
interpret-top t = Ans.tko "not an equation" [ t ]

-- SECTION : quoting things by hand

quote-ℕ : ℕ → Term
quote-ℕ zero = con qZ []
quote-ℕ (suc n) = con qS (arg visible relevant (quote-ℕ n) ∷ [])

quote-Vec : ∀ {a} {A : Set a} → (A → Term) → ∀ {n} → Vec A n → Term
quote-Vec {A = A} quote-A = body
  where
  body : ∀ {n} → Vec A n → Term
  body [] = con (quote Vec.[]) []
  body (_∷_ {n = n} x xs)
    = con (quote Vec._∷_) ( arg hidden  relevant (quote-ℕ n)
                          ∷ arg visible relevant (quote-A x)
                          ∷ arg visible relevant (body xs)
                          ∷ [])

quote-Fin : ∀ {n} → Fin n → Term
quote-Fin (Fin.zero {n}) = con (quote Fin.zero)
                               [ arg hidden relevant (quote-ℕ n) ]
quote-Fin (Fin.suc {n} i) = con (quote Fin.suc)
                                (arg hidden  relevant (quote-ℕ n) ∷
                                 arg visible relevant (quote-Fin i) ∷ [])

quote-Polynomial : ∀ {n} → Polynomial n → Term
quote-Polynomial {n} = run
  where
  infix 10 ‼_
  ‼_ = arg visible relevant
  c[+] = Term.con (quote RSg.[+]) []
  c[*] = Term.con (quote RSg.[*]) []
  c-op = λ o → Term.con (quote RSg.op) ∘ mapL (‼_) ∘ (_∷_ o)
  c-con = Term.con (quote RSg.Polynomial.con)
  c-var = Term.con (quote RSg.var)
  c:^ = Term.con (quote RSg._:^_)
  c:- = Term.con (quote RSg.:-_)

  run : Polynomial n → Term
  run (op [+] p₁ p₂) = c-op c[+] (run p₁ ∷ run p₂ ∷ [])
  run (op [*] p₁ p₂) = c-op c[*] (run p₁ ∷ run p₂ ∷ [])
  run (con c) = c-con [ ‼ quote-ℕ c ]
  run (var x) = c-var [ ‼ quote-Fin x ]
  run (_:^_ p i) = c:^ (‼ run p ∷ ‼ quote-ℕ i ∷ [])
  run (:-_ p) = c:- [ ‼ run p ]

quote-prove : ClosedEquation → Term
quote-prove eqn = def (quote prove)
                      (arg hidden  relevant (quote-ℕ depth) ∷
                       arg visible relevant (quote-Vec id env) ∷
                       arg visible relevant (quote-Polynomial lhs) ∷
                       arg visible relevant (quote-Polynomial rhs) ∷
                       arg visible relevant (con (quote refl) []) ∷
                       [])
  where open ClosedEquation eqn

-- SECTION : public API

solve-goal : (g : Term) {apt : IsOK (interpret-top g)} → Term
solve-goal _ {apt} = quote-prove eqn
  where eqn = IsOK.witness apt

-- SECTION : tests

shuffle-test : (a b c : ℕ) → a + b + 2 + c + b ≡ 1 + b * 2 + (c + a) + 1
shuffle-test a b c = quoteGoal g in (unquote (solve-goal g))
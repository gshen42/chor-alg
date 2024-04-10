open import AlgEff
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)

module Choreography.Choreo
  (Loc : Set) (_≟_ : (l l′ : Loc) → Dec (l ≡ l′))
  (𝕃 : Sig)
  where

open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Effectful renaming (monad to maybe-monad)
open import Data.Product using (_,_)
open import Effect.Monad using (RawMonad)
open import Function using (_∘_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

import Choreography.Process
open module Process = Choreography.Process Loc 𝕃 hiding (Op; Arity)

import Choreography.Network
open module Network = Choreography.Network Loc _≟_ 𝕃

open RawMonad ⦃...⦄

infix 20 _▷_
infix 20 _⇨_◇_

private
  variable
    ℓ     : Level
    A B   : Set
    a     : A
    l s r : Loc

----------------------------------------------------------------------
-- Located values

_＠_ : Set ℓ → Loc → Set ℓ
A ＠ l = Maybe A

instance
  ＠-monad : RawMonad {ℓ} (_＠ l)
  ＠-monad = maybe-monad

----------------------------------------------------------------------
-- Choreographies

data Op : Set₁ where
  `comm : (s r : Loc) → (Term 𝕃 A) ＠ s → Op

Arity : Op → Set _
Arity (`comm {A} _ r _) = A ＠ r

ℂ : Sig
ℂ = Op ◁ Arity

----------------------------------------------------------------------
-- Help functions

ℂhoreo : Set → Set _
ℂhoreo A = Term ℂ A

-- Local computations
-- use `\Tw` to type `▷`

_▷_ :  (s : Loc) → (Term 𝕃 A) ＠ s → Term ℂ (A ＠ s)
s ▷ t = perform (`comm s s t)

-- Communication
-- use `\r` to type `⇨`
-- use `\di` to type `◇`

_⇨_◇_ :  (s r : Loc) → (Term 𝕃 A) ＠ s → Term ℂ (A ＠ r)
s ⇨ r ◇ t = perform (`comm s r t)

----------------------------------------------------------------------
--

private
  variable
    n     : Network A
    t     : Term 𝕃 A
    k     : Maybe A → ℂhoreo B
    k′ k″ : A → ℙrocess B
    c     : ℂhoreo A

data _~_ {A} : ℂhoreo A → Network A → Set₁ where

  done : var a ~ (\_ → var a)

  step-▷-just : n l ≡ op (`locally t , k′) →
                k (just (𝕃-handler t)) ~ update l (k′ (𝕃-handler t)) n →
                op (`comm l l (just t) , k) ~ n

  step-▷-nothing : k nothing ~ n →
                   op (`comm l l nothing , k) ~ n

  step-⇨-just : s ≢ r →
                n s ≡ op (`send r t , k′) →
                n r ≡ op (`recv s , k″) →
                k (just (𝕃-handler t)) ~ update s (k′ tt) (update r (k″ (𝕃-handler t)) n) →
                op (`comm s r (just t) , k) ~ n

  step-⇨-nothing : s ≢ r →
                   k nothing ~ n →
                   op (`comm s r nothing , k) ~ n

foo : c ~ n → n ✓
foo done = ✓-done λ _ → _ , refl
foo (step-▷-just {l = l} x t) = ✓-step (local⇒ⁿ x) (foo t)
foo (step-▷-nothing t) = foo t
foo (step-⇨-just x y z t) = ✓-step (comm⇒ⁿ y z) (foo t)
foo (step-⇨-nothing x t) = foo t

----------------------------------------------------------------------
-- Endpoint projection

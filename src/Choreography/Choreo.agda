open import AlgEff
open import Level using (Level)

-- Parameterize all definitions over a signature `𝕃` that specifies
-- what local computation a process can do

module Choreography.Choreo {ℓ₁ ℓ₂ : Level} (𝕃 : Sig  ℓ₁ ℓ₂) where

open import Choreography.Loc
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_,_)
open import Effect.Monad using (RawMonad)
open import Effect.Monad.MyStuff using (mkRawMonad)
open import Function using (_∘_)
open import Level using (_⊔_; suc; Setω)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

private
  variable
    ℓ ℓ′  : Level
    A B   : Set
    l s r : Loc

----------------------------------------------------------------------
-- An general interface for _＠_

At : Setω
At = ∀ {ℓ} → Set ℓ → Loc → Set ℓ

module _ {_＠_ : At} where

----------------------------------------------------------------------
-- Signature

  data Op : Set (suc (ℓ₁ ⊔ ℓ₂)) where
    `comm : (s r : Loc) → (Term 𝕃 A) ＠ s → Op

  Arity : Op → Set _
  Arity (`comm {A} _ r _) = A ＠ r

  ℂ : Sig _ _
  ℂ = Op ◁ Arity

--------------------------------------------------------------------
-- Shorthands

  infix 20 _▷_
  infix 20 _⇨_◇_

  -- use `\Tw` to type `▷`

  _▷_ : (s : Loc) → (Term 𝕃 A) ＠ s → Term ℂ (A ＠ s)
  s ▷ t = perform (`comm s s t)

  -- use `\r` to type `⇨`
  -- use `\di` to type `◇`

  _⇨_◇_ : (s r : Loc) → (Term 𝕃 A) ＠ s → Term ℂ (A ＠ r)
  s ⇨ r ◇ t = perform (`comm s r t)

  ℂhoreoFocused : Set → Set _
  ℂhoreoFocused A = Term ℂ A

ℂhoreo : (At → Set) → Setω
ℂhoreo F = ∀ {_＠_ : At} {{＠-monad : ∀ {ℓ} {l} → RawMonad {ℓ} (_＠ l) }} → ℂhoreoFocused {_＠_} (F _＠_)

----------------------------------------------------------------------
-- Endpoint projection

-- the stdlib's ⊤ is not universe-polymorphic
record ⊤ {ℓ : Level} : Set ℓ where
  constructor tt

focus : Loc → At
focus l A s with l ≟ s
... | yes _ = A
... | no  _ = ⊤

id-monad : RawMonad {ℓ} (λ A → A)
id-monad = mkRawMonad _ (λ x → x) (λ x f → f x)

top-monad : RawMonad {ℓ} {ℓ′} (λ A → ⊤)
top-monad = mkRawMonad _ (λ _ → tt) (λ _ _ → tt)

instance
  focus-monad : ∀ {l s} → RawMonad {ℓ} (λ A → focus l A s)
  focus-monad {l = l} {s = s} with l ≟ s
  ... | yes _ = id-monad
  ... | no  _ = top-monad

import Choreography.Process
open module Process = Choreography.Process 𝕃 hiding (Op; Arity)

open RawMonad ⦃...⦄

epp : ∀ {F} → ℂhoreo F → (l : Loc) → ℙrocess (F (focus l))
epp c l = interp alg return c
  where
  alg : (ℂ {focus l}) -Alg[ Term ℙ A ]
  alg (`comm s r a , k) with l ≟ s | l ≟ r
  ... | yes _ | yes _ = locally a >>= k
  ... | yes _ | no  _ = locally a >>= (λ x → send r x) >> k tt
  ... | no  _ | yes _ = recv s >>= k
  ... | no  _ | no  _ = k tt

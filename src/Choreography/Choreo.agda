open import AlgEff
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)

module Choreography.Choreo
  (Loc : Set) (_≟_ : (l l′ : Loc) → Dec (l ≡ l′))
  {ℓ₁ ℓ₂ : Level} (𝕃 : Sig  ℓ₁ ℓ₂)
  where

open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_,_)
open import Effect.Monad using (RawMonad)
open import Effect.Monad.MyStuff using (mkRawMonad)
open import Function using (_∘_)
open import Level using (_⊔_; suc; Setω)
open import Relation.Binary.PropositionalEquality using (refl)
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
    ℓ ℓ′  : Level
    A B   : Set
    l s r : Loc

----------------------------------------------------------------------
-- An general interface for _＠_

At : Setω
At = ∀ {ℓ} → Set ℓ → Loc → Set ℓ

-- the stdlib's ⊤ is not universe-polymorphic

record ⊤ {ℓ : Level} : Set ℓ where
  constructor tt

opaque
  local : Loc → At
  local l A s with l ≟ s
  ... | yes _ = A
  ... | no  _ = ⊤

  id-monad : RawMonad {ℓ} (λ A → A)
  id-monad = mkRawMonad _ (λ x → x) (λ x f → f x)

  top-monad : RawMonad {ℓ} {ℓ′} (λ A → ⊤)
  top-monad = mkRawMonad _ (λ _ → tt) (λ _ _ → tt)

  instance
    local-monad : ∀ {l s} → RawMonad {ℓ} (λ A → local l A s)
    local-monad {l = l} {s = s} with l ≟ s
    ... | yes _ = id-monad
    ... | no  _ = top-monad

opaque
  global : At
  global A s = A

instance
  postulate
    global-monad : ∀ {l} → RawMonad {ℓ} {ℓ} (λ A → global A l)

----------------------------------------------------------------------
-- Choreography

module _ (_＠_ : At) where

  data Op : Set (suc (ℓ₁ ⊔ ℓ₂)) where
    `comm : (s r : Loc) → (Term 𝕃 A) ＠ s → Op

  Arity : Op → Set _
  Arity (`comm {A} _ r _) = A ＠ r

  ℂ : Sig _ _
  ℂ = Op ◁ Arity

----------------------------------------------------------------------
-- Help functions

private
  variable
    _＠_ : At

-- Local computations
-- use `\Tw` to type `▷`

_▷_ :  (s : Loc) → (Term 𝕃 A) ＠ s → Term (ℂ _＠_) (A ＠ s)
s ▷ t = perform (`comm s s t)


-- Communication
-- use `\r` to type `⇨`
-- use `\di` to type `◇`

_⇨_◇_ :  (s r : Loc) → (Term 𝕃 A) ＠ s → Term (ℂ _＠_) (A ＠ r)
s ⇨ r ◇ t = perform (`comm s r t)

ℂhoreo : (At → Set) → Setω
ℂhoreo F =
  ∀ (_＠_ : At) ⦃ ＠-monad : ∀ {ℓ} {l} → RawMonad {ℓ} (_＠ l) ⦄ →
  Term (ℂ _＠_) (F _＠_)

----------------------------------------------------------------------
-- Endpoint projection

opaque
  unfolding local

  epp : ∀ {F} → ℂhoreo F → (l : Loc) → ℙrocess (F (local l))
  epp c l = interp alg return (c _)
    where
      alg : ℂ (local l) -Alg[ Term ℙ A ]
      alg (`comm s r a , k) with l ≟ s | l ≟ r
      ... | yes _ | yes _ = locally a >>= k
      ... | yes _ | no  _ = locally a >>= (λ x → send r x) >> k tt
      ... | no  _ | yes _ = recv s >>= k
      ... | no  _ | no  _ = k tt

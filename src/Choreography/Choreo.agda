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
open import Level using (_⊔_; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

import Choreography.Process
open module Process = Choreography.Process 𝕃 hiding (Op; Arity)

open RawMonad ⦃...⦄

infix 20 _▷_
infix 20 _⇨_◇_

private
  variable
    A B   : Set
    l s r : Loc

----------------------------------------------------------------------
-- Signature

data Op (l : Loc) : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  `comm : (s r : Loc) → ((Term 𝕃 A) at s) l → Op l

Arity : (l : Loc) → Op l → Set _
Arity l (`comm {A} _ r _) = (A at r) l

ℂ : Loc → Sig _ _
ℂ l = Op l ◁ Arity l

----------------------------------------------------------------------
-- Shorthands

ℂhoreo : Set → Set (suc (ℓ₁ ⊔ ℓ₂))
ℂhoreo A = ∀ {l} → Term (ℂ l) A

-- use `\Tw` to type `▷`

_▷_ : (s : Loc) → ((Term 𝕃 A) at s) l → Term (ℂ l) ((A at s) l)
s ▷ t = perform (`comm s s t)

-- use `\r` to type `⇨`
-- use `\di` to type `◇`

_⇨_◇_ : (s r : Loc) → ((Term 𝕃 A) at s) l → Term (ℂ l) ((A at r) l)
s ⇨ r ◇ t = perform (`comm s r t)

----------------------------------------------------------------------
-- Endpoint projection

epp : ℂhoreo A → Loc → ℙrocess A
epp c l = interp alg return (c {l})
  where
  alg : (ℂ l) -Alg[ ℙrocess A ]
  alg (`comm s r a , k) with l ≟ s | l ≟ r
  ... | yes _ | yes _ = locally a >>= k
  ... | yes _ | no  _ = locally a >>= (λ x → send r x) >> k tt
  ... | no  _ | yes _ = recv s >>= k
  ... | no  _ | no  _ = k tt

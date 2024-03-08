open import AlgEff
open import Level using (Level)

-- Parameterize all definitions over a signature `𝕃` that specifies
-- what local computation a process can do

module Choreography.Choreo {ℓ₁ ℓ₂ : Level} (𝕃 : Sig  ℓ₁ ℓ₂) where

open import Choreography.Loc
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_,_)
open import Effect.Monad using (RawMonad)
open import Function using (_∘_)
open import Level using (_⊔_; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

import Choreography.Process
open module Process = Choreography.Process 𝕃 hiding (Op; Arity)

open RawMonad ⦃...⦄

private
  variable
    A B   : Set
    a     : A
    l     : Loc
    t₁ t₂ : Term 𝕃 A

----------------------------------------------------------------------
-- Signature

data Op (l : Loc) : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  `comm : (s r : Loc) → ((Term 𝕃 A) at s) l → Op l

Arity : (l : Loc) → Op l → Set _
Arity l (`comm {A} _ r _) = (A at r) l

ℂ : Loc → Sig _ _
ℂ l = Op l ◁ Arity l

ℂhoreo : Set → Set _
ℂhoreo A = ∀ {l} → Term (ℂ l) A

----------------------------------------------------------------------
-- Endpoint projection

epp : ℂhoreo A → Loc → ℙrocess A
epp c l = interp alg return (c {l})
  where
    alg : ℂ l -Alg[ ℙrocess A ]
    alg (`comm s r a , k) with l ≟ s | l ≟ r
    ... | yes _ | yes _ = perform (`locally a) >>= k
    ... | yes _ | no  _ = perform (`locally a) >>= (λ x → perform (`send r x)) >> k tt
    ... | no  _ | yes _ = perform (`recv s) >>= k
    ... | no  _ | no  _ = k tt

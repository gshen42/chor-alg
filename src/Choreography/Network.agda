open import AlgEff
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)

module Choreography.Network
  (Loc : Set) (_≟_ : (l l′ : Loc) → Dec (l ≡ l′))
  {ℓ₁ ℓ₂ : Level} (𝕃 : Sig ℓ₁ ℓ₂)
  where

open import Data.Empty using (⊥-elim)
open import Data.Product using (∃; ∃-syntax; _,_; _×_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (yes; no)

import Choreography.Process
open module Process = Choreography.Process Loc 𝕃

private
  variable
    A B   : Set
    l l′  : Loc
    F     : Loc → Set
    p     : ℙrocess A
    t     : Term 𝕃 A

-- A network is a collection of processes, each of which might return a different value

Network : (Loc → Set) → Set _
Network F = (l : Loc) → ℙrocess (F l)

private
  variable
    n n′  : Network F

-- Update one of the process in a network
-- no unfolding by default

opaque
  update : (l : Loc) → ℙrocess (F l) → Network F → Network F
  update l p n l′ with l ≟ l′
  ... | yes refl = p
  ... | no  _    = n l′

  rewrite₁ : (update l p n) l ≡ p
  rewrite₁ {l = l} with l ≟ l
  ... | yes refl = refl
  ... | no  f    = ⊥-elim (f refl)

  rewrite₂ : l ≢ l′ → (update l p n) l′ ≡ n l′
  rewrite₂ {l = l} {l′ = l′} l≢l′ with l ≟ l′
  ... | yes x = ⊥-elim (l≢l′ x)
  ... | no  _ = refl

-- An operational semantics for networks.

data _⇒ⁿ_ {F} : Network F → Network F → Set (suc (ℓ₁ ⊔ ℓ₂))where

  local⇒ⁿ : ∀ l a {k} →
            n l ≡ op (`locally t , k) →
            n ⇒ⁿ (update l (k a) n)

  comm⇒ⁿ : ∀ s r a {k} {k′} →
           n s ≡ op (`send {A} r a , k) →
           n r ≡ op (`recv {A} s , k′) →
           n ⇒ⁿ (update s (k tt) (update r (k′ a) n))

-- Deadlock freedom

data _✓ {F} : Network F → Set (suc (ℓ₁ ⊔ ℓ₂)) where

  end : (∀ l → ∃[ x ] n l ≡ var x) → n ✓

  step : (∀ n′ → n ⇒ⁿ n′ → n′ ✓) → n ✓

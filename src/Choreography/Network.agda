open import AlgEff
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)

module Choreography.Network
  (Loc : Set) (_≟_ : (l l′ : Loc) → Dec (l ≡ l′))
  (𝕃 : Sig)
  where

open import Data.Empty using (⊥-elim)
open import Data.Product using (∃; ∃-syntax; _,_; _×_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_; trans; sym; subst)
open import Relation.Nullary using (yes; no)

import Choreography.Process
open module Process = Choreography.Process Loc 𝕃

private
  variable
    A B   : Set
    l l′  : Loc
    F     : Loc → Set
    p p′  : ℙrocess A
    t     : Term 𝕃 A

-- A network is a collection of processes, each of which might return a different value

Network : (Loc → Set) → Set _
Network F = (l : Loc) → ℙrocess (F l)

private
  variable
    n n′ n″ n‴ : Network F

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

  postulate
    swap : l ≢ l′ → update l p (update l′ p′ n) ≡ update l′ p′ (update l p n)

-- An operational semantics for networks.

postulate
  𝕃-handler : ∀ {A : Set} → Term 𝕃 A → A

data _⇒ⁿ_ {F} : Network F → Network F → Set₁ where

  local⇒ⁿ : ∀ l {k} {t : Term 𝕃 A} →
            n l ≡ op (`locally t , k) →
            n ⇒ⁿ (update l (k (𝕃-handler t)) n)

  comm⇒ⁿ : ∀ s r t {k} {k′} →
           n s ≡ op (`send {A} r t , k) →
           n r ≡ op (`recv {A} s , k′) →
           n ⇒ⁿ (update s (k tt) (update r (k′ (𝕃-handler t)) n))

data _⇒⋆_ {F} : Network F → Network F → Set₁ where

  refl : n ⇒⋆ n

  step : n ⇒ⁿ n′ → n′ ⇒⋆ n″ → n ⇒⋆ n″

-- ⇒ⁿ has the diamond property

postulate
  diamond : n ⇒ⁿ n′ → n ⇒ⁿ n″ → ∃[ n‴ ] n′ ⇒⋆ n‴ × n″ ⇒⋆ n‴

  -- diamond {n = n} (local⇒ⁿ l eq₁) (local⇒ⁿ l′ eq₂) with l ≟ l′
  -- ... | yes refl with trans (sym eq₁) eq₂
  -- ...   | refl = _ , refl , refl
  -- diamond {n = n} (local⇒ⁿ l {k} {t} eq₁) (local⇒ⁿ l′ {k′} {t′} eq₂) | no l≢l′ =
  --   update l′ (k′ (𝕃-handler t′)) (update l (k (𝕃-handler t)) n)
  --   , step (local⇒ⁿ l′ (trans (rewrite₂ l≢l′) eq₂)) refl
  --   , subst (λ x → update l′ (k′ (𝕃-handler t′)) n ⇒⋆ x) (swap l≢l′) (step (local⇒ⁿ l (trans (rewrite₂ λ x → ⊥-elim (l≢l′ (Eq.sym x))) eq₁)) refl)

  -- diamond (local⇒ⁿ l eq₁) (comm⇒ⁿ s r a eq₂ eq₃) = {!!}

  -- diamond (comm⇒ⁿ s r a eq₂ eq₃) y = {!!}

-- Deadlock freedom

data _✓ {F} : Network F → Set₁ where

  end : (∀ l → ∃[ x ] n l ≡ var x) → n ✓

  step : n ⇒ⁿ n′ → n′ ✓ → n ✓

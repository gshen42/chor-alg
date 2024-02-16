module Choreography.Choreo where

open import AlgEff
open import Choreography.Loc
open import Choreography.Process using (Process; `locally; `send; `recv)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_,_)
open import Function using (_∘_)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

private
  variable
    a b : Level
    L   : Sig a b

----------------------------------------------------------------------
-- Signature

data Op (L : Sig a b) : Set (suc (a ⊔ b)) where
  `locally : ∀ {A : Set} → Loc → Term L A → Op L
  `comm    : ∀ {A : Set} → (s r : Loc) → A at s → Op L

Arity : Op L → Set
Arity (`locally {A} l _) = A at l
Arity (`comm {A} _ r _)  = A at r

Choreo : Sig a b → Sig _ _
Choreo L = Op L ◁ Arity

----------------------------------------------------------------------
-- Semantics

epp : ∀ {A : Set} → Term (Choreo L) A → Loc → Term (Process L) A
epp c l = interp alg return c
  where
    opaque
      unfolding _at_

      alg : ∀ {A : Set} → Choreo L -Alg[ Term (Process L) A ]
      alg (`locally l′ t , k) with l ≟ l′
      ... | yes _ = perform (`locally (t >>= (return ∘ just))) >>= k
      ... | no  _ = k nothing
      alg (`comm s r a , k) with l ≟ s | l ≟ r
      ... | yes _ | yes _ = k a
      ... | yes _ | no  _ = perform (`send r a) >> k nothing
      ... | no  _ | yes _ = perform (`recv s) >>= k
      ... | no  _ | no  _ = k nothing

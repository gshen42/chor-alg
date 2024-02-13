{-# OPTIONS --guardedness #-}

module Interaction where

open import AlgEff
open import CoalgEff
open import Level using (Level; _⊔_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    a b ℓ : Levelx

open CoTerm

data _⇔_ {𝔽 : Sig a b} {A : Set ℓ} {B : Set ℓ} : Term 𝔽 A → CoTerm 𝔽 B → Set (a ⊔ b ⊔ ℓ) where

  done : ∀ {a} {τ}
       → return a ⇔ τ

  step : ∀ {o} {k} {ar} {τ τ′}
       → coop τ ≡ (o , ar , τ′)
       → k ar ⇔ τ′
       → op (o , k) ⇔ τ

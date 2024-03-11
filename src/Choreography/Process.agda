open import AlgEff
open import Level using (Level)

module Choreography.Process {ℓ₁ ℓ₂ : Level} (𝕃 : Sig  ℓ₁ ℓ₂) where

open import Choreography.Loc hiding (⊤)
open import Data.Unit using (⊤)
open import Level using (_⊔_; suc)

private
  variable
    A : Set

----------------------------------------------------------------------
-- Signature

data Op : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  `locally : Term 𝕃 A → Op
  `send    : Loc → A → Op
  `recv    : {A : Set} → Loc → Op

Arity : Op → Set
Arity (`locally {A} _) = A
Arity (`send _ _)      = ⊤
Arity (`recv {A} _)    = A

ℙ : Sig _ _
ℙ = Op ◁ Arity

----------------------------------------------------------------------
-- Shorthands

ℙrocess : Set → Set _
ℙrocess A = Term ℙ A

locally : Term 𝕃 A → ℙrocess A
locally t = perform (`locally t)

send : Loc → A → ℙrocess ⊤
send l a = perform (`send l a)

recv : Loc → ℙrocess A
recv {A} l = perform (`recv {A} l)

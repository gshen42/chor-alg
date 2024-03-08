open import AlgEff
open import Level using (Level)

-- Parameterize all definitions over a signature `𝕃` that specifies
-- what local computation a process can do

module Choreography.Process {ℓ₁ ℓ₂ : Level} (𝕃 : Sig  ℓ₁ ℓ₂) where

open import Choreography.Loc hiding (⊤)
open import Data.Unit using (⊤)
open import Level using (_⊔_; suc)

private
  variable
    A : Set

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

ℙrocess : Set → Set _
ℙrocess A = Term ℙ A

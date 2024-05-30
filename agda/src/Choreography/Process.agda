open import AlgEff

module Choreography.Process
  (Loc : Set) (𝕃 : Sig)
  where

open import Data.Unit using (⊤)

private
  variable
    A : Set

----------------------------------------------------------------------
-- Processes

data Op : Set₁ where
  `locally : Term 𝕃 A → Op
  `send    : Loc → Term 𝕃 A → Op
  `recv    : {A : Set} → Loc → Op

Arity : Op → Set
Arity (`locally {A} _) = A
Arity (`send _ _)      = ⊤
Arity (`recv {A} _)    = A

ℙ : Sig
ℙ = Op ◁ Arity

----------------------------------------------------------------------
-- Helper functions

ℙrocess : Set → Set _
ℙrocess A = Term ℙ A

locally : Term 𝕃 A → ℙrocess A
locally t = perform (`locally t)

send : Loc → Term 𝕃 A → ℙrocess ⊤
send l a = perform (`send l a)

recv : Loc → ℙrocess A
recv {A} l = perform (`recv {A} l)

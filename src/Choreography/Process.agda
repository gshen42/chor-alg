module Choreography.Process where

open import AlgEff
open import Choreography.Loc
open import Data.Unit using (⊤)
open import Level using (Level; _⊔_; suc)

private
  variable
    a b : Level
    L   : Sig a b

----------------------------------------------------------------------
-- Signature

data Op (L : Sig a b) : Set (suc (a ⊔ b)) where
  `locally : ∀ {A : Set} → Term L A → Op L
  `send    : ∀ {A : Set} → Loc → A → Op L
  `recv    : ∀ {A : Set} → Loc → Op L

Arity : Op L → Set
Arity (`locally {A} _) = A
Arity (`send _ _)      = ⊤
Arity (`recv {A} _)    = A

Process : Sig a b → Sig _ _
Process L = Op L ◁ Arity

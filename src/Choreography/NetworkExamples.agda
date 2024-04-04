{-# OPTIONS --guardedness #-}

open import AlgEff
open import Level using (Level; suc; _⊔_)

module Choreography.NetworkExamples
  {ℓ₁ ℓ₂ : Level} (𝕃 : Sig ℓ₁ ℓ₂)
  where

open import Choreography.Loc
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Effect.Monad using (RawMonad)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

import Choreography.Process
open module Process = Choreography.Process ABC 𝕃

import Choreography.Network
open module Network = Choreography.Network ABC _≟_ 𝕃

open RawMonad ⦃...⦄

postulate
  X Y Z W U : Set
  getInput : Term 𝕃 X
  x : X
  f : X → Y
  g : Y → Z
  h : Z → W
  showResults : W → Term 𝕃 U
  u : U

alice : ℙrocess U
alice = do
  x ← locally getInput
  send `bob (f x)
  w ← recv `carol
  locally (showResults w)

bob : ℙrocess ⊤
bob = do
  y ← recv `alice
  send `carol (g y)

carol : ℙrocess ⊤
carol = do
  z ← recv `bob
  send `alice (h z)

F : ABC → Set
F `alice = U
F `bob   = ⊤
F `carol = ⊤

ex₁ : Network F
ex₁ `alice = alice
ex₁ `bob   = bob
ex₁ `carol = carol

ex₁✓ : ex₁ ✓
ex₁✓ = step (local⇒ⁿ {l = `alice} {a = x} refl)
         (step (comm⇒ⁿ {s = `alice} {r = `bob} (rewrite₁) (rewrite₂ λ ()))
           (step (comm⇒ⁿ {s = `bob} {r = `carol} (trans (rewrite₂ λ ()) rewrite₁) (trans (rewrite₂ λ ()) (trans (rewrite₂ λ ()) (rewrite₂ λ ()))))
             (step (comm⇒ⁿ {s = `carol} {r = `alice} (trans (rewrite₂ λ ()) rewrite₁) (trans (rewrite₂ λ ()) (trans (rewrite₂ λ ()) rewrite₁)))
              (step (local⇒ⁿ {l = `alice} {a = u} (trans (rewrite₂ λ ()) rewrite₁))
                (end
                  λ where
                  `alice → _ , rewrite₁
                  `bob   → _ , trans (rewrite₂ λ ()) (trans (rewrite₂ λ ()) (trans (rewrite₂ λ ()) rewrite₁))
                  `carol → _ , trans (rewrite₂ λ ()) rewrite₁)))))

alice′ : ℙrocess U
alice′ = do
  x ← locally getInput
  send `bob (f x)
  w ← recv `bob
  locally (showResults w)

ex₂ : Network F
ex₂ `alice = alice′
ex₂ `bob   = bob
ex₂ `carol = carol

-- TODO: prove this
-- ¬ex₂✓ : ex₂ ✓ → ⊥

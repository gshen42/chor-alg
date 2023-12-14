--------------------------------------------------------------------------------
-- This module defines a general framework for algebraic effects, highly inspired
-- by https://doisinkidney.com/pdfs/algebraic-free-monads.pdf.
--------------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Primitive renaming (Set to Type)

module AlgEff where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_)

--------------------------------------------------------------------------------
-- Signature

record Sig : Type₁ where
  constructor _◁_
  field
    Op : Type
    Ar : Op → Type

--------------------------------------------------------------------------------
-- Algebra

⟦_⟧ : Sig → Type → Type
⟦ Op ◁ Ar ⟧ X = Σ[ o ∈ Op ] (Ar o → X)

_-Alg[_] : Sig → Type → Type
𝔽 -Alg[ 𝒞 ] = ⟦ 𝔽 ⟧ 𝒞 → 𝒞

-- `⟦ 𝔽 ⟧` is a functor

fmap : ∀ {𝔽} {A B} → (A → B) → ⟦ 𝔽 ⟧ A → ⟦ 𝔽 ⟧ B
fmap f (o , k) = (o , f ∘ k)

--------------------------------------------------------------------------------
-- Free algebra

data Free (𝔽 : Sig) (A : Type) : Type where
  var : A → Free 𝔽 A
  op  : ⟦ 𝔽 ⟧ (Free 𝔽 A) → Free 𝔽 A

-- `Free` is a monad

return : ∀ {𝔽} {A} → A → Free 𝔽 A
return x = var x

_>>=_ : ∀ {𝔽} {A B} → Free 𝔽 A → (A → Free 𝔽 B) → Free 𝔽 B
var x      >>= ρ = ρ x
op (o , k) >>= ρ = op (o , (_>>= ρ) ∘ k)

-- `Free` is a algebra of any `𝔽`

free-alg : ∀ {𝔽} {A} → 𝔽 -Alg[ Free 𝔽 A ]
free-alg = op

-- TODO: freeness of `Free`

--------------------------------------------------------------------------------
-- Effect handler

handle : ∀ {𝔽} {𝒞 A} → (A → 𝒞) → 𝔽 -Alg[ 𝒞 ] → Free 𝔽 A → 𝒞
handle ρ ϕ (var x)      = ρ x
handle ρ ϕ (op (o , k)) = ϕ (o , handle ρ ϕ ∘ k)

--------------------------------------------------------------------------------
-- Coalgebra

⟦_⟧′ : Sig → Type → Type
⟦ Op ◁ Ar ⟧′ X = ∀ (o : Op) → (Ar o × X)

_-Coalg[_] : Sig → Type → Type
𝔽 -Coalg[ 𝒞 ] = 𝒞 → ⟦ 𝔽 ⟧′ 𝒞

-- ⟦ 𝔽 ⟧′ is a functor

fmap′ : ∀ {𝔽} {A B} → (A → B) → ⟦ 𝔽 ⟧′ A → ⟦ 𝔽 ⟧′ B
fmap′ f x o = proj₁ (x o) , f (proj₂ (x o)) -- TODO: is there a more concise way to write this?

--------------------------------------------------------------------------------
-- Free coalgebra

record Cofree (𝔽 : Sig) (A : Type) : Type where
  coinductive
  field
    coop : ⟦ 𝔽 ⟧′ (Cofree 𝔽 A)

open Cofree

-- QUESTION: Is `Cofree` a comonad?

-- `Cofree` is a coalgebra for any `𝔽`

cofree-coalg : ∀ {𝔽} {A} → 𝔽 -Coalg[ Cofree 𝔽 A ]
cofree-coalg = coop

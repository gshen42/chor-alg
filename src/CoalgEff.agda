{-# OPTIONS --guardedness #-}

module CoalgEff where

open import AlgEff
open import Data.Product using (Σ; Σ-syntax; _×_)
open import Level using (Level; _⊔_)

private
  variable
    a b ℓ : Level
    A     : Set
    𝔽     : Sig a b

----------------------------------------------------------------------
-- Coalgebra

-- A signature can be interpreted coalgebraically, which also induces
-- a functor

⟦_⟧′ : Sig a b → Set ℓ → Set _
⟦ Op ◁ Ar ⟧′ X = Σ[ o ∈ Op ] (Ar o × X)

_-Coalg[_] : Sig a b → Set ℓ → Set _
𝔽 -Coalg[ 𝒞 ] = 𝒞 → ⟦ 𝔽 ⟧′ 𝒞

----------------------------------------------------------------------
-- Coterms of a coalgebra

record CoTerm (𝔽 : Sig a b) (A : Set ℓ) : Set (a ⊔ b ⊔ ℓ) where
  coinductive
  field
    covar : A
    coop  : ⟦ 𝔽 ⟧′ (CoTerm 𝔽 A)

open CoTerm

-- `CoTerm` is a coalgebra for any signature `𝔽` through `coop`

coterm-coalg : 𝔽 -Coalg[ CoTerm 𝔽 A ]
coterm-coalg = coop

-- TODO: Is `CoTerm` a comonad?

----------------------------------------------------------------------
-- TODO: Coterms are the final coalgebra

-- A final coalgebra of a signature has an unique homomorphism *from*
-- arbitrary algebra of the same signature.

----------------------------------------------------------------------
-- This module defines a general framework for algebraic effects,
-- highly inspired by https://doisinkidney.com/pdfs/algebraic-free-monads.pdf.
----------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Primitive renaming (Set to Type)

module AlgEff where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    A B : Type

----------------------------------------------------------------------
-- Signature

record Sig : Type₁ where
  constructor _◁_
  field
    Op    : Type
    Arity : Op → Type

open Sig

private
  variable
    𝔽 : Sig

----------------------------------------------------------------------
-- Algebra

-- A signature 𝔽 induces a functor ⟦ 𝔽 ⟧

⟦_⟧ : Sig → Type → Type
⟦ Op ◁ Ar ⟧ X = Σ[ o ∈ Op ] (Ar o → X)

fmap : (A → B) → ⟦ 𝔽 ⟧ A → ⟦ 𝔽 ⟧ B
fmap f (o , k) = (o , f ∘ k)

-- An 𝔽-algebra on the carrier 𝒞

_-Alg[_] : Sig → Type → Type
𝔽 -Alg[ 𝒞 ] = ⟦ 𝔽 ⟧ 𝒞 → 𝒞

private
  variable
    𝒞 𝒟 : Type

----------------------------------------------------------------------
-- Terms of an algebra (or free monads)

data Term (𝔽 : Sig) (A : Type) : Type where
  var : A → Term 𝔽 A
  op  : ⟦ 𝔽 ⟧ (Term 𝔽 A) → Term 𝔽 A

-- `Term` is a monad

return : A → Term 𝔽 A
return = var

_>>=_ : Term 𝔽 A → (A → Term 𝔽 B) → Term 𝔽 B
var x      >>= f = f x
op (o , k) >>= f = op (o , _>>= f ∘ k)
  -- ^ why `op t >>= f = op (fmap (_>>= f) t)` doesn't pass the
  -- termination checking?

-- `Term` is an algebra of any `𝔽` through `op`

term-alg : 𝔽 -Alg[ Term 𝔽 A ]
term-alg = op

----------------------------------------------------------------------
-- Terms are the initial algebra

-- A homomorphism between two 𝔽-algebras is a function h between the
-- two carriers 𝒞 and 𝒟 that commutes with the operations of the
-- signature.

_⇒_ : 𝔽 -Alg[ 𝒞 ] → 𝔽 -Alg[ 𝒟 ] → Type
_⇒_ {_} {𝒞} {𝒟} c d = Σ[ h ∈ (𝒞 → 𝒟) ] h ∘ c ≡ d ∘ fmap h

-- `toAlg` is also known as the effect handler

interp : 𝔽 -Alg[ 𝒞 ] → (A → 𝒞) → Term 𝔽 A → 𝒞
interp c f (var x)      = f x
interp c f (op (o , k)) = c (o , interp c f ∘ k)
  -- ^ why `interp c f (op t) = c (fmap (interp c f) t)` doesn't pass
  -- the termination checking?

-- TODO: prove that `Term` is the initial algebra and `handle` is the
-- homomorphism fomr it to any algebra

----------------------------------------------------------------------
-- Coalgebra

_-Coalg[_] : Sig → Type → Type
𝔽 -Coalg[ 𝒞 ] = 𝒞 → ⟦ 𝔽 ⟧ 𝒞

----------------------------------------------------------------------
-- Coterms of a coalgebra

record CoTerm (𝔽 : Sig) (A : Type) : Type where
  coinductive
  field
    covar : A
    coop  : ⟦ 𝔽 ⟧ (CoTerm 𝔽 A)

open CoTerm

-- TODO: Is `CoTerm` a comonad?

-- `CoTerm` is a coalgebra for any `𝔽` through `coop`

coterm-coalg : 𝔽 -Coalg[ CoTerm 𝔽 A ]
coterm-coalg = coop

----------------------------------------------------------------------
-- Coterms are the final coalgebra

-- cohandle : ∀ {𝔽} {𝒞 A} → 𝔽 -Coalg[ 𝒞 ] → Free 𝔽 A → (𝒞 → A × 𝒞)
-- cohandle ϕ (var x)      = λ w → x , w
-- cohandle ϕ (op (o , k)) = λ w →  cohandle ϕ (k (proj₁ (ϕ w o))) (proj₂ (ϕ w o))

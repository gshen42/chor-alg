----------------------------------------------------------------------
-- This module defines a general framework for algebraic effects,
-- highly inspired by https://doisinkidney.com/pdfs/algebraic-free-monads.pdf.
----------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Primitive renaming (Set to Type)

module AlgEff where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; [_,_])
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

_:+:_ : Sig → Sig → Sig
𝔽 :+: 𝔾 = (Op 𝔽 ⊎ Op 𝔾) ◁ [ Arity 𝔽 , Arity 𝔾 ]

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
-- Terms of an algebra

data Term (𝔽 : Sig) (A : Type) : Type where
  var : A → Term 𝔽 A
  op  : ⟦ 𝔽 ⟧ (Term 𝔽 A) → Term 𝔽 A

-- `Term` is an algebra for any signature `𝔽` through `op`

term-alg : 𝔽 -Alg[ Term 𝔽 A ]
term-alg = op

-- `Term` is a monad (the free monad)

return : A → Term 𝔽 A
return = var

_>>=_ : Term 𝔽 A → (A → Term 𝔽 B) → Term 𝔽 B
var x      >>= f = f x
op (o , k) >>= f = op (o , _>>= f ∘ k)
  -- ^ why `op t >>= f = op (fmap (_>>= f) t)` doesn't pass the
  -- termination checking?

----------------------------------------------------------------------
-- Terms are the initial algebra

-- An initial algebra of a signature has an unique homomorphism
-- (structure-preserving mapping) to arbitrary algebra of the same
-- signature. Such a homomorphism gives rise to effect handlers in
-- algebraic effects.

interp : 𝔽 -Alg[ 𝒞 ] → (A → 𝒞) → Term 𝔽 A → 𝒞
interp c f (var x)      = f x
interp c f (op (o , k)) = c (o , interp c f ∘ k)
  -- ^ why `interp c f (op t) = c (fmap (interp c f) t)` doesn't pass
  -- the termination checking?

-- A homomorphism between two 𝔽-algebras is a function h between the
-- two carriers 𝒞 and 𝒟 that commutes with the operations of the
-- signature.

_⇒_ : 𝔽 -Alg[ 𝒞 ] → 𝔽 -Alg[ 𝒟 ] → Type
_⇒_ {_} {𝒞} {𝒟} c d = Σ[ h ∈ (𝒞 → 𝒟) ] h ∘ c ≡ d ∘ fmap h

-- TODO: prove that `Term` is the initial algebra

----------------------------------------------------------------------
-- Coalgebra

-- A signature can be interpreted coalgebraically, which also induces
-- a functor

⟦_⟧′ : Sig → Type → Type
⟦ Op ◁ Ar ⟧′ X = Σ[ o ∈ Op ] (Ar o × X)

_-Coalg[_] : Sig → Type → Type
𝔽 -Coalg[ 𝒞 ] = 𝒞 → ⟦ 𝔽 ⟧′ 𝒞

----------------------------------------------------------------------
-- Coterms of a coalgebra

record CoTerm (𝔽 : Sig) (A : Type) : Type where
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

----------------------------------------------------------------------
-- Program/environment interactions

data _⇔_ {𝔽 : Sig} {A} {B} : Term 𝔽 A → CoTerm 𝔽 B → Type₁ where

  done : ∀ {a} {τ}
       → return a ⇔ τ

  step : ∀ {o} {k} {ar} {τ τ′}
       → coop τ ≡ (o , ar , τ′)
       → k ar ⇔ τ′
       → op (o , k) ⇔ τ

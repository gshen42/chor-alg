----------------------------------------------------------------------
-- This module defines a general framework for algebraic effects,
-- highly inspired by https://doisinkidney.com/pdfs/algebraic-free-monads.pdf.
----------------------------------------------------------------------

module AlgEff where

open import Data.Product using (Σ; Σ-syntax; _,_)
open import Effect.Monad using (RawMonad)
open import Effect.Monad.MyStuff using (mkRawMonad)
open import Function using (_∘_)

private
  variable
    A B : Set
    X   : Set _

----------------------------------------------------------------------
-- Signature

record Sig : Set₂ where
  constructor _◁_
  field
    Op    : Set₁
    Arity : Op → Set

open Sig

private
  variable
    𝔽 : Sig

----------------------------------------------------------------------
-- Algebra

-- A signature `𝔽` induces a functor ⟦ 𝔽 ⟧

⟦_⟧ : Sig → Set₁ → Set₁
⟦ Op ◁ Ar ⟧ X = Σ[ o ∈ Op ] (Ar o → X)

-- An 𝔽-algebra on carrier set C

_-Alg[_] : Sig → Set₁ → Set₁
𝔽 -Alg[ C ] = ⟦ 𝔽 ⟧ C → C

----------------------------------------------------------------------
-- Terms of an algebra

data Term (𝔽 : Sig) (A : Set) : Set₁ where
  var : A → Term 𝔽 A
  op  : ⟦ 𝔽 ⟧ (Term 𝔽 A) → Term 𝔽 A

-- `Term` is an algebra for any signature `𝔽` through `op`

term-alg : 𝔽 -Alg[ Term 𝔽 A ]
term-alg = op

-- `Term` is a monad (the free monad)

instance
  term-monad : RawMonad (Term 𝔽)
  term-monad = mkRawMonad _ var _>>=_
    where
      _>>=_ : Term 𝔽 A → (A → Term 𝔽 B) → Term 𝔽 B
      var x      >>= f = f x
      op (o , k) >>= f = op (o , _>>= f ∘ k)

perform : ∀ (o : Op 𝔽) → Term 𝔽 (Arity 𝔽 o)
perform o = op (o , var)

----------------------------------------------------------------------
-- Terms are the initial algebra

interp : 𝔽 -Alg[ X ] → (A → X) → Term 𝔽 A → X
interp alg f (var x)      = f x
interp alg f (op (o , k)) = alg (o , interp alg f ∘ k)

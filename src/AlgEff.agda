----------------------------------------------------------------------
-- This module defines a general framework for algebraic effects,
-- highly inspired by https://doisinkidney.com/pdfs/algebraic-free-monads.pdf.
----------------------------------------------------------------------

module AlgEff where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; [_,_])
open import Effect.Functor using (RawFunctor)
open import Effect.Monad using (RawMonad)
open import Function using (_∘_)
open import Level using (Level; suc; _⊔_; Lift)
open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    ℓ₁ ℓ₂ ℓ : Level
    A B C D : Set ℓ

----------------------------------------------------------------------
-- Signature

record Sig (ℓ₁ : Level) (ℓ₂ : Level) : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  constructor _◁_
  field
    Op    : Set ℓ₁
    Arity : Op → Set ℓ₂

open Sig

private
  variable
    𝔽 : Sig ℓ₁ ℓ₂

----------------------------------------------------------------------
-- Algebra

-- A signature `𝔽` induces a functor ⟦ 𝔽 ⟧

⟦_⟧ : Sig ℓ₁ ℓ₂ → Set ℓ → Set _
⟦ Op ◁ Ar ⟧ X = Σ[ o ∈ Op ] (Ar o → X)

instance
  ⟦𝔽⟧-functor : RawFunctor {ℓ} ⟦ 𝔽 ⟧
  ⟦𝔽⟧-functor = record
    { _<$>_ = _<$>_
    }
    where
      _<$>_ : (A → B) → ⟦ 𝔽 ⟧ A → ⟦ 𝔽 ⟧ B
      f <$> (o , k) = (o , f ∘ k)

-- An 𝔽-algebra on carrier set C

_-Alg[_] : Sig ℓ₁ ℓ₂ → Set ℓ → Set _
𝔽 -Alg[ C ] = ⟦ 𝔽 ⟧ C → C

----------------------------------------------------------------------
-- Terms of an algebra

data Term (𝔽 : Sig ℓ₁ ℓ₂) (A : Set ℓ) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ) where
  var : A → Term 𝔽 A
  op  : ⟦ 𝔽 ⟧ (Term 𝔽 A) → Term 𝔽 A

-- `Term` is an algebra for any signature `𝔽` through `op`

term-alg : 𝔽 -Alg[ Term 𝔽 A ]
term-alg = op

-- `Term` is a monad (the free monad)

instance
  term-monad : RawMonad {ℓ} (Term 𝔽)
  term-monad = record
    { rawApplicative = record
      { rawFunctor = record
        { _<$>_ = λ f ma → ma >>= λ a → pure (f a)
        }
      ; pure = pure
      ; _<*>_ = λ mf mx → do
          f <- mf
          x <- mx
          pure (f x)
      }
    ; _>>=_ = _>>=_
    }
    where
      pure : A → Term 𝔽 A
      pure = var

      _>>=_ : Term 𝔽 A → (A → Term 𝔽 B) → Term 𝔽 B
      var x      >>= f = f x
      op (o , k) >>= f = op (o , _>>= f ∘ k)

perform : ∀ (o : Op 𝔽) → Term 𝔽 (Arity 𝔽 o)
perform o = op (o , var)

----------------------------------------------------------------------
-- Terms are the initial algebra

interp : 𝔽 -Alg[ C ] → (A → C) → Term 𝔽 A → C
interp c f (var x)      = f x
interp c f (op (o , k)) = c (o , interp c f ∘ k)

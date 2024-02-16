----------------------------------------------------------------------
-- This module defines a general framework for algebraic effects,
-- highly inspired by https://doisinkidney.com/pdfs/algebraic-free-monads.pdf.
----------------------------------------------------------------------

module AlgEff where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; [_,_])
open import Function using (_∘_)
open import Level using (Level; suc; _⊔_; Lift)
open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    a b c d ℓ : Level
    A B C D   : Set ℓ

----------------------------------------------------------------------
-- Signature

record Sig (a : Level) (b : Level) : Set (suc (a ⊔ b)) where
  constructor _◁_
  field
    Op    : Set a
    Arity : Op → Set b

open Sig

private
  variable
    𝔽 : Sig a b

_:+:_ : Sig a b → Sig c d → Sig (a ⊔ c) (suc (b ⊔ d))
𝔽 :+: 𝔽′ = (Op 𝔽 ⊎ Op 𝔽′) ◁ [ Lift _ ∘ Arity 𝔽 , Lift _ ∘ Arity 𝔽′ ]

-- ^ I don't fully understand why the above definition works.

----------------------------------------------------------------------
-- Algebra

-- A signature 𝔽` induces a functor ⟦ 𝔽 ⟧

⟦_⟧ : Sig a b → Set ℓ → Set _
⟦ Op ◁ Ar ⟧ X = Σ[ o ∈ Op ] (Ar o → X)

fmap : (A → B) → ⟦ 𝔽 ⟧ A → ⟦ 𝔽 ⟧ B
fmap f (o , k) = (o , f ∘ k)

-- An 𝔽-algebra on carrier set C

_-Alg[_] : Sig a b → Set ℓ → Set _
𝔽 -Alg[ C ] = ⟦ 𝔽 ⟧ C → C

----------------------------------------------------------------------
-- Terms of an algebra

data Term (𝔽 : Sig a b) (A : Set ℓ) : Set (a ⊔ b ⊔ ℓ) where
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

_>>_ : Term 𝔽 A → Term 𝔽 B → Term 𝔽 B
t₁ >> t₂ = t₁ >>= λ _ → t₂

perform : ∀ (o : Op 𝔽) → Term 𝔽 (Arity 𝔽 o)
perform o = op (o , return)

----------------------------------------------------------------------
-- Terms are the initial algebra

-- An initial algebra of a signature has an unique homomorphism
-- (structure-preserving mapping) to arbitrary algebra of the same
-- signature. Such a homomorphism gives rise to effect handlers in
-- algebraic effects.

interp : 𝔽 -Alg[ C ] → (A → C) → Term 𝔽 A → C
interp c f (var x)      = f x
interp c f (op (o , k)) = c (o , interp c f ∘ k)
  -- ^ why `interp c f (op t) = c (fmap (interp c f) t)` doesn't pass
  -- the termination checking?

-- A homomorphism between two 𝔽-algebras is a function h between the
-- two carriers C and D that commutes with the operations of the
-- signature.

_⇒_ : 𝔽 -Alg[ C ] → 𝔽 -Alg[ D ] → Set _
_⇒_ {C = C} {D = D} c d = Σ[ h ∈ (C → D) ] h ∘ c ≡ d ∘ fmap h

-- TODO: prove that `Term` is the initial algebra

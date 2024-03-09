-- The stdlib's `Effect.Monad.mkRawMonad` is over constrained, this
-- module defines a new version that fixes that. It is as simple as
-- changing the type of `F` to `Set f → Set g`.

-- TODO: submit a PR to stdlib

module Effect.Monad.MyStuff where

open import Effect.Applicative hiding (mkRawApplicative)
open import Effect.Functor
open import Effect.Monad hiding (mkRawMonad)
open import Function.Base using (_$′_; _∘′_)
open import Level using (Level)

private
  variable
    f g : Level

open RawFunctor
open RawApplicative
open RawMonad

mkRawApplicative :
  (F : Set f → Set g) →
  (pure : ∀ {A} → A → F A) →
  (app : ∀ {A B} → F (A → B) → F A → F B) →
  RawApplicative F
mkRawApplicative F pure app .rawFunctor ._<$>_ = app ∘′ pure
mkRawApplicative F pure app .pure = pure
mkRawApplicative F pure app ._<*>_ = app

mkRawMonad :
  (F : Set f → Set g) →
  (pure : ∀ {A} → A → F A) →
  (bind : ∀ {A B} → F A → (A → F B) → F B) →
  RawMonad F
mkRawMonad F pure _>>=_ .rawApplicative =
  mkRawApplicative _ pure $′ λ mf mx → do
      f ← mf
      x ← mx
      pure (f x)
mkRawMonad F pure _>>=_ ._>>=_ = _>>=_

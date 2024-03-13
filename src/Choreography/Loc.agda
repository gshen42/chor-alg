module Choreography.Loc where

open import Data.String as String using (String)
open import Effect.Monad using (RawMonad)
open import Effect.Monad.MyStuff using (mkRawMonad)
open import Level using (Level)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    ℓ ℓ′ : Level

----------------------------------------------------------------------
-- Locations

Loc : Set
Loc = String

opaque
  _≟_ : (l l′ : Loc) → Dec (l ≡ l′)
  _≟_ = String._≟_

-- ----------------------------------------------------------------------
-- -- Located Values

-- _at_ : Set ℓ → Loc → (Loc → Set ℓ)
-- (A at l) l′ with l′ ≟ l
-- ... | yes _ = A
-- ... | no  _ = ⊤

-- top-monad : RawMonad {ℓ} {ℓ′} (λ A → ⊤)
-- top-monad = mkRawMonad _ (λ _ → tt) (λ _ _ → tt)

-- id-monad : RawMonad {ℓ} (λ A → A)
-- id-monad = mkRawMonad _ (λ x → x) (λ x f → f x)

-- instance
--   weird-monad : ∀ {l l′} → RawMonad {ℓ} (λ A → (A at l) l′)
--   weird-monad {l = l} {l′ = l′} with l′ ≟ l
--   ... | yes _ = id-monad
--   ... | no  _ = top-monad

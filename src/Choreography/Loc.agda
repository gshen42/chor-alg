module Choreography.Loc where

open import Data.String as String using (String)
open import Level using (Level)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

infix 20 _at_

private
  variable
    ℓ : Level

opaque
  Loc : Set
  Loc = String

  _≟_ : (l l′ : Loc) → Dec (l ≡ l′)
  _≟_ = String._≟_

-- the stdlib's ⊤ is not universe-polymorphic
record ⊤ : Set ℓ where
  constructor tt

_at_ : Set ℓ → Loc → (Loc → Set ℓ)
(A at l) l′ with l′ ≟ l
... | yes _ = A
... | no  _ = ⊤

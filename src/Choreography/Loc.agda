module Choreography.Loc where

open import Data.String as String using (String)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

Loc : Set
Loc = String

opaque
  _≟_ : (l l′ : Loc) → Dec (l ≡ l′)
  _≟_ = String._≟_

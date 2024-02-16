module Choreography.Loc where

open import Data.Bool using (Bool)
open import Data.String as String using (String)
open import Data.Maybe using (Maybe; just)
open import Level using (Level)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

infix 21 #_
infix 20 _at_

opaque
  Loc : Set
  Loc = String

  _≟_ : (l l′ : Loc) → Dec (l ≡ l′)
  _≟_ = String._≟_

  #_ : String → Loc
  # s = s

  _at_ : Set → Loc → Set
  A at l = Maybe A

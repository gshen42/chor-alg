module Choreography.Loc where

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Any type with decidable equality can be used as a location type

-- Here, we present a canonical location type `ABC`, which contains
-- three familiar locations --- Alice, Bob, and Carol --- that we'll
-- be using in examples.

data ABC : Set where
  `alice : ABC
  `bob   : ABC
  `carol : ABC

_≟_ : (l l′ : ABC) → Dec (l ≡ l′)
`alice ≟ `alice = yes refl
`alice ≟ `bob   = no λ ()
`alice ≟ `carol = no λ ()
`bob   ≟ `alice = no λ ()
`bob   ≟ `bob   = yes refl
`bob   ≟ `carol = no λ ()
`carol ≟ `alice = no λ ()
`carol ≟ `bob   = no λ ()
`carol ≟ `carol = yes refl

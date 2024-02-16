module Choreography.Examples where

open import AlgEff
open import Choreography.Choreo
open import Choreography.Loc
open import Data.Product using (_,_)
open import Data.Nat using (ℕ)
open import Level using (Level)

private
  variable
    a b : Level
    L   : Sig a b

alice : Loc
alice = # "alice"

bob : Loc
bob = # "bob"

foo : Term (Choreo L) (ℕ at # "bob")
foo = do
  x <- perform (`locally alice (return 42))
  perform (`comm alice bob x)

-- _ = {!epp foo bob!}

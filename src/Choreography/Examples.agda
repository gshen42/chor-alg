module Choreography.Examples  where

open import AlgEff
open import Choreography.Loc
open import Data.Product using (_,_)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Nat using (ℕ; _+_)
open import Data.String using (String)
open import Effect.Monad using (RawMonad)
open import Function using (_∘′_)
open import Level using (Level; 0ℓ)

open RawMonad ⦃...⦄

private
  variable
    ℓ : Level

----------------------------------------------------------------------
-- Postulated IO computations

postulate
  𝕀 : Sig 0ℓ 0ℓ

IO : Set ℓ → Set _
IO A = Term 𝕀 A

postulate
  getLine  : IO String
  putStrLn : String → IO String

----------------------------------------------------------------------
-- A choreography with IO as the local computation

module Foo where

  import Choreography.Choreo
  open module Choreo  = Choreography.Choreo 𝕀

  postulate
    parse : String → IO ℕ
    _≥_ : ℕ → ℕ → Bool

  max : ℂhoreo (ℕ at "alice")
  max = do
    x ← "bob" ⇨ "alice" ◇ do
      let t = getLine >>= parse
      return t
      
    y ← "carol" ⇨ "alice" ◇ do
      let t = getLine >>= parse
      return t

    -- bob can't access alice's data
    -- "bob" ▷ do
    --   x′ ← x
    --   let t = putStrLn x′
    --   return t
      
    "alice" ▷ do
      x′ ← x
      y′ ← y
      let t = if x′ ≥ y′ then return x′ else return y′ 
      return t

  test = epp max "alice"

----------------------------------------------------------------------
-- TODO: generalize `>>=` to make the following code type check

-- The problem: _>>=_ : M A → (A → M B) → M B forces A and B to come
-- from the same universe `ℓ`.

-- module _ {ℓ₁ ℓ₂ : Level} (𝕃 : Sig ℓ₁ ℓ₂) where

--   import Choreography.Choreo
--   open module Choreo = Choreography.Choreo 𝕃 

--   foo : ℂhoreo (ℕ at "bob")
--   foo = do
--     x ← "alice" ▷ return (return 42)
--     "alice" ⇨ "bob" ◇ do
--       x′ ← x
--       let t = return (x′ + 2)
--       return t

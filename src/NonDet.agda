{-# OPTIONS --guardedness #-}

module NonDet where

open import AlgEff
open import Codata.Guarded.Stream using (Stream; _∷_) renaming (head to hd; tail to tl)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_)

----------------------------------------------------------------------
-- Signature of nondeterministic computations

data Op : Set where
  `<|>  : Op
  `fail : Op

Arity : Op → Set
Arity `<|>  = Bool
Arity `fail = ⊥

ℕ𝔻 : Sig
ℕ𝔻 = Op ◁ Arity

----------------------------------------------------------------------
-- Smart constructors

private
  variable
    A : Set

_<|>_ : Term ℕ𝔻 A → Term ℕ𝔻 A → Term ℕ𝔻 A
t₁ <|> t₂ = op (`<|> , λ { true → t₁ ; false → t₂ })

fail : Term ℕ𝔻 A
fail = op (`fail , λ ())

----------------------------------------------------------------------
-- An example program

data Coin : Set where
  head   : Coin
  tail   : Coin

three-tosses : Term ℕ𝔻 (List Coin)
three-tosses = do
  coin₁ <- return head <|> return tail
  coin₂ <- return head <|> return tail
  coin₃ <- return head <|> return tail
  return (coin₁ ∷ coin₂ ∷ coin₃ ∷ [])

----------------------------------------------------------------------
-- Semantics (internal)

all-results : Term ℕ𝔻 A → List A
all-results = interp alg sub
  where
    -- Semancitcs for operations

    alg : ℕ𝔻 -Alg[ List A ]
    alg (`<|> , k)  = k true ++ k false
    alg (`fail , k) = []

    -- Semantics for variables

    sub : A → List A
    sub a =  a ∷ []

    -- Together `alg` and `sub` form an (internal) effect handler for
    -- nondeterministic computations. In a practical algebraic effects
    -- language/library, they're often unified. For example:
    --
    -- ```
    -- handler {
    --   return a  -> [a]
    --   t₁ <|> t₂ -> t₁ ++ t₂
    --   fail      -> []
    -- }
    -- ```

test : List (List Coin)
test = all-results three-tosses

-- An alternative semantics

one-result : Term ℕ𝔻 A → (Stream Bool → Maybe A)
one-result = interp alg sub
  where
    alg : ℕ𝔻 -Alg[ (Stream Bool → Maybe A) ]
    alg (`<|>  , k) s = k (hd s) (tl s)
    alg (`fail , k) _ = nothing

    sub : A → (Stream Bool → Maybe A)
    sub a _ = just a

test₂ : Maybe (List Coin)
test₂ = one-result three-tosses randoms
  where
    randoms : Stream Bool
    hd randoms           = true
    hd (tl randoms)      = false
    hd (tl (tl randoms)) = true
    tl (tl (tl randoms)) = randoms

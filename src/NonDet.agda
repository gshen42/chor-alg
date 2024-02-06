----------------------------------------------------------------------
-- Nondeterministic computations
----------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

module NonDet where

open import AlgEff
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; [_,_])
open import Data.Unit using (⊤)

private
  variable
    A : Set

----------------------------------------------------------------------
-- Signature

data Op : Set where
  `choose : Op
  `fail   : Op

Arity : Op → Set
Arity `choose = Bool
Arity `fail   = ⊥

NonDet : Sig _ _
NonDet = Op ◁ Arity

----------------------------------------------------------------------
-- Operations

choose : Term NonDet Bool
choose = op (`choose , return)

fail : Term NonDet A
fail = op (`fail , λ ())

_<|>_ : Term NonDet A → Term NonDet A → Term NonDet A
t₁ <|> t₂ = op (`choose , λ { true → t₁ ; false → t₂ })

----------------------------------------------------------------------
-- Semantics

all-results : Term NonDet A → List A
all-results = interp alg sub
  where
    -- Semancitcs for operations

    alg : NonDet -Alg[ List A ]
    alg (`choose , k) = k true ++ k false
    alg (`fail   , k) = []

    -- Semantics for variables

    sub : A → List A
    sub a =  a ∷ []

-- An alternative semantics

one-result : Term NonDet A → Σ[ I ∈ Set ] (I → A)
one-result = interp alg sub
  where
    alg : NonDet -Alg[ Σ[ I ∈ Set ] (I → A) ]
    alg (`choose  , k) = let (I₁ , f₁) = k true
                             (I₂ , f₂) = k false
                         in (I₁ ⊎ I₂ ) , [ f₁ , f₂ ]
    alg (`fail    , k) = ⊥ , λ ()

    sub : A → Σ[ I ∈ Set ] (I → A)
    sub a = (⊤ , λ _ → a)

----------------------------------------------------------------------
-- Examples

data Coin : Set where
  head   : Coin
  tail   : Coin

_≡ᵇ_ : Coin → Coin → Bool
head ≡ᵇ head = true
tail ≡ᵇ tail = true
_    ≡ᵇ _    = false

three-tosses : Term NonDet (List Coin)
three-tosses = do
  coin₁ <- return head <|> return tail
  coin₂ <- return head <|> return tail
  coin₃ <- return head <|> return tail
  if coin₁ ≡ᵇ coin₂
    then fail
    else return (coin₁ ∷ coin₂ ∷ coin₃ ∷ [])

test : List (List Coin)
test = all-results three-tosses

test₂ : Σ[ I ∈ Set ] (I → List Coin)
test₂ = one-result three-tosses

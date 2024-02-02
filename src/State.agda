{-# OPTIONS --guardedness #-}

open import Agda.Primitive renaming (Set to Type)

module State where

open import AlgEff
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

----------------------------------------------------------------------
-- Signature of statuful compuations

data Op (S : Type) : Type where
  `get : Op S
  `put : S → Op S

Arity : ∀ {S} → Op S → Type
Arity {S} `get = S
Arity (`put _) = ⊤

State : Type → Sig
State S = Op S ◁ Arity

----------------------------------------------------------------------
-- Smart constructors

get : ∀ {S} → Term (State S) S
get = op (`get , return)

put : ∀ {S} → S → Term (State S) ⊤
put s = op (`put s , return)

----------------------------------------------------------------------
-- An example program

inc : Term (State ℕ) ℕ
inc = do
  x ← get
  _ ← put (x + 1)
  return x

----------------------------------------------------------------------
-- Semantics

private
  variable
    S A : Type

st-trans : Term (State S) A → (S → A × S)
st-trans = interp alg sub
  where
    alg : (State S) -Alg[ (S → A × S) ]
    alg (`get   , k) = λ s → k s s
    alg (`put s , k) = λ _ → k tt s

    sub : A → (S → A × S)
    sub a = λ s → a , s

test : ℕ × ℕ
test = st-trans inc 10

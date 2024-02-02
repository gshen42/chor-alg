{-# OPTIONS --guardedness #-}

module StateInteract where

open import AlgEff
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import State

inc′ : Term (State ℕ) ℕ
inc′ = do
  x ← get
  _ ← put (x + 1)
  x <- get
  return x

open CoTerm

mem : CoTerm (State ℕ) ⊤
covar mem = tt
coop  mem = `get , 42 , mem′
  where
   mem′ : CoTerm (State ℕ) ⊤
   covar mem′ = tt
   coop  mem′ = `put (42 + 1) , tt , mem″
     where
       mem″ : CoTerm (State ℕ) ⊤
       covar mem″ = tt
       coop  mem″ = `get , 43 , mem

correct : inc′ ⇔ mem
correct = step refl (step refl (step refl done))

mem-bad : CoTerm (State ℕ) ⊤
covar mem-bad = tt
coop  mem-bad = `get , 42 , mem-bad

wrong : inc′ ⇔ mem-bad → ⊥
wrong (step refl (step () _))

{-# OPTIONS --guardedness #-}

open import Agda.Primitive renaming (Set to Type)

module State where

open import AlgEff
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Op (S : Type) : Type where
  `get : Op S
  `put : S → Op S

Arity : ∀ {S} → Op S → Type
Arity {S} `get = S
Arity (`put _) = ⊤

𝕊 : Type → Sig
𝕊 S = Op S ◁ Arity

get : ∀ {S} → Term (𝕊 S) S
get = op (`get , return)

put : ∀ {S} → S → Term (𝕊 S) ⊤
put s = op (`put s , return)

inc : Term (𝕊 ℕ) ℕ
inc = do
  x ← get
  _ ← put (x + 1)
  x ← get
  return x

open CoTerm

mem : CoTerm (𝕊 ℕ) ⊤
covar mem = tt
coop  mem = `get , 42 , mem′
  where
   mem′ : CoTerm (𝕊 ℕ) ⊤
   covar mem′ = tt
   coop  mem′ = `put (42 + 1) , tt , mem″
     where
       mem″ : CoTerm (𝕊 ℕ) ⊤
       covar mem″ = tt
       coop  mem″ = `get , 43 , mem

correct : inc ⇔ mem
correct = step refl (step refl (step refl done))

mem-bad : CoTerm (𝕊 ℕ) ⊤
covar mem-bad = tt
coop  mem-bad = `get , 42 , mem-bad

wrong : inc ⇔ mem-bad → ⊥
wrong (step refl (step () _))

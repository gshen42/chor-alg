--------------------------------------------------------------------------------
--
--------------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Agda.Primitive renaming (Set to Type)

module State where

open import AlgEff
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

data Op (S : Type) : Type where
  `get : Op S
  `put : S → Op S

Ar : ∀ {S} → Op S → Type
Ar {S} `get = S
Ar (`put _) = ⊤

𝕊 : Type → Sig
𝕊 S = Op S ◁ Ar

get : ∀ {S} → Free (𝕊 S) S
get = op (`get , return)

put : ∀ {S} → S → Free (𝕊 S) ⊤
put s = op (`put s , return)

inc : Free (𝕊 ℕ) ℕ
inc = do
  x ← get
  _ ← put (x + 1) 
  return x

state-alg : ∀ {S A} → (𝕊 S) -Alg[ (S → A × S) ]
state-alg (`get    , k) s₁ = k s₁ s₁
state-alg (`put s₂ , k) s₁ = k tt s₂

run-inc : ℕ × ℕ
run-inc = handle (λ x s → (x , s)) state-alg inc 42

state-coalg : ∀ {S} → (𝕊 S) -Coalg[ S ]
state-coalg w `get     = w , w
state-coalg w (`put s) = tt , s

{-# OPTIONS --guardedness #-}

module Compose where

open import AlgEff
open import Data.Bool using (Bool; true; false)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ; _+_)
open import Function using (_∘_)
open import NonDet using (ℕ𝔻; `<|>)
open import State using (𝕊; `put; `get)

_<|>⁺_ : ∀ {S A} → Term (ℕ𝔻 :+: 𝕊 S) A → Term (ℕ𝔻 :+: 𝕊 S) A → Term (ℕ𝔻 :+: 𝕊 S) A
t₁ <|>⁺ t₂ = op (inj₁ `<|> , λ { true → t₁ ; false → t₂ })

get⁺ : ∀ {S} → Term (ℕ𝔻 :+: 𝕊 S) S
get⁺ = op (inj₂ `get , return)

put⁺ : ∀ {S} → S → Term (ℕ𝔻 :+: 𝕊 S) ⊤
put⁺ s = op (inj₂ (`put s) , return)

prog : Term (ℕ𝔻 :+: 𝕊 ℕ) ⊤
prog = do
   n <- get⁺
   put⁺ n <|>⁺ put⁺ (n + 1)

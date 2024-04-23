open import AlgEff
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)

module Choreography.Choreo
  (Loc : Set) (_≟_ : (l l′ : Loc) → Dec (l ≡ l′))
  (𝕃 : Sig)
  where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Effectful renaming (monad to maybe-monad)
open import Data.Product using (_×_; _,_)
open import Effect.Monad using (RawMonad)
open import Function using (_∘_; case_of_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; trans; sym)
open import Relation.Nullary using (yes; no)

import Choreography.Process
open module Process = Choreography.Process Loc 𝕃 hiding (Op; Arity)

import Choreography.Network
open module Network = Choreography.Network Loc _≟_ 𝕃

open RawMonad ⦃...⦄

infix 20 _▷_
infix 20 _⇨_◇_

private
  variable
    ℓ     : Level
    A B   : Set
    a     : A
    l s r : Loc

----------------------------------------------------------------------
-- Located values

_＠_ : Set ℓ → Loc → Set ℓ
A ＠ l = Maybe A

instance
  ＠-monad : RawMonad {ℓ} (_＠ l)
  ＠-monad = maybe-monad

----------------------------------------------------------------------
-- Choreographies

data Op : Set₁ where
  `comm : (s r : Loc) → (Term 𝕃 A) ＠ s → Op

Arity : Op → Set _
Arity (`comm {A} _ r _) = A ＠ r

ℂ : Sig
ℂ = Op ◁ Arity

----------------------------------------------------------------------
-- Help functions

ℂhoreo : Set → Set _
ℂhoreo A = Term ℂ A

-- Local computations
-- use `\Tw` to type `▷`

_▷_ :  (s : Loc) → (Term 𝕃 A) ＠ s → Term ℂ (A ＠ s)
s ▷ t = perform (`comm s s t)

-- Communication
-- use `\r` to type `⇨`
-- use `\di` to type `◇`

_⇨_◇_ :  (s r : Loc) → (Term 𝕃 A) ＠ s → Term ℂ (A ＠ r)
s ⇨ r ◇ t = perform (`comm s r t)

----------------------------------------------------------------------
--

private
  variable
    n n′  : Network A
    t     : Term 𝕃 A
    k     : Maybe A → ℂhoreo B
    k′ k″ : A → ℙrocess B
    c     : ℂhoreo A

data _~_ {A} : ℂhoreo A → Network A → Set₁ where

  done : var a ~ (\_ → var a)

  step-▷ :
    s ≡ r →
    n s ≡ op (`locally t , k′) →
    k (just (𝕃-handler t)) ~ update s (k′ (𝕃-handler t)) n →
    op (`comm s r (just t) , k) ~ n

  step-⇨ :
    s ≢ r →
    n s ≡ op (`send r t , k′) →
    n r ≡ op (`recv s , k″) →
    k (just (𝕃-handler t)) ~ update s (k′ tt) (update r (k″ (𝕃-handler t)) n) →
    op (`comm s r (just t) , k) ~ n

  step-nothing :
    k nothing ~ n →
    op (`comm s r nothing , k) ~ n

subst~ : n′ ≡ n → c ~ n → c ~ n′
subst~ refl x = x

~implies✓ : c ~ n → n ✓
~implies✓ done             = ✓-done λ _ → _ , refl
~implies✓ (step-▷ _ x y)   = ✓-step (local⇒ⁿ x) (~implies✓ y)
~implies✓ (step-⇨ _ x y z) = ✓-step (comm⇒ⁿ x y) (~implies✓ z)
~implies✓ (step-nothing x) = ~implies✓ x

----------------------------------------------------------------------
-- Endpoint projection

alg : Loc → ℂ -Alg[ ℙrocess A ]
alg l (`comm s r nothing  , k) = k nothing
alg l (`comm s r (just t) , k) with l ≟ s | l ≟ r
... | yes _ | yes _ = locally t >>= k ∘ just
... | yes _ | no  _ = send r t >>= \_ →  k nothing
... | no _  | yes _ = recv s >>= k ∘ just
... | no _  | no _  = k nothing

epp : ℂhoreo A → Loc → ℙrocess A
epp c l = interp (alg l) var c

----------------------------------------------------------------------
-- Deadlock Freedom of EPP

epp-▷-norm : s ≡ r →
             epp (op (`comm s r (just t) , k)) s ≡ op (`locally t , \x → epp (k (just x)) s)
epp-▷-norm {s = s} {r = r} s≡r with s ≟ s | s ≟ r
... | yes _  | yes _  = refl
... | yes _  | no s≢r = ⊥-elim (s≢r s≡r)
... | no s≢s | _      = ⊥-elim (s≢s refl)

epp-⇨-norm₁ : s ≢ r →
              epp (op (`comm s r (just t) , k)) s ≡ op (`send r t , \_ → epp (k nothing) s)
epp-⇨-norm₁ {s = s} {r = r} s≢r with s ≟ s | s ≟ r
... | yes _  | yes s≡r = ⊥-elim (s≢r s≡r)
... | yes _  | no  _   = refl
... | no s≢s | _       = ⊥-elim (s≢s refl)

epp-⇨-norm₂ : s ≢ r →
              epp (op (`comm s r (just t) , k)) r ≡ op (`recv s , \x → epp (k (just x)) r)
epp-⇨-norm₂ {s = s} {r = r} s≢r with r ≟ s | r ≟ r
... | yes r≡s | yes _  = ⊥-elim (s≢r (sym r≡s))
... | no _    | yes _  = refl
... | _       | no r≢r = ⊥-elim (r≢r refl)

postulate
  lemma₁ : s ≡ r →
           update s (epp (k (just (𝕃-handler t))) s) (epp (op (`comm s r (just t) , k))) ≡ epp (k (just (𝕃-handler t)))

  lemma₂ : s ≢ r →
           update s (epp (k nothing) s) (update r (epp (k (just (𝕃-handler t))) r) (epp (op (`comm s r (just t) , k)))) ≡ epp (k (just (𝕃-handler t)))

epp~ : ∀ (c : ℂhoreo A) → c ~ epp c
epp~ (var x) = done
epp~ (op (`comm s r nothing  , k)) = step-nothing (epp~ (k nothing))
epp~ (op (`comm s r (just t) , k)) with s ≟ r
... | yes s≡r = step-▷ s≡r (epp-▷-norm {k = k} s≡r) (subst~ (lemma₁ {k = k} s≡r) (epp~ (k (just (𝕃-handler t)))))
... | no s≢r  = step-⇨ s≢r (epp-⇨-norm₁ {k = k} s≢r) (epp-⇨-norm₂ {k = k} s≢r) (subst~ (lemma₂ {k = k} s≢r) (epp~ (k (just (𝕃-handler t)))))

epp✓ : ∀ (c : ℂhoreo A) → (epp c) ✓
epp✓ = ~implies✓ ∘ epp~

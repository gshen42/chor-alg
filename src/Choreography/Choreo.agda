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
    k (just (𝕃-handler t)) ~ update s (k′ (𝕃-handler t)) n →
    op (`comm s r (just t) , k) ~ update s (op (`locally t , k′)) n

  step-⇨ :
    s ≢ r →
    k (just (𝕃-handler t)) ~ update s (k′ tt) (update r (k″ (𝕃-handler t)) n) →
    op (`comm s r (just t) , k) ~ update s (op (`send r t , k′)) (update r (op (`recv s , k″)) n)

  step-nothing :
    k nothing ~ n →
    op (`comm s r nothing , k) ~ n

subst~ : n′ ≡ n → c ~ n → c ~ n′
subst~ refl x = x

foo : c ~ n → n ✓
foo done             = ✓-done λ _ → _ , refl
foo (step-▷ _ x)     = ✓-step local⇒ⁿ (foo x)
foo (step-⇨ _ x)     = ✓-step comm⇒ⁿ (foo x)
foo (step-nothing x) = foo x

----------------------------------------------------------------------
-- Endpoint projection

alg : Loc → ℂ -Alg[ ℙrocess A ]
alg l (`comm s r nothing  , k) = k nothing
alg l (`comm s r (just t) , k) = case (s ≟ r , l ≟ s , l ≟ r) of λ
  { (yes _ , yes _ , _    ) → locally t >>= k ∘ just
  ; (yes _ , no _  , _    ) → k nothing
  ; (no x  , yes y , yes z) → ⊥-elim (x (trans (sym y) z))
  ; (no _  , yes _ , no _ ) → send r t >> k nothing
  ; (no _  , no _  , yes _) → recv s >>= k
  ; (no _  , no _  , no _ ) → k nothing
  }

epp : ℂhoreo A → Loc → ℙrocess A
epp c l = interp (alg l) var c

postulate
  lemma : ∀ {l} {o : Op} {k⋆ : Arity o → ℂhoreo A} {a⋆ : Arity o} →
          epp (k⋆ a⋆) ≡ update l (epp (k⋆ a⋆) l) (epp (op (o , k⋆)))

  lemma₁ : ∀ {t : Term 𝕃 A} {k : Maybe A → ℂhoreo B} →
    s ≡ r →
    epp (op (`comm s r (just t) , k)) ≡ update s (locally t >>= (λ n → n s) ∘ epp ∘ k ∘ just) (epp (k nothing))

bar : ∀ (c : ℂhoreo A) → c ~ epp c
bar (var x) = done
bar (op (`comm s r nothing  , k)) = step-nothing (bar (k nothing))
bar (op (`comm s r (just t) , k)) = case s ≟ r of λ
  { (yes s≡r) → subst~ (lemma₁ {k = k} s≡r) (step-▷ s≡r (subst~ {!!} (bar (k (just (𝕃-handler t))))))
  ; (no  s≢r) → {!!}
  }

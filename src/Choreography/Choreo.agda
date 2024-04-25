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
open import Effect.Monad.MyStuff using (mkRawMonad)
open import Function using (_∘_; case_of_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; trans; sym)
open import Relation.Nullary using (yes; no)

import Choreography.Process
open module Process = Choreography.Process Loc 𝕃 hiding (Op; Arity)

import Choreography.Network
open module Network = Choreography.Network Loc _≟_ 𝕃

open RawMonad ⦃...⦄

infix 20 ⦉_⦊
infix 20 _▷_
infix 20 _⇨_◇_

private
  variable
    ℓ       : Level
    A B     : Set ℓ
    a       : A
    l s r u : Loc

----------------------------------------------------------------------
-- Located values

data _＠_ (A : Set ℓ) (l : Loc) : Set ℓ where
  ϵ   : A ＠ l
  ⦉_⦊ : A → A ＠ l

instance
  ＠-monad : RawMonad {ℓ} (_＠ l)
  ＠-monad = mkRawMonad _ ⦉_⦊ ＠-bind
    where
    ＠-bind : A ＠ l → (A → B ＠ l) → B ＠ l
    ＠-bind ϵ     f = ϵ
    ＠-bind ⦉ x ⦊ f = f x

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
-- Endpoint projection

alg : Loc → ℂ -Alg[ ℙrocess A ]
alg l (`comm s r ϵ  , k) = k ϵ
alg l (`comm s r ⦉ t ⦊ , k) with l ≟ s | l ≟ r
... | yes _ | yes _ = locally t >>= k ∘ ⦉_⦊
... | yes _ | no  _ = send r t >>= \_ →  k ϵ
... | no _  | yes _ = recv s >>= k ∘ ⦉_⦊
... | no _  | no _  = k ϵ

epp : ℂhoreo A → Loc → ℙrocess A
epp c l = interp (alg l) var c

----------------------------------------------------------------------
-- Deadlock Freedom of EPP

private
  variable
    n n′  : Network A
    t     : Term 𝕃 A
    k     : A ＠ l → ℂhoreo B
    k′ k″ : A → ℙrocess B
    c     : ℂhoreo A

postulate
  fun-ext : ∀ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} {f g : A → B} →
            (∀ a → f a ≡ g a) → f ≡ g

  irrelevance : ∀ {k : A ＠ r → ℂhoreo B} {x y : A ＠ r} →
                l ≢ r → epp (k x) l ≡ epp (k y) l

epp-▷-norm : s ≡ r →
             epp (op (`comm s r ⦉ t ⦊ , k)) s ≡ op (`locally t , \x → epp (k ⦉ x ⦊) s)
epp-▷-norm {s = s} {r = r} s≡r with s ≟ s | s ≟ r
... | yes _  | yes _  = refl
... | yes _  | no s≢r = ⊥-elim (s≢r s≡r)
... | no s≢s | _      = ⊥-elim (s≢s refl)

epp-⇨-norm₁ : s ≢ r →
              epp (op (`comm s r ⦉ t ⦊ , k)) s ≡ op (`send r t , \_ → epp (k ϵ) s)
epp-⇨-norm₁ {s = s} {r = r} s≢r with s ≟ s | s ≟ r
... | yes _  | yes s≡r = ⊥-elim (s≢r s≡r)
... | yes _  | no  _   = refl
... | no s≢s | _       = ⊥-elim (s≢s refl)

epp-⇨-norm₂ : s ≢ r →
              epp (op (`comm s r ⦉ t ⦊ , k)) r ≡ op (`recv s , \x → epp (k ⦉ x ⦊) r)
epp-⇨-norm₂ {s = s} {r = r} s≢r with r ≟ s | r ≟ r
... | yes r≡s | yes _  = ⊥-elim (s≢r (sym r≡s))
... | no _    | yes _  = refl
... | _       | no r≢r = ⊥-elim (r≢r refl)

opaque
  unfolding update

  lemma₁ : s ≡ r → ∀ l → epp (k ⦉ 𝕃-handler t ⦊) l ≡ update s (epp (k ⦉ 𝕃-handler t ⦊) s) (epp (op (`comm s r ⦉ t ⦊ , k))) l
  lemma₁ {s = s} {r = r} {k = k} s≡r l with s ≟ l
  ... | yes refl = refl
  ... | no s≢l with l ≟ s | l ≟ r
  ...          | yes l≡s | _       = ⊥-elim (s≢l (sym l≡s))
  ...          | no  _   | yes l≡r = ⊥-elim (s≢l (trans s≡r (sym l≡r)))
  ...          | no l≢s  | no l≢r  = irrelevance {k = k} l≢r

  lemma₂ : s ≢ r → ∀ l → epp (k ⦉ 𝕃-handler t ⦊) l ≡ update s (epp (k ϵ) s) (update r (epp (k ⦉ 𝕃-handler t ⦊) r) (epp (op (`comm s r ⦉ t ⦊ , k)))) l
  lemma₂ {s = s} {r = r} {k = k} s≢r l with s ≟ l
  ... | yes refl = irrelevance {k = k} s≢r
  ... | no  s≢r  with r ≟ l
  ...            | yes refl = refl
  ...            | no  r≢l  with l ≟ s | l ≟ r
  ...                       | yes refl | yes _    = ⊥-elim (s≢r refl)
  ...                       | yes refl | no  _    = ⊥-elim (s≢r refl)
  ...                       | no  _    | yes refl = ⊥-elim (r≢l refl)
  ...                       | no _     | no _     = irrelevance {k = k} \x → ⊥-elim (r≢l (sym x))

epp✓ : ∀ (c : ℂhoreo A) → (epp c) ✓
epp✓ (var x) = ✓-done \_ → _ , refl
epp✓ (op (`comm s r ϵ     , k)) = epp✓ (k ϵ)
epp✓ (op (`comm s r ⦉ t ⦊ , k)) with s ≟ r
... | yes s≡r = ✓-step (local⇒ⁿ {l = s} (epp-▷-norm {k = k} s≡r)) (subst (_✓) (fun-ext (lemma₁ {k = k} s≡r)) (epp✓ (k ⦉ 𝕃-handler t ⦊)))
... | no  s≢r = ✓-step (comm⇒ⁿ {s = s} {r = r} (epp-⇨-norm₁ {k = k} s≢r) (epp-⇨-norm₂ {k = k} s≢r)) (subst (_✓) (fun-ext (lemma₂ {k = k} s≢r)) (epp✓ (k ⦉ 𝕃-handler t ⦊)))

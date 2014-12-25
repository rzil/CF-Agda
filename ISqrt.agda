module ISqrt where

-- integer square roots
-- http://en.wikipedia.org/wiki/Integer_square_root

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.DivMod
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Function
open import Data.Unit hiding (_≤_; _≤?_; _≟_)
--open import Induction.WellFounded
--open import Induction.Nat

_IsIntegerSqrtOf_ : ℕ → ℕ → Set
_IsIntegerSqrtOf_ n m = n * n ≤ m × m ≤ (suc n) * (suc n)

_√?_ : Decidable {A = ℕ} _IsIntegerSqrtOf_
_√?_ n m with (n * n) ≤? m | m ≤? ((suc n) * (suc n))
... | yes x | yes y = yes (x , y)
... | no x | _ = no (x ∘ proj₁)
... | _ | no y = no (y ∘ proj₂)

√0≡0 : 0 IsIntegerSqrtOf 0
√0≡0 = z≤n , z≤n

√1≡1 : 1 IsIntegerSqrtOf 1
√1≡1 = s≤s z≤n , s≤s z≤n

√10≡3 : 3 IsIntegerSqrtOf 10
√10≡3 = from-yes (3 √? 10)

step : ℕ → (x : ℕ) → {x≢0 : False (x ≟ 0)} → ℕ
step _ 0 {()}
step n (suc x-1) {1≤x} = (x + (n div x)) div 2
 where x = suc x-1

bung : ∀ {n m} {m≢0 : False (m ≟ 0)} → _div_ n m {m≢0} ≡ 0 → n < m
bung = {!!}

step≢0 : ∀ n x {n≢0 : False (n ≟ 0)} {x≢0 : False (x ≟ 0)} → ¬ step n x {x≢0} ≡ 0
step≢0 n x fnx≡0 = {!!}

thm : ∀ n x {x≢0 : False (x ≟ 0)} {n<x*x : n < x * x} → step n x {x≢0} <′ x
thm = {!!}

data Terminates (n x : ℕ) : Set where
  termination-proof : (∀ y → (y <′ x) → Terminates n y) → Terminates n x

isqrtGo : (n : ℕ) → (x : ℕ) → {x≢0 : False (x ≟ 0)} → Terminates n x → ℕ
isqrtGo 0 _ _ = 0
isqrtGo _ 0 {()}
isqrtGo (suc n-1) (suc x-1) {_} (termination-proof term) with (2 + n-1) ≤? ((suc x-1) * (suc x-1))
... | no _ = suc x-1
... | yes n<x*x = isqrtGo (suc n-1) (step (suc n-1) (suc x-1) {tt}) {fromWitnessFalse (step≢0 (suc n-1) (suc x-1))} (term (step (suc n-1) (suc x-1) {tt}) (thm (suc n-1) (suc x-1) {tt} {n<x*x}))

baseCase : ∀ {n} y → (y <′ zero) → Terminates n y
baseCase _ ()

generateTerminationProof : ∀ {n} y → Terminates n y

induction : ∀ {m} (n : ℕ) → (y : ℕ) → (y <′ n) → Terminates m y
induction n zero _ = termination-proof baseCase
induction .(suc (suc y')) (suc y') ≤′-refl =  generateTerminationProof (suc y')
induction .(suc n) (suc y') (≤′-step {n} m≤′n) = induction n (suc y') m≤′n

generateTerminationProof zero = termination-proof baseCase
generateTerminationProof (suc limit) = termination-proof (induction (suc limit))

isqrt : ℕ → ℕ
isqrt 0 = 0
isqrt (suc n-1) = isqrtGo n n {tt} (generateTerminationProof n)
 where n = suc n-1

record ISqrt (n : ℕ) : Set where
 field
  ⌊√n⌋ : ℕ
  property : ⌊√n⌋ IsIntegerSqrtOf n

stepFixPoint : ∀ n x {x≢0 : False (x ≟ 0)} → step n x {x≢0} ≡ x → x IsIntegerSqrtOf n
stepFixPoint n x stepnx≡x = {!!}

stepTwoCycle : ∀ n x {x≢0 : False (x ≟ 0)} → step n x {x≢0} ≡ suc x → x IsIntegerSqrtOf n
stepTwoCycle n x stepnx≡1+x = {!!}

isqrtProof : (n : ℕ) → ISqrt n
isqrtProof n = record {
  ⌊√n⌋ = isqrt n;
  property = {!!}
 }

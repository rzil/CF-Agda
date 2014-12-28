module ISqrt where

-- integer square roots
-- http://en.wikipedia.org/wiki/Integer_square_root

open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.DivMod
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Function
open import Data.Fin as Fin renaming (_≤_ to _F≤_; _+_ to _F+_; _<_ to _F<_; zero to fzero; suc to fsuc)
open import Data.Fin.Properties hiding (_≟_)
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

private
 0<n→n≢0 : ∀ {n} → 0 < n → n ≢ 0
 0<n→n≢0 {zero} ()
 0<n→n≢0 {suc n} _ ()

 n≤0→n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
 n≤0→n≡0 {0} _ = refl
 n≤0→n≡0 {suc _} ()

 n≤n : ∀ n → n ≤ n
 n≤n zero = z≤n
 n≤n (suc n-1) = s≤s (n≤n n-1)

 k+[1+z]≡1+[k+z] : ∀ k z → k + (1 + z) ≡ 1 + (k + z)
 k+[1+z]≡1+[k+z] k z = begin
   k + (1 + z)   ≡⟨ sym (+-assoc k 1 z) ⟩
   (k + 1) + z   ≡⟨ cong (flip _+_ z) (+-comm k 1) ⟩
   (1 + k) + z   ≡⟨ +-assoc 1 k z ⟩
   1 + (k + z)   ∎
  where open ≡-Reasoning

cancel-*-right-< : ∀ i j k → i * suc k < j * suc k → i < j
cancel-*-right-< zero    zero       _ ()
cancel-*-right-< zero    (suc j-1)  _ _  = s≤s z≤n
cancel-*-right-< (suc i) zero    _ ()
cancel-*-right-< (suc i) (suc j) k le = s≤s (cancel-*-right-< i j k (cancel-+-left-≤ k lem))
 where open ≤-Reasoning
       lem : k + (suc (i * suc k)) ≤ k + j * suc k
       lem = begin k + (suc (i * suc k)) ≡⟨ k+[1+z]≡1+[k+z] k (i * suc k) ⟩ suc (k + i * suc k) ≤⟨ ≤-pred le ⟩  k + j * suc k ∎

div-right : ∀ n m k {k≢0 : False (k ≟ 0)} → n < m * k → _div_ n k {k≢0} < m
div-right _ _ 0 {()}
div-right n m (suc k-1) {k≢0} n<m*k = cancel-*-right-< (_div_ n k {k≢0}) m k-1 lem
 where open ≤-Reasoning
       n/k = n divMod (suc k-1)
       k = suc k-1
       lem : (_div_ n k {k≢0}) * k < m * k
       lem = begin
          suc ((_div_ n k {k≢0}) * k)                                    ≤⟨ s≤s (≤-steps (toℕ (DivMod.remainder n/k)) (n≤n ((DivMod.quotient n/k) * k))) ⟩
          suc (toℕ (DivMod.remainder n/k) + (DivMod.quotient n/k) * k)   ≡⟨ cong suc (sym (DivMod.property n/k)) ⟩
          suc n                                                          ≤⟨ n<m*k ⟩
          m * k   ∎

div-left : ∀ n m k {k≢0 : False (k ≟ 0)} → n < k * m → _div_ n k {k≢0} < m
div-left n m k {k≢0} n<k*m = div-right n m k {k≢0} (begin n <⟨ n<k*m ⟩ k * m ≡⟨ *-comm k m ⟩ m * k ∎)
 where open ≤-Reasoning

a<b→n+a<n+b : ∀ n {a b} → a < b → n + a < n + b
a<b→n+a<n+b zero a<b = a<b
a<b→n+a<n+b (suc n) a<b = s≤s (a<b→n+a<n+b n a<b)

thm : ∀ n x {x≢0 : False (x ≟ 0)} {n<x*x : n < x * x} → step n x {x≢0} <′ x
thm n 0 {()}
thm n (suc x-1) {_} {n<x*x} = ≤⇒≤′ (div-left (x + (n div x)) x 2 lem)
 where open ≤-Reasoning
       x = suc x-1
       lem : x + (n div x) < 2 * x
       lem = begin
         x + (n div x)         <⟨ a<b→n+a<n+b x (div-right n x x n<x*x) ⟩
         x + x                 ≡⟨ sym (+-right-identity _) ⟩
         (x + x) + 0           ≡⟨ +-assoc x x 0 ⟩
         2 * x                 ∎

n%1≡0 : ∀ n → toℕ (n mod 1) ≡ 0
n%1≡0 n = n≤0→n≡0 (≤-pred (bounded (n mod 1)))

*-right-identity : ∀ n → n * 1 ≡ n
*-right-identity n = begin n * 1 ≡⟨ *-comm n 1 ⟩ 1 * n ≡⟨ +-right-identity n ⟩ n ∎
 where open ≡-Reasoning

*-left-identity : ∀ n → 1 * n ≡ n
*-left-identity = +-right-identity

n/1≡n : ∀ {n} → n div 1 ≡ n
n/1≡n {n} = begin
   n div 1                         ≡⟨ sym (*-left-identity _) ⟩
   1 * (n div 1)                   ≡⟨ *-comm 1 (n div 1) ⟩
   (n div 1) * 1                   ≡⟨ sym refl ⟩
   0 + ((n div 1) * 1)             ≡⟨ cong (flip _+_ _) (sym (n%1≡0 n)) ⟩
   toℕ (n mod 1) + ((n div 1) * 1) ≡⟨ sym (DivMod.property dm) ⟩
   n ∎
 where dm = n divMod 1
       open ≡-Reasoning

toℕ-inject₁ : ∀ {n} i → toℕ {n} i ≡ toℕ (inject₁ i)
toℕ-inject₁ fzero = refl
toℕ-inject₁ (fsuc i) = cong suc (toℕ-inject₁ i)

mod-class : ∀ n k → n mod (suc k) ≡ (n + (suc k)) mod (suc k)
mod-class n k = {!DivMod.property ((n + (suc k)) divMod (suc k))!}

div-class : ∀ n k → suc (n div (suc k)) ≡ (n + (suc k)) div (suc k)
div-class n k = {!!}

div-pred : ∀ n k → (suc n) mod (suc k) ≢ fzero → (suc n) div (suc k) ≡ n div (suc k)
div-pred n k x with n div (suc k) | (suc n) div (suc k)
... | 0 | 0 = refl
... | suc _ | 0 = {!!}
... | 0 | suc _ = {!!}
... | suc n/[1+k] | suc [1+n]/[1+k] = {!div-class (suc (n ∸ suc k)) (n ∸ suc k) k (div-pred (n ∸ (suc k)) k ?)!}

cancel-+-right : ∀ i {j k} → j + i ≡ k + i → j ≡ k
cancel-+-right i {j} {k} eq = cancel-+-left i {j} {k} (begin i + j ≡⟨ +-comm i j ⟩ j + i ≡⟨ eq ⟩ k + i ≡⟨ +-comm k i ⟩ i + k ∎)
 where open ≡-Reasoning

cancel-toℕ : ∀ {n} i j → toℕ {n} i ≡ toℕ j → i ≡ j
cancel-toℕ fzero fzero eq = refl
cancel-toℕ fzero (fsuc _) ()
cancel-toℕ (fsuc _) fzero ()
cancel-toℕ (fsuc i) (fsuc j) eq = cong fsuc (cancel-toℕ i j (cong Nat.pred eq))

cancel-inject₁ : ∀ {n} i j → inject₁ {n} i ≡ inject₁ j → i ≡ j
cancel-inject₁ fzero fzero eq = refl
cancel-inject₁ fzero (fsuc _) ()
cancel-inject₁ (fsuc _) fzero ()
cancel-inject₁ {suc n} (fsuc i-1) (fsuc j-1) eq = cong fsuc (cancel-inject₁ i-1 j-1 (cong (λ {fzero → fzero; (fsuc z) → reduce≥ (fsuc z) (s≤s z≤n)}) eq))

mod-pred : ∀ n k i → (suc n) mod (suc k) ≡ fsuc i → n mod (suc k) ≡ (inject₁ i)
mod-pred n k i [1+n]%[1+k]≡[1+i] = cancel-inject₁ _ _ (cong Fin.pred (cancel-toℕ _ _ lem₁))
 where open ≡-Reasoning
       lem₀ : (toℕ (fsuc (n mod (suc k)))) + (n div (suc k)) * (suc k) ≡ toℕ (fsuc i) + (n div (suc k)) * (suc k)
       lem₀ = begin
          (toℕ (fsuc (n mod (suc k)))) + (n div (suc k)) * (suc k)     ≡⟨ sym (cong suc (DivMod.property (n divMod (suc k)))) ⟩
          suc n                                                        ≡⟨ DivMod.property ((suc n) divMod (suc k)) ⟩
          toℕ ((suc n) mod (suc k)) + ((suc n) div (suc k)) * (suc k)  ≡⟨ cong (λ z → toℕ z + ((suc n) div (suc k)) * (suc k)) [1+n]%[1+k]≡[1+i] ⟩
          toℕ (fsuc i) + ((suc n) div (suc k)) * (suc k)               ≡⟨ cong (λ z → toℕ (fsuc i) + z * (suc k)) (div-pred n k (λ z → contradiction (begin fzero ≡⟨ sym z ⟩ (suc n) mod (suc k) ≡⟨ [1+n]%[1+k]≡[1+i] ⟩ fsuc i ∎) (λ ()))) ⟩
          toℕ (fsuc i) + (n div (suc k)) * (suc k)  ∎
       lem₁ : toℕ (fsuc (n mod (suc k))) ≡ toℕ (inject₁ (fsuc i))
       lem₁ = begin _ ≡⟨ cancel-+-right _ lem₀ ⟩ toℕ (fsuc i) ≡⟨ toℕ-inject₁ _ ⟩ _ ∎

div-monotonic : ∀ n k {k≢0 : False (k ≟ 0)} → _div_ n k {k≢0} ≤ _div_ (suc n) k {k≢0}
div-monotonic _ 0 {()}
div-monotonic n (suc k-1) {k≢0} with _mod_ (suc n) (suc k-1) {k≢0} | inspect (λ z → _mod_ z (suc k-1) {k≢0}) (suc n)
... | fzero | [ eq ] = cancel-*-right-≤ _ _ k-1 lem₁
 where k = suc k-1
       [1+n]%k≡0 : (suc n) mod k ≡ fzero
       [1+n]%k≡0 = eq
       lem₀ : (suc (toℕ (n mod k))) + (n div k) * k ≡ ((suc n) div k) * k
       lem₀ = begin
          (suc (toℕ (n mod k))) + (n div k) * k       ≡⟨ sym (cong suc (DivMod.property (n divMod k))) ⟩
          suc n                                       ≡⟨ DivMod.property ((suc n) divMod k) ⟩
          toℕ ((suc n) mod k) + ((suc n) div k) * k   ≡⟨ cong (λ z → toℕ z + ((suc n) div k) * k)  [1+n]%k≡0  ⟩
          ((suc n) div k) * k                         ∎
        where open ≡-Reasoning
       lem₁ : (n div k) * k ≤ ((suc n) div k) * k
       lem₁ = begin
         (n div k) * k                                 ≤⟨ ≤-steps (suc (toℕ (n mod k))) (n≤n _) ⟩
         (suc (toℕ (n mod k))) + (n div k) * k         ≡⟨ lem₀ ⟩
         ((suc n) div k) * k                           ∎
        where open ≤-Reasoning
... | fsuc i | [ eq ] = begin n div k ≡⟨ sym lem₁ ⟩ (suc n) div k ∎
 where k = suc k-1
       n_dm = n divMod k
       [1+n]_dm = (suc n) divMod k
       [1+n]%k≡1+i : (suc n) mod k ≡ fsuc i
       [1+n]%k≡1+i = eq
       n%k≡i : n mod k ≡ (inject₁ i)
       n%k≡i = mod-pred n k-1 i [1+n]%k≡1+i
       lem₀ : toℕ (fsuc i) + ((suc n) div k) * k ≡ toℕ (fsuc i) + (n div k) * k
       lem₀ = begin
         toℕ (fsuc i) + ((suc n) div k) * k            ≡⟨ cong (λ z → toℕ z + ((suc n) div k) * k) {fsuc i} {(suc n) mod k} (sym [1+n]%k≡1+i) ⟩
         toℕ ((suc n) mod k) + ((suc n) div k) * k     ≡⟨ sym (DivMod.property [1+n]_dm) ⟩
         suc n                                         ≡⟨ cong suc (DivMod.property n_dm) ⟩
         suc (toℕ (n mod k) + (n div k) * k)           ≡⟨ sym (+-assoc 1 (toℕ (n mod k)) _) ⟩
         (suc (toℕ (n mod k))) + (n div k) * k         ≡⟨ cong (flip _+_ ((n div k) * k)) {suc (toℕ (n mod k))} refl ⟩
         (toℕ (fsuc (n mod k))) + (n div k) * k        ≡⟨ cong (λ z → toℕ (fsuc z) + (n div k) * k) n%k≡i ⟩
         toℕ (fsuc (inject₁ i)) + (n div k) * k        ≡⟨ cong (λ z → (suc z) + (n div k) * k) (sym (toℕ-inject₁ i)) ⟩
         toℕ (fsuc i) + (n div k) * k                  ∎
        where open ≡-Reasoning
       lem₁ : (suc n) div k ≡ n div k
       lem₁ = cancel-*-right _ _ (cancel-+-left (toℕ (fsuc i)) lem₀)
       open ≤-Reasoning

div-blam : ∀ n m k {k≢0 : False (k ≟ 0)} → _div_ n k {k≢0} ≤ _div_ (m + n) k {k≢0}
div-blam _ _ 0 {()}
div-blam _ zero _ = n≤n _
div-blam n (suc m-1) (suc k-1) = begin
   n div k                ≤⟨ div-blam n m-1 k ⟩
   (m-1 + n) div k        ≤⟨ div-monotonic (m-1 + n) k ⟩
   (suc (m-1 + n)) div k  ≡⟨ cong (λ z → z div k) (sym (+-assoc 1 m-1 n)) ⟩
   (m + n) div k          ∎
 where open ≤-Reasoning
       m = suc m-1
       k = suc k-1

m∸n+n≡m : ∀ n m → n ≤ m → (m ∸ n) + n ≡ m
m∸n+n≡m zero m _ = +-right-identity m
m∸n+n≡m (suc _) zero ()
m∸n+n≡m (suc n-1) (suc m-1) n≤m = begin
   (m ∸ n) + n                 ≡⟨ sym (+-assoc (m-1 ∸ n-1) 1 n-1) ⟩
   ((m-1 ∸ n-1) + 1) + n-1     ≡⟨ cong (flip _+_ n-1) (+-comm (m-1 ∸ n-1) 1) ⟩
   suc ((m-1 ∸ n-1) + n-1)     ≡⟨ cong suc (m∸n+n≡m n-1 m-1 (≤-pred n≤m)) ⟩
   m                           ∎
 where open ≡-Reasoning
       n = suc n-1
       m = suc m-1

≤-div : ∀ n m k {k≢0 : False (k ≟ 0)} → n ≤ m → _div_ n k {k≢0} ≤ _div_ m k {k≢0}
≤-div n m k {k≢0} n≤m = begin
   _div_ n k {k≢0}              ≤⟨ div-blam n (m ∸ n) k ⟩
   _div_ (m ∸ n + n) k {k≢0}    ≡⟨ cong (λ z → _div_ z k {k≢0}) (m∸n+n≡m n m n≤m) ⟩
   _div_ m k {k≢0}              ∎
 where open ≤-Reasoning

step≢0 : ∀ n x {n≢0 : False (n ≟ 0)} {x≢0 : False (x ≟ 0)} → ¬ step n x {x≢0} ≡ 0
step≢0 0 _ {()}
step≢0 _ 0 {_} {()}
step≢0 1 1 ()
step≢0 (suc (suc n-2)) 1 = 0<n→n≢0 lem₂
 where n = 2 + n-2
       lem₀ : (step n 1) ≡ ((suc n) div 2)
       lem₀ = cong (λ z → (1 + z) div 2) {n div 1} {n} n/1≡n
       lem₁ : 0 < (suc n) div 2
       lem₁ = ≤-div 2 (suc n) 2 (s≤s (s≤s z≤n))
       open ≤-Reasoning
       lem₂ : 0 < step n 1
       lem₂ = begin 0 <⟨ lem₁ ⟩ (suc n) div 2 ≡⟨ sym lem₀ ⟩ step n 1 ∎
step≢0 (suc n-1) (suc (suc x-2)) fnx≡0 = {!!}

data Terminates (n x : ℕ) : Set where
  termination-proof : (∀ y → (y <′ x) → Terminates n y) → Terminates n x

isqrtGo : (n : ℕ) → (x : ℕ) → {x≢0 : False (x ≟ 0)} → Terminates n x → ℕ
isqrtGo 0 _ _ = 0
isqrtGo _ 0 {()}
isqrtGo (suc n-1) (suc x-1) {_} (termination-proof term) with (2 + n-1) ≤? ((suc x-1) * (suc x-1))
... | no _ = suc x-1
... | yes n<x*x = isqrtGo n (step n x {tt}) {fromWitnessFalse (step≢0 n x)}
                  (term (step n x {tt}) (thm n x {tt} {n<x*x}))
 where n = suc n-1
       x = suc x-1

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

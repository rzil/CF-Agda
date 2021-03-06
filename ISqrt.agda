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

open import Lemmas
open import DivModUniqueness

_IsIntegerSqrtOf_ : ℕ → ℕ → Set
_IsIntegerSqrtOf_ n m = n * n ≤ m × m < (suc n) * (suc n)

_√?_ : Decidable {A = ℕ} _IsIntegerSqrtOf_
_√?_ n m with (n * n) ≤? m | suc m ≤? ((suc n) * (suc n))
... | yes x | yes y = yes (x , y)
... | no x | _ = no (x ∘ proj₁)
... | _ | no y = no (y ∘ proj₂)

√0≡0 : 0 IsIntegerSqrtOf 0
√0≡0 = z≤n , s≤s z≤n

√1≡1 : 1 IsIntegerSqrtOf 1
√1≡1 = s≤s z≤n , s≤s (s≤s z≤n)

√10≡3 : 3 IsIntegerSqrtOf 10
√10≡3 = from-yes (3 √? 10)

step : ℕ → (x : ℕ) → {x≢0 : False (x ≟ 0)} → ℕ
step _ 0 {()}
step n (suc x-1) = (x + (n div x)) div 2
 where x = suc x-1

private
 0<n→n≢0 : ∀ {n} → 0 < n → n ≢ 0
 0<n→n≢0 {zero} ()
 0<n→n≢0 {suc n} _ ()

 n≤0→n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
 n≤0→n≡0 {0} _ = refl
 n≤0→n≡0 {suc _} ()

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

step-decreasing : ∀ n x {x≢0 : False (x ≟ 0)} {n<x*x : n < x * x} → step n x {x≢0} <′ x
step-decreasing n 0 {()}
step-decreasing n (suc x-1) {_} {n<x*x} = ≤⇒≤′ (div-left (x + (n div x)) x 2 lem)
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

step≢0 : ∀ n x {n≢0 : False (n ≟ 0)} {x≢0 : False (x ≟ 0)} → ¬ step n x {x≢0} ≡ 0
step≢0 0 _ {()}
step≢0 _ 0 {_} {()}
step≢0 1 1 ()
step≢0 (suc (suc n-2)) 1 = 0<n→n≢0 lem₂
 where
  n = 2 + n-2
  lem₀ : (step n 1) ≡ ((suc n) div 2)
  lem₀ = cong (λ z → (1 + z) div 2) {n div 1} {n} n/1≡n
  lem₁ : 0 < (suc n) div 2
  lem₁ = div-k-≤ 2 (suc n) 2 (s≤s (s≤s z≤n))
  open ≤-Reasoning
  lem₂ : 0 < step n 1
  lem₂ = begin 0 <⟨ lem₁ ⟩ (suc n) div 2 ≡⟨ sym lem₀ ⟩ step n 1 ∎
step≢0 (suc n-1) (suc (suc x-2)) = 0<n→n≢0 lem
 where
  n = suc n-1
  x = 2 + x-2
  open ≤-Reasoning
  lem : 0 < step n x
  lem = begin
    0                      <⟨ s≤s z≤n ⟩
    suc (x-2 div 2)        ≡⟨ proj₂ (divMod-step x-2 _) ⟩
    (x-2 + 2) div 2        ≡⟨ cong (λ z → z div 2) (+-comm x-2 2) ⟩
    x div 2                ≤⟨ div-steps x (n div x) 2 ⟩
    ((n div x) + x) div 2  ≡⟨ cong (λ z → z div 2) (+-comm (n div x) x) ⟩
    (x + (n div x)) div 2  ≡⟨ refl ⟩
    step n x               ∎

private
 data Terminates (n x : ℕ) : Set where
   termination-proof : (∀ y → (y <′ x) → Terminates n y) → Terminates n x

isqrtGo : (n : ℕ) → (x : ℕ) → {x≢0 : False (x ≟ 0)} → Terminates n x → ℕ
isqrtGo 0 _ _ = 0
isqrtGo _ 0 {()}
isqrtGo (suc n-1) (suc x-1) {_} (termination-proof term) with (2 + n-1) ≤? ((suc x-1) * (suc x-1))
... | no _ = suc x-1
... | yes n<x*x = isqrtGo n (step n x {tt}) {fromWitnessFalse (step≢0 n x)}
                  (term (step n x {tt}) (step-decreasing n x {tt} {n<x*x}))
 where n = suc n-1
       x = suc x-1

private
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

fixPointBounded : ∀ n x y {y≢0 : False (y ≟ 0)} → (x * x) ≤ n → step n y {y≢0} ≡ y → x ≤ y
fixPointBounded _ _ 0 {()}
fixPointBounded _ 0 _ _ _ = z≤n
fixPointBounded n (suc x-1) (suc y-1) x*x≤n fny≡y with (suc x-1) ≤? (suc y-1)
... | yes x≤y = x≤y
... | no ¬x≤y = contradiction 1+y≤y (¬1+n≤n {y})
 where
  x = suc x-1
  y = suc y-1
  y<x : y < x
  y<x = ¬b≤a→a<b ¬x≤y
  open ≤-Reasoning
  n/x<n/y : n div x < n div y
  n/x<n/y = divisor-< n y x y<x x*x≤n
  x≤n/x : x ≤ n div x
  x≤n/x = begin _ ≡⟨ sym (n*d/d≡n x x) ⟩ _ ≤⟨ div-k-≤ _ _ x x*x≤n ⟩ _ ∎
  x<n/y : x < n div y
  x<n/y = begin suc x ≤⟨ s≤s x≤n/x ⟩ suc (n div x) ≤⟨ n/x<n/y ⟩ n div y ∎
  2+y≤n/y : 2 + y ≤ n div y
  2+y≤n/y = begin 2 + y ≤⟨ s≤s y<x ⟩ suc x ≤⟨ x<n/y ⟩ n div y ∎
  [1+y]*2≤y+n/y : (1 + y) * 2 ≤ y + (n div y)
  [1+y]*2≤y+n/y = begin
    (1 + y) * 2   ≡⟨ distribʳ-*-+ 2 1 y ⟩
    _             ≡⟨ cong₂ _+_ (*-comm 1 2) (*-comm y 2) ⟩
    2 + 2 * y     ≡⟨ cong (_+_ 2) (cong (_+_ y) (*-left-identity y)) ⟩
    2 + (y + y)   ≡⟨ refl ⟩
    (2 + y) + y   ≡⟨ cong (flip _+_ y) (+-comm 2 y) ⟩
    (y + 2) + y   ≡⟨ +-assoc y 2 y ⟩
    y + (2 + y)   ≤⟨ add-≤ (n≤n y) 2+y≤n/y ⟩
    y + (n div y) ∎
  1+y≤y : suc y ≤ y
  1+y≤y = begin _ ≡⟨ sym (n*d/d≡n (suc y) 2) ⟩ _ ≤⟨ div-k-≤ _ _ 2 [1+y]*2≤y+n/y ⟩ _ ≡⟨ fny≡y ⟩ _ ∎

stepFixPoint⇒isqrt : ∀ n x {x≢0 : False (x ≟ 0)} → step n x {x≢0} ≡ x → x IsIntegerSqrtOf n
stepFixPoint⇒isqrt _ 0 {()}
stepFixPoint⇒isqrt n (suc x-1) fnx≡x = lem₂ , ¬b<a→a≤b (λ z → ¬[1+n]≤n (fixPointBounded n (suc x) x (≤-pred z) fnx≡x))
 where
  x = suc x-1
  open ≤-Reasoning
  lem₀ : 2 * x ≤ (x + (n div x))
  lem₀ = begin
    2 * x                          ≡⟨ *-comm 2 x ⟩
    x * 2                          ≡⟨ cong (flip _*_ 2) (sym fnx≡x) ⟩
    ((x + (n div x)) div 2) * 2    ≤⟨ n/d*d≤n _ 2 ⟩
    x + (n div x)                  ∎
  lem₁ : (x * x) + (x * x) ≤ x * x + n
  lem₁ = begin
    _                       ≡⟨ n+n≡2*n (x * x) ⟩
    2 * (x * x)             ≡⟨ sym (*-assoc 2 x x) ⟩
    (2 * x) * x             ≤⟨ a≤b→ak≤bk x lem₀ ⟩
    (x + (n div x)) * x     ≡⟨ distribʳ-*-+ x x _ ⟩
    x * x + (n div x) * x   ≤⟨ add-≤ (n≤n (x * x)) (n/d*d≤n n x) ⟩
    x * x + n               ∎
  lem₂ : x * x ≤ n
  lem₂ = cancel-+-left-≤ (x * x) lem₁

{-
stepTwoCycle : ∀ n x {x≢0 : False (x ≟ 0)} → step n x {x≢0} ≡ suc x → suc n ≡ (suc x) * (suc x)
stepTwoCycle _ 0 {()}
stepTwoCycle n (suc x-1) fnx≡1+x = {!!}

stepTwoCycle⇒isqrt : ∀ n x {x≢0 : False (x ≟ 0)} → step n x {x≢0} ≡ suc x → x IsIntegerSqrtOf n
stepTwoCycle⇒isqrt _ 0 {()}
stepTwoCycle⇒isqrt n (suc x-1) fnx≡1+x = x*x≤n , n<[1+x]^2 
 where
  x = suc x-1
  open ≤-Reasoning
  ¬n<x*x : ¬ n < x * x
  ¬n<x*x n<x*x = ¬1+n≤n (≤-pred (≤-step (begin _ ≡⟨ sym (cong suc fnx≡1+x) ⟩ _ ≤⟨ ≤′⇒≤ (step-decreasing n x {tt} {n<x*x}) ⟩ _ ∎)))
  x*x≤n : x * x ≤ n
  x*x≤n = ¬b<a→a≤b ¬n<x*x
  n<[1+x]^2 : n < (suc x) * (suc x)
  n<[1+x]^2 = begin _ ≡⟨ stepTwoCycle n x fnx≡1+x ⟩ _ ∎
-}

{-
isqrtProof : (n : ℕ) → ISqrt n
isqrtProof n = record {
  ⌊√n⌋ = isqrt n;
  property = {!!}
 }

record ISqrt (n : ℕ) : Set where
 constructor isqrt-result
 field
  ⌊√n⌋ : ℕ
  property : ⌊√n⌋ IsIntegerSqrtOf n
-}

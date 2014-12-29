module Lemmas where

{-
Author: Ruben Zilibowitz
Date: 28th December 2014
Description: Some lemmas needed in the other files
License: BSD New. See file LICENSE
-}

open import Data.Nat
open import Data.Nat.Properties.Simple
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Fin hiding (_≤_; _<_; _+_) renaming (zero to fzero; suc to fsuc)
open import Function

¬b<a→a≤b : ∀ {a b} → ¬ (b < a) → a ≤ b
¬b<a→a≤b {zero} {zero} x = z≤n
¬b<a→a≤b {zero} {suc b} x = z≤n
¬b<a→a≤b {suc a} {zero} x = contradiction (s≤s z≤n) x
¬b<a→a≤b {suc a} {suc b} x = s≤s (¬b<a→a≤b (x ∘ s≤s))

a≤b→¬b<a : ∀ {a b} → a ≤ b → ¬ (b < a)
a≤b→¬b<a z≤n ()
a≤b→¬b<a (s≤s x) y = a≤b→¬b<a x (≤-pred y)

k+[1+z]≡1+[k+z] : ∀ k z → k + (1 + z) ≡ 1 + (k + z)
k+[1+z]≡1+[k+z] k z = begin
  k + (1 + z)   ≡⟨ sym (+-assoc k 1 z) ⟩
  (k + 1) + z   ≡⟨ cong (flip _+_ z) (+-comm k 1) ⟩
  (1 + k) + z   ≡⟨ +-assoc 1 k z ⟩
  1 + (k + z)   ∎
 where open ≡-Reasoning

a+k*[1+a]≡k+[1+k]*a : ∀ a k → a + k * suc a ≡ k + (suc k) * a
a+k*[1+a]≡k+[1+k]*a a k = begin
   a + k * suc a     ≡⟨ cong (_+_ a) (*-comm k _) ⟩
   a + suc a * k     ≡⟨ cong (_+_ a) refl ⟩
   a + (k + a * k)   ≡⟨ sym (+-assoc a k (a * k)) ⟩
   (a + k) + a * k   ≡⟨ cong (flip _+_ (a * k)) (+-comm a k) ⟩
   (k + a) + a * k   ≡⟨ +-assoc k a (a * k) ⟩
   k + (a + a * k)   ≡⟨ cong ((_+_ k) ∘ (_+_ a)) (*-comm a k) ⟩
   k + (a + k * a)   ≡⟨ refl ⟩
   k + (suc k) * a   ∎
 where open ≡-Reasoning

i*[1+j]≡0⇒i≡0 : ∀ i {j} → i * suc j ≡ 0 → i ≡ 0
i*[1+j]≡0⇒i≡0 zero eq = refl
i*[1+j]≡0⇒i≡0 (suc i) ()

n≤n : ∀ n → n ≤ n
n≤n zero = z≤n
n≤n (suc n-1) = s≤s (n≤n n-1)

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

toℕ-inject₁ : ∀ {n} {i : Fin n} → toℕ i ≡ toℕ (inject₁ i)
toℕ-inject₁ {i = fzero} = refl
toℕ-inject₁ {i = fsuc i} = cong suc (toℕ-inject₁ {i = i})

n+n≡2*n : ∀ n → n + n ≡ 2 * n
n+n≡2*n n = cong (_+_ n) (sym (+-right-identity n))

n+n≡n*2 : ∀ n → n + n ≡ n * 2
n+n≡n*2 n = trans (n+n≡2*n n) (*-comm 2 n)

add-≤ : ∀ {a b c d} → a ≤ b → c ≤ d → a + c ≤ b + d
add-≤ {.0} {b} {.0} {d} z≤n z≤n = z≤n
add-≤ {.0} {b} {._} {._} z≤n (s≤s c≤d) = begin _ ≤⟨ s≤s (add-≤ {0} {b} {_} {_} z≤n c≤d) ⟩ suc (b + _) ≡⟨ sym (k+[1+z]≡1+[k+z] b _) ⟩ _ ∎
 where open ≤-Reasoning
add-≤ {._} {._} {c} {d} (s≤s a≤b) c≤d = s≤s (add-≤ {_} {_} {c} {d} a≤b c≤d)

[1+a]*[1+c]≡a+[1+c]+a*c : ∀ a c → (suc a) * (suc c) ≡ a + (suc c + a * c)
[1+a]*[1+c]≡a+[1+c]+a*c a c = begin
   (suc c) + a * (suc c)       ≡⟨ cong (_+_ (suc c)) (*-comm a (suc c)) ⟩
   suc c + (a + c * a)         ≡⟨ sym (+-assoc (suc c) _ _) ⟩
   (suc c + a) + c * a         ≡⟨ cong₂ _+_ (+-comm _ a) (*-comm c _) ⟩
   (a + suc c) + a * c         ≡⟨ +-assoc a _ _ ⟩
   _ ∎
 where open ≡-Reasoning

mul-≤ : ∀ {a b c d} → a ≤ b → c ≤ d → a * c ≤ b * d
mul-≤ z≤n c≤d = z≤n
mul-≤ {suc a} (s≤s a≤b) z≤n = begin _ ≡⟨ *-comm (suc a) 0 ⟩ 0 ≤⟨ z≤n ⟩ _ ∎
 where open ≤-Reasoning
mul-≤ {suc a} {suc b} {suc c} {suc d} (s≤s a≤b) (s≤s c≤d) = begin
   _       ≡⟨ [1+a]*[1+c]≡a+[1+c]+a*c a c ⟩
   _       ≤⟨ add-≤ a≤b (add-≤ (s≤s c≤d) (mul-≤ a≤b c≤d)) ⟩
   _       ≡⟨ sym ([1+a]*[1+c]≡a+[1+c]+a*c b d) ⟩
   _       ∎
 where open ≤-Reasoning

a≤b→ak≤bk : ∀ {a b k} → a ≤ b → a * k ≤ b * k
a≤b→ak≤bk {_} {_} {k} a≤b = mul-≤ a≤b (n≤n k)

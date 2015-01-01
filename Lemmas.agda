module Lemmas where

{-
Author: Ruben Zilibowitz
Date: 28th December 2014
Description: Some lemmas needed in the other files
License: BSD New. See file LICENSE
-}

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Relation.Nullary.Negation
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Data.Fin hiding (_≤_; _<_; _+_; pred) renaming (zero to fzero; suc to fsuc)
open import Function

n≤n : ∀ n → n ≤ n
n≤n zero = z≤n
n≤n (suc n-1) = s≤s (n≤n n-1)

¬b<a→a≤b : ∀ {a b} → ¬ (b < a) → a ≤ b
¬b<a→a≤b {zero} {zero} x = z≤n
¬b<a→a≤b {zero} {suc b} x = z≤n
¬b<a→a≤b {suc a} {zero} x = contradiction (s≤s z≤n) x
¬b<a→a≤b {suc a} {suc b} x = s≤s (¬b<a→a≤b (x ∘ s≤s))

¬b≤a→a<b : ∀ {a b} → ¬ (b ≤ a) → a < b
¬b≤a→a<b {zero} {zero} ¬b≤a = ⊥-elim (¬b≤a (n≤n _))
¬b≤a→a<b {zero} {suc b} ¬b≤a = s≤s z≤n
¬b≤a→a<b {suc a} {zero} ¬b≤a = ⊥-elim (¬b≤a z≤n)
¬b≤a→a<b {suc a} {suc b} ¬b≤a = s≤s (¬b≤a→a<b (¬b≤a ∘ s≤s))

a≤b→¬b<a : ∀ {a b} → a ≤ b → ¬ (b < a)
a≤b→¬b<a z≤n ()
a≤b→¬b<a (s≤s x) y = a≤b→¬b<a x (≤-pred y)

a≢b→a≤b→a<b : ∀ {a b} → ¬ (a ≡ b) → a ≤ b → a < b
a≢b→a≤b→a<b {zero} {zero} x _ = contradiction refl x
a≢b→a≤b→a<b {zero} {suc _} _ _ = s≤s z≤n
a≢b→a≤b→a<b x (s≤s a≤b) = s≤s (a≢b→a≤b→a<b (x ∘ (cong suc)) a≤b)

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

add-k-≤ : ∀ {a b} k → a ≤ b → a + k ≤ b + k
add-k-≤ {a} {b} k a≤b = add-≤ a≤b (n≤n k)

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

a≤b→ak≤bk : ∀ {a b} k → a ≤ b → a * k ≤ b * k
a≤b→ak≤bk {_} {_} k a≤b = mul-≤ a≤b (n≤n k)

a≤b→ka≤kb : ∀ {a b} k → a ≤ b → k * a ≤ k * b
a≤b→ka≤kb {_} {_} k a≤b = mul-≤ (n≤n k) a≤b

¬[1+n]≤n : ∀ {n} → ¬ suc n ≤ n
¬[1+n]≤n {zero} ()
¬[1+n]≤n {suc n} x = ¬[1+n]≤n {n} (≤-pred x)

*-right-identity : ∀ n → n * 1 ≡ n
*-right-identity n = begin n * 1 ≡⟨ *-comm n 1 ⟩ 1 * n ≡⟨ +-right-identity n ⟩ n ∎
 where open ≡-Reasoning

*-left-identity : ∀ n → 1 * n ≡ n
*-left-identity = +-right-identity

a+b≡c→a≤c : ∀ a b c → a + b ≡ c → a ≤ c
a+b≡c→a≤c a b .(a + b) refl = begin _ ≤⟨ ≤-steps b (n≤n a) ⟩ _ ≡⟨ +-comm b a ⟩ _ ∎
 where open ≤-Reasoning

sum-sizes : ∀ a b c d → a + b ≡ c + d → d ≤ b → a ≤ c
sum-sizes a b c .0 a+b≡c+d z≤n = a+b≡c→a≤c _ _ _ (trans (a+b≡c+d) (+-right-identity c))
sum-sizes a (suc b-1) c (suc d-1) a+b≡c+d (s≤s d-1≤b-1) = sum-sizes a b-1 c d-1 (cong pred lem) d-1≤b-1
 where
  open ≡-Reasoning
  lem : suc (a + b-1) ≡ suc (c + d-1)
  lem = begin
   _ ≡⟨ sym (k+[1+z]≡1+[k+z] a b-1) ⟩
   _ ≡⟨ a+b≡c+d ⟩
   _ ≡⟨ k+[1+z]≡1+[k+z] c d-1 ⟩
   _ ∎

cancel-*-left : ∀ i j {k} → suc k * i ≡ suc k * j → i ≡ j
cancel-*-left i j {k} eq = cancel-*-right i j {k} (begin _ ≡⟨ *-comm i (suc k) ⟩ _ ≡⟨ eq ⟩ _ ≡⟨ *-comm (suc k) j ⟩ _ ∎)
 where open ≡-Reasoning

¬1+n≤n : ∀ {n} → ¬ suc n ≤ n
¬1+n≤n (s≤s 1+n≤n) = ¬1+n≤n 1+n≤n

{-
distribˡ-*-+ : ∀ m n o → m * (n + o) ≡ m * n + m * o
distribˡ-*-+ m n o = begin _ ≡⟨ *-comm m _ ⟩ _ ≡⟨ distribʳ-*-+ m n o ⟩ _ ≡⟨ cong₂ _+_ (*-comm n m) (*-comm o m) ⟩ _  ∎
 where open ≡-Reasoning
-}

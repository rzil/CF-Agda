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

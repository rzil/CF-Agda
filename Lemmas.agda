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

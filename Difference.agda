module Difference where

{-
Author: Ruben Zilibowitz
Date: 28th December 2014
Description: Definition and proofs about the difference of two natural numbers
License: BSD New. See file LICENSE
-}

open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Fin hiding (_+_; _-_; _<_; _≤_; pred) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties hiding (_≟_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Sum
open import Function

open import Lemmas

-------------
-- Difference
-- This is equivalent to ∣ x - y ∣ for integers
-- It is defined purely in terms of natural numbers however
-------------
difference : ℕ → ℕ → ℕ
difference x 0 = x
difference 0 (suc y) = suc y
difference (suc x) (suc y) = difference x y

0-a≡a : ∀ {a} → difference 0 a ≡ a
0-a≡a {zero} = refl
0-a≡a {suc a} = refl

zero-difference : ∀ {a b} → difference a b ≡ 0 → a ≡ b
zero-difference {zero} eq = trans (sym eq) 0-a≡a
zero-difference {suc _} {zero} eq = eq
zero-difference {suc a} {suc b} eq = cong suc (zero-difference {a} {b} eq)

difference-bounded : ∀ {n} (a b : Fin n) → difference (toℕ a) (toℕ b) < n
difference-bounded fzero fzero = s≤s z≤n
difference-bounded fzero (fsuc b) = s≤s (bounded b)
difference-bounded (fsuc a) fzero = s≤s (bounded a)
difference-bounded (fsuc a) (fsuc b) = ≤-step (difference-bounded a b)

difference-cancel : ∀ a b → difference (a + b) b ≡ a
difference-cancel zero zero = refl
difference-cancel zero (suc b) = difference-cancel zero b
difference-cancel (suc a) zero = +-right-identity (suc a)
difference-cancel (suc a) (suc b) = begin
   difference (suc a + suc b) (suc b)    ≡⟨ cong (flip difference b) (k+[1+z]≡1+[k+z] a b) ⟩
   difference (suc a + b) b              ≡⟨ difference-cancel (suc a) b ⟩
   suc a                                 ∎
 where open ≡-Reasoning

difference-comm : ∀ a b → difference a b ≡ difference b a
difference-comm zero zero = refl
difference-comm zero (suc _) = refl
difference-comm (suc _) zero = refl
difference-comm (suc a) (suc b) = difference-comm a b

rearrange-+-eq : ∀ a b c d → a + b ≡ c + d → difference a c ≡ difference b d
rearrange-+-eq zero .(c + d) c d refl = begin
   difference zero c    ≡⟨ difference-comm 0 c ⟩
   c                    ≡⟨ sym (difference-cancel c d) ⟩
   difference (c + d) d ∎
 where open ≡-Reasoning
rearrange-+-eq a b zero .(a + b) refl = begin
   a                      ≡⟨ sym (difference-cancel a b) ⟩
   difference (a + b) b   ≡⟨ difference-comm (a + b) b ⟩
   difference b (a + b)   ∎
 where open ≡-Reasoning
rearrange-+-eq (suc a) (suc b) (suc c) (suc d) eq = rearrange-+-eq a b c d (begin
   a + b                ≡⟨ cong pred (sym (k+[1+z]≡1+[k+z] a b)) ⟩
   pred (a + (suc b))   ≡⟨ cong (pred ∘ pred) eq ⟩
   pred (c + (suc d))   ≡⟨ cong pred (k+[1+z]≡1+[k+z] c d) ⟩
   c + d                ∎)
 where open ≡-Reasoning
rearrange-+-eq (suc a) zero (suc c) d eq = rearrange-+-eq a 0 c d (cong pred eq)
rearrange-+-eq (suc a) (suc b) (suc c) zero eq = rearrange-+-eq a (suc b) c 0 (cong pred eq)

difference-steps : ∀ a b k → difference (k + a) (k + b) ≡ difference a b
difference-steps a b zero = refl
difference-steps a b (suc k) = difference-steps a b k

difference-left-factor : ∀ a b k → difference (k * a) (k * b) ≡ k * (difference a b)
difference-left-factor a b zero = refl
difference-left-factor a zero (suc k) = cong (difference (suc k * a)) (*-right-zero (suc k))
difference-left-factor zero (suc b) (suc k) = cong (flip difference (suc k * suc b)) (*-right-zero (suc k))
difference-left-factor (suc a) (suc b) (suc k) = begin
   difference (a + k * suc a) (b + k * suc b)       ≡⟨ cong₂ difference (a+k*[1+a]≡k+[1+k]*a a k) (a+k*[1+a]≡k+[1+k]*a b k) ⟩
   difference (k + (a + k * a)) (k + (b + k * b))   ≡⟨ difference-steps _ _ k ⟩
   difference (a + k * a) (b + k * b)               ≡⟨ difference-left-factor a b (suc k) ⟩
   suc k * difference a b                           ∎
 where open ≡-Reasoning

difference-right-factor : ∀ a b k → difference (a * k) (b * k) ≡ (difference a b) * k
difference-right-factor a b k = begin
   difference (a * k) (b * k)     ≡⟨ cong₂ difference (*-comm a k) (*-comm b k) ⟩
   difference (k * a) (k * b)     ≡⟨ difference-left-factor a b k ⟩
   k * (difference a b)           ≡⟨ *-comm k _ ⟩
   (difference a b) * k           ∎
 where open ≡-Reasoning

difference-to-monus : ∀ a b → a ≤ b → difference a b ≡ b ∸ a
difference-to-monus .0 b z≤n = 0-a≡a
difference-to-monus (suc a) (suc b) (s≤s a≤b) = difference-to-monus a b a≤b

open ≤-Reasoning

≤-difference : ∀ d a b → d ≤ difference a b → (d + a ≤ b ⊎ d + b ≤ a)
≤-difference d zero b d≤∣a-b∣ = inj₁ (begin d + 0 ≡⟨ +-right-identity d ⟩ d ≤⟨ d≤∣a-b∣ ⟩ _ ≡⟨ 0-a≡a ⟩ b ∎)
≤-difference d (suc a) zero d≤∣a-b∣ = inj₂ (begin d + 0 ≡⟨ +-right-identity d ⟩ d ≤⟨ d≤∣a-b∣ ⟩ suc a ∎)
≤-difference d (suc a) (suc b) d≤∣a-b∣ with ≤-difference d a b d≤∣a-b∣
... | (inj₁ d+a≤b) = inj₁ (begin d + suc a ≡⟨ k+[1+z]≡1+[k+z] d a ⟩ suc d + a ≤⟨ s≤s d+a≤b ⟩ suc b  ∎)
... | (inj₂ d+b≤a) = inj₂ (begin d + suc b ≡⟨ k+[1+z]≡1+[k+z] d b ⟩ suc d + b ≤⟨ s≤s d+b≤a ⟩ suc a  ∎)

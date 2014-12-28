module DivModUniqueness where

{-
Author: Ruben Zilibowitz
Date: 28th December 2014
Description: Proof of the uniqueness of the division algorithm on natural numbers.
 Also a simple corollary of this.
License: BSD New. See file LICENSE
-}

open import Data.Nat as Nat
open import Data.Nat.Properties.Simple
open import Data.Nat.DivMod
open import Data.Nat.Divisibility
open import Data.Fin hiding (_+_; _-_; _<_; _≤_) renaming (zero to fzero; suc to fsuc; pred to fpred)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation
open import Data.Product
open import Function
open import Relation.Nullary.Decidable

open import Lemmas
open import Difference

---------------
-- Main theorem
-- The uniqueness of the quotient and remainder from the division algorithm on natural numbers
---------------
unique-divMod : ∀ dividend divisor {d≢0 : False (divisor ≟ 0)} → (dm₀ : DivMod dividend divisor) → (dm₁ : DivMod dividend divisor) → (DivMod.remainder dm₀ ≡ DivMod.remainder dm₁) × (DivMod.quotient dm₀ ≡ DivMod.quotient dm₁)
unique-divMod _ 0 {()}
unique-divMod dividend (suc divisor-1) dm₀ dm₁ with
   difference (toℕ (DivMod.remainder dm₀)) (toℕ (DivMod.remainder dm₁))
   | inspect (difference (toℕ (DivMod.remainder dm₀))) (toℕ (DivMod.remainder dm₁))
... | 0 | [ eq ] = cancel-toℕ _ _ (zero-difference eq) , zero-difference (i*[1+j]≡0⇒i≡0 q-diff factor-eq)
 where
  divisor = suc divisor-1
  r₀ = DivMod.remainder dm₀
  r₁ = DivMod.remainder dm₁
  q₀ = DivMod.quotient dm₀
  q₁ = DivMod.quotient dm₁
  r-diff = difference (toℕ r₀) (toℕ r₁)
  q-diff = difference q₀ q₁
  lem₀ : r-diff ≡ 0
  lem₀ = eq
  equiv : toℕ r₀ + q₀ * divisor ≡ toℕ r₁ + q₁ * divisor
  equiv = trans (sym (DivMod.property dm₀)) (DivMod.property dm₁)
  lem₁ : difference (q₀ * divisor) (q₁ * divisor) ≡ 0
  lem₁ = trans (sym (rearrange-+-eq (toℕ r₀) _ (toℕ r₁) _ equiv)) eq
  factor-eq : q-diff * divisor ≡ 0
  factor-eq = trans (sym (difference-right-factor q₀ q₁ divisor)) lem₁
... | suc r-diff-1 | [ eq ] = contradiction lem₀ (a≤b→¬b<a (∣⇒≤ divisible))
 where
  divisor = suc divisor-1
  r₀ = DivMod.remainder dm₀
  r₁ = DivMod.remainder dm₁
  q₀ = DivMod.quotient dm₀
  q₁ = DivMod.quotient dm₁
  r-diff = suc r-diff-1
  q-diff = difference q₀ q₁
  lem₀ : r-diff < divisor
  lem₀ = begin
    suc r-diff                                                                    ≡⟨ sym (cong suc eq) ⟩
    suc (difference (toℕ (DivMod.remainder dm₀)) (toℕ (DivMod.remainder dm₁)))   ≤⟨ difference-bounded (DivMod.remainder dm₀) (DivMod.remainder dm₁) ⟩
    divisor                                                                       ∎
   where open ≤-Reasoning
  equiv : toℕ r₀ + q₀ * divisor ≡ toℕ r₁ + q₁ * divisor
  equiv = trans (sym (DivMod.property dm₀)) (DivMod.property dm₁)
  lem₁ : r-diff ≡ difference (q₀ * divisor) (q₁ * divisor)
  lem₁ = trans (sym eq) (rearrange-+-eq (toℕ r₀) _ (toℕ r₁) _ equiv)
  factor-eq : r-diff ≡ q-diff * divisor
  factor-eq = trans lem₁ (difference-right-factor q₀ q₁ divisor)
  divisible : divisor ∣ r-diff
  divisible = divides q-diff factor-eq

------------
-- Corollary
-- If you add the divisor to the dividend, then the remainder is unchanged.
-- The quotient increases by one.
------------
divMod-step : ∀ n k → (n mod (suc k) ≡ (n + (suc k)) mod (suc k)) × (suc (n div (suc k)) ≡ (n + (suc k)) div (suc k))
divMod-step n k = unique-divMod (n + suc k) (suc k) lem ((n + suc k) divMod (suc k))
 where
  r₀ = n mod (suc k)
  r₁ = (n + suc k) mod (suc k)
  q₀ = n div (suc k)
  q₁ = (n + suc k) div (suc k)
  property : n + suc k ≡ toℕ r₀ + (suc q₀) * (suc k)
  property = begin
     n + suc k                           ≡⟨ cong (flip _+_ (suc k)) (DivMod.property (n divMod (suc k))) ⟩
     (toℕ r₀ + q₀ * (suc k)) + suc k     ≡⟨ +-assoc (toℕ r₀) _ _ ⟩
     toℕ r₀ + (q₀ * (suc k) + suc k)     ≡⟨ cong (_+_ (toℕ r₀)) (+-comm _ (suc k)) ⟩
     toℕ r₀ + (suc k + q₀ * (suc k))     ≡⟨ refl ⟩
     toℕ r₀ + (suc q₀) * (suc k)         ∎
   where open ≡-Reasoning
  lem : DivMod (n + suc k) (suc k)
  lem = result (suc q₀) r₀ property


div-pred : ∀ n k → (suc n) mod (suc k) ≢ fzero → fpred ((suc n) mod (suc k)) ≡ (n mod (suc k)) × (suc n) div (suc k) ≡ n div (suc k)
div-pred n k x = unique-divMod n (suc k) lem (n divMod (suc k))
 where
  r₀ = (suc n) mod (suc k)
  r₁ = n mod (suc k)
  q₀ = (suc n) div (suc k)
  q₁ = n div (suc k)
  property : n ≡ toℕ (fpred r₀) + q₀ * (suc k)
  property = begin
     n                                 ≡⟨ cong pred (DivMod.property ((suc n) divMod (suc k))) ⟩
     pred (toℕ r₀ + q₀ * (suc k))      ≡⟨ {!!} ⟩
     toℕ (fpred r₀) + q₀ * (suc k)     ∎
   where open ≡-Reasoning
  lem : DivMod n (suc k)
  lem = result q₀ (fpred r₀) property

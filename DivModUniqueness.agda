module DivModUniqueness where

{-
Author: Ruben Zilibowitz
Date: 28th December 2014
Description: Proof of the uniqueness of the division algorithm on natural numbers.
 Also a simple corollary of this.
License: BSD New. See file LICENSE
-}

open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.DivMod
open import Data.Nat.Divisibility
open import Data.Fin hiding (_+_; _-_; _<_; _≤_) renaming (zero to fzero; suc to fsuc; pred to fpred)
open import Data.Fin.Properties hiding (_≟_)
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
... | 0 | [ eq ] = toℕ-injective (zero-difference eq) , zero-difference (i*[1+j]≡0⇒i≡0 q-diff factor-eq)
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

toℕ-inject₁ : ∀ {n} {i : Fin n} → toℕ i ≡ toℕ (inject₁ i)
toℕ-inject₁ {i = fzero} = refl
toℕ-inject₁ {i = fsuc i} = cong suc (toℕ-inject₁ {i = i})

---------------------------------------------------------
-- Integer division by a constant is monotonic increasing
---------------------------------------------------------
div-monotonic : ∀ n k {k≢0 : False (k ≟ 0)} → _div_ n k {k≢0} ≤ _div_ (suc n) k {k≢0}
div-monotonic _ 0 {()}
div-monotonic n (suc k-1) with (suc n) mod (suc k-1) | inspect (λ z → _mod_ z (suc k-1)) (suc n)
... | fzero | [ eq ] = begin q₀ ≤⟨ ≤-step (n≤n q₀) ⟩ suc q₀ ≡⟨ final-lemma ⟩ q₁ ∎
 where
  k = suc k-1
  r₀ = n mod k
  r₁ = (suc n) mod k
  q₀ = n div k
  q₁ = (suc n) div k
  property₁ : suc n ≡ q₁ * k
  property₁ = begin
     suc n               ≡⟨ DivMod.property ((suc n) divMod k) ⟩
     toℕ r₁ + q₁ * k     ≡⟨ cong (λ z → toℕ z + q₁ * k) eq ⟩
     q₁ * k              ∎
   where open ≡-Reasoning
  divMod₁ : DivMod (suc n) k
  divMod₁ = result q₁ fzero property₁
  lem₀ : r₀ ≡ fromℕ≤ {k-1} (n≤n k)
  lem₀ with ((suc n) div k) | inspect (λ z → _div_ z k) (suc n)
  ... | 0 | [ eq ] = contradiction (trans property₁ (cong (flip _*_ k) eq)) (λ ())
  ... | suc q₁-1 | [ eq ] = proj₁ (unique-divMod n k (n divMod k) (result q₁-1 (fromℕ≤ {k-1} (n≤n k)) property-n)) 
   where
    property-n : n ≡ toℕ (fromℕ≤ {k-1} (n≤n k)) + q₁-1 * k
    property-n = begin
       n                   ≡⟨ cong pred (trans property₁ (cong (flip _*_ k) eq)) ⟩
       k-1 + q₁-1 * k      ≡⟨ cong (flip _+_ (q₁-1 * k)) (sym (toℕ-fromℕ≤ {k-1} (n≤n k))) ⟩
       _                   ∎
     where open ≡-Reasoning
  property₀ : suc n ≡ (suc q₀) * k
  property₀ = begin
     suc n                                               ≡⟨ cong suc (DivMod.property (n divMod k)) ⟩
     _                                                   ≡⟨ cong (suc ∘ (flip _+_ ((n div k) * k)) ∘ toℕ) lem₀ ⟩
     suc (toℕ (fromℕ≤ {k-1} (n≤n k)) + (n div k) * k)    ≡⟨ cong (suc ∘ (flip _+_ ((n div k) * k))) (toℕ-fromℕ≤ {k-1} (n≤n k)) ⟩
     (suc q₀) * k                                         ∎
   where open ≡-Reasoning
  final-lemma : suc q₀ ≡ q₁
  final-lemma = cancel-*-right _ _ (trans (sym property₀) property₁)
  open ≤-Reasoning

... | fsuc i | [ eq ] = begin q₀ ≡⟨ lem ⟩ q₁ ∎
 where
  k = suc k-1
  r₀ = n mod k
  r₁ = (suc n) mod k
  q₀ = n div k
  q₁ = (suc n) div k
  property₁ : suc n ≡ suc (toℕ i) + q₁ * k
  property₁ = trans (DivMod.property ((suc n) divMod k)) (cong ((flip _+_ (q₁ * k)) ∘ toℕ) eq)
  property₀ : n ≡ toℕ (inject₁ i) + q₁ * k
  property₀ = trans (cong pred property₁) (cong (flip _+_ (q₁ * k)) {toℕ i} toℕ-inject₁)
  lem : q₀ ≡ q₁
  lem = proj₂ (unique-divMod n k (n divMod k) ((result _ (inject₁ i) property₀)))
  open ≤-Reasoning

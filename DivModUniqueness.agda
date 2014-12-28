module DivModUniqueness where

open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.DivMod
open import Data.Nat.Divisibility
open import Data.Fin hiding (_+_; _-_; _<_; _≤_; pred) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties hiding (_≟_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Nullary.Decidable

a≤b→¬b<a : ∀ {a b} → a ≤ b → ¬ (b < a)
a≤b→¬b<a z≤n ()
a≤b→¬b<a (s≤s x) y = a≤b→¬b<a x (≤-pred y)

difference : ℕ → ℕ → ℕ
difference x 0 = x
difference 0 y = y
difference (suc x) (suc y) = difference x y

0-a : ∀ {a} → difference 0 a ≡ a
0-a {zero} = refl
0-a {suc a} = refl

zero-difference : ∀ {a b} → difference a b ≡ 0 → a ≡ b
zero-difference {zero} eq = trans (sym eq) 0-a
zero-difference {suc _} {zero} eq = eq
zero-difference {suc a} {suc b} eq = cong suc (zero-difference {a} {b} eq)

fin-difference : ∀ {n} (a b : Fin n) → difference (toℕ a) (toℕ b) < n
fin-difference fzero fzero = s≤s z≤n
fin-difference fzero (fsuc b) = s≤s (bounded b)
fin-difference (fsuc a) fzero = s≤s (bounded a)
fin-difference (fsuc a) (fsuc b) = ≤-step (fin-difference a b)

cancel-toℕ : ∀ {n} i j → toℕ {n} i ≡ toℕ j → i ≡ j
cancel-toℕ fzero fzero eq = refl
cancel-toℕ fzero (fsuc _) ()
cancel-toℕ (fsuc _) fzero ()
cancel-toℕ (fsuc i) (fsuc j) eq = cong fsuc (cancel-toℕ i j (cong Nat.pred eq))

k+[1+z]≡1+[k+z] : ∀ k z → k + (1 + z) ≡ 1 + (k + z)
k+[1+z]≡1+[k+z] k z = begin
  k + (1 + z)   ≡⟨ sym (+-assoc k 1 z) ⟩
  (k + 1) + z   ≡⟨ cong (flip _+_ z) (+-comm k 1) ⟩
  (1 + k) + z   ≡⟨ +-assoc 1 k z ⟩
  1 + (k + z)   ∎
 where open ≡-Reasoning

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

i*[1+j]≡0⇒i≡0 : ∀ i {j} → i * suc j ≡ 0 → i ≡ 0
i*[1+j]≡0⇒i≡0 zero eq = refl
i*[1+j]≡0⇒i≡0 (suc i) ()

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
    suc (difference (toℕ (DivMod.remainder dm₀)) (toℕ (DivMod.remainder dm₁)))   ≤⟨ fin-difference (DivMod.remainder dm₀) (DivMod.remainder dm₁) ⟩
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

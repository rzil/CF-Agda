module CF where

-- http://rosettacode.org/wiki/Continued_fraction/Arithmetic/G(matrix_NG,_Contined_Fraction_N)#NG

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.DivMod
open import Data.Fin hiding (_+_; _-_; _≤_)
open import Data.Bool hiding (_≟_)
open import Coinduction
-- open import Data.Stream hiding (repeat)
open import Data.List as List renaming (_∷_ to _L∷_; [] to L[]) hiding (take)
open import Data.Colist as Colist
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
open import Data.Unit hiding (_≟_; _≤_)
open import Relation.Binary.PropositionalEquality as PropEq
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Function

private
 n≤n : ∀ n → n ≤ n
 n≤n zero = z≤n
 n≤n (suc n-1) = s≤s (n≤n n-1)

 quot*divid≤divis : ∀ m n → {n≢0 : False (n ≟ 0)} → (_div_ m n {n≢0}) * n ≤ m
 quot*divid≤divis _ 0  {()}
 quot*divid≤divis m (suc n-1) = begin
    (_div_ m n) * n                                      ≤⟨ ≤-steps (toℕ (DivMod.remainder dm)) (n≤n (DivMod.quotient dm * n)) ⟩
    toℕ (DivMod.remainder dm) + DivMod.quotient dm * n   ≡⟨ sym (DivMod.property dm) ⟩
    m                                                    ∎
  where n = suc n-1
        dm = _divMod_ m n
        open ≤-Reasoning

record NG : Set where
 constructor ng
 field
  a1 : ℕ
  a : ℕ
  b1 : ℕ
  b : ℕ
 
 output : {b≢0 : False (b ≟ 0)} → {b1≢0 : False (b1 ≟ 0)} → Set
 output {b≢0} {b1≢0} = _div_ a b {b≢0} ≡ _div_ a1 b1 {b1≢0}

 output? : {b≢0 : False (b ≟ 0)} → {b1≢0 : False (b1 ≟ 0)} → Dec (output {b≢0} {b1≢0})
 output? = a div b ≟ a1 div b1
 
 term : {b≢0 : False (b ≟ 0)} → ℕ
 term {b≢0} = _div_ a b {b≢0}
 
 ingress : ℕ → NG
 ingress t = record {a = a1; a1 = a + t * a1; b = b1; b1 = b + t * b1}

 -- equivalent to ingress with an argument of ∞ (in some sense)
 ∞-ingress : NG
 ∞-ingress = record {a = a1; a1 = a1; b = b1; b1 = b1}
 
 egress : (t : ℕ) → {tb≤a : t * b ≤ a} → {tb1≤a1 : t * b1 ≤ a1} → NG
 egress t = record {a = b; b = a ∸ t * b; a1 = b1; b1 = a1 ∸ t * b1}
 
 lemma : {b≢0 : False (b ≟ 0)} → {b1≢0 : False (b1 ≟ 0)} → output {b≢0} {b1≢0} → (term {b≢0}) * b1 ≤ a1
 lemma prf = begin
     term * b1              ≡⟨ cong (flip _*_ b1) prf ⟩
     (a1 div b1) * b1       ≤⟨ quot*divid≤divis a1 b1 ⟩
     a1                     ∎
   where open ≤-Reasoning

-- type for continued fractions
CF : Set
CF = Colist ℕ

ng-apply : NG → CF → Colist (Maybe ℕ)

-- No terms left in the input. Inject ∞ into input.
ng-apply op [] with NG.b op ≟ 0 | NG.b1 op ≟ 0
... | yes _ | yes _ = []   -- We are done here. No more terms to output
... | yes _ | _ = nothing ∷ ♯ (ng-apply (NG.∞-ingress op) [])
... | _ | yes _ = nothing ∷ ♯ (ng-apply (NG.∞-ingress op) [])   -- nb: repetition of code here. not nice.
... | no b≢0 | no b1≢0 with NG.output? op {fromWitnessFalse b≢0} {fromWitnessFalse b1≢0}
...    | yes prf = just t ∷ ♯ ng-apply (NG.∞-ingress (NG.egress op t {quot*divid≤divis (NG.a op) (NG.b op)} {NG.lemma op prf})) []
                   where t = NG.term op {fromWitnessFalse b≢0}
...    | no _ = nothing ∷ ♯ (ng-apply (NG.∞-ingress op) [])   -- nb: repetition of code here. not nice.

-- Eat up an input term
ng-apply op (x ∷ xs) with NG.b op ≟ 0 | NG.b1 op ≟ 0
... | yes _ | _ = nothing ∷ ♯ (ng-apply (NG.ingress op x) (♭ xs))
... | _ | yes _ = nothing ∷ ♯ (ng-apply (NG.ingress op x) (♭ xs))   -- nb: repetition of code here. not nice.
... | no b≢0 | no b1≢0 with NG.output? op {fromWitnessFalse b≢0} {fromWitnessFalse b1≢0}
...    | yes prf = just t ∷ ♯ ng-apply (NG.ingress (NG.egress op t {quot*divid≤divis (NG.a op) (NG.b op)} {NG.lemma op prf}) x) (♭ xs)
                   where t = NG.term op {fromWitnessFalse b≢0}
...    | no _ = nothing ∷ ♯ (ng-apply (NG.ingress op x) (♭ xs))   -- nb: repetition of code here. not nice.

-- convert the output of ng-apply to an equivalent continued fraction
ng-output-to-CF : Colist (Maybe ℕ) → CF
ng-output-to-CF [] = []
ng-output-to-CF (nothing ∷ xs) = 0 ∷ ♯ (0 ∷ ♯ ng-output-to-CF (♭ xs))
ng-output-to-CF (just x ∷ xs) = x ∷ (♯ ng-output-to-CF (♭ xs))

-- helper functions for continued fractions
repeat : ℕ → CF
repeat x = x ∷ (♯ (repeat x))

cycle : List ℕ → CF
cycle xs = cycle' xs xs
 where
  cycle' : List ℕ → List ℕ → CF
  cycle' _ L[] = []
  cycle' xs (y L∷ L[]) = y ∷ ♯ (cycle' xs xs)
  cycle' xs (y L∷ ys) = y ∷ ♯ (cycle' xs ys)

-- rational to continued fraction
r2cf : (numerator : ℕ) → (denominator : ℕ) → CF
r2cf _ 0 = []
r2cf n (ℕ.suc d-1) = DivMod.quotient x ∷ ♯ (r2cf d (toℕ (DivMod.remainder x)))
 where
  d = ℕ.suc d-1
  x = n divMod d

-- square root of 2 as a continued fraction
sqrt2 : CF
sqrt2 = 1 ∷ (♯ (repeat 2))

-- some tests
test₀ = take 10 $ ng-apply (ng 2 1 0 2) (r2cf 13 11)
test₁ = take 10 $ ng-apply (ng 2 1 0 2) (r2cf 22 7)
test₂ = take 10 $ ng-apply (ng 1 0 0 4) (r2cf 22 7)
test₃ = take 10 $ ng-apply (ng 1 0 0 4) sqrt2

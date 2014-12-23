module CF2 where

-- http://rosettacode.org/wiki/Continued_fraction/Arithmetic/G(matrix_NG,_Contined_Fraction_N)#NG

open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.Nat.Properties.Simple
open import Data.Nat.DivMod
open import Data.Fin hiding (_+_; _-_; _≤_)
open import Data.Bool hiding (_≟_)
open import Coinduction
-- open import Data.Stream hiding (repeat)
open import Data.List as List renaming (_∷_ to _L∷_; [] to L[]; _++_ to _L++_) hiding (take)
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
 
 0<n→n≢0 : ∀ {n} → 0 Nat.< n → n ≢ 0
 0<n→n≢0 {zero} ()
 0<n→n≢0 {suc n-1} 0<n ()
 
 nonZeroLemma : ∀ {n m} → n ≢ 0 → n + m ≢ 0
 nonZeroLemma {n} n≢0 n+m≡0 = n≢0 (i+j≡0⇒i≡0 n n+m≡0)
 
 quot*divid≤divis : ∀ m n → {n≢0 : False (n ≟ 0)} → (_div_ m n {n≢0}) * n ≤ m
 quot*divid≤divis _ 0  {()}
 quot*divid≤divis m (suc n-1) = begin
    (_div_ m n) * n                                      ≤⟨ ≤-steps (toℕ (DivMod.remainder dm)) (n≤n (DivMod.quotient dm * n)) ⟩
    toℕ (DivMod.remainder dm) + DivMod.quotient dm * n   ≡⟨ sym (DivMod.property dm) ⟩
    m                                                    ∎
  where n = suc n-1
        dm = _divMod_ m n
        open ≤-Reasoning

-- represents the homographic transform
--          a1*z + a
-- f(z) --> --------
--          b1*z + b
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

-- helper functions
repeat : ∀ {a} {A : Set a} → A → Colist A
repeat x = x ∷ (♯ (repeat x))

cycle : ∀ {a} {A : Set a} → List A → Colist A
cycle xs = cycle' xs xs
 where
  cycle' : ∀ {a} {A : Set a} → List A → List A → Colist A
  cycle' _ L[] = []
  cycle' xs (y L∷ L[]) = y ∷ ♯ (cycle' xs xs)
  cycle' xs (y L∷ ys) = y ∷ ♯ (cycle' xs ys)

ng-terminate : (m : NG) → {b≡0 : True (NG.b m ≟ 0)} → {b1≡0 : True (NG.b1 m ≟ 0)} → Colist (Maybe ℕ)
ng-terminate _ = []

-- Declaration of ng-apply type
-- Function defition below
ng-apply : NG → (ds : Colist ℕ) → {condition : Colist.All (Nat._<_ 0) ds} → Colist (Maybe ℕ)

ng-∞-step-output : (m : NG) → {b≢0 : False (NG.b m ≟ 0)} → {b1≢0 : False (NG.b1 m ≟ 0)} → {output : NG.output m {b≢0} {b1≢0}} → Colist (Maybe ℕ)
ng-∞-step-output (ng _ _ 0 _) {_} {()}
ng-∞-step-output (ng _ _ _ 0) {()}
ng-∞-step-output (ng a1 a (suc b1-1) (suc b-1)) {_} {_} {prf} = just t ∷ ♯ ng-apply (NG.∞-ingress (NG.egress op t {quot*divid≤divis a (suc b-1)} {NG.lemma op prf})) [] {[]}
                where op = ng a1 a (suc b1-1) (suc b-1)
                      t = NG.term op {tt}

ng-∞-step : (m : NG) → {b≢0 : False (NG.b m ≟ 0)} → {b1≢0 : False (NG.b1 m ≟ 0)} → Colist (Maybe ℕ)
ng-∞-step (ng _ _ 0 _) {_} {()}
ng-∞-step (ng _ _ _ 0) {()}
ng-∞-step (ng a1 a (suc b1-1) (suc b-1)) with NG.output? (ng a1 a (suc b1-1) (suc b-1)) {tt} {tt}
... | yes prf = ng-∞-step-output (ng a1 a (suc b1-1) (suc b-1)) {tt} {tt} {prf}
... | no _ = ng-∞-step-output (NG.∞-ingress (ng a1 a (suc b1-1) (suc b-1))) {tt} {tt} {refl}

ng-step : (m : NG) → {b≢0 : False (NG.b m ≟ 0)} → {b1≢0 : False (NG.b1 m ≟ 0)} → (ds : Colist ℕ) → {condition : Colist.All (Nat._<_ 0) ds} → Colist (Maybe ℕ)
ng-step (ng _ _ 0 _) {_} {()}
ng-step (ng _ _ _ 0) {()}
ng-step (ng a1 a (suc b1-1) (suc b-1)) (x ∷ xs) {c ∷ cs} with NG.output? (ng a1 a (suc b1-1) (suc b-1)) {tt} {tt}
... | yes prf = just t ∷ ♯ ng-apply (NG.ingress (NG.egress op t {quot*divid≤divis (NG.a op) (NG.b op)} {NG.lemma op prf}) x) (♭ xs) {♭ cs}
                where op = ng a1 a (suc b1-1) (suc b-1)
                      t = NG.term op {tt}
... | no _ = nothing ∷ ♯ (ng-apply (NG.ingress (ng a1 a (suc b1-1) (suc b-1)) x) (♭ xs) {♭ cs})
ng-step op {b≢0} {b1≢0} [] = ng-∞-step op {b≢0} {b1≢0}

ns-step-b≡0 : (m : NG) → {b≡0 : True (NG.b m ≟ 0)} → {b1≢0 : False (NG.b1 m ≟ 0)} → (ds : Colist ℕ) → {condition : Colist.All (Nat._<_ 0) ds} → Colist (Maybe ℕ)
ns-step-b≡0  (ng _ _ 0 _) {_} {()}
ns-step-b≡0  (ng a1 a _ (suc _)) {()}
ns-step-b≡0  (ng a1 a (suc b1-1) 0) [] = ng-∞-step (NG.∞-ingress (ng a1 a (suc b1-1) 0))
ns-step-b≡0  (ng a1 a (suc b1-1) 0) (x ∷ xs) {c ∷ cs} = ng-step (NG.ingress (ng a1 a (suc b1-1) 0) x) {tt} {fromWitnessFalse prf} (♭ xs) {♭ cs}
 where lem : ¬ (x ≡ 0 ⊎ suc b1-1 ≡ 0)
       lem (inj₁ x≡0) = 0<n→n≢0 c x≡0
       lem (inj₂ ())
       prf : ¬ NG.b1 (NG.ingress (ng a1 a (suc b1-1) 0) x) ≡ 0
       prf b1≡0 = contradiction (i*j≡0⇒i≡0∨j≡0 x b1≡0) lem

-- We are done here since b == b1 == 0
ng-apply (ng a1 a 0 0) _ = ng-terminate (ng a1 a 0 0)

-- No terms left in the input. Inject ∞ into input.
ng-apply (ng a1 a 0 b) [] = ng-terminate (NG.∞-ingress (ng a1 a 0 b))
ng-apply (ng a1 a (suc b1-1) 0) [] = ng-∞-step (NG.∞-ingress (ng a1 a (suc b1-1) 0))
ng-apply (ng a1 a (suc b1-1) (suc b-1)) [] {c} = ng-∞-step (ng a1 a (suc b1-1) (suc b-1))

-- Eat up an input term
ng-apply (ng a1 a 0 (suc b-1)) (x ∷ xs) {c ∷ cs} = ns-step-b≡0 (NG.ingress (ng a1 a 0 (suc b-1)) x) (♭ xs) {♭ cs}
ng-apply (ng a1 a (suc b1-1) 0) (x ∷ xs) {c ∷ cs} = ns-step-b≡0 (ng a1 a (suc b1-1) 0) (x ∷ xs) {c ∷ cs}
ng-apply (ng a1 a (suc b1-1) (suc b-1)) xs {cs} = ng-step (ng a1 a (suc b1-1) (suc b-1)) xs {cs}

-- rational to continued fraction
r2cf : (numerator : ℕ) → (denominator : ℕ) → Colist ℕ
r2cf _ 0 = []
r2cf n (ℕ.suc d-1) = DivMod.quotient x ∷ ♯ (r2cf d (toℕ (DivMod.remainder x)))
 where
  d = ℕ.suc d-1
  x = n divMod d

-- can be a helpful lemma
map-suc-pred-lemma : (list : Colist ℕ) → Colist.All (Nat._<_ 0) (Colist.map (Nat.suc ∘ Nat.pred) list)
map-suc-pred-lemma [] = []
map-suc-pred-lemma (x ∷ xs) = s≤s z≤n ∷ ♯ (map-suc-pred-lemma (♭ xs))

-- square root of 2 as a continued fraction
sqrt2 : Colist ℕ
sqrt2 = 1 ∷ (♯ (repeat 2))

private
 e-pattern : ℕ → Colist ℕ
 e-pattern x = x ∷ ♯ (1 ∷ ♯ (1 ∷ ♯ (e-pattern (2 + x))))
 
 e-pattern-condition : (n : ℕ) → {cond : 0 Nat.< n} → Colist.All (Nat._<_ 0) (e-pattern n)
 e-pattern-condition 0 {()}
 e-pattern-condition (suc n-1) = (s≤s z≤n) ∷ ♯ ((s≤s z≤n) ∷ ♯ ((s≤s z≤n) ∷ ♯ (e-pattern-condition (3 + n-1) {s≤s z≤n})))

-- constant e from natural logarithm
e-constant : Colist ℕ
e-constant = 2 ∷ ♯ (1 ∷ ♯ (e-pattern 2))

e-condition : Colist.All (Nat._<_ 0) e-constant
e-condition = (s≤s z≤n) ∷ ♯ ((s≤s z≤n) ∷ ♯ (e-pattern-condition 2 {s≤s z≤n}))

-- some tests
test₀ = take 10 $ ng-apply (ng 2 1 0 2) (r2cf 13 11) {s≤s z≤n ∷ ♯ (s≤s z≤n ∷ ♯ (s≤s z≤n ∷ ♯ []))}
test₁ = take 10 $ ng-apply (ng 2 1 0 2) (r2cf 22 7) {s≤s z≤n ∷ ♯ (s≤s z≤n ∷ ♯ [])}
test₂ = take 10 $ ng-apply (ng 1 0 0 4) (r2cf 22 7) {s≤s z≤n ∷ ♯ (s≤s z≤n ∷ ♯ [])}
test₃ = take 10 $ ng-apply (ng 1 0 0 4) sqrt2 {s≤s z≤n ∷ ♯ prf}
  where prf : Colist.All (Nat._<_ 0) (repeat 2)
        prf = s≤s z≤n ∷ ♯ prf
test₄ = take 20 $ ng-apply (ng 1 0 1 2) (less-1 e-constant) {(s≤s z≤n) ∷ ♯ ((s≤s z≤n) ∷ ♯ (e-pattern-condition 2 {s≤s z≤n}))}   -- (e-1)/(e+1)
 where less-1 : Colist ℕ → Colist ℕ
       less-1 [] = []
       less-1 (x ∷ xs) = (Nat.pred x) ∷ xs

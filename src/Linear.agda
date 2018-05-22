module Linear where

open import Data.Product
open import Data.Sum
open import Data.Empty

-- 1. PROPOSITIONAL FRAGMENT


infixr 0 _⊸_
infixr 1 _⊕_ _⅋_
infixr 2 _&_ _⊗_


-- Linear propositions consist of a positive part (affirmation, φ₊) and a negative
-- part (refutation, φ₋). We prove a linear proposition by proving its affirmation.
-- If we have a refutation then we cannot have an affirmation, on pain of contra-
-- diction.
data LProp : Set₁ where
  lprop : (φ₊ : Set) → (φ₋ : Set) → (φ₋ → φ₊ → ⊥) → LProp


-- Linear negation exchanges affirmations and refutations.
~ : LProp → LProp
~ (lprop φ₊ φ₋ p) = lprop φ₋ φ₊ (λ a b → p b a)


-- Additive conjunction
_&_ : LProp → LProp → LProp
(lprop φ₊ φ₋ p) & (lprop ψ₊ ψ₋ q) = lprop (φ₊ × ψ₊) (φ₋ ⊎ ψ₋) pq where
  pq : (φ₋ ⊎ ψ₋) → (φ₊ × ψ₊) → ⊥
  pq (inj₁ ~a) (a , b) = p ~a a
  pq (inj₂ ~b) (a , b) = q ~b b


-- Additive disjunction: notice the symmetry between the proofs `pq` between
-- additive conjunctions and additive disjunctions.
_⊕_ : LProp → LProp → LProp
(lprop φ₊ φ₋ p) ⊕ (lprop ψ₊ ψ₋ q) = lprop (φ₋ ⊎ ψ₋) (φ₊ × ψ₊) pq where
  pq : (φ₊ × ψ₊) → (φ₋ ⊎ ψ₋) → ⊥
  pq (a , b) (inj₁ ~a) = p ~a a
  pq (a , b) (inj₂ ~b) = q ~b b


-- Multiplicative conjunction
_⊗_ : LProp → LProp → LProp
(lprop φ₊ φ₋ p) ⊗ (lprop ψ₊ ψ₋ q) = lprop (φ₊ × ψ₊) ((φ₊ → ψ₋) × (ψ₊ → φ₋)) pq where
  pq : ((φ₊ → ψ₋) × (ψ₊ → φ₋)) → (φ₊ × ψ₊) → ⊥
  pq (f , g) (a , b) = q (f a) b


-- Multiplicative disjunction
_⅋_ : LProp → LProp → LProp
(lprop φ₊ φ₋ p) ⅋ (lprop ψ₊ ψ₋ q) = lprop ((ψ₋ → φ₊) × (φ₋ → ψ₊)) (φ₋ × ψ₋) pq where
  pq : (φ₋ × ψ₋) → ((ψ₋ → φ₊) × (φ₋ → ψ₊)) → ⊥
  pq (~a , ~b) (f , g) = q ~b (g ~a)


-- Linear implication
_⊸_ : LProp → LProp → LProp
p ⊸ q = (~ p) ⅋ q


⟦_⟧ : LProp → Set
⟦ lprop φ₊ _ _ ⟧ = φ₊ 


----------
-- Here we prove that these connectives satisfy Hesselink's axioms and rules
-- for the multiplicative fragment of linear logic. See also:
-- W. H. Hesselink: Axioms and models of linear logic, in Formal Aspects of Computing, 1990)


-- Identity axiom.
axiom-1 : (P : LProp) → ⟦ P ⊸ P ⟧
axiom-1 (lprop φ₊ φ₋ p) =
  (λ x → x) ,
  (λ x → x)


-- Commutativity of ⅋.
axiom-2 : (P Q : LProp) → ⟦ (P ⅋ Q) ⊸ (Q ⅋ P) ⟧
axiom-2 (lprop φ₊ φ₋ p) (lprop ψ₊ ψ₋ q) =
  (λ x → proj₂ x , proj₁ x) ,
  (λ x → proj₂ x , proj₁ x)


-- Associativity of ⅋: the proof looks ugly, but we really just re-associate ×.
axiom-3 : (P Q R : LProp) → ⟦ ((P ⅋ Q) ⅋ R) ⊸ (P ⅋ (Q ⅋ R)) ⟧
axiom-3
  (lprop φ₊ φ₋ p)
  (lprop ψ₊ ψ₋ q)
  (lprop ρ₊ ρ₋ r) =
    (λ x → (proj₁ x , proj₁ (proj₂ x)) , proj₂ (proj₂ x)) ,
    (λ x → (λ y → proj₁ (proj₁ x (proj₂ y)) (proj₁ y)) ,
    (λ y → (λ (z : ρ₋) → proj₂ (proj₁ x z) y) ,
    (λ z → proj₂ x (y , z))))


-- Finally, the analogues of the rules of inferece work as expected.
mp-rule : (P Q : LProp) → ⟦ P ⟧ → ⟦ P ⊸ Q ⟧ → ⟦ Q ⟧
mp-rule
  (lprop φ₊ φ₋ p)
  (lprop ψ₊ ψ₋ q) a ab =
    proj₂ ab a


mp-rule-ctx : (Γ P Q : LProp) → ⟦ Γ ⅋ P ⟧ → ⟦ P ⊸ Q ⟧ → ⟦ Γ ⅋ Q ⟧
mp-rule-ctx
  (lprop γ₊ γ₋ g)
  (lprop φ₊ φ₋ p)
  (lprop ψ₊ ψ₋ q) a ab =
    (λ x → proj₁ a (proj₁ ab x)) ,
    (λ x → proj₂ ab (proj₂ a x))


----------
-- Here we prove the involutive property of negation.

open import Relation.Binary.PropositionalEquality

theorem : (P : LProp) → ~ (~ P) ≡ P
theorem (lprop φ₊ φ₋ x) = refl

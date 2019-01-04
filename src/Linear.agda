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


_⊢_ : LProp → LProp → Set
Γ ⊢ P = ⟦ Γ ⊸ P ⟧

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

-- A deduction-like variant of the same result.
deduction : (Γ P Q : LProp) → (Γ ⅋ P) ⊢ Q → Γ ⊢ (P ⊸ Q)
deduction
  (lprop γ₊ γ₋ _)
  (lprop φ₊ φ₋ _)
  (lprop ψ₊ ψ₋ _) gpq =
    (λ pq → helper1 (proj₂ pq)) ,
    (λ g → helper2 ,
    (λ p → helper3 (λ _ → g) (λ _ → p))) where
      helper1 : ψ₋ → γ₋
      helper1 x = proj₁ (proj₁ gpq x)
      helper2 : ψ₋ → φ₋
      helper2 x = proj₂ (proj₁ gpq x)
      helper3 : (φ₋ → γ₊) → (γ₋ → φ₊) → ψ₊
      helper3 x y = proj₂ gpq (x , y)

----------
-- Here we prove the involutive property of negation.

open import Relation.Binary.PropositionalEquality

theorem : (P : LProp) → ~ (~ P) ≡ P
theorem (lprop φ₊ φ₋ x) = refl


-- 2. PROPOSITIONAL-EXPONENTIAL FRAGMENT

-- The "of course!" modality
! : LProp → LProp
! (lprop φ₊ φ₋ _) = lprop φ₊ (φ₊ → ⊥) λ z → z

-- The "why not?" modality
⁇ : LProp → LProp
⁇ (lprop φ₊ φ₋ _) = lprop (φ₋ → ⊥) φ₋ λ x y → y x

----------
-- Here we verify that the H-CLL axioms hold for the modalities.

-- A weakening axiom
axiom-1! : (P Q : LProp) → ⟦ P ⊸ (! Q ⊸ P) ⟧
axiom-1!
  (lprop φ₊ φ₋ p)
  (lprop ψ₊ ψ₋ q) =
    proj₂ ,
    λ y → (λ x _ → p x y) , (λ _ → y)

axiom-2! : (P Q : LProp) → ⟦ ! (P ⊸ Q) ⊸ (! P ⊸ ! Q) ⟧
axiom-2!
  (lprop φ₊ φ₋ p)
  (lprop ψ₊ ψ₋ q) =
    (λ x y → proj₂ x (proj₂ y (proj₁ x))) ,
    (λ x → (λ y z → y (proj₂ x z)) , proj₂ x)

axiom-3! : (P : LProp) → ⟦ ! P ⊸ P ⟧
axiom-3! (lprop φ₊ φ₋ p) = p , (λ x → x)

axiom-4! : (P : LProp) → ⟦ ! P ⊸ ! (! P) ⟧
axiom-4! (lprop φ₊ φ₋ p) = (λ x → x) , (λ x → x)

-- A contraction axiom
axiom-5! : (P Q : LProp) → ⟦ (! P ⊸ (! P ⊸ Q)) ⊸ (! P ⊸ Q) ⟧
axiom-5!
  (lprop φ₊ φ₋ p)
  (lprop ψ₊ ψ₋ q) =
  (λ pq → proj₁ pq , proj₁ pq , proj₂ pq) ,
  (λ x → (λ y z → proj₁ x (z , y) z) ,
  (λ y → proj₂ (proj₂ x y) y))

-- Fortunately, the modal inference rule is trivially verified.

modal-rule : (P : LProp) → ⟦ P ⟧ → ⟦ ! P ⟧
modal-rule (lprop φ₊ φ₋ p) x = x


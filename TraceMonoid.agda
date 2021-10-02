{-# OPTIONS --cubical #-}

module TraceMonoid where

open import Agda.Primitive
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Monoid

private
  variable
    ℓ : Level
    ℓ' : Level

record IsIndependency {ℓ'} {A : Type ℓ} (_#_ : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ')  where
  field

    #-irrefl : ∀ {x} → ¬ ( x # x )
    #-sym : ∀ {x y} → x # y → y # x

infixr 20 _̇_

-- Partially commutative monoid allowing for commuting independent letters.
-- The definition is inspired by ListedFiniteSet
data Pcm {ℓ'} (A : Type ℓ) (_#_ : A → A → Type ℓ') {{φ : IsIndependency _#_}} : Type (ℓ-max ℓ ℓ') where
  ε    : Pcm A _#_
  _̇_ : A → Pcm A _#_ → Pcm A _#_
  pcm-comm : ∀ (a b : A) (s : Pcm A _#_) {ind : a # b} → a ̇ b ̇ s ≡ b ̇ a ̇ s
  squashPcm : (x y : Pcm A _#_) (p q : x ≡ y) → p ≡ q


-- Elimination  principle for PCMs
module Elim {ℓ' ℓ''} {A : Type ℓ} {_#_ : A → A → Type ℓ''}
                 {{φ : IsIndependency _#_}}
                 {B : (Pcm A _#_) → Type ℓ'}
       (ε* : B ε) (_̇*_ : (x : A) {xs : Pcm A _#_} → B xs → B (x ̇ xs))
       (pcm-comm* :  (x y : A) {xs : Pcm A _#_} (b : B xs)
              → (ind : x # y)
              → PathP (λ i → B (pcm-comm x y xs {ind} i)) (x ̇* (y ̇* b)) (y ̇* (x ̇* b)))
       (squashPcm* : (xs : Pcm A _#_) → isSet (B xs)) where

 f : (xs : Pcm A _#_) → B xs
 f ε = ε*
 f (x ̇ xs) = x ̇* f xs
 f (pcm-comm x y xs i) = pcm-comm* x y (f xs) _ i
 f (squashPcm xs ys p q i j) = isOfHLevel→isOfHLevelDep 2 squashPcm*  (f xs) (f ys) (cong f p) (cong f q) (squashPcm xs ys p q) i j

module Rec {ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} (BType : isSet B) {_#_ : A → A → Type ℓ''}
                   {{φ : IsIndependency _#_}}
       (ε* : B) (_̇*_ : (x : A) → B → B)
       (pcm-comm* :  (x y : A) (b : B)
              → (ind : x # y)
              → (x ̇* (y ̇* b)) ≡ (y ̇* (x ̇* b))) where
 f : (xs : Pcm A _#_) → B
 f = Elim.f ε* (λ x b → x ̇* b) (λ x y b ind → pcm-comm* x y b ind) (λ _ → BType)


size  : {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} → (m : Pcm A _#_) → ℕ
size m = Rec.f isSetℕ 0 (λ _ n → 1 + n) (λ x y b _ → refl) m

infixr 5 _^_

_^_ : {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} (p₁ p₂ : Pcm A _#_) → Pcm A _#_
ε ^ p₂ = p₂
x ̇ p₁ ^ p₂ = x ̇ (p₁ ^ p₂)
pcm-comm a b p₁ {ind = ind} i ^ p₂ = pcm-comm a b (p₁ ^ p₂) {ind} i
squashPcm p₁ p₃ p q i j ^ p₂ = squashPcm (p₁ ^ p₂) (p₃ ^ p₂) (cong (_^ p₂) p) (cong (_^ p₂) q) i j


^-idR : {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} (p : Pcm A _#_) → p ^ ε ≡ p
^-idR ε = refl
^-idR (x ̇ p) = cong (x ̇_) (^-idR _)
^-idR (pcm-comm a b p i) = (cong (λ x → pcm-comm a b x i) (^-idR _))
^-idR (squashPcm p p₁ p₂ q i j) =
  isOfHLevelPathP' {A = λ i → PathP (λ j → (squashPcm p p₁ p₂ q i j) ^ ε ≡ squashPcm p p₁ p₂ q i j) (^-idR p) (^-idR p₁)}
                   0 ((isOfHLevelPathP' 1 (isOfHLevelSuc 2 squashPcm _ _) _ _)) (cong ^-idR p₂) (cong ^-idR q) .fst i j

^-assoc : {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} (s₁ s₂ s₃ : Pcm A _#_) → s₁ ^ s₂ ^ s₃ ≡ (s₁ ^ s₂) ^ s₃
^-assoc ε s₂ s₃ = refl
^-assoc (x ̇ s₁) s₂ s₃ = cong (x ̇_) (^-assoc s₁ s₂ s₃)
^-assoc (pcm-comm a b s₁ {ind} i) s₂ s₃ = (cong (λ x → pcm-comm a b x {ind} i) (^-assoc s₁ s₂ s₃))
^-assoc (squashPcm s₁ s₄ p q i j) s₂ s₃ =
  isOfHLevelPathP' {A = λ i → PathP (λ j → squashPcm s₁ s₄ p q i j ^ s₂ ^ s₃ ≡ (squashPcm s₁ s₄ p q i j ^ s₂) ^ s₃) (^-assoc s₁ s₂ s₃) ( ^-assoc s₄ s₂ s₃)}
                   0 ((isOfHLevelPathP' 1 (isOfHLevelSuc 2 squashPcm _ _) _ _)) (cong (λ x → ^-assoc x s₂ s₃) p) (cong (λ x → ^-assoc x s₂ s₃) q) .fst i j

pcm-cong-head : ∀ {A : Set } {_#_ : A → A → Set} {{φ : IsIndependency _#_}} {s₁ s₂ s₃ : Pcm A _#_} → s₂ ≡ s₃ → s₁ ^ s₂ ≡ s₁ ^ s₃
pcm-cong-head {s₁ = s₁} p = cong (_^_ s₁) p

monPcm : ∀ {A : Set } {_#_ : A → A → Set} {{φ : IsIndependency _#_}} → IsMonoid ε _^_
monPcm = makeIsMonoid squashPcm ^-assoc ^-idR (λ x → refl)

{-# OPTIONS --cubical #-}

module TraceMonoid where

open import Agda.Primitive
open import Cubical.Data.Empty as ⊥
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Monoid


infix 3 ¬_

¬_ : Set → Set
¬ X = X → ⊥

record IsIndependency {A : Set} (_#_ : A → A → Set) : Set where
  field

    #-irrefl : ∀ {x} → ¬ ( x # x )
    #-sym : ∀ {x y} → x # y → y # x

infixr 20 _̇_

-- Partially commutative monoid allowing for commuting independent letters.
-- The definition is inspired by ListedFiniteSet
data Pcm (A : Set) (_#_ : A → A → Set) {{φ : IsIndependency _#_}} : Set where
  ε    : Pcm A _#_
  _̇_ : A → Pcm A _#_ → Pcm A _#_
  pcm-comm : ∀ (a b : A) (s : Pcm A _#_) {ind : a # b} → a ̇ b ̇ s ≡ b ̇ a ̇ s
  squashPcm : (x y : Pcm A _#_) (p q : x ≡ y) → p ≡ q

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

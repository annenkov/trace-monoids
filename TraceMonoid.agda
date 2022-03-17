{-# OPTIONS --cubical -W noNoEquivWhenSplitting #-}

module TraceMonoid where

open import Agda.Primitive
open import Cubical.Relation.Nullary
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (_∙_)
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.Monoid

private
  variable
    ℓ : Level
    ℓ₀ : Level
    ℓ₁ : Level

record IsIndependence {A : Type ℓ} (_#_ : A → A → Type ℓ₀) : Type (ℓ-max ℓ ℓ₀)  where
  field
    #-irrefl : ∀ {x} → ¬ ( x # x )
    #-sym : ∀ {x y} → x # y → y # x

infixr 20 _∙_

-- Free partially commutative monoid allowing for commuting independent letters.
-- The definition is inspired by ListedFiniteSet
data FreePcm (A : Type ℓ) (_#_ : A → A → Type ℓ₀) ⦃ _ : IsIndependence _#_ ⦄ : Type (ℓ-max ℓ ℓ₀) where
  ε    : FreePcm A _#_
  _∙_ : A → FreePcm A _#_ → FreePcm A _#_
  pcm-comm : ∀ a b s → a # b → a ∙ b ∙ s ≡ b ∙ a ∙ s
  squashFreePcm : isSet (FreePcm A _#_)

-- Elimination  principle for FreePcm
module Elim {ℓ₀ ℓ₁} {A : Type ℓ} {_#_ : A → A → Type ℓ₁}
                 {{φ : IsIndependence _#_}}
                 {B : (FreePcm A _#_) → Type ℓ₀}
       (ε* : B ε) (_∙*_ : (x : A) {xs : FreePcm A _#_} → B xs → B (x ∙ xs))
       (pcm-comm* :  (x y : A) {xs : FreePcm A _#_} (b : B xs)
              → (ind : x # y)
              → PathP (λ i → B (pcm-comm x y xs ind i)) (x ∙* (y ∙* b)) (y ∙* (x ∙* b)))
       (squashFreePcm* : (xs : FreePcm A _#_) → isSet (B xs)) where

 f : (xs : FreePcm A _#_) → B xs
 f ε = ε*
 f (x ∙ xs) = x ∙* f xs
 f (pcm-comm x y xs _ i) = pcm-comm* x y (f xs) _ i
 f (squashFreePcm xs ys p q i j) = isOfHLevel→isOfHLevelDep 2 squashFreePcm*  (f xs) (f ys) (cong f p) (cong f q) (squashFreePcm xs ys p q) i j

module Rec {ℓ₀ ℓ₁} {A : Type ℓ} {B : Type ℓ₀} (BType : isSet B) {_#_ : A → A → Type ℓ₁}
                   {{φ : IsIndependence _#_}}
       (ε* : B) (_∙*_ : (x : A) → B → B)
       (pcm-comm* :  (x y : A) (b : B)
              → (ind : x # y)
              → (x ∙* (y ∙* b)) ≡ (y ∙* (x ∙* b))) where
 f : (xs : FreePcm A _#_) → B
 f = Elim.f ε* (λ x b → x ∙* b) (λ x y b ind → pcm-comm* x y b ind) (λ _ → BType)


size  : {A : Set} {_#_ : A → A → Set} {{φ : IsIndependence _#_}} → (m : FreePcm A _#_) → ℕ
size m = Rec.f isSetℕ 0 (λ _ n → 1 + n) (λ x y b _ → refl) m

infixr 5 _^_

_^_ : {A : Set} {_#_ : A → A → Set} {{φ : IsIndependence _#_}} (p₁ p₂ : FreePcm A _#_) → FreePcm A _#_
ε ^ p₂ = p₂
x ∙ p₁ ^ p₂ = x ∙ (p₁ ^ p₂)
pcm-comm a b p₁ ind i ^ p₂ = pcm-comm a b (p₁ ^ p₂) ind i
squashFreePcm p₁ p₃ p q i j ^ p₂ = squashFreePcm (p₁ ^ p₂) (p₃ ^ p₂) (cong (_^ p₂) p) (cong (_^ p₂) q) i j


^-idR : {A : Set} {_#_ : A → A → Set} {{φ : IsIndependence _#_}} (p : FreePcm A _#_) → p ^ ε ≡ p
^-idR ε = refl
^-idR (x ∙ p) = cong (x ∙_) (^-idR _)
^-idR (pcm-comm a b p ind i) = (cong (λ x → pcm-comm a b x ind i) (^-idR _))
^-idR (squashFreePcm p p₁ p₂ q i j) =
  isOfHLevelPathP' {A = λ i → PathP (λ j → (squashFreePcm p p₁ p₂ q i j) ^ ε ≡ squashFreePcm p p₁ p₂ q i j) (^-idR p) (^-idR p₁)}
                   0 ((isOfHLevelPathP' 1 (isOfHLevelSuc 2 squashFreePcm _ _) _ _)) (cong ^-idR p₂) (cong ^-idR q) .fst i j

^-assoc : {A : Set} {_#_ : A → A → Set} {{φ : IsIndependence _#_}} (s₁ s₂ s₃ : FreePcm A _#_) → s₁ ^ s₂ ^ s₃ ≡ (s₁ ^ s₂) ^ s₃
^-assoc ε s₂ s₃ = refl
^-assoc (x ∙ s₁) s₂ s₃ = cong (x ∙_) (^-assoc s₁ s₂ s₃)
^-assoc (pcm-comm a b s₁ ind i) s₂ s₃ = (cong (λ x → pcm-comm a b x ind i) (^-assoc s₁ s₂ s₃))
^-assoc (squashFreePcm s₁ s₄ p q i j) s₂ s₃ =
  isOfHLevelPathP' {A = λ i → PathP (λ j → squashFreePcm s₁ s₄ p q i j ^ s₂ ^ s₃ ≡ (squashFreePcm s₁ s₄ p q i j ^ s₂) ^ s₃) (^-assoc s₁ s₂ s₃) ( ^-assoc s₄ s₂ s₃)}
                   0 ((isOfHLevelPathP' 1 (isOfHLevelSuc 2 squashFreePcm _ _) _ _)) (cong (λ x → ^-assoc x s₂ s₃) p) (cong (λ x → ^-assoc x s₂ s₃) q) .fst i j

pcm-cong-head : ∀ {A : Set } {_#_ : A → A → Set} {{φ : IsIndependence _#_}} {s₁ s₂ s₃ : FreePcm A _#_} → s₂ ≡ s₃ → s₁ ^ s₂ ≡ s₁ ^ s₃
pcm-cong-head {s₁ = s₁} p = cong (_^_ s₁) p

monFreePcm : ∀ {A : Set } {_#_ : A → A → Set} {{φ : IsIndependence _#_}} → IsMonoid ε _^_
monFreePcm = makeIsMonoid squashFreePcm ^-assoc ^-idR (λ x → refl)

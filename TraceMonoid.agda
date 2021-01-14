{-# OPTIONS --cubical #-}

module TraceMonoid where

open import Agda.Primitive
open import Cubical.Data.Empty as ⊥
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Monoid


infixr 40 _^_


infix 3 ¬_

¬_ : Set → Set
¬ X = X → ⊥

record IsIndependency {A : Set} (_#_ : A → A → Set) : Set where
  field

    #-irrefl : ∀ {x} → ¬ ( x # x )
    #-sym : ∀ {x y} → x # y → y # x

--| Partially commutative monoid allowing for commuting independent letters.
--| The definition is based on "join" lists
data Pcm (A : Set) (_#_ : A → A → Set) {{φ : IsIndependency _#_}} : Set where
  ε    : Pcm A _#_
  [_]  : A → Pcm A _#_
  _^_ : Pcm A _#_ → Pcm A _#_ → Pcm A _#_
  assoc : ∀ {s₁ s₂ s₃ : Pcm A _#_} → s₁ ^ s₂ ^ s₃ ≡ (s₁ ^ s₂) ^ s₃
  idR : ∀ {s : Pcm A _#_} → s ^ ε ≡ s
  idL : ∀ {s : Pcm A _#_} → ε ^ s ≡ s
  abComm : ∀ (s₁ s₂ : Pcm A _#_) (a b : A) → (s₁ ^ ([ a ] ^ [ b ]) ^ s₂) ≡ (s₁ ^ ([ b ] ^ [ a ]) ^ s₂)
  squashPcm : ∀ x y → (p q : x ≡ y) → p ≡ q


infixr 20 _̇_

_̇_ : ∀ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} → A → Pcm A _#_ → Pcm A _#_
x ̇ xs =  [ x ] ^ xs

pcm-cong-head : ∀ {A : Set } {_#_ : A → A → Set} {{φ : IsIndependency _#_}} {s₁ s₂ s₃ : Pcm A _#_} → s₂ ≡ s₃ → s₁ ^ s₂ ≡ s₁ ^ s₃
pcm-cong-head {s₁ = s₁} p = cong (_^_ s₁) p

monPcm : ∀ {A : Set } {_#_ : A → A → Set} {{φ : IsIndependency _#_}} → IsMonoid ε _^_
monPcm = makeIsMonoid squashPcm (λ x y z → assoc) (λ x → idR)  (λ x → idL )

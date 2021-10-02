{-# OPTIONS --cubical --rewriting #-}

module DoubleCat where

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
-- open import Cubical.Data.Graph

record Graph (V : Set) : Type₁ where
  field
    Edge : V → V → Set

  -- constructor _⟶_
infixl 5 _•_

-- open Arr

data GPath {V : Set} (G : Graph V) : V → V → Type₁ where
  id    : ∀ {a : V} → GPath G a a
  _⟶_   : ∀ (a b : V) → Graph.Edge G a b → GPath G a b
  _•_ : ∀ {a b c} → GPath G a b → GPath G b c → GPath G a c
  assoc : ∀ {a b c d} {f : GPath G a b} {g : GPath G b c} {h : GPath G c d} → f • g • h ≡ (f • g) • h
  idR : ∀ {a b} {f : GPath G a b} → f • id ≡ f
  idL : ∀ {a b} {f : GPath G a b} → id • f ≡ f
  -- abComm : ∀ (s₁ s₂ : Pcm A _#_) (a b : A) {i : a # b} → (s₁ ^ ([ a ] ^ [ b ]) ^ s₂) ≡ (s₁ ^ ([ b ] ^ [ a ]) ^ s₂)
  -- squashPcm : ∀ x y → (p q : x ≡ y) → p ≡ q

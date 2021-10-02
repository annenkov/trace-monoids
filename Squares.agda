{-# OPTIONS --cubical --rewriting #-}

module Squares where

open import Agda.Primitive
open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import TraceMonoid


data □ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} (left top bottom right : Pcm A _#_ ) : Set  where
  □-ctor : □ left top bottom right

□-left : ∀ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} {l t b r} (s : □ l t b r) → Pcm A _#_
□-left {l = l} _ = l

□-top : ∀ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} {l t b r} (s : □ l t b r) → Pcm A _#_
□-top {t = t} _ = t

□-bottom : ∀ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} {l t b r} (s : □ l t b r) → Pcm A _#_
□-bottom {b = b} _ = b

□-right : ∀ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} {l t b r} (s : □ l t b r) → Pcm A _#_
□-right {r = r} _ = r

■-filled : ∀ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} (l t b r : Pcm A _#_) → Set
■-filled l t b r = Σ[ s ∈ □ l t b r ] (□-left s ^ □-top s ≡ □-bottom s ^ □-right s)

■-deg-hor : ∀ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} (l : Pcm A _#_) → ■-filled l ε ε l
■-deg-hor l = ( □-ctor , ^-idR l )

■-deg-ver : ∀ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} (t : Pcm A _#_) → ■-filled ε t t ε
■-deg-ver t = ( □-ctor , sym (^-idR _) )


-- horisontal composition

infixr 5 _﹔_

_﹔_ : ∀ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} {l₁ t₁ b₁ r₁ t₂ b₂ r₂}
       (f : □ l₁ t₁ b₁ r₁) (g : □ r₁ t₂ b₂ r₂) → □ l₁ (t₁ ^ t₂) (b₁ ^ b₂) r₂
f ﹔ g = □-ctor

﹔-idL : ∀ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} {l t b r}
         (s : □ l t b r) → (■-deg-hor l) .fst ﹔ s ≡ s
﹔-idL □-ctor = refl

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE ^-idR #-}

﹔-idR : ∀ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} {l t b r}
         (s : □ l t b r) → s ﹔ (■-deg-hor r) .fst ≡ s
﹔-idR □-ctor = refl

{-# REWRITE ^-assoc #-}

﹔-assoc : ∀ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} {l₁ t₁ b₁ r₁ t₂ b₂ r₂ t₃ b₃ r₃}
       (f : □ l₁ t₁ b₁ r₁) (g : □ r₁ t₂ b₂ r₂) (h : □ r₂ t₃ b₃ r₃) → f ﹔ g ﹔ h ≡ (f ﹔ g) ﹔ h
﹔-assoc _ _ _ = refl

-- vertical composition

infixr 5 _⋆_

_⋆_ : ∀ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} {l₁ t₁ b₁ r₁ l₂ b₂ r₂}
       (f : □ l₁ t₁ b₁ r₁) (g : □ l₂ b₁ b₂ r₂) → □ (l₁ ^ l₂) t₁ b₂ (r₁ ^ r₂)
f ⋆ g = □-ctor

⋆-idL : ∀ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} {l t b r}
         (s : □ l t b r) → (■-deg-ver t) .fst ⋆ s ≡ s
⋆-idL □-ctor = refl

⋆-idR : ∀ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} {l t b r}
         (s : □ l t b r) → s ⋆ (■-deg-ver b) .fst  ≡ s
⋆-idR □-ctor = refl

⋆-assoc : ∀ {A : Set} {_#_ : A → A → Set} {{φ : IsIndependency _#_}} {l₁ t₁ b₁ r₁ l₂ b₂ r₂ l₃ b₃ r₃}
       (f : □ l₁ t₁ b₁ r₁) (g : □ l₂ b₁ b₂ r₂) (h : □ l₃ b₂ b₃ r₃) → f ⋆ g ⋆ h ≡ (f ⋆ g) ⋆ h
⋆-assoc _ _ _ = refl

data PVLang : Set where
  Pa : PVLang
  Pb : PVLang
  Va : PVLang
  Vb : PVLang
  LocalC : PVLang -- local computation

Prog = ℕ × PVLang

data _#'_ : PVLang → PVLang → Set where
  VaVb : Va #' Vb
  VbVa : Vb #' Va
  LocalCLocalC : LocalC #' LocalC

#'-sym : ∀ {e₁ e₂ : PVLang} → e₁ #' e₂ → e₂ #' e₁
#'-sym VaVb = VbVa
#'-sym VbVa = VaVb
#'-sym LocalCLocalC = LocalCLocalC


_≠_ : ∀ {A : Set} (a b : A) → Set
a ≠ b = a ≡ b → ⊥

≠-sym : ∀ {A : Set} {a b : A} → a ≠ b → b ≠ a
≠-sym np q =  np (sym q)


data _#_ : Prog → Prog → Set where
  #-neq : ∀ pv₁ pv₂ →
          pv₁ .fst ≠ pv₂ .fst →
          pv₁ .snd #' pv₂ .snd →
          pv₁ # pv₂

#-irrefl : ∀ (x : Prog) → ¬ (x # x)
#-irrefl _ (#-neq _ _ q _) = q refl

#-sym : ∀ {e₁ e₂ : Prog} → e₁ # e₂ → e₂ # e₁
#-sym (#-neq _ _ q x) = #-neq _ _ (≠-sym q) (#'-sym x)

instance
  #-indep : IsIndependency _#_
  #-indep = record { #-irrefl = #-irrefl _ ;
                     #-sym = #-sym }

-- Program: LocalC.Pa.Va || LocalC.Pa.Va

row1 : □ ((1 , LocalC) ̇ ε) ((0 , LocalC) ̇ (0 , Pa) ̇ (0 , Va) ̇ ε ) ((0 , LocalC) ̇ (0 , Pa) ̇ (0 , Va) ̇ ε ) ((1 , LocalC) ̇ ε)
row1 = □-ctor

row2 : □ ((1 , Pa ) ̇ ε) ((0 , LocalC) ̇ (0 , Pa) ̇ (0 , Va) ̇ ε ) ((0 , LocalC) ̇ (0 , Pa) ̇ (0 , Va) ̇ ε ) ((1 , Pa) ̇ ε)
row2 = □-ctor

row3 : □ ((1 , Va ) ̇ ε) ((0 , LocalC) ̇ (0 , Pa) ̇ (0 , Va) ̇ ε ) ((0 , LocalC) ̇ (0 , Pa) ̇ (0 , Va) ̇ ε ) ((1 , Va) ̇ ε)
row3 = □-ctor


comp-rows = row3 ⋆ row2 ⋆ row1

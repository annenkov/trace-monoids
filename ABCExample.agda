{-# OPTIONS --cubical #-}

module ABCExample  where

open import TraceMonoid
open import Cubical.Foundations.Prelude hiding ( _∙_ )
open import Cubical.Relation.Nullary


--| alphabet
data 𝕃 : Set where
  A : 𝕃
  B : 𝕃
  C : 𝕃


data _#L_ : 𝕃 → 𝕃 → Set where
  AB : A #L B
  BA : B #L A

#L-irrefl : ∀ (x : 𝕃) → ¬ (x #L x)
#L-irrefl A = λ ()
#L-irrefl B =  λ ()
#L-irrefl C = λ ()

instance
  #L-indep : IsIndependence _#L_
  #L-indep = record { #-irrefl = #L-irrefl _;
                      #-sym = λ { AB → BA ; BA → AB }}

example1 : C ∙ A ∙ B ∙ ε ≡ C ∙ B ∙ A ∙ ε
example1 = pcm-cong-head {s₁ = C ∙ ε} (pcm-comm A B ε AB)

example2 : C ∙ A ∙ B ∙ B ∙ A ∙ ε ≡ C ∙ A ∙ A ∙ B ∙ B ∙ ε
example2 = pcm-cong-head {s₁ = C ∙ A ∙ ε}
           (B ∙ B ∙ A ∙ ε
            ≡⟨ cong (B ∙_) (pcm-comm B A ε BA) ⟩
            B ∙ A ∙ B ∙ ε
            ≡⟨ pcm-comm _ _ _ BA ⟩
            A ∙ B ∙ B ∙ ε ∎)

example-B-bubbles-up : A ∙ A ∙ A ∙ B ∙ ε ≡ B ∙ A ∙ A ∙ A ∙ ε
example-B-bubbles-up =
  sym (B ∙ A ∙ A ∙ A ∙ ε
       ≡⟨ pcm-comm _ _ _ BA ⟩
       A ∙ B ∙ A ∙ A ∙ ε
       ≡⟨ cong (A ∙_) (pcm-comm _ _ _ BA) ⟩
       A ∙ A ∙ B ∙ A ∙ ε
       ≡⟨ pcm-cong-head {s₁ = A ∙ A ∙ ε} (pcm-comm _ _ _ BA) ⟩
       A ∙ A ∙ A ∙ B ∙ ε ∎)

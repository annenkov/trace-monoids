{-# OPTIONS --cubical #-}

module ABCExample  where

open import TraceMonoid
open import Cubical.Foundations.Prelude


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
  #L-indep : IsIndependency _#L_
  #L-indep = record { #-irrefl = #L-irrefl _;
                      #-sym = λ { AB → BA ; BA → AB }}

example1 : (C ̇ A ̇ B ̇ ε) ≡ (C ̇ B ̇ A ̇ ε)
example1 = pcm-cong-head (swap-head {i = AB})

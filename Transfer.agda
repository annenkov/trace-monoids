{-# OPTIONS --cubical -W noNoEquivWhenSplitting #-}

module Transfer  where

open import Cubical.Foundations.Everything hiding (_∙_)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Nat hiding (_∸_)
open import Cubical.Data.Bool hiding (_≟_)

open import Lang

-- transfer some amount from one location to another
-- note that it's a valid transfer only if there is enough "money" of the "from" account
_-[_]->_ : Location → Location → ℕ → Transaction
a -[ v ]-> b =
  Ṙ a ﹔
  Ẇ a (Load ∸ ` v) ﹔
  Ṙ b ﹔
  Ẇ b (Load ∔ ` v) ﹔
  end

Alice : Location
Alice = 0

Bob : Location
Bob = 1

transfer-Alice-Bob : ℕ → Transaction
transfer-Alice-Bob v = Alice -[ v ]-> Bob

transfer-Alice-to-Bob : ∀ n →
  eval evalE (mk-sch 0 (Alice -[ 1 ]-> Bob)) init-regs ([ Alice ~> 1 ] ⊛ ([ Bob ~> 0 ] ⊛ ∅)) n ≡ ( [ Alice ~> 0 ] ⊛ ([ Bob ~> 1 ] ⊛ ∅)) n
transfer-Alice-to-Bob 0 = refl
transfer-Alice-to-Bob 1 = refl
transfer-Alice-to-Bob (suc (suc i)) = refl

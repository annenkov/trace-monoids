{-# OPTIONS --cubical #-}

module Lang  where

open import TraceMonoid
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Foundations.Prelude

open import Agda.Builtin.List
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

Location = ℕ

data Action : Set where
  Read  : Location → Action
  Write : Location → Action

Transaction = List Action

_≠_ : ∀ {A : Set} (a b : A) → Set
a ≠ b = a ≡ b → ⊥

≠-sym : ∀ {A : Set} {a b : A} → a ≠ b → b ≠ a
≠-sym np q =  np (sym q)

data _#'_ : Action → Action → Set where
  #'-RR : ∀ l → Read l #' Read l
  #'-WW : ∀ l₁ l₂ → l₁ ≠ l₂ → Write l₁ #' Write l₂
  #'-WR : ∀ l₁ l₂ → l₁ ≠ l₂ → Write l₁ #' Read l₂
  #'-RW : ∀ l₁ l₂ → l₁ ≠ l₂ → Read l₁ #' Write l₂

Event = ℕ × Action

data _#_ : Event → Event → Set where
  #-neq-tr : ∀ (e₁ e₂ : Event)
           → fst e₁ ≠ fst e₂
           → snd e₁ #' snd e₂
           → e₁ # e₂

#-irrefl : ∀ (x : Event) → ¬ (x # x)
#-irrefl (i , e) (#-neq-tr _ _ p _) = p refl

#'-sym : ∀ {e₁ e₂ : Action} → e₁ #' e₂ → e₂ #' e₁
#'-sym (#'-RR l) = #'-RR l
#'-sym (#'-WW l₁ l₂ x) = #'-WW l₂ l₁ (≠-sym x)
#'-sym (#'-WR l₁ l₂ x) = #'-RW l₂ l₁ (≠-sym x)
#'-sym (#'-RW l₁ l₂ x) = #'-WR l₂ l₁ (≠-sym x)

#-sym : ∀ {e₁ e₂ : Event} → e₁ # e₂ → e₂ # e₁
#-sym (#-neq-tr _ _ x y) = #-neq-tr _ _ (≠-sym x) (#'-sym y)

instance
  #-indep : IsIndependency _#_
  #-indep = record { #-irrefl = #-irrefl _;
                      #-sym = #-sym }

Trace : Set
Trace = Pcm (ℕ × Action) _#_

Ident = ℕ

data Exp : Set where
  _∔_ : Exp → Exp → Exp
  Load : Exp -- thread-local variable
  `_ : ℕ → Exp  -- nat literal

infix 22 `_

data RWLang : Set where
  ReadLoc : Location → RWLang
  WriteLoc : Location → Exp → RWLang

Prog = List (ℕ × RWLang)
Map = Location → ℕ
Registers = Map
Store = Map
RegisterVal = ℕ

∅ : Map
∅ = λ _ → 0

_[_~>_] : Map → Location → ℕ → Map
ρ [ l₁ ~> i ] = λ l₂ → if l₁ == l₂ then i else ρ l₂

evalE : RegisterVal → Exp → ℕ
evalE v (e₁ ∔ e₂) = evalE v e₁ + evalE v e₂
evalE v Load = v
evalE v (` i) = i

--| Take a global store, registers and return potentially updated global state and registers
eval : Store → Registers → Prog → Store × Registers
eval σ ρ [] = σ , ρ
eval σ ρ ( (i , ReadLoc l) ∷ xs) = eval σ (ρ [ i ~> σ l ]) xs
eval σ ρ ( (i , WriteLoc l e) ∷ xs) = eval (σ [ l ~> evalE (ρ i) e ]) ρ xs

mk-prog : ℕ → List RWLang → Prog
mk-prog i xs = map (λ c → (i , c)) xs

Task = Prog × Prog

mk-task : List RWLang → List RWLang → Task
mk-task xs ys = (mk-prog 0 xs , mk-prog 1 ys)

seq-task : Task → Prog
seq-task (p₁ , p₂) = p₁ ++ p₂

Task₁ : Task → Prog
Task₁ = fst

Task₂ : Task → Prog
Task₂ = snd


eval-seq : Store → Registers → Task → Store × Registers
eval-seq σ ρ t = eval σ ρ (seq-task t)

A = 0
B = 1

x = 0
y = 1

infixr 5 _﹔_

_﹔_ : {A : Set} → A → List A → List A
x ﹔ xs = x ∷ xs

end : {A : Set} → List A
end = []

rw-prog₁ : ℕ → List RWLang
rw-prog₁ a = ReadLoc A ﹔ WriteLoc A (Load ∔ ` a) ﹔(ReadLoc  B) ﹔( WriteLoc B (Load ∔ ` 10)) ﹔ end

ex1 : Prog
ex1 = mk-prog 0 (rw-prog₁ 1)

xy-to-list : Store × Registers → (List (ℕ × ℕ)) × (List (ℕ × ℕ))
xy-to-list (σ , ρ) = (0 , σ 0) ∷ (1 , σ 1) ∷ [] , (0 , ρ 0) ∷ (1 , ρ 1) ∷ []

ex-eval : xy-to-list (eval ∅ ∅ ex1) ≡ (((0 , 1) ∷ (1 , 10) ∷ []) , ((0 , 0) ∷ (1 , 0) ∷ []))
ex-eval = refl


⟦_⟧ᵖ : Prog → Trace
⟦ [] ⟧ᵖ = ε
⟦ (i , ReadLoc l) ∷ xs ⟧ᵖ = (i , Read l) ̇ ⟦ xs ⟧ᵖ
⟦ (i , WriteLoc l e) ∷ xs ⟧ᵖ = (i , Write l) ̇ ⟦ xs ⟧ᵖ

-- of-list : ℕ → List Action → Trace
-- of-list i [] =  ε
-- of-list i (x ∷ xs) = (i , x) ̇ of-list i xs

⟦_⟧ : Task → Trace
⟦ p₁ , p₂  ⟧ = ⟦ p₁ ⟧ᵖ  ^  ⟦ p₂ ⟧ᵖ

_∼_ : Prog → Prog → Set
p₁ ∼ p₂ = ⟦ p₁ ⟧ᵖ ≡ ⟦ p₂ ⟧ᵖ

_≈_ : Prog → Prog → Set
p₁ ≈ p₂ = fst (eval ∅ ∅ p₁) ≡  fst (eval ∅ ∅ p₂)

ex-task : ℕ → Task
ex-task a = mk-task (rw-prog₁ a) (rw-prog₁ a)

ex-interleaving : ℕ → Prog
ex-interleaving a =
  (0 , ReadLoc A) ﹔ (0 , WriteLoc A (Load ∔ ` a)) ﹔(0 , ReadLoc  B) ﹔(1 , ReadLoc A) ﹔
  (0 , WriteLoc B (Load ∔ ` 10)) ﹔ (1 , WriteLoc A (Load ∔ ` a)) ﹔(1 , ReadLoc  B) ﹔(1 , WriteLoc B (Load ∔ ` 10)) ﹔
  end

ex-trace-equiv : {a : ℕ} → ex-interleaving a ∼ seq-task (ex-task a)
ex-trace-equiv = pcm-cong-head
  (pcm-cong-head
     (pcm-cong-head ((1 , Read A) ̇ (0 , Write B) ̇ (1 , Write A) ̇ (1 , Read B) ̇ (1 , Write B) ̇ ε ≡⟨ assoc ⟩
                    ((Pcm.[ 1 , Read A ] ^ Pcm.[ 0 , Write B ]) ^ ((1 , Write A) ̇ (1 , Read B) ̇ (1 , Write B) ̇ ε)) ≡⟨  sym idL ⟩
                    (ε ^ (Pcm.[ 1 , Read A ] ^ Pcm.[ 0 , Write B ]) ^ ((1 , Write A) ̇ (1 , Read B) ̇ (1 , Write B) ̇ ε)) ≡⟨ abComm _ _ _ _ ⟩
                    (ε ^ (Pcm.[ 0 , Write B ] ^ Pcm.[ 1 , Read A ]) ^ ((1 , Write A) ̇ (1 , Read B) ̇ (1 , Write B) ̇ ε)) ≡⟨ idL ⟩
                    ((Pcm.[ 0 , Write B ] ^ Pcm.[ 1 , Read A ]) ^ ((1 , Write A) ̇ (1 , Read B) ̇ (1 , Write B) ̇ ε)) ≡⟨ sym assoc ⟩
                    ((0 , Write B) ̇ (1 , Read A) ̇ (1 , Write A) ̇ (1 , Read B) ̇ (1 , Write B) ̇ ε) ∎)))

ex-eval-equiv : {a : ℕ} → ex-interleaving a ≈ seq-task (ex-task a)
ex-eval-equiv = refl

_==ₑ_ : Exp → Exp → Bool
(e₁ ∔ e₂) ==ₑ (e₃ ∔ e₄) =  (e₁ ==ₑ e₃) and (e₂ ==ₑ e₄)
Load ==ₑ Load = true
(` i₁) ==ₑ (` i₂)  =  i₁ == i₂
_ ==ₑ _ = false

_===_ : RWLang → RWLang → Bool
(ReadLoc x₁) === (ReadLoc x₂) =  x₁ == x₂
(ReadLoc x₁) === (WriteLoc x₂ x₃) = false
(WriteLoc x₁ x₂) === (ReadLoc x₃) =  false
(WriteLoc l₁ e₁) === (WriteLoc l₂ e₂) = (l₁ == l₂) and (e₁ ==ₑ e₂)

all : {A : Set} → (p : A → Bool) → List A → Bool
all p [] = true
all p (x₁ ∷ xs) with p x₁
... | true = all p xs
... | false = false

exists : {A : Set} → (p : A → Bool) → List A → Bool
exists p [] = false
exists p (x₁ ∷ xs) with p x₁
... | true = true
... | false = exists p xs


in-prog : RWLang → Prog → Bool
in-prog e₁ = exists (λ p → e₁ === snd p)

same-commands : Prog → Prog → Bool
same-commands p₁ p₂ =
  all (λ c → in-prog c p₂) (map snd p₁) and (all (λ c → in-prog c p₁) (map snd p₂))

ex-same1 : same-commands (ex-interleaving 1) (seq-task (ex-task 1)) ≡ true
ex-same1 = refl


trace-sem-adequate : {p₁ p₂ : Prog} → same-commands p₁ p₂ ≡ true → p₁ ∼ p₂ → p₁ ≈ p₂
trace-sem-adequate {[]} {x₂ ∷ p₂} s teq = ⊥.rec (true≢false (sym s))
trace-sem-adequate {[]} {[]} s teq = refl
trace-sem-adequate {x₁ ∷ p₁} {x₂ ∷ p₂} s teq = ?
trace-sem-adequate {x₁ ∷ p₁} {[]} s teq = ⊥.rec (true≢false (sym s))

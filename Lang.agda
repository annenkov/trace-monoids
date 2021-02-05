{-# OPTIONS --cubical #-}

module Lang  where

open import TraceMonoid

open import Cubical.Foundations.Everything
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.Monoid

open import Agda.Builtin.List
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat


---------------------------------
-- Traces of Read/Write actions -
---------------------------------

Location = ℕ

data Action : Set where
  Read  : Location → Action
  Write : Location → Action

_≠_ : ∀ {A : Set} (a b : A) → Set
a ≠ b = a ≡ b → ⊥

≠-sym : ∀ {A : Set} {a b : A} → a ≠ b → b ≠ a
≠-sym np q =  np (sym q)

data _#'_ : Action → Action → Set where
  #'-RR : ∀ l₁ l₂ → Read l₁ #' Read l₂
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
#'-sym (#'-RR l₁ l₂) = #'-RR l₂ l₁
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
Trace = Pcm Event _#_

----------------------------
-- The Read-Write language -
----------------------------

data Exp : Set where
  _∔_ : Exp → Exp → Exp
  Load : Exp -- load a thread-local variable
  `_ : ℕ → Exp  -- nat literal

infix 22 `_

data RWLang : Set where
  ReadLoc : Location → RWLang
  WriteLoc : Location → Exp → RWLang

Transaction = List RWLang

Schedule = List (ℕ × RWLang)
Map = Location → Maybe ℕ
Registers = ℕ → ℕ
Store = Map
RegisterVal = ℕ

∅ : Map
∅ = λ _ → nothing

init-regs : Registers
init-regs = λ _ → 0

_[_~>_] : Map → Location → ℕ → Map
ρ [ l₁ ~> i ] = λ l₂ → if l₁ == l₂ then just i else ρ l₂

set-reg : Registers → ℕ → ℕ → Registers
set-reg ρ r₁ v = λ r₂ → if r₁ == r₂ then v else ρ r₂

merge : Map → Map → Map
merge m₁ m₂ l with m₁ l
... | just v = just v
... | nothing = m₂ l


infixl 100 _⋆_

_⋆_ : Map → Map → Map
m₁ ⋆ m₂ = merge m₁ m₂

⋆-assoc : ∀ (m₁ m₂ m₃ : Map) (l : Location) → (merge m₁ (merge m₂ m₃)) l ≡ (merge (merge m₁ m₂) m₃) l
⋆-assoc m₁ m₂ m₃ l with m₁ l
⋆-assoc m₁ m₂ m₃ l | just v₁ with m₂ l
⋆-assoc m₁ m₂ m₃ l | just v₁ | just v₂ = refl
⋆-assoc m₁ m₂ m₃ l | just v₁ | nothing = refl
⋆-assoc m₁ m₂ m₃ l | nothing with m₂ l
⋆-assoc m₁ m₂ m₃ l | nothing | just v₂ = refl
⋆-assoc m₁ m₂ m₃ l | nothing | nothing = refl

-- isSet-Map : isSet Map
-- isSet-Map = isSetΠ λ n → isSetℕ

-- mon-map : IsMonoid ∅ _⋆_
-- mon-map = makeIsMonoid isSet-Map (λ f g h → ∘-assoc h g f) (λ f → ∘-idʳ f) {! ∘-idˡ!}


-- Semantics of the Read-Write language

get-default : Map → Location → ℕ
get-default σ l with σ l
... | just v = v
... | nothing = 0

evalE : RegisterVal → Exp → ℕ
evalE v (e₁ ∔ e₂) = evalE v e₁ + evalE v e₂
evalE v Load = v
evalE v (` i) = i

-- Take a global store, registers and return potentially updated global state and registers
eval : Store → Registers → Schedule → Store × Registers
eval σ ρ [] = σ , ρ
eval σ ρ ( (i , ReadLoc l) ∷ xs) = eval σ (set-reg ρ i (get-default σ l)) xs
eval σ ρ ( (i , WriteLoc l e) ∷ xs) = eval (σ [ l ~> evalE (ρ i) e ]) ρ xs

mk-sch : ℕ → Transaction → Schedule
mk-sch i xs = map (λ c → (i , c)) xs


-- A sequential scheduler: it schedules all the commands of the first transation first
-- and afterwards all the commands of the second transation.
seq-scheduler : Transaction → Transaction → Schedule
seq-scheduler xs ys = mk-sch 0 xs ++ mk-sch 1 ys

eval-seq : Store → Registers → Transaction × Transaction → Store × Registers
eval-seq σ ρ (t₁ , t₂) = eval σ ρ (seq-scheduler t₁ t₂)

infixr 5 _﹔_

_﹔_ : {A : Set} → A → List A → List A
x ﹔ xs = x ∷ xs

end : {A : Set} → List A
end = []

A = 0
B = 1

rw-prog₁ : ℕ → List RWLang
rw-prog₁ a = ReadLoc A ﹔ WriteLoc A (Load ∔ ` a) ﹔(ReadLoc  B) ﹔( WriteLoc B (Load ∔ ` 10)) ﹔ end

ex1 : Schedule
ex1 = mk-sch 0 (rw-prog₁ 1)

xy-to-list : Store × Registers → List (ℕ × Maybe ℕ) × List ℕ
xy-to-list (σ , ρ) = (0 , σ 0) ∷ (1 , σ 1) ∷ [] , ρ 0 ∷ ρ 1 ∷ []

ex-eval : xy-to-list (eval ∅ init-regs ex1) ≡ (((0 , just 1) ∷ (1 , just 10) ∷ []) ,  0 ∷ 0 ∷ [])
ex-eval = refl

-- Interpretation of the Read-Write language into traces of Read/Write actions
-- The interpretation "forgets" the comutational part and leaves only occurences of reads and writes
⟦_⟧ : Schedule → Trace
⟦ [] ⟧ = ε
⟦ (i , ReadLoc l) ∷ xs ⟧ = (i , Read l) ̇ ⟦ xs ⟧
⟦ (i , WriteLoc l e) ∷ xs ⟧ = (i , Write l) ̇ ⟦ xs ⟧


-- Trace-equivalent schedules are just schedules with equal traces
_∼_ : Schedule → Schedule → Set
p₁ ∼ p₂ = ⟦ p₁ ⟧ ≡ ⟦ p₂ ⟧


-- A schedule is serializable if it is trace-equivalent to a sequental composition of the two schedules
serializable : Schedule → Set
serializable p = Σ[ (p₁ , p₂) ∈ Transaction × Transaction ] (⟦ p ⟧ ≡ ⟦ seq-scheduler p₁ p₂ ⟧)

-- Semantically equivalent programs result in the same store (we ignore the state of the registers)
_≈_ : Schedule → Schedule → Set
p₁ ≈ p₂ = ∀ l → fst (eval ∅ init-regs p₁) l ≡  fst (eval ∅ init-regs p₂) l

ex-interleaving : ℕ → Schedule
ex-interleaving a =
  (0 , ReadLoc A) ﹔ (0 , WriteLoc A (Load ∔ ` a)) ﹔(0 , ReadLoc  B) ﹔(1 , ReadLoc A) ﹔ (1 , WriteLoc A (Load ∔ ` a)) ﹔
  (0 , WriteLoc B (Load ∔ ` 10)) ﹔ (1 , ReadLoc  B) ﹔(1 , WriteLoc B (Load ∔ ` 10)) ﹔
  end

infix 40 _%T₀
infix 40 _%T₁

_%T₀ : Action → ℕ × Action
e %T₀ = (0 , e)

_%T₁ : Action → ℕ × Action
e %T₁ = (1 , e)


-- The program `ex-interleaving` corresponds to the following schedule
ex-schedule : ∀ a →
  ⟦ ex-interleaving a ⟧ ≡
  Read A %T₀ ̇ Write A %T₀ ̇ Read B %T₀ ̇ Read A %T₁ ̇ Write A %T₁ ̇ Write B %T₀ ̇ Read B %T₁ ̇ Write B %T₁ ̇ ε
ex-schedule _ = refl

-- It can be rewritten in the standard "textbook" 2-dimentional notation as follows
-- (we asssume that each transaction commits immedately after the last operation).

-------------------------------------|
--| T₀ : RA  WA  RB       WB         |
--| T₁ :            RA WA    RB  WB  |
-------------------------------------|

-- Clealry, it's ok to read A and write A in T₁, while reading B in T₀, and write A in T₁ while writing B in T₀
-- since the locations are disjoint and there is no conflict.


ex-trace-equiv : {a : ℕ} → ex-interleaving a ∼ seq-scheduler (rw-prog₁ a) (rw-prog₁ a)
ex-trace-equiv = pcm-cong-head {s₁ = Read A %T₀ ̇ Write A %T₀ ̇ Read B %T₀ ̇ ε}
                 (Read A %T₁ ̇ Write A %T₁ ̇ Write B %T₀ ̇ Read B %T₁ ̇ Write B %T₁ ̇ ε
                  ≡⟨ cong (Read A %T₁ ̇_) (pcm-comm _ _ _ {#-neq-tr _ _ snotz (#'-WW _ _ znots)}) ⟩
                  Read A %T₁ ̇ Write B %T₀ ̇ Write A %T₁ ̇ Read B %T₁ ̇ Write B %T₁ ̇ ε
                  ≡⟨ (pcm-comm _ _ _ {#-neq-tr _ _ snotz (#'-RW _ _ znots)}) ⟩
                  Write B %T₀ ̇ Read A %T₁ ̇ Write A %T₁ ̇ Read B %T₁ ̇ Write B %T₁ ̇ ε ∎)

-- The interleaved schedule is serializable, therefore safe.
ex-serializable : ∀ {a : ℕ} → serializable (ex-interleaving a)
ex-serializable {a = a} =  ( (rw-prog₁ a , rw-prog₁ a) , ex-trace-equiv {a = a})

-- Moreover it gives the same result under the evaluation semantics.
ex-eval-equiv : {a : ℕ} → ex-interleaving a ≈ seq-scheduler (rw-prog₁ a) (rw-prog₁ a)
ex-eval-equiv zero = refl
ex-eval-equiv (suc zero) = refl
ex-eval-equiv (suc _) = refl

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


in-prog : RWLang → Schedule → Bool
in-prog e₁ = exists (λ p → e₁ === snd p)

same-commands : Schedule → Schedule → Bool
same-commands p₁ p₂ =
  all (λ c → in-prog c p₂) (map snd p₁) and (all (λ c → in-prog c p₁) (map snd p₂))

ex-same1 : same-commands (ex-interleaving 1) (seq-scheduler (rw-prog₁ 1) (rw-prog₁ 1)) ≡ true
ex-same1 = refl


-- A possible way of stating correctness of the interpretations into traces

-- trace-sem-adequate : {p₁ p₂ : Schedule} → same-commands p₁ p₂ ≡ true → p₁ ∼ p₂ → p₁ ≈ p₂
-- trace-sem-adequate {[]} {x₂ ∷ p₂} s teq = ⊥.rec (true≢false (sym s))
-- trace-sem-adequate {[]} {[]} s teq = refl
-- trace-sem-adequate {x₁ ∷ p₁} {x₂ ∷ p₂} s teq = {!!}
-- trace-sem-adequate {x₁ ∷ p₁} {[]} s teq = ⊥.rec (true≢false (sym s))

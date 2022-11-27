{-# OPTIONS --cubical -W noNoEquivWhenSplitting #-}

module Lang  where

open import TraceMonoid

open import Cubical.Foundations.Everything hiding (_∙_)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat hiding (_∸_)
open import Cubical.Data.Bool hiding (_≟_)
open import Cubical.Foundations.Prelude renaming (_∙_ to compPath)
open import Cubical.Algebra.Monoid
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidableEq

open import Agda.Primitive
open import Agda.Builtin.List
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

----------------------------
-- The Read-Write language -
----------------------------

data Exp : Set where
  _∔_ : Exp → Exp → Exp -- addition
  _∸_ : Exp → Exp → Exp -- addition
  Load : Exp              -- load a thread-local variable
  `_ : ℕ → Exp          -- nat literal

infix 22 `_

Location = ℕ

data Action : Set where
  Ṙ : Location → Action
  Ẇ : Location → Exp → Action

Transaction = List Action

---------------------------------
-- Traces of Read/Write actions -
---------------------------------

_≠_ : ∀ {A : Set} (a b : A) → Set
a ≠ b = a ≡ b → ⊥

≠-sym : ∀ {A : Set} {a b : A} → a ≠ b → b ≠ a
≠-sym np q =  np (sym q)

data _#ₐ_ : Action → Action → Set where
  #ₐ-RR : ∀ l₁ l₂ → Ṙ l₁ #ₐ Ṙ l₂
  #ₐ-WW : ∀ l₁ l₂ e₁ e₂ → l₁ ≠ l₂ → Ẇ l₁ e₁ #ₐ Ẇ l₂ e₂
  #ₐ-WR : ∀ l₁ l₂ e → l₁ ≠ l₂ → Ẇ l₁ e #ₐ Ṙ l₂
  #ₐ-RW : ∀ l₁ l₂ e → l₁ ≠ l₂ → Ṙ l₁ #ₐ Ẇ l₂ e

Event = ℕ × Action

data _#_ : Event → Event → Set where
  #-neq-tr : ∀ (e₁ e₂ : Event) → fst e₁ ≠ fst e₂ → snd e₁ #ₐ snd e₂ → e₁ # e₂

#-irrefl : ∀ (x : Event) → ¬ (x # x)
#-irrefl (i , e) (#-neq-tr _ _ p _) = p refl

#ₐ-sym : ∀ {a₁ a₂ : Action} → a₁ #ₐ a₂ → a₂ #ₐ a₁
#ₐ-sym (#ₐ-RR l₁ l₂) = #ₐ-RR l₂ l₁
#ₐ-sym (#ₐ-WW l₁ l₂ e₁ e₂ x) = #ₐ-WW l₂ l₁ e₂ e₁ (≠-sym x)
#ₐ-sym (#ₐ-WR l₁ l₂ e x) = #ₐ-RW l₂ l₁ e (≠-sym x)
#ₐ-sym (#ₐ-RW l₁ l₂ e x) = #ₐ-WR l₂ l₁ e (≠-sym x)

#-sym : ∀ {e₁ e₂ : Event} → e₁ # e₂ → e₂ # e₁
#-sym (#-neq-tr _ _ x y) = #-neq-tr _ _ (≠-sym x) (#ₐ-sym y)

instance
  #-indep : IsIndependence _#_
  #-indep = record { #-irrefl = #-irrefl _;
                     #-sym = #-sym }

-- Two actions conflict, if they operate on the same location and one of the actions is Ẇ
data IsConflict : ∀ (a₁ a₂ : Action) → Set where
  is-conflict-rw : ∀ l e → IsConflict (Ṙ l) (Ẇ l e)
  is-conflict-wr : ∀ l e → IsConflict (Ẇ l e) (Ṙ l)
  is-conflict-ww : ∀ l e₁ e₂ → IsConflict (Ẇ l e₁) (Ẇ l e₂)

#-not-IsConflict : ∀ {e₁ e₂ : Event} → e₁ # e₂ → ¬ IsConflict (snd e₁) (snd e₂)
#-not-IsConflict (#-neq-tr _ _ neq (#ₐ-RR l₁ l₂)) ()
#-not-IsConflict (#-neq-tr _ _ neq (#ₐ-WW l₁ .l₁ e₁ e₂ x)) (is-conflict-ww .l₁ .e₁ .e₂) = x refl
#-not-IsConflict (#-neq-tr _ _ neq (#ₐ-WR l₁ .l₁ e x)) (is-conflict-wr .l₁ .e) = x refl
#-not-IsConflict (#-neq-tr _ _ neq (#ₐ-RW l₁ .l₁ e x)) (is-conflict-rw .l₁ .e) = x refl

Trace : Set
Trace = FreePcm Event _#_

Schedule = List Event
Map = Location → Maybe ℕ
Registers = ℕ → ℕ
Store = Map
RegisterVal = ℕ

isJust : ∀ {A : Set} → Maybe A → Bool
isJust (just _) = true
isJust _ = false

infixl 100 _⊛_

_⊛_ : Map → Map → Map
(m₁ ⊛ m₂) l = if isJust (m₁ l) then m₁ l else m₂ l

⊛-assoc' : ∀ (m₁ m₂ m₃ : Map) (l : Location) → (m₁ ⊛ (m₂ ⊛ m₃)) l ≡ ((m₁ ⊛ m₂) ⊛ m₃) l
⊛-assoc' m₁ m₂ m₃ l with m₁ l
⊛-assoc' m₁ m₂ m₃ l | just v₁ with m₂ l
⊛-assoc' m₁ m₂ m₃ l | just v₁ | just v₂ = refl
⊛-assoc' m₁ m₂ m₃ l | just v₁ | nothing = refl
⊛-assoc' m₁ m₂ m₃ l | nothing with m₂ l
⊛-assoc' m₁ m₂ m₃ l | nothing | just v₂ = refl
⊛-assoc' m₁ m₂ m₃ l | nothing | nothing = refl

⊛-assoc : ∀ (m₁ m₂ m₃ : Map) → (m₁ ⊛ (m₂ ⊛ m₃)) ≡ ((m₁ ⊛ m₂) ⊛ m₃)
⊛-assoc m₁ m₂ m₃ = funExt (⊛-assoc' m₁ m₂ m₃)


∅ : Map
∅ = λ _ → nothing

[_~>_] : Location → ℕ → Map
[ l₁ ~> i ] = λ l₂ → if l₁ == l₂ then just i else nothing


-- isSet-Map : isSet Map
-- isSet-Map = isSetΠ λ n → isSetℕ

-- mon-map : IsMonoid ∅ _⊛_
-- mon-map = makeIsMonoid isSet-Map (λ f g h → ∘-assoc h g f) (λ f → ∘-idʳ f) {! ∘-idˡ!}

init-regs : Registers
init-regs = λ _ → 0

set-reg : Registers → ℕ → ℕ → Registers
set-reg ρ r₁ v = λ r₂ → if r₁ == r₂ then v else ρ r₂

-----------------------------------------------
-- Store semantics of the Read-Write language -
-----------------------------------------------

get-default : Map → Location → ℕ
get-default σ l with σ l
... | just v = v
... | nothing = 0

evalE : RegisterVal → Exp → Maybe ℕ
evalE v (e₁ ∔ e₂) with evalE v e₁ | evalE v e₂
...                  | just v₁    | just v₂ = just (v₁ + v₂)
...                  | _          | _       = nothing
evalE v (e₁ ∸ e₂) with evalE v e₁ | evalE v e₂
...                  | just v₁    | just v₂ = if v₁ < v₂ then nothing else just (v₁ - v₂)
...                  | _          | _       = nothing
evalE v Load = just v
evalE v (` i) = just i

bind-Maybe : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
bind-Maybe (just v) f = f v
bind-Maybe nothing _ = nothing

-- Take an expresison eval function, global store, registers and return a potentially updated global state
eval : (RegisterVal → Exp → Maybe ℕ) → Schedule → Registers → Store  → Maybe Store
eval evalExp []   = λ ρ σ → just σ
eval evalExp ((i , Ṙ l) ∷ xs)  = λ ρ σ → eval evalExp xs (set-reg ρ i (get-default σ l)) σ
eval evalExp ((i , Ẇ l e) ∷ xs) = λ ρ σ → bind-Maybe ( map-Maybe (λ v →([ l ~> v ])) (evalExp (ρ i) e)) (λ v → eval evalExp xs ρ (v ⊛ σ))
-- with evalExp (ρ i) e
-- ...                                    | just v = eval evalExp xs ρ ([ l ~> v ] ⊛ σ)
-- ...                                    | nothing = nothing
mk-sch : ℕ → Transaction → Schedule
mk-sch i xs = map (λ c → (i , c)) xs


-- A sequential scheduler: it schedules all the commands of the first transation first
-- and afterwards all the commands of the second transation.
seq-scheduler : Transaction → Transaction → Schedule
seq-scheduler xs ys = mk-sch 0 xs ++ mk-sch 1 ys

eval-seq : (RegisterVal → Exp → Maybe ℕ) → Store → Registers → Transaction × Transaction → Maybe Store
eval-seq evalExp σ ρ (t₁ , t₂) = eval evalExp (seq-scheduler t₁ t₂) ρ σ

infixr 5 _﹔_

_﹔_ : {A : Set} → A → List A → List A
x ﹔ xs = x ∷ xs

end : {A : Set} → List A
end = []

A = 0
B = 1

rw-prog₁ : ℕ → List Action
rw-prog₁ a = Ṙ A ﹔ Ẇ A (Load ∔ ` a) ﹔(Ṙ  B) ﹔( Ẇ B (Load ∔ ` 10)) ﹔ end

ex1 : Schedule
ex1 = mk-sch 0 (rw-prog₁ 1)

xy-to-list : Maybe Store → List (ℕ × Maybe ℕ)
xy-to-list (just σ) = (0 , σ 0) ∷ (1 , σ 1) ∷ []
xy-to-list _ = []

ex-eval : xy-to-list (eval evalE ex1 init-regs ∅) ≡ ((0 , just 1) ∷ (1 , just 10) ∷ [])
ex-eval = refl

rw-prog₂ : List Action
rw-prog₂ = Ṙ A ﹔ Ẇ A (Load ∔ ` 1) ﹔(Ṙ  A) ﹔( Ẇ B (Load ∔ ` 10)) ﹔ end

ex2 : Schedule
ex2 = mk-sch 0 rw-prog₂

ex₂-eval : xy-to-list (eval evalE ex2 init-regs ∅) ≡ ((0 , just 1) ∷ (1 , just 11) ∷ [])
ex₂-eval = refl


of-list : {A : Set} -> {R : A → A → Set } -> {{_ : IsIndependence R}} -> List A → FreePcm A R
of-list [] = ε
of-list (x ∷ xs) = x ∙ of-list xs

-- Interpretation of the Read-Write language as a trace
⟦_⟧ : Schedule → Trace
⟦ s ⟧ = of-list s

-- Trace-equivalent schedules are just schedules with equal traces
_∼_ : Schedule → Schedule → Set
p₁ ∼ p₂ = ⟦ p₁ ⟧ ≡ ⟦ p₂ ⟧


-- A schedule is serializable if it is trace-equivalent to a sequental composition of the two schedules
serializable : Schedule → Set
serializable p = Σ[(p₁ , p₂)∈ Transaction × Transaction ] (⟦ p ⟧ ≡ ⟦ seq-scheduler p₁ p₂ ⟧)

-- Semantically equivalent programs result in the same store
_≈_ : Schedule → Schedule → Set
p₁ ≈ p₂ = (λ (f : RegisterVal → Exp → Maybe ℕ) → eval f p₁) ≡ (λ (f : RegisterVal → Exp → Maybe ℕ) → eval f p₂)

infix 40 T₀:_
infix 40 T₁:_


T₀:_ : Action → ℕ × Action
T₀: e = (0 , e)

T₁:_ : Action → ℕ × Action
T₁: e = (1 , e)


-- a simple example of a schedule with interleaving
ex-interleaving-simple : Schedule
ex-interleaving-simple =
  T₀: Ṙ A ﹔ T₁: Ẇ B (` 10) ﹔ T₀: Ẇ A (Load ∔ ` 1) ﹔ T₁: Ẇ A (` 2) ﹔ end

-- The schedule can be rewritten in the standard "textbook" 2-dimentional notation as follows
-- (we asssume that each transaction commits immedately after the last operation).

--------------------------------|
--| T₀ : RA      WA      Commit |
--| T₁ :     WB      WA  Commit |
--------------------------------|
-- note that that RB (Read B) can be executed at some point beteween RA and WA (Write A). And WA, in turn can be executed between RB and WB.
-- We would like to know whether it's valid, that is, the outcome of the two transactions is the same if we run them sequentially (one after another) is some order.
-- Informally, it's clear that reading B and writing A are independent, so we can swap them ending with
---------------------------------|
--| T₀ : RA  WA           Commit |
--| T₁ :         WB  WA   Commit |
---------------------------------|

T₀-acts : Transaction
T₀-acts = Ṙ A ﹔ Ẇ A (Load ∔ ` 1) ﹔ end

T₁-acts : Transaction
T₁-acts = Ẇ B (` 10) ﹔ Ẇ A (` 2) ﹔ end

ex-simple-interleaving-trace-equiv :
  ex-interleaving-simple ∼ seq-scheduler T₀-acts T₁-acts
ex-simple-interleaving-trace-equiv = pcm-cong-head {s₁ =  T₀: Ṙ A ∙ ε } (pcm-comm _ _ _ (#-neq-tr _ _ snotz (#ₐ-WW _ _ _ _ (≠-sym znots))))


-- more complex interleaving
ex-interleaving : ℕ → Schedule
ex-interleaving a =
  (0 , Ṙ A) ﹔ (0 , Ẇ A (Load ∔ ` a)) ﹔(0 , Ṙ  B) ﹔(1 , Ṙ A) ﹔ (1 , Ẇ A (Load ∔ ` a)) ﹔
  (0 , Ẇ B (Load ∔ ` 10)) ﹔ (1 , Ṙ  B) ﹔(1 , Ẇ B (Load ∔ ` 10)) ﹔
  end

-- in the texbook notations:
-----------------------------------------|
--| T₀ : RA  WA  RB          WB          |
--| T₁ :             RA  WA      RB  WB  |
-----------------------------------------|

-- Clealry, it's ok to read A and write A in T₁, while reading B in T₀, and write A in T₁ while writing B in T₀
-- since the locations are disjoint and there is no conflict.

-- The sequential scheduling would look like this:
-----------------------------------------|
--| T₀ : RA  WA  RB  WB                  |
--| T₁ :                 RA  WA  RB  WB  |
-----------------------------------------|


ex-trace-equiv : {a : ℕ} → ex-interleaving a ∼ seq-scheduler (rw-prog₁ a) (rw-prog₁ a)
ex-trace-equiv = pcm-cong-head {s₁ = T₀: Ṙ A  ∙ T₀: Ẇ A _ ∙ T₀: Ṙ B ∙ ε}
                 (T₁: Ṙ A  ∙ T₁: Ẇ A _ ∙ T₀: Ẇ B _ ∙ T₁: Ṙ B ∙ T₁: Ẇ B _ ∙ ε
                  ≡⟨ cong (T₁: Ṙ A ∙_) (pcm-comm _ _ _ (#-neq-tr _ _ snotz (#ₐ-WW _ _ _ _ znots))) ⟩
                  T₁: Ṙ A ∙ T₀: Ẇ B _ ∙ T₁: Ẇ A _ ∙ T₁: Ṙ B ∙ T₁: Ẇ B _ ∙ ε
                  ≡⟨ (pcm-comm _ _ _ (#-neq-tr _ _ snotz (#ₐ-RW _ _ _ znots))) ⟩
                  T₀: Ẇ B _ ∙ T₁: Ṙ A ∙ T₁: Ẇ A _ ∙ T₁: Ṙ B  ∙ T₁: Ẇ B _ ∙ ε ∎)

-- The interleaved schedule is serializable, therefore safe
ex-serializable : ∀ {a : ℕ} → serializable (ex-interleaving a)
ex-serializable {a = a} =  ( (rw-prog₁ a , rw-prog₁ a) , ex-trace-equiv {a = a})


-- Some machinery for maintaning information during pattern-matching, it's standard, but yet missing in the distribution of Cubical Agda (maybe it's updated now?)
record Reveal_·_is_ {a b} {A : Set a} {B : A → Set b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set (a ⊔ b) where
  constructor [_]
  field eq : f x ≡ y

inspect : ∀ {a b} {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = [ refl ]

ℕ==→≡ : ∀ {n m : ℕ} → (n == m) ≡ true → n ≡ m
ℕ==→≡ {zero} {zero} p = refl
ℕ==→≡ {zero} {suc m} p = ⊥.elim {A = λ _ → zero ≡ (suc m)} (true≢false (sym p))
ℕ==→≡ {suc n} {zero} p = ⊥.elim {A = λ _ → (suc n) ≡ zero } (true≢false (sym p))
ℕ==→≡ {suc n} {suc m} p = cong suc (ℕ==→≡ p)

--------------
-- Soundness -
--------------

-- First, we show that the independent operations commute

set-reg-≠-regs : ∀ {j i₁ i₂ v₁ v₂ ρ} → i₁ ≠ i₂ → set-reg (set-reg ρ i₁ v₁) i₂ v₂ j ≡ set-reg (set-reg ρ i₂ v₂) i₁ v₁ j
set-reg-≠-regs {j} {i₁} {i₂} {v₁} {v₂} {ρ} neq with (i₁ == j) | inspect (λ x → i₁ == x) j  | i₂ == j | inspect (λ x → i₂ == x) j
... | true  | [ eq1 ] | true  | [ eq2 ] = ⊥.elim (neq (compPath (ℕ==→≡ eq1) (sym (ℕ==→≡ eq2))))
... | true  | [ eq1 ] | false | [ eq2 ] = refl
... | false | _ | true  | _ = refl
... | false | _ | false | _ = refl

get-default-≠ : ∀ {l₁ l₂ v σ } → l₁ ≠ l₂ → get-default ([ l₁ ~> v ] ⊛ σ) l₂ ≡ get-default σ l₂
get-default-≠ {l₁} {l₂} {v} {σ} p with (l₁ == l₂) | inspect (l₁ ==_) l₂
... | true  | [ eq ] = ⊥.elim (p (ℕ==→≡ eq))
... | false | [ eq ] = refl

set-reg-≠-regs-ext : ∀ {i₁ i₂ v₁ v₂ ρ} → i₁ ≠ i₂  → set-reg (set-reg ρ i₁ v₁) i₂ v₂ ≡ set-reg (set-reg ρ i₂ v₂) i₁ v₁
set-reg-≠-regs-ext {i₁} {i₂} {v₁} {v₂} {ρ} neq = funExt (λ x → set-reg-≠-regs {x} {i₁} {i₂} {v₁} {v₂} {ρ} neq)

set-reg-irrel : ∀ {ρ i₁ i₂ v} → i₁ ≠ i₂ → set-reg ρ i₁ v i₂ ≡ ρ i₂
set-reg-irrel {ρ} {i₁} {i₂} {v} neq with (i₁ == i₂)| inspect (λ x → i₁ == x) i₂
... | true  | [ eq ] = ⊥.elim (neq (ℕ==→≡ eq))
... | false  | [ eq ] = refl

update-commutes : ∀ {l₁ v₁ l₂ v₂} l → l₁ ≠ l₂ → ([ l₁ ~> v₁ ] ⊛ ([ l₂ ~> v₂ ])) l ≡ ([ l₂ ~> v₂ ] ⊛ ([ l₁ ~> v₁ ])) l
update-commutes {l₁} {v₁} {l₂} {v₂} l neq with (l₁ == l) | inspect (λ x → l₁ == x) l | (l₂ == l) | inspect (l₂ ==_) l
... | true  | [ eq1 ] | true  | [ eq2 ] = ⊥.elim (neq (compPath (ℕ==→≡ eq1) (sym (ℕ==→≡ eq2))))
... | true  | [ eq1 ] | false | [ eq2 ]  = refl
... | false  | [ eq1 ] | true | [ eq2 ]  = refl
... | false  | [ eq1 ] | false | [ eq2 ]  = refl

update-commutes-ext : ∀ {l₁ v₁ l₂ v₂} → l₁ ≠ l₂ → ([ l₁ ~> v₁ ] ⊛ ([ l₂ ~> v₂ ])) ≡ ([ l₂ ~> v₂ ] ⊛ ([ l₁ ~> v₁ ]))
update-commutes-ext neq = funExt (λ l → update-commutes l neq)


⊛-cong : ∀ {σ₁ σ₂ σ₃ σ₄} → σ₁ ≡ σ₂ → σ₃ ≡ σ₄ → σ₁ ⊛ σ₃ ≡ σ₂ ⊛ σ₄
⊛-cong p q = cong₂ _⊛_ p q

⊛-cong-assoc : ∀ {σ₁ σ₂ σ₃ σ₄ σ} → σ₁ ≡ σ₂ → σ₃ ≡ σ₄ → σ₁ ⊛ (σ₃ ⊛ σ) ≡ σ₂ ⊛ (σ₄ ⊛ σ)
⊛-cong-assoc p q = ⊛-cong p (⊛-cong q refl )

is-set-eval-t : isSet (Registers → Store → Maybe Map)
is-set-eval-t = isSetΠ2 (λ _ _ → isOfHLevelMaybe zero (isSetΠ ( λ _ → isOfHLevelMaybe zero isSetℕ)))

eval-t-rec : (RegisterVal → Exp → Maybe ℕ) → Event → (Registers → Store → Maybe Map) → Registers → Store → Maybe Map
eval-t-rec evalExp (i , Ṙ l) rec = λ ρ σ → rec (set-reg ρ i (get-default σ l)) σ
eval-t-rec evalExp (i , Ẇ l e) rec = λ ρ σ → bind-Maybe ( map-Maybe (λ v →([ l ~> v ])) (evalExp (ρ i) e)) (λ v → rec ρ (v ⊛ σ))

-- eval-t-rec evalExp (i , Ẇ l e) rec ρ σ with evalExp (ρ i) e
-- ...                                       | just v = rec ρ ([ l ~> v ] ⊛ σ)
-- ...                                       | nothing = nothing


-- et-comm : (Registers → Store  → Maybe Store) → (Registers → Store  → Maybe Store) → Registers → Store → Set
-- et-comm f g ρ σ with f ρ σ | g ρ σ
-- ... | just m₁ | just m₂ =


eval-t-commute : ∀ (evalExp : RegisterVal → Exp → Maybe ℕ) →
                 (x y : Event) (tr : Trace) →
                 (rec :  Registers → Store → Maybe Map) →
                 x # y →
                 eval-t-rec evalExp x (eval-t-rec evalExp y rec) ≡ eval-t-rec evalExp y (eval-t-rec evalExp x rec)
eval-t-commute _ (i₁ , _) (i₂ , _) tr rec (#-neq-tr _ _ neq (#ₐ-RR l₁ l₂)) =
                        funExt (λ _ → funExt λ _ → cong₂ rec (set-reg-≠-regs-ext neq) refl)
eval-t-commute f (i₁ , _) (i₂ , _) tr rec (#-neq-tr _ _ neq (#ₐ-WW l₁ l₂ e₁ e₂ x)) =
                        funExt (λ ρ → funExt λ σ → {!!}
                        -- cong (rec ρ)
                        --        (
                               -- [ l₂ ~> f (ρ i₂) e₂ ] ⊛ ([ l₁ ~> f (ρ i₁) e₁ ] ⊛ σ) ≡⟨ ⊛-assoc [ l₂ ~> f (ρ i₂) e₂ ] _ _ ⟩
                               --  ([ l₂ ~> f (ρ i₂) e₂ ] ⊛ [ l₁ ~> f (ρ i₁) e₁ ]) ⊛ σ  ≡⟨ ⊛-cong (update-commutes-ext (≠-sym x)) refl ⟩
                               --  ([ l₁ ~> f (ρ i₁) e₁ ] ⊛ [ l₂ ~> f (ρ i₂) e₂ ]) ⊛ σ  ≡⟨ sym (⊛-assoc ([ l₁ ~> f (ρ i₁) e₁ ]) _ _) ⟩
                               --   [ l₁ ~> f (ρ i₁) e₁ ] ⊛ ([ l₂ ~> f (ρ i₂) e₂ ] ⊛ σ) ∎
                                 -- )
                                 )
eval-t-commute f (i₁ , _) (i₂ , _) tr rec (#-neq-tr _ _ neq (#ₐ-WR l₁ l₂ e x)) = {!!}
                        -- funExt (λ ρ →
                        --   funExt λ σ →
                        --     cong₂ rec (funExt λ v →
                        --       cong₂ (set-reg ρ i₂)
                        --             ((get-default-≠ {σ = σ} x)) refl)
                        --             (cong (λ x → [ l₁ ~> f x e ] ⊛ σ) (sym (set-reg-irrel {ρ = ρ} (≠-sym neq)))))
eval-t-commute f (i₁ , _) (i₂ , _) tr rec (#-neq-tr _ _ neq (#ₐ-RW l₁ l₂ e x)) = {!!}
                        -- funExt (λ ρ →
                        --   funExt λ σ →
                        --     cong₂ rec (cong (set-reg ρ i₁) (sym (get-default-≠ {σ = σ} (≠-sym x))) )
                        --               (⊛-cong (cong (λ x → [ l₂ ~> f x e ]) (set-reg-irrel {ρ = ρ} neq)) refl ))

-- We define new sematics by evaluating a trace directly.
-- We use the recursion principle for the trace monoid, which forces us to prove that
-- the permutation of independent actions does not change the store
eval-t : (RegisterVal → Exp → Maybe ℕ) → Trace → Registers → Store → Maybe Store
eval-t evalExp tr =
  Rec.f is-set-eval-t (λ _ σ → just σ) (eval-t-rec evalExp) (λ x y rec → eval-t-commute evalExp x y tr rec ) tr

-- The store semantics on lists of commands gives the same result as the semantics on traces
eval-eval-t : ∀ (evalExp  : RegisterVal → Exp → Maybe ℕ) (s : Schedule) →
              eval evalExp s ≡ eval-t evalExp ⟦ s ⟧
eval-eval-t _ [] = refl
eval-eval-t f ((i , Ṙ l1) ∷ xs)  = eval-eval-t f {!!}  --eval-eval-t _ xs _ _
eval-eval-t f ((i , Ẇ l1 e) ∷ xs) = eval-eval-t f {!!} -- eval-eval-t _ xs _ _

eval-eval-t-ext : ∀ (evalExp  : RegisterVal → Exp → Maybe ℕ) (s : Schedule) → eval evalExp s ≡ eval-t evalExp ⟦ s ⟧
eval-eval-t-ext _ s =  {!!} --funExt (λ σ → funExt (λ ρ → eval-eval-t _ s σ ρ))

  -- funExt (λ σ → funExt (λ ρ → funExt (λ l → eval-eval-t _ s σ ρ l)))

-- Soundness: equal traces give semantically equivalent schedules
trace-sem-sound : {p₁ p₂ : Schedule} → (RegisterVal → Exp → ℕ) → ⟦ p₁ ⟧ ≡ ⟦ p₂ ⟧ → p₁ ≈ p₂
trace-sem-sound {p₁} {p₂} f tr≡ =
  funExt (λ f →
  eval f p₁       ≡⟨ eval-eval-t-ext f p₁ ⟩
  eval-t f ⟦ p₁ ⟧ ≡⟨ cong (eval-t f) tr≡ ⟩
  eval-t f ⟦ p₂ ⟧ ≡⟨ sym (eval-eval-t-ext f p₂) ⟩
  eval f p₂ ∎)

-- The semantic counterpart of serializability (the one that we don't want to use directly)
serializable-eval : Schedule → Set
serializable-eval p = Σ[ (p₁ , p₂) ∈ Transaction × Transaction ] (p ≈ seq-scheduler p₁ p₂)

-- The example schedule is serialisable wrt. store semantics as a consequence of the soundness theorem
ex-serializable-eval : ∀ {evalExp : RegisterVal → Exp → ℕ} {a : ℕ} → serializable-eval (ex-interleaving a)
ex-serializable-eval {evalExp = evalExp} {a = a} =  ( (rw-prog₁ a , rw-prog₁ a) , trace-sem-sound evalExp (ex-trace-equiv {a = a}))

postulate
  ii : ℕ
  ll : ℕ
  xs : Schedule

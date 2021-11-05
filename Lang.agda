{-# OPTIONS --cubical #-}

module Lang  where

open import TraceMonoid

open import Cubical.Foundations.Everything
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Bool hiding (_≟_)
open import Cubical.Foundations.Prelude
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
  Load : Exp              -- load a thread-local variable
  `_ : ℕ → Exp          -- nat literal

infix 22 `_

Location = ℕ

data Action : Set where
  ReadLoc : Location → Action
  WriteLoc : Location → Exp → Action

Transaction = List Action

---------------------------------
-- Traces of Read/Write actions -
---------------------------------

_≠_ : ∀ {A : Set} (a b : A) → Set
a ≠ b = a ≡ b → ⊥

≠-sym : ∀ {A : Set} {a b : A} → a ≠ b → b ≠ a
≠-sym np q =  np (sym q)

data _#'_ : Action → Action → Set where
  #'-RR : ∀ l₁ l₂ → ReadLoc l₁ #' ReadLoc l₂
  #'-WW : ∀ l₁ l₂ e₁ e₂ → l₁ ≠ l₂ → WriteLoc l₁ e₁ #' WriteLoc l₂ e₂
  #'-WR : ∀ l₁ l₂ e → l₁ ≠ l₂ → WriteLoc l₁ e #' ReadLoc l₂
  #'-RW : ∀ l₁ l₂ e → l₁ ≠ l₂ → ReadLoc l₁ #' WriteLoc l₂ e

Event = ℕ × Action

data _#_ : Event → Event → Set where
  #-neq-tr : ∀ (e₁ e₂ : Event)
           → fst e₁ ≠ fst e₂
           → snd e₁ #' snd e₂
           → e₁ # e₂

#-irrefl : ∀ (x : Event) → ¬ (x # x)
#-irrefl (i , e) (#-neq-tr _ _ p _) = p refl

#'-sym : ∀ {a₁ a₂ : Action} → a₁ #' a₂ → a₂ #' a₁
#'-sym (#'-RR l₁ l₂) = #'-RR l₂ l₁
#'-sym (#'-WW l₁ l₂ e₁ e₂ x) = #'-WW l₂ l₁ e₂ e₁ (≠-sym x)
#'-sym (#'-WR l₁ l₂ e x) = #'-RW l₂ l₁ e (≠-sym x)
#'-sym (#'-RW l₁ l₂ e x) = #'-WR l₂ l₁ e (≠-sym x)

#-sym : ∀ {e₁ e₂ : Event} → e₁ # e₂ → e₂ # e₁
#-sym (#-neq-tr _ _ x y) = #-neq-tr _ _ (≠-sym x) (#'-sym y)

instance
  #-indep : IsIndependency _#_
  #-indep = record { #-irrefl = #-irrefl _;
                     #-sym = #-sym }

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

evalE : RegisterVal → Exp → ℕ
evalE v (e₁ ∔ e₂) = evalE v e₁ + evalE v e₂
evalE v Load = v
evalE v (` i) = i

-- Take a global store, registers and return a potentially updated global state
eval : Schedule → Registers → Store  → Store
eval [] ρ σ   = σ
eval ((i , ReadLoc l) ∷ xs) ρ σ  = eval xs (set-reg ρ i (get-default σ l)) σ
eval ((i , WriteLoc l e) ∷ xs) ρ σ  = eval xs ρ ([ l ~> evalE (ρ i) e ] ⊛ σ)

mk-sch : ℕ → Transaction → Schedule
mk-sch i xs = map (λ c → (i , c)) xs


-- A sequential scheduler: it schedules all the commands of the first transation first
-- and afterwards all the commands of the second transation.
seq-scheduler : Transaction → Transaction → Schedule
seq-scheduler xs ys = mk-sch 0 xs ++ mk-sch 1 ys

eval-seq : Store → Registers → Transaction × Transaction → Store
eval-seq σ ρ (t₁ , t₂) = eval (seq-scheduler t₁ t₂) ρ σ

infixr 5 _﹔_

_﹔_ : {A : Set} → A → List A → List A
x ﹔ xs = x ∷ xs

end : {A : Set} → List A
end = []

A = 0
B = 1

rw-prog₁ : ℕ → List Action
rw-prog₁ a = ReadLoc A ﹔ WriteLoc A (Load ∔ ` a) ﹔(ReadLoc  B) ﹔( WriteLoc B (Load ∔ ` 10)) ﹔ end

ex1 : Schedule
ex1 = mk-sch 0 (rw-prog₁ 1)

xy-to-list : Store → List (ℕ × Maybe ℕ)
xy-to-list σ = (0 , σ 0) ∷ (1 , σ 1) ∷ []

ex-eval : xy-to-list (eval ex1 init-regs ∅) ≡ ((0 , just 1) ∷ (1 , just 10) ∷ [])
ex-eval = refl

rw-prog₂ : List Action
rw-prog₂ = ReadLoc A ﹔ WriteLoc A (Load ∔ ` 1) ﹔(ReadLoc  A) ﹔( WriteLoc B (Load ∔ ` 10)) ﹔ end

ex2 : Schedule
ex2 = mk-sch 0 rw-prog₂

ex₂-eval : xy-to-list (eval ex2 init-regs ∅) ≡ ((0 , just 1) ∷ (1 , just 11) ∷ [])
ex₂-eval = refl


of-list : {A : Set} -> {R : A → A → Set } -> {{_ : IsIndependency R}} -> List A → FreePcm A R
of-list [] = ε
of-list (x ∷ xs) = x ̇ of-list xs

-- Interpretation of the Read-Write language as a trace
⟦_⟧ : Schedule → Trace
⟦ s ⟧ = of-list s


-- Trace-equivalent schedules are just schedules with equal traces
_∼_ : Schedule → Schedule → Set
p₁ ∼ p₂ = ⟦ p₁ ⟧ ≡ ⟦ p₂ ⟧


-- A schedule is serializable if it is trace-equivalent to a sequental composition of the two schedules
serializable : Schedule → Set
serializable p = Σ[ (p₁ , p₂) ∈ Transaction × Transaction ] (⟦ p ⟧ ≡ ⟦ seq-scheduler p₁ p₂ ⟧)

-- Semantically equivalent programs result in the same store (we ignore the state of the registers)
_≈_ : Schedule → Schedule → Set
p₁ ≈ p₂ = eval p₁ ≡ eval p₂

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


-- The schedule can be rewritten in the standard "textbook" 2-dimentional notation as follows
-- (we asssume that each transaction commits immedately after the last operation).

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
ex-trace-equiv = pcm-cong-head {s₁ = ReadLoc A %T₀ ̇ WriteLoc A _ %T₀ ̇ ReadLoc B %T₀ ̇ ε}
                 (ReadLoc A %T₁ ̇ WriteLoc A _ %T₁ ̇ WriteLoc B _ %T₀ ̇ ReadLoc B %T₁ ̇ WriteLoc B _ %T₁ ̇ ε
                  ≡⟨ cong (ReadLoc A %T₁ ̇_) (pcm-comm _ _ _ {#-neq-tr _ _ snotz (#'-WW _ _ _ _ znots)}) ⟩
                  ReadLoc A %T₁ ̇ WriteLoc B _ %T₀ ̇ WriteLoc A _ %T₁ ̇ ReadLoc B %T₁ ̇ WriteLoc B _ %T₁ ̇ ε
                  ≡⟨ (pcm-comm _ _ _ {#-neq-tr _ _ snotz (#'-RW _ _ _ znots)}) ⟩
                  WriteLoc B _ %T₀ ̇ ReadLoc A %T₁ ̇ WriteLoc A _ %T₁ ̇ ReadLoc B %T₁ ̇ WriteLoc B _ %T₁ ̇ ε ∎)

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
... | true  | [ eq1 ] | true  | [ eq2 ] = ⊥.elim (neq ((ℕ==→≡ eq1) ∙ sym (ℕ==→≡ eq2)))
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
... | true  | [ eq1 ] | true  | [ eq2 ] = ⊥.elim (neq ((ℕ==→≡ eq1) ∙ sym (ℕ==→≡ eq2)))
... | true  | [ eq1 ] | false | [ eq2 ]  = refl
... | false  | [ eq1 ] | true | [ eq2 ]  = refl
... | false  | [ eq1 ] | false | [ eq2 ]  = refl

update-commutes-ext : ∀ {l₁ v₁ l₂ v₂} → l₁ ≠ l₂ → ([ l₁ ~> v₁ ] ⊛ ([ l₂ ~> v₂ ])) ≡ ([ l₂ ~> v₂ ] ⊛ ([ l₁ ~> v₁ ]))
update-commutes-ext neq = funExt (λ l → update-commutes l neq)


⊛-cong : ∀ {σ₁ σ₂ σ₃ σ₄} → σ₁ ≡ σ₂ → σ₃ ≡ σ₄ → σ₁ ⊛ σ₃ ≡ σ₂ ⊛ σ₄
⊛-cong p q = cong₂ _⊛_ p q

⊛-cong-assoc : ∀ {σ₁ σ₂ σ₃ σ₄ σ} → σ₁ ≡ σ₂ → σ₃ ≡ σ₄ → σ₁ ⊛ (σ₃ ⊛ σ) ≡ σ₂ ⊛ (σ₄ ⊛ σ)
⊛-cong-assoc p q = ⊛-cong p (⊛-cong q refl )

postulate
  -- TODO: use stdlib to show this (e.g. HLevels.isSetΠ and properties of Maybe)
  is-set-eval-t : isSet
      (Registers → Store → Map)

eval-t-rec : Event → (Registers → Store → Map) → Registers → Store → Map
eval-t-rec (i , ReadLoc l) rec ρ σ = rec (set-reg ρ i (get-default σ l)) σ
eval-t-rec (i , WriteLoc l e) rec ρ σ = rec ρ ([ l ~> evalE (ρ i) e ] ⊛ σ)

eval-t-commute : ∀ (x y : Event) (tr : Trace) →
                 (rec :  Registers → Store → Map) →
                 x # y →
                 eval-t-rec x (eval-t-rec y rec) ≡ eval-t-rec y (eval-t-rec x rec)
eval-t-commute (i₁ , _) (i₂ , _) tr rec (#-neq-tr _ _ neq (#'-RR l₁ l₂)) =
                        funExt (λ _ → funExt λ _ → cong₂ rec (set-reg-≠-regs-ext neq) refl)
eval-t-commute (i₁ , _) (i₂ , _) tr rec (#-neq-tr _ _ neq (#'-WW l₁ l₂ e₁ e₂ x)) =
                        funExt (λ ρ → funExt λ σ → cong (rec ρ)
                               ( [ l₂ ~> evalE (ρ i₂) e₂ ] ⊛ ([ l₁ ~> evalE (ρ i₁) e₁ ] ⊛ σ) ≡⟨ ⊛-assoc [ l₂ ~> evalE (ρ i₂) e₂ ] _ _ ⟩
                                ([ l₂ ~> evalE (ρ i₂) e₂ ] ⊛ [ l₁ ~> evalE (ρ i₁) e₁ ]) ⊛ σ  ≡⟨ ⊛-cong (update-commutes-ext (≠-sym x)) refl ⟩
                                ([ l₁ ~> evalE (ρ i₁) e₁ ] ⊛ [ l₂ ~> evalE (ρ i₂) e₂ ]) ⊛ σ  ≡⟨ sym (⊛-assoc ([ l₁ ~> evalE (ρ i₁) e₁ ]) _ _) ⟩
                                 [ l₁ ~> evalE (ρ i₁) e₁ ] ⊛ ([ l₂ ~> evalE (ρ i₂) e₂ ] ⊛ σ) ∎))
eval-t-commute (i₁ , _) (i₂ , _) tr rec (#-neq-tr _ _ neq (#'-WR l₁ l₂ e x)) =
                        funExt (λ ρ →
                          funExt λ σ →
                            cong₂ rec (funExt λ v →
                              cong₂ (set-reg ρ i₂)
                                    ((get-default-≠ {σ = σ} x)) refl)
                                    (cong (λ x → [ l₁ ~> evalE x e ] ⊛ σ) (sym (set-reg-irrel {ρ = ρ} (≠-sym neq)))))
eval-t-commute (i₁ , _) (i₂ , _) tr rec (#-neq-tr _ _ neq (#'-RW l₁ l₂ e x)) =
                        funExt (λ ρ →
                          funExt λ σ →
                            cong₂ rec (cong (set-reg ρ i₁) (sym (get-default-≠ {σ = σ} (≠-sym x))) )
                                      (⊛-cong (cong (λ x → [ l₂ ~> evalE x e ]) (set-reg-irrel {ρ = ρ} neq)) refl ))

-- We define new sematics by evaluating a trace directly.
-- We use the recursion principle for the trace monoid, which forces us to prove that
-- the permutation of independent actions does not change the store
eval-t : Trace → Registers → Store → Store
eval-t tr =
  Rec.f is-set-eval-t (λ _ σ → σ)  eval-t-rec (λ x y rec → eval-t-commute x y tr rec ) tr --

-- The store semantics on lists of commands gives the same result as the semantics on traces
eval-eval-t : ∀ (s : Schedule) (ρ : Registers) (σ : Store) (l : Location) → eval s ρ σ l ≡ eval-t ⟦ s ⟧ ρ σ l
eval-eval-t [] ρ σ l = refl
eval-eval-t ((i , ReadLoc l1) ∷ xs) ρ σ  l = eval-eval-t xs _ _ _
eval-eval-t ((i , WriteLoc l1 e) ∷ xs) ρ σ l =  eval-eval-t xs _ _ _

eval-eval-t-ext : ∀ (s : Schedule) → eval s ≡ eval-t ⟦ s ⟧
eval-eval-t-ext s = funExt (λ σ → funExt (λ ρ → funExt (λ l → eval-eval-t s σ ρ l)))

-- Soundness: equal traces give semantically equivalent schedules
trace-sem-sound : {p₁ p₂ : Schedule} → ⟦ p₁ ⟧ ≡ ⟦ p₂ ⟧ → p₁ ≈ p₂
trace-sem-sound {p₁} {p₂} tr≡ =
  eval p₁      ≡⟨ eval-eval-t-ext p₁ ⟩
  eval-t ⟦ p₁ ⟧ ≡⟨ cong eval-t tr≡ ⟩
  eval-t ⟦ p₂ ⟧ ≡⟨ sym (eval-eval-t-ext p₂) ⟩
  eval p₂ ∎

-- The semantic counterpart of serializability (the one that we don't want to use directly)
serializable-eval : Schedule → Set
serializable-eval p = Σ[ (p₁ , p₂) ∈ Transaction × Transaction ] (p ≈ seq-scheduler p₁ p₂)

-- The example schedule is serialisable wrt. store semantics as a consequence of the soundness theorem
ex-serializable-eval : ∀ {a : ℕ} → serializable-eval (ex-interleaving a)
ex-serializable-eval {a = a} =  ( (rw-prog₁ a , rw-prog₁ a) , trace-sem-sound (ex-trace-equiv {a = a}))

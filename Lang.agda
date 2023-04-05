{-# OPTIONS --cubical -W noUnsupportedIndexedMatch #-}

module Lang  where

open import TraceMonoid

open import Cubical.Foundations.Everything hiding (_∙_)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Bool hiding (_≟_)
open import Cubical.Foundations.Prelude renaming (_∙_ to compPath)
open import Cubical.Algebra.Monoid
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidablePropositions

open import Agda.Primitive
open import Agda.Builtin.List
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

module Lang (Location : Set) (isDiscr : Discrete Location) where

  ----------------------------
  -- The Read-Write language -
  ----------------------------

  data Exp : Set where
    _∔_ : Exp → Exp → Exp -- addition
    Load : Exp              -- load a thread-local variable
    `_ : ℕ → Exp          -- nat literal

  infix 22 `_

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
  [ l₁ ~> i ] l₂ with isDiscr l₁ l₂
  ... | yes _ = just i 
  ... | no _ = nothing


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
  eval ((i , Ṙ l) ∷ xs) ρ σ  = eval xs (set-reg ρ i (get-default σ l)) σ
  eval ((i , Ẇ l e) ∷ xs) ρ σ  = eval xs ρ ([ l ~> evalE (ρ i) e ] ⊛ σ)

  mk-sch : ℕ → Transaction → Schedule
  mk-sch i xs = map (λ c → (i , c)) xs


  -- A sequential scheduler: it schedules all the commands of the first transation first
  -- and afterwards all the commands of the second transation.
  seq-scheduler : Transaction → Transaction → Schedule
  seq-scheduler xs ys = mk-sch 0 xs ++ mk-sch 1 ys

  eval-seq : Store → Registers → Transaction × Transaction → Store
  eval-seq σ ρ (t₁ , t₂) = eval (seq-scheduler t₁ t₂) ρ σ


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
  p₁ ≈ p₂ = eval p₁ ≡ eval p₂
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
  ... | true  | [ eq1 ]ᵢ  | true  | [ eq2 ]ᵢ = ⊥.elim (neq (compPath (ℕ==→≡ eq1) (sym (ℕ==→≡ eq2))))
  ... | true  | [ eq1 ]ᵢ  | false | [ eq2 ]ᵢ  = refl
  ... | false | _ | true  | _ = refl
  ... | false | _ | false | _ = refl

  get-default-≠ : ∀ {l₁ l₂ v σ } → l₁ ≠ l₂ → get-default ([ l₁ ~> v ] ⊛ σ) l₂ ≡ get-default σ l₂
  get-default-≠ {l₁} {l₂} {v} {σ} p with isDiscr l₁ l₂
  ... | yes eq  = ⊥.elim  (p eq)
  ... | no _    = refl

  set-reg-≠-regs-ext : ∀ {i₁ i₂ v₁ v₂ ρ} → i₁ ≠ i₂  → set-reg (set-reg ρ i₁ v₁) i₂ v₂ ≡ set-reg (set-reg ρ i₂ v₂) i₁ v₁
  set-reg-≠-regs-ext {i₁} {i₂} {v₁} {v₂} {ρ} neq = funExt (λ x → set-reg-≠-regs {x} {i₁} {i₂} {v₁} {v₂} {ρ} neq)

  set-reg-irrel : ∀ {ρ i₁ i₂ v} → i₁ ≠ i₂ → set-reg ρ i₁ v i₂ ≡ ρ i₂
  set-reg-irrel {ρ} {i₁} {i₂} {v} neq with (i₁ == i₂)| inspect (λ x → i₁ == x) i₂
  ... | true  | [ eq ]ᵢ = ⊥.elim (neq (ℕ==→≡ eq))
  ... | false  | [ eq ]ᵢ = refl

  update-commutes : ∀ {l₁ v₁ l₂ v₂} l → l₁ ≠ l₂ → ([ l₁ ~> v₁ ] ⊛ ([ l₂ ~> v₂ ])) l ≡ ([ l₂ ~> v₂ ] ⊛ ([ l₁ ~> v₁ ])) l
  update-commutes {l₁} {v₁} {l₂} {v₂} l neq with isDiscr l₁ l | isDiscr l₂ l
  ... | yes eq1  | yes eq2  = ⊥.elim (neq (compPath eq1 (sym eq2)))
  ... | yes eq1  | no _     = refl
  ... | no _     | yes eq2  = refl
  ... | no _     | no  _    = refl

  update-commutes-ext : ∀ {l₁ v₁ l₂ v₂} → l₁ ≠ l₂ → ([ l₁ ~> v₁ ] ⊛ ([ l₂ ~> v₂ ])) ≡ ([ l₂ ~> v₂ ] ⊛ ([ l₁ ~> v₁ ]))
  update-commutes-ext neq = funExt (λ l → update-commutes l neq)


  ⊛-cong : ∀ {σ₁ σ₂ σ₃ σ₄} → σ₁ ≡ σ₂ → σ₃ ≡ σ₄ → σ₁ ⊛ σ₃ ≡ σ₂ ⊛ σ₄
  ⊛-cong p q = cong₂ _⊛_ p q

  ⊛-cong-assoc : ∀ {σ₁ σ₂ σ₃ σ₄ σ} → σ₁ ≡ σ₂ → σ₃ ≡ σ₄ → σ₁ ⊛ (σ₃ ⊛ σ) ≡ σ₂ ⊛ (σ₄ ⊛ σ)
  ⊛-cong-assoc p q = ⊛-cong p (⊛-cong q refl )

  is-set-eval-t : isSet (Registers → Store → Map)
  is-set-eval-t = isSetΠ2 (λ _ _ → isSetΠ (λ _ → isOfHLevelMaybe zero isSetℕ))

  eval-t-rec : Event → (Registers → Store → Map) → Registers → Store → Map
  eval-t-rec (i , Ṙ l) rec ρ σ = rec (set-reg ρ i (get-default σ l)) σ
  eval-t-rec (i , Ẇ l e) rec ρ σ = rec ρ ([ l ~> evalE (ρ i) e ] ⊛ σ)

  eval-t-commute : ∀ (x y : Event) (tr : Trace) →
                  (rec :  Registers → Store → Map) →
                  x # y →
                  eval-t-rec x (eval-t-rec y rec) ≡ eval-t-rec y (eval-t-rec x rec)
  eval-t-commute (i₁ , _) (i₂ , _) tr rec (#-neq-tr _ _ neq (#ₐ-RR l₁ l₂)) =
                          funExt (λ _ → funExt λ _ → cong₂ rec (set-reg-≠-regs-ext neq) refl)
  eval-t-commute (i₁ , _) (i₂ , _) tr rec (#-neq-tr _ _ neq (#ₐ-WW l₁ l₂ e₁ e₂ x)) =
                          funExt (λ ρ → funExt λ σ → cong (rec ρ)
                                ( [ l₂ ~> evalE (ρ i₂) e₂ ] ⊛ ([ l₁ ~> evalE (ρ i₁) e₁ ] ⊛ σ) ≡⟨ ⊛-assoc [ l₂ ~> evalE (ρ i₂) e₂ ] _ _ ⟩
                                  ([ l₂ ~> evalE (ρ i₂) e₂ ] ⊛ [ l₁ ~> evalE (ρ i₁) e₁ ]) ⊛ σ  ≡⟨ ⊛-cong (update-commutes-ext (≠-sym x)) refl ⟩
                                  ([ l₁ ~> evalE (ρ i₁) e₁ ] ⊛ [ l₂ ~> evalE (ρ i₂) e₂ ]) ⊛ σ  ≡⟨ sym (⊛-assoc ([ l₁ ~> evalE (ρ i₁) e₁ ]) _ _) ⟩
                                  [ l₁ ~> evalE (ρ i₁) e₁ ] ⊛ ([ l₂ ~> evalE (ρ i₂) e₂ ] ⊛ σ) ∎))
  eval-t-commute (i₁ , _) (i₂ , _) tr rec (#-neq-tr _ _ neq (#ₐ-WR l₁ l₂ e x)) =
                          funExt (λ ρ →
                            funExt λ σ →
                              cong₂ rec (funExt λ v →
                                cong₂ (set-reg ρ i₂)
                                      ((get-default-≠ {σ = σ} x)) refl)
                                      (cong (λ x → [ l₁ ~> evalE x e ] ⊛ σ) (sym (set-reg-irrel {ρ = ρ} (≠-sym neq)))))
  eval-t-commute (i₁ , _) (i₂ , _) tr rec (#-neq-tr _ _ neq (#ₐ-RW l₁ l₂ e x)) =
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
  eval-eval-t ((i , Ṙ l1) ∷ xs) ρ σ  l = eval-eval-t xs _ _ _
  eval-eval-t ((i , Ẇ l1 e) ∷ xs) ρ σ l =  eval-eval-t xs _ _ _

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

-------------
-- Example --
-------------

open module Langℕ = Lang Nat (discreteℕ)

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

xy-to-list : Store → List (ℕ × Maybe ℕ)
xy-to-list σ = (0 , σ 0) ∷ (1 , σ 1) ∷ []

ex-eval : xy-to-list (eval ex1 init-regs ∅) ≡ ((0 , just 1) ∷ (1 , just 10) ∷ [])
ex-eval = refl

rw-prog₂ : List Action
rw-prog₂ = Ṙ A ﹔ Ẇ A (Load ∔ ` 1) ﹔(Ṙ  A) ﹔( Ẇ B (Load ∔ ` 10)) ﹔ end

ex2 : Schedule
ex2 = mk-sch 0 rw-prog₂

ex₂-eval : xy-to-list (eval ex2 init-regs ∅) ≡ ((0 , just 1) ∷ (1 , just 11) ∷ [])
ex₂-eval = refl

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

-- The example schedule is serialisable wrt. store semantics as a consequence of the soundness theorem
ex-serializable-eval : ∀ {a : ℕ} → serializable-eval (ex-interleaving a)
ex-serializable-eval {a = a} =  ( (rw-prog₁ a , rw-prog₁ a) , trace-sem-sound (ex-trace-equiv {a = a}))

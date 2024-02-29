{-# OPTIONS --cubical -W noUnsupportedIndexedMatch --rewriting  #-}

module Lang  where

open import TraceMonoid

open import Agda.Builtin.Equality.Rewrite

open import Cubical.Foundations.Everything hiding (_∙_)
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Bool hiding (_≟_ ; _≤_)
open import Cubical.Foundations.Prelude renaming (_∙_ to compPath)
open import Cubical.Algebra.Monoid
open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.DecidablePropositions

open import Agda.Primitive
open import Agda.Builtin.List
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat hiding (_<_)

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

  infixr 5 _﹔_

  _﹔_ : {A : Set} → A → List A → List A
  x ﹔ xs = x ∷ xs

  end : {A : Set} → List A
  end = []

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

  TxId = ℕ
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

  data SameTx (txId : TxId) : List Event → Set where
    same-tx-[] : SameTx txId []
    same-tx-∷ : ∀ a xs → SameTx txId xs → SameTx txId ((txId , a) ∷ xs)

  same-tx : List Event → TxId → Bool
  same-tx [] _ = true
  same-tx ((i , _) ∷ es) txId = if i == txId  then same-tx es txId else false
  -- same-tx ((i , _) ∷ es) txId with discreteℕ i txId 
  -- ... | yes _ = same-tx es txId 
  -- ... | no _ = false

  same-tx-++ : ∀ {xs₁ xs₂ i} → same-tx xs₁ i ≡ true → same-tx xs₂ i ≡ true → same-tx (xs₁ ++ xs₂) i ≡ true
  same-tx-++ {[]} {xs₂} {i} s₁ s₂ = s₂
  same-tx-++ {x ∷ xs₁} {xs₂} {i} s₁ s₂ = {!   !}

  has-same-tx : List Event → TxId → Set
  has-same-tx xs txId = same-tx xs txId ≡ true

  Tx# : TxId → Set
  Tx# txId = Σ[ xs ∈ List Event ] has-same-tx xs txId

  Transaction : Set
  Transaction = Σ[ txId ∈ TxId ] Tx# txId


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

  mk-sch : ℕ → List Action → Schedule
  mk-sch txId xs = map (λ c → (txId , c)) xs

  -- Sequential scheduling: schedules all the events of the first transation first
  -- and afterwards all the events of the second transation.
  seq-scheduler : Transaction → Transaction → Schedule
  seq-scheduler xs ys =  xs .snd .fst ++ ys .snd .fst

  of-list : {A : Set} -> {R : A → A → Set } -> {{_ : IsIndependence R}} -> List A → FreePcm A R
  of-list [] = ε
  of-list (x ∷ xs) = x ∙ of-list xs

  -- Interpretation of the Read-Write language as a trace
  ⟦_⟧ : Schedule → Trace
  ⟦ s ⟧ = of-list s

  -- Trace-equivalent schedules are just schedules with equal traces
  _∼_ : Schedule → Schedule → Set
  p₁ ∼ p₂ = ⟦ p₁ ⟧ ≡ ⟦ p₂ ⟧

  -- A schedule is serializable if it is trace-equivalent to a sequental composition of two schedules
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
  ... | yes eq  = ⊥.elim (p eq)
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

module Example where
  
  open module Langℕ = Lang ℕ (discreteℕ)

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
  T₀-acts = 0 , (T₀: Ṙ A ﹔ T₀: Ẇ A (Load ∔ ` 1) ﹔ end) , refl

  T₁-acts : Transaction
  T₁-acts = 1 , (T₁: Ẇ B (` 10) ﹔ T₁: Ẇ A (` 2) ﹔ end) , refl

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


  ex-trace-equiv : {a : ℕ} → ex-interleaving a ∼ seq-scheduler (0 , mk-sch 0 (rw-prog₁ a) , refl) (1 , mk-sch 1 (rw-prog₁ a) , refl)
  ex-trace-equiv = pcm-cong-head {s₁ = T₀: Ṙ A  ∙ T₀: Ẇ A _ ∙ T₀: Ṙ B ∙ ε}
                  (T₁: Ṙ A  ∙ T₁: Ẇ A _ ∙ T₀: Ẇ B _ ∙ T₁: Ṙ B ∙ T₁: Ẇ B _ ∙ ε
                    ≡⟨ cong (T₁: Ṙ A ∙_) (pcm-comm _ _ _ (#-neq-tr _ _ snotz (#ₐ-WW _ _ _ _ znots))) ⟩
                   T₁: Ṙ A ∙ T₀: Ẇ B _ ∙ T₁: Ẇ A _ ∙ T₁: Ṙ B ∙ T₁: Ẇ B _ ∙ ε
                    ≡⟨ (pcm-comm _ _ _ (#-neq-tr _ _ snotz (#ₐ-RW _ _ _ znots))) ⟩
                   T₀: Ẇ B _ ∙ T₁: Ṙ A ∙ T₁: Ẇ A _ ∙ T₁: Ṙ B  ∙ T₁: Ẇ B _ ∙ ε ∎)

  -- The interleaved schedule is serializable, therefore safe
  ex-serializable : ∀ {a : ℕ} → serializable (ex-interleaving a)
  ex-serializable {a = a} =  ( ((0 , mk-sch 0 (rw-prog₁ a) , refl) , (1 , mk-sch 1 (rw-prog₁ a) , refl)) , ex-trace-equiv {a = a})

  -- The example schedule is serialisable wrt. store semantics as a consequence of the soundness theorem
  ex-serializable-eval : ∀ {a : ℕ} → serializable-eval (ex-interleaving a)
  ex-serializable-eval {a = a} =  ( ((0 , mk-sch 0 (rw-prog₁ a) , refl) , (1 , mk-sch 1 (rw-prog₁ a) , refl)) , trace-sem-sound (ex-trace-equiv {a = a}))

data Location : Set where
    A : Location
    B : Location

_≟_ : Discrete Location
A ≟ A = yes refl
B ≟ A  = no λ p → subst (λ {A → ⊥ ;  B → Location}) p B
A ≟ B = no λ p → subst (λ {A → Location ;  B → ⊥}) p A
B ≟ B  = yes refl

Location-rec : ∀ {ℓ} {A : Set ℓ} → (a b : A) → (l : Location) → A
Location-rec a b A = a
Location-rec a b B = b

A≢B : ¬ A ≡ B
A≢B p = subst (Location-rec Location ⊥) p A

module SequentalScheduler where

  {-# BUILTIN REWRITE _≡_ #-}

  open module LangBool = Lang Location (_≟_)
  
  -- Schedules two transaction actions in the following way:
  -- if the first action belongs to T₀ (T₁) , then schedule all operation of T₀ (T₁) first and put all T₁ (T₀) operation in the queue;
  -- once no actions left in the input, schedule all actions waiting in the queue. 
  sequential-scheduler : List Event → List Event → Maybe TxId → Schedule
  sequential-scheduler [] queue i = rev queue
  sequential-scheduler (a@(0 , _) ∷ xs) queue nothing = a ∷ sequential-scheduler xs queue (just 0)
  sequential-scheduler (a@(1 , _) ∷ xs) queue nothing = a ∷ sequential-scheduler xs queue (just 1)
  sequential-scheduler (a@(0 , _) ∷ xs) queue i@(just 0) = a ∷ sequential-scheduler xs queue i
  sequential-scheduler (a@(1 , _) ∷ xs) queue i@(just 1) = a ∷ sequential-scheduler xs queue i
  sequential-scheduler (a@(0 , _) ∷ xs) queue i@(just 1) = sequential-scheduler xs (a ∷ queue) i
  sequential-scheduler (a@(1 , _) ∷ xs) queue i@(just 0) = sequential-scheduler xs (a ∷ queue) i
  sequential-scheduler (_ ∷ xs ) q i = sequential-scheduler xs q i

  get-tx-aux : TxId → List Event → List Event
  get-tx-aux _ [] = []
  get-tx-aux n ((i , a) ∷ es) = if i == n then (i , a) ∷ get-tx-aux n es else get-tx-aux n es

  get-tx-aux-has-same-tx : ∀ n xs → has-same-tx (get-tx-aux n xs) n
  get-tx-aux-has-same-tx n [] = refl
  get-tx-aux-has-same-tx n ((i , a) ∷ xs) with i == n | inspect (_== n) i
  ... | true  | [ p ]ᵢ = subst (λ x → (if x then same-tx (get-tx-aux n xs) n else false) ≡ true) (sym p) (get-tx-aux-has-same-tx n xs)
  ... | false | [ p ]ᵢ = get-tx-aux-has-same-tx n xs

  get-tx : TxId → List Event → Transaction
  get-tx n xs = (n , get-tx-aux n xs , get-tx-aux-has-same-tx n xs)

  get-tx-aux-++ : ∀ xs₁ xs₂ txId → get-tx-aux txId (xs₁ ++ xs₂) ≡ get-tx-aux txId xs₁ ++ get-tx-aux txId xs₂
  get-tx-aux-++ [] xs₂ txId = refl
  get-tx-aux-++ ( (i , x) ∷ xs₁) xs₂ txId with i == txId 
  ... | true = cong (_ ∷_) (get-tx-aux-++ xs₁ xs₂ txId)
  ... | false = get-tx-aux-++ xs₁ xs₂ txId

  {-# REWRITE ++-unit-r get-tx-aux-++ ++-assoc #-}

  get-tx-aux-same-tx : ∀ txId xs → has-same-tx xs txId → get-tx-aux txId xs ≡ xs
  get-tx-aux-same-tx txId [] s = refl
  get-tx-aux-same-tx txId ( (i , a) ∷ xs) s with i == txId 
  ... | true = cong (_ ∷_) (get-tx-aux-same-tx _ _ s)
  ... | false = ⊥.elim {A = λ _ → get-tx-aux txId xs ≡ (i , a) ∷ xs} (true≢false (sym s))

  sequental-scheduler-eq-0 : ∀ (xs : List Event) (q : List Event) (s : same-tx (rev q) 0 ≡ true) → 
    sequential-scheduler xs q (just 1) ≡ seq-scheduler (get-tx 1 xs) (get-tx 0 (rev q ++ xs))
  sequental-scheduler-eq-0 [] q s = sym (get-tx-aux-same-tx _ _ s)
  sequental-scheduler-eq-0 ((0 , a) ∷ xs) q s = sequental-scheduler-eq-0 xs ((0 , a) ∷ q) (same-tx-++ {rev q} {[ (0 , a) ]} s refl)
  sequental-scheduler-eq-0 ((1 , a) ∷ xs) q s = cong ( (1 , a) ∷_) (sequental-scheduler-eq-0 xs _ s)
  sequental-scheduler-eq-0 ((suc (suc _) , _) ∷ xs) q s = sequental-scheduler-eq-0 xs q s

  sequental-scheduler-eq-1 : ∀ (xs : List Event) (q : List Event) (s : same-tx (rev q) 1 ≡ true) → 
    sequential-scheduler xs q (just 0) ≡ seq-scheduler (get-tx 0 xs) (get-tx 1 (rev q ++ xs))
  sequental-scheduler-eq-1 [] q s = sym (get-tx-aux-same-tx _ _ s)
  sequental-scheduler-eq-1 ((0 , a) ∷ xs) q s = cong ( (0 , a) ∷_) (sequental-scheduler-eq-1 xs _ s)
  sequental-scheduler-eq-1 ((1 , a) ∷ xs) q s = sequental-scheduler-eq-1 xs ((1 , a) ∷ q) (same-tx-++ {rev q} {[ (1 , a) ]} s refl)
  sequental-scheduler-eq-1 ((suc (suc _) , _) ∷ xs) q s = sequental-scheduler-eq-1 xs q s

  sequential-scheduler-serializable : ∀ es → serializable (sequential-scheduler es [] nothing)
  sequential-scheduler-serializable [] =  ((0 , [] , refl) , 0 , ([] , refl)) , refl 
  sequential-scheduler-serializable es@((0 , a) ∷ xs) = (get-tx 0 es , get-tx 1 es) , cong of-list (cong (_ ∷_) ((sequental-scheduler-eq-1 xs [] refl)))
  sequential-scheduler-serializable es@((1 , a) ∷ xs) = (get-tx 1 es , get-tx 0 es) , cong of-list (cong (_ ∷_) ((sequental-scheduler-eq-0 xs [] refl)))
  sequential-scheduler-serializable ((suc (suc i) , a) ∷ es) = sequential-scheduler-serializable es
 

module TwoPhaseLocking where

  open module LangBool = Lang Location (_≟_)

  infix 40 T₀:_
  infix 40 T₁:_

  T₀:_ : Action → TxId × Action
  T₀: e = (0 , e)

  T₁:_ : Action → TxId × Action
  T₁: e = (1 , e)

  data Lock : Set where
    S : List TxId → Lock -- shared
    X : TxId → Lock -- exclusive

  record LockTable : Set where

    constructor LT

    field 
      lockA : Maybe Lock
      lockB : Maybe Lock
    
  open LockTable

  record Discr (A : Set) : Set where
    field
      discr : Discrete A

  instance
    DiscrLocation : Discr Location
    DiscrLocation = record { discr = _≟_ }

  open Discr

  _∈_ : {A : Set} {{ d : Discr A }} → A → List A → Bool
  _∈_ a [] = false
  _∈_ {{d = d}} a (x ∷ xs) with (discr d a x)
  ... | yes _ =  true 
  ... | no _  = a ∈ xs

  ∅-table : LockTable
  ∅-table = LT nothing nothing

  -- lock compatibility table
  acquire-lock : Lock → Lock → Maybe Lock
  acquire-lock (S xs₁) (S xs₂) = just (S (xs₁ ++ xs₂))
  acquire-lock (S (x₁ ∷ [])) (X x₂) = if x₁ == x₂ then just (X x₂) else nothing -- already locked with an exclusive lock in the same tx
  acquire-lock (S _) (X _) = nothing
  acquire-lock (X x₁) (S (x₂ ∷ [])) = if x₁ == x₂ then just (X x₁) else nothing -- promote S to X for the same tx
  acquire-lock (X _) (S _) = nothing
  acquire-lock (X x₁) (X x₂) = if x₁ == x₂ then just (X x₁) else nothing
  
  acquire-locks : LockTable → LockTable → Maybe LockTable
  acquire-locks (LT (just lA₁) (just lB₁)) (LT (just lA₂) (just lB₂)) with acquire-lock lA₁ lA₂ | acquire-lock lB₁ lB₂
  ... | just t₁' | just t₂' = just (LT (just t₁') (just t₂'))
  ... | _        | _        = nothing
  acquire-locks (LT nothing (just lB₁)) (LT lA₂ (just lB₂)) with acquire-lock lB₁ lB₂
  ... | just t₂' = just (LT lA₂ (just t₂'))
  ... | _        = nothing
  acquire-locks (LT (just lA₁) nothing) (LT (just lA₂) lB₂) with acquire-lock lA₁ lA₂
  ... | just t₁' = just (LT (just t₁') lB₂)
  ... | _        = nothing
  acquire-locks (LT lA₁ (just lB₁)) (LT nothing (just lB₂)) with acquire-lock lB₁ lB₂
  ... | just t₂' = just (LT lA₁ (just t₂'))
  ... | _        = nothing
  acquire-locks (LT (just lA₁) lB₁) (LT (just lA₂) nothing)  with acquire-lock lA₁ lA₂
  ... | just t₁' = just (LT (just t₁') lB₁)
  ... | _        = nothing
  acquire-locks (LT lA₁ nothing) (LT nothing lB₂) = just (LT lA₁ lB₂)
  acquire-locks (LT nothing lB₁) (LT lA₂ nothing) = just (LT lA₂ lB₁)
  acquire-locks (LT nothing nothing) t = just t
  acquire-locks t (LT nothing nothing) = just t
  
  has-X : Location → LockTable → Bool
  has-X A (LT nothing _) = false
  has-X B (LT _ nothing) = false
  has-X A (LT (just (X _)) _) = true
  has-X B (LT _ (just (X _))) = true
  has-X _ _ = false
  
  acquire-locks-tx₀-alt : List Event → LockTable → LockTable
  acquire-locks-tx₀-alt [] t = t
  acquire-locks-tx₀-alt ((0 , Ṙ A) ∷ xs) t = 
      let t' = if has-X A t then t else record t { lockA = just (S (0 ∷ [])) }
      in acquire-locks-tx₀-alt xs t'
  acquire-locks-tx₀-alt ((0 , Ṙ B) ∷ xs) t = 
      let t' = if has-X B t then t else record t { lockB = just (S (0 ∷ [])) }
      in acquire-locks-tx₀-alt xs t'
  acquire-locks-tx₀-alt ((0 , Ẇ A e) ∷ xs) t = acquire-locks-tx₀-alt xs (record t { lockA = just (X 0) })
  acquire-locks-tx₀-alt ((0 , Ẇ B e) ∷ xs) t = acquire-locks-tx₀-alt xs (record t { lockB = just (X 0) })
  acquire-locks-tx₀-alt (_ ∷ xs) t = acquire-locks-tx₀-alt xs t

  acquire-locks-tx₁-alt : List Event → LockTable → LockTable
  acquire-locks-tx₁-alt [] t = t
  acquire-locks-tx₁-alt ((1 , Ṙ A) ∷ xs) t = 
      let t' = if has-X A t then t else record t { lockA = just (S (1 ∷ [])) }
      in acquire-locks-tx₁-alt xs t'
  acquire-locks-tx₁-alt ((1 , Ṙ B) ∷ xs) t = 
      let t' = if has-X B t then t else record t { lockB = just (S (1 ∷ [])) }
      in acquire-locks-tx₁-alt xs t'
  acquire-locks-tx₁-alt ((1 , Ẇ A e) ∷ xs) t = acquire-locks-tx₁-alt xs (record t { lockA = just (X 1) })
  acquire-locks-tx₁-alt ((1 , Ẇ B e) ∷ xs) t = acquire-locks-tx₁-alt xs (record t { lockB = just (X 1) })
  acquire-locks-tx₁-alt (_ ∷ xs) t = acquire-locks-tx₁-alt xs t

  acquire-locks-tx₀ : List Event → Maybe LockTable
  acquire-locks-tx₀ [] = just (LT nothing nothing)
  acquire-locks-tx₀ ((i , Ṙ A) ∷ xs) with acquire-locks-tx₀ xs 
  ... | just t = acquire-locks (LT (just (S (0 ∷ []))) nothing )  t
  ... | nothing = nothing
  acquire-locks-tx₀ ((i , Ṙ B) ∷ xs) with acquire-locks-tx₀ xs 
  ... | just t = acquire-locks (LT nothing (just (S (0 ∷ []))))  t
  ... | nothing = nothing
  acquire-locks-tx₀ ((i , Ẇ A e) ∷ xs) with acquire-locks-tx₀ xs 
  ... | just t = acquire-locks (LT (just (X 0)) nothing )  t
  ... | nothing = nothing 
  acquire-locks-tx₀ ((i , Ẇ B e) ∷ xs) with acquire-locks-tx₀ xs 
  ... | just t = acquire-locks (LT nothing (just (X 0)) ) t
  ... | nothing = nothing 

  lock-scheduler : List Event → List Event → Maybe LockTable → Maybe LockTable → Schedule
  lock-scheduler [] queue _ _ = rev queue
  lock-scheduler (a@(0 , _) ∷ xs) queue nothing nothing = 
        let locksTx₀ = acquire-locks-tx₀-alt (a ∷ xs) ∅-table
        in a ∷ lock-scheduler xs queue (just locksTx₀) nothing
  lock-scheduler (a@(0 , _) ∷ xs) queue lAs@(just _) lBs = a ∷ lock-scheduler xs queue lAs lBs
  lock-scheduler (a@(1 , _) ∷ xs) queue nothing nothing = 
        let locksTx₁ = acquire-locks-tx₁-alt (a ∷ xs) ∅-table 
        in a ∷ lock-scheduler xs queue  nothing (just locksTx₁)
  lock-scheduler (a@(1 , _) ∷ xs) queue lAs lBs@(just _) = a ∷ lock-scheduler xs queue lAs lBs
  lock-scheduler (a@(0 , _) ∷ xs) queue nothing (just lBs) with acquire-locks (acquire-locks-tx₀-alt (a ∷ xs) ∅-table) lBs 
  ... | just newLT = a ∷ lock-scheduler xs queue (just newLT) (just lBs)
  ... | nothing = lock-scheduler xs (a ∷ queue) nothing (just lBs)
  lock-scheduler (a@(1 , _) ∷ xs) queue (just lAs) nothing with acquire-locks (acquire-locks-tx₁-alt (a ∷ xs) ∅-table) lAs 
  ... | just newLT = a ∷ lock-scheduler xs queue (just lAs) (just newLT)
  ... | nothing = lock-scheduler xs (a ∷ queue) (just lAs) nothing
  lock-scheduler _ _ _ _ = []

  -- TBD: proof of serializability of the two-phase locking scheduler.
  postulate 
  
    lock-scheduler-serialisable : ∀ es → serializable (lock-scheduler es [] nothing nothing)

  -- lock-scheduler-serialisable [] = ((0 , [] , refl) , 0 , ([] , refl)) , refl 
  -- lock-scheduler-serialisable ((0 , Ṙ A) ∷ es) = {!   !}
  -- lock-scheduler-serialisable ((0 , Ṙ B) ∷ es) = {!   !}
  -- lock-scheduler-serialisable ((0 , Ẇ x x₁) ∷ es) = {!   !}
  -- lock-scheduler-serialisable ((1 , a) ∷ es) = {!   !}
  -- lock-scheduler-serialisable ((_ , a) ∷ es) = {!   !}
  
open TwoPhaseLocking

open TwoPhaseLocking.LangBool

-- a list of input transactions
input-txs : List Event
input-txs =
  T₀: Ṙ A ﹔ T₁: Ẇ B (` 10) ﹔ T₀: Ẇ A (Load ∔ ` 1) ﹔ T₁: Ẇ A (` 10) ﹔ end

table0 : LockTable
table0 = acquire-locks-tx₀-alt input-txs ∅-table

table1 : LockTable
table1 = acquire-locks-tx₁-alt input-txs ∅-table

example-lock-schedule : Schedule
example-lock-schedule = lock-scheduler input-txs [] nothing nothing

-- T₀ acquires an exclusive lock on A and B, so T₁ cannot aquire any locks until T₀ commits and releases the locks.
-- The resulting schedule looks as follows
-------------------------|
--| T₀ : RA  WA          |
--| T₁ :         WB  WA  |
-------------------------|

example-lock-schedule-eq : 
  example-lock-schedule ≡ T₀: Ṙ A ﹔ T₀: Ẇ A (Load ∔ ` 1) ﹔ T₁: Ẇ B (` 10) ﹔ T₁: Ẇ A (` 10) ﹔ end
example-lock-schedule-eq = refl

input-txs-different-locations : List Event
input-txs-different-locations =
  T₀: Ṙ A ﹔ T₁: Ṙ B ﹔ T₀: Ẇ A (Load ∔ ` 1) ﹔ T₁: Ẇ B (Load ∔ ` 1) ﹔ end

different-locations-schedule : Schedule
different-locations-schedule = lock-scheduler input-txs-different-locations [] nothing nothing

-- The two transactions use disjoint locations. 
-- Therefore, there are no dependency between actions and they can be executed in any order.
-- The lock scheduler keep the order in which the evets have arrived.
-------------------------|
--| T₀ : RA      WA      |
--| T₁ :     RB      WB  |
-------------------------|
different-locations-schedule-eq : 
  different-locations-schedule ≡ T₀: Ṙ A ﹔ T₁: Ṙ B ﹔ T₀: Ẇ A (Load ∔ ` 1) ﹔ T₁: Ẇ B (Load ∔ ` 1) ﹔ end
different-locations-schedule-eq = refl

pcm-comm-R-W : ∀ e (s : Trace) → T₁: Ṙ B ∙ T₀: Ẇ A e ∙ s ≡ T₀: Ẇ A e ∙ T₁: Ṙ B ∙ s
pcm-comm-R-W e s = pcm-comm _ _ _ (#-neq-tr _ _ (λ x → znots (sym x)) (#ₐ-RW _ _ _ (≠-sym A≢B)))

-- Compute sequiential schedule and prove that it is trace-equivalent to the example schedule
different-locations-schedule-trace-equiv-sequential : 
  ⟦ different-locations-schedule ⟧ ≡ ⟦ SequentalScheduler.sequential-scheduler different-locations-schedule [] nothing ⟧
different-locations-schedule-trace-equiv-sequential = pcm-cong-head {s₁ = T₀: Ṙ A ∙ ε} (pcm-comm-R-W _ _)

-- Now, we use the fact that the sequiential scheduler produces serializable schedules to construct a proof that
-- our example scedule with different locations is serializable.
-- This way, we do not need to provide transactions to the serializability proof explicitly
different-locations-schedule-serialisable : serializable different-locations-schedule
different-locations-schedule-serialisable = 
  let s = SequentalScheduler.sequential-scheduler-serializable (SequentalScheduler.sequential-scheduler different-locations-schedule [] nothing) in
  let p = s .snd 
  in ((s .fst .fst) , (s .fst .snd)) , subst (λ x → x ≡ ⟦ SequentalScheduler.sequential-scheduler different-locations-schedule [] nothing ⟧) (sym different-locations-schedule-trace-equiv-sequential) p
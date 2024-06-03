import Init.Data.Nat.Basic

-- We start with a base type and an arrow type --
inductive typ : Type
  | base : typ
  | arrow : typ → typ → typ

-- Conveniance notations --
notation A"->"B => typ.arrow A B


-- We define terms in a recursive manner --
inductive term : Type
  | var : Nat → term            -- Each variables is identitifed by a natural number
  | abs : Nat → term → term     -- Lambda abstraction
  | app : term → term → term    -- Application

notation "$"n => term.var n

-- We define lists here to be able to embed the context as a list we no duplicates --
inductive list (T : Type): Type
  | nil : list T
  | append : (t : T) → (l : list T) → list T

notation "[]" => list.nil
notation t","l => list.append t l

inductive in_list (t : T) : list T → Prop
  | cons : (t = t₀) → in_list t (t₀ , l)

def not_in : T → list T → Prop :=
  λt => λl => ¬ (in_list t l)

inductive no_duplicates (T : Type) : list T → Prop
  | nil : no_duplicates T nil
  | head (t : T) (l : list T): not_in t l → no_duplicates T (t , l)

-- A context is a list of Natural number paired with a type that do not contain duplicates in names --
structure ctx_elem where
  name : Nat
  type : typ

notation "ctx" => list ctx_elem
-- Carefull, this is "\ :" and not just ":" in the following notation
notation n"∶"t => ctx_elem.mk n t

def ctx1 : ctx := (3∶typ.base) , []

example : no_duplicates ctx_elem ctx1 := by
  unfold ctx1
  apply no_duplicates.head
  unfold not_in
  intro p
  cases p


-- We define substitution of the term u for the variable named n in the term t --
def subst : Nat → term → term → term := by
  sorry

notation t"[" u "//" n"]" => subst n t u

-- Typing relation --
inductive TR : ctx → term → typ → Type
  | var :(n:Nat) → (T : typ) → TR ((n∶T) , []) ($ n) T
  | abs : (A B : typ) → (n:Nat) → (Γ : ctx ) → (t : term) → TR ((n∶A) , Γ) t B → TR Γ (term.abs n t) (A -> B)
  | app : (A B : typ) → (Γ : ctx) → (t₀ t₁ : term) →  TR Γ t₀ (A -> B) → TR Γ t₁ A → TR Γ (term.app t₀ t₁) B
  | sub : (A : typ) → (n:Nat) → (t u : term) → TR Γ t A → TR Γ (t[u // n]) A

notation Γ"⊢"t"∶∶"A => TR Γ t A
#check ctx1 ⊢ ($ 3) ∶∶ typ.base

example : ctx1 ⊢ ($ 3) ∶∶ typ.base := by
  apply TR.var

-- We define the beta reduction relation here --
inductive beta : term → term → Type
  | cons : beta (term.app (term.abs n t) u) (t[u // n])

-- We prove that betw reduction preserve the typing relation --
theorem beta_preservation : (A : typ) → (Γ ⊢ t ∶∶ A) → beta t t' → (Γ ⊢ t' ∶∶ A) := by
  intro A p b
  induction p
  case var n T => contradiction
  case abs B C n Γ₀ t₀ q₀ q₁  => sorry
  case app B C Γ₀ t₀ t₁ d₀ q₀ q₁ q₂ => sorry
  case sub B n t₀ u₀ d₀ q₀ q₁ => sorry

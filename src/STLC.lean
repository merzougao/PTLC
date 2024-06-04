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
  | abs : term → term → term    -- Lambda abstraction
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
  intros n t u
  cases t
  case var k => exact if k = n then u else $ k
  case abs x q =>
    cases x
    case var k => exact term.abs (subst n ($ k) u) (subst n q u)
    case abs t₀ t₁ => exact term.abs (term.abs t₀ t₁) q           -- Note that this case is not possible for well typed terms --
    case app t₀ t₁ => exact term.abs (term.app t₀ t₁) q           -- Note that this case is not possible for well typed terms --
  case app t₀ t₁ => exact term.app (subst n t₀ u) (subst n t₁ u)

notation t"[" u "//" n"]" => subst n t u

-- Typing relation --
inductive TR : ctx → term → typ → Type
  | var :(n:Nat) → (T : typ) → TR ((n∶T) , []) ($ n) T
  | abs : (A B : typ) → (n:Nat) → (Γ : ctx ) → (t : term) → TR ((n∶A) , Γ) t B → TR Γ (term.abs ($ n) t) (A -> B)
  | app : (A B : typ) → (Γ : ctx) → (t₀ t₁ : term) →  TR Γ t₀ (A -> B) → TR Γ t₁ A → TR Γ (term.app t₀ t₁) B
  | sub : (A : typ) → (n:Nat) → (t u : term) → TR Γ t A → TR Γ (t[u // n]) A

notation Γ"⊢"t"∶∶"A => TR Γ t A
#check ctx1 ⊢ ($ 3) ∶∶ typ.base

example : ctx1 ⊢ ($ 3) ∶∶ typ.base := by
  apply TR.var

-- We define the α equivalence here, two terms are equivalent up to renaming of the bound variables --
-- We start by defining variable swap --
def rename : Nat → term → term := by
  intros n t
  cases t
  case var m => exact $ m
  case abs k u => exact term.abs ($ n) (rename n u)
  case app u v => exact term.app (rename n u) (rename n v)

def var_swap : Nat → Nat → term → term := by
  intros n m t
  cases t
  case var k => exact if k = n then ($ m) else (if k = m then ($ n) else ($ k))
  case abs k u => exact term.abs (var_swap n m k) (var_swap n m u)
  case app u v => exact term.app (var_swap n m u) (var_swap n m v)

-- Now the α equivalence, it is an equivalence relation up to renaming bound variables in abstraction --
-- Note that this equivalence is weaker than the one we want because there is no well typed restriction here --

inductive αeq : term → term → Type
  | refl : αeq t t
  | trans : αeq t q → αeq q r → αeq t r
  | comm : αeq t q  → αeq q t
  | abs (n : Nat) (t : term) : αeq (term.abs ($ n) t) (rename n (term.abs ($ n) t))


-- Substitution preserves alpha equivalence --
theorem alpha_preservation : αeq t₀ t₁ → αeq (t₀ [ x // u ]) t₁ := by
  intro p
  sorry

-- We define the beta reduction relation here --
-- We first start with a one step reduction --
inductive β₁ : term → term → Type
  | cons (n : Nat) : β₁ (term.app (term.abs ($ n) t) u) (t[u // n])

-- Now we define the beta reduction relation to be transitive closure of beta₁ --
inductive  β : term → term → Type
  | id : β₁ t₀ t₁ → β t₀ t₁
  | cons : β₁ t₀ t₁ → β₁ t₁ t₂ → β t₀ t₂

-- We define now the beta equivalence relation to be the reflexive closure of beta --
inductive βeq : term → term → Type
  | id : β t₀ t₁ → βeq t₀ t₁
  | refl : βeq t₀ t₁ → βeq t₁ t₀


-- We prove that beta reduction preserve the typing relation --
theorem beta_preservation : (A : typ) → (Γ ⊢ t ∶∶ A) → βeq t t' → (Γ ⊢ t' ∶∶ A) := by
  intro A p b
  induction p
  case var n T => sorry
  case abs B C n Γ₀ t₀ q₀ q₁  => sorry
  case app B C Γ₀ t₀ t₁ d₀ q₀ q₁ q₂ => sorry
  case sub B n t₀ u₀ d₀ q₀ q₁ => sorry

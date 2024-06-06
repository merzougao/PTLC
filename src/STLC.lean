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

def print_term : term → String := by
  intro t
  cases t
  case var k => exact toString k
  case abs t₀ t₁ => exact "λ" ++ (print_term t₀)++"."++ (print_term t₁)
  case app u v => exact (print_term u) ++ "(" ++(print_term v)++")"


-- A context is a list of Natural number paired with a type that do not contain duplicates in names --
structure ctx_elem where
  name : Nat
  type : typ

-- Carefull, this is "\ :" and not just ":" in the following notation
notation n"∶"t => ctx_elem.mk n t

-- notation "ctx" => list ctx_elem
inductive ctx : Type
  | nil : ctx
  | append : ctx_elem → ctx → ctx

notation "[]" => ctx.nil
notation t","Γ => ctx.append t Γ

def ctx1 : ctx := (3∶typ.base) , []

inductive not_in : Nat → ctx → Prop
  | nil : not_in n []
  | cons : n ≠ m → not_in m Γ → not_in m ((n∶A) , Γ)

inductive valid_ctx : ctx → Prop
  | nil : valid_ctx []
  | cons : valid_ctx Γ → not_in n Γ → valid_ctx ((n∶A) , Γ)


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

inductive valid_ctx : ctx → Prop
  | var : valid_ctx ((x∶A) , [])
  | cons : valid_ctx Γ →

-- Weakening is admissible --
theorem weakening : (Γ ⊢ t ∶∶ A) → valid_ctx ((y∶B) , Γ) → (((y∶B) , Γ) ⊢ t ∶∶ A) := by
  sorry

-- We define the α equivalence here, two terms are equivalent up to renaming of the bound variables --

-- We start by defining variable swap --
def var_swap ( n m : Nat) : term → term := by
  intro t
  cases t
  case var k => exact if k = n then ($ m) else (if k = m then ($ n) else ($ k))
  case abs k u =>  exact term.abs (var_swap n m k) (var_swap n m u)
  case app u v => exact term.app (var_swap n m u) (var_swap n m v)

-- Now the α equivalence, it is an equivalence relation up to renaming bound variables in abstraction --
-- Note that this equivalence is weaker than the one we want because there is no well typed restriction here --

inductive αeq : term → term → Type
  | refl : αeq t t
  | trans : αeq t q → αeq q r → αeq t r
  | comm : αeq t q  → αeq q t
  | swap (n m : Nat) (t : term) : αeq t (var_swap n m t)

-- We define the beta reduction relation here --

-- Reduction of lambda abstraction applied to a term --
inductive βr : term → term → Type
  | cons : βr (term.app (term.abs ($ x) t) s) (t [ s // x ])

notation t "▸" q => βr t q

-- One step reduction --
inductive β₁ : term → term → Type
  | incl : (t ▸ q) → β₁ t q
  | app₁ : (t ▸ q) → β₁ (term.app t u) (term.app q u)
  | app₂ : (t ▸ q) → β₁ (term.app u t) (term.app u q)
  | abs : (t ▸ q) → β₁ (term.abs ($ x) t) (term.abs ($ x) q)

notation t "▸₁" q => β₁ t q

-- Arbitrary long reduction --
inductive β : term  → term → Type
  | incl : (t ▸ q) → β t q
  | trans : β t q → β q r → β t r

notation t "▸β" q => β t q

-- Beta equivalence adds commutativity and reflexivity --
inductive βeq : term → term → Type
  | refl : βeq t t
  | incl : (t ▸β q) → βeq t q
  | comm : βeq t q → βeq q t

notation t "≅β " q => βeq t q

-- We now show that beta equivalence preserve the typing relation --

theorem β_preservation : (t ≅β q) → (Γ ⊢ t ∶∶ A) → (Γ ⊢ q ∶∶ A) := by
  intros c p
  cases c
  case refl => assumption
  case incl p₀ =>
    cases p₀
    case incl p₁ =>
      cases p₁
      case cons n q₀ q₁ =>
        apply TR.sub
        cases q₀
        case a.var m => sorry
        case a.abs => sorry
        case a.app => sorry
    case trans => sorry
  case comm => sorry

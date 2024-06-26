import Init.Data.Nat.Basic
-- import Init.Data.List.Basic



-- We start with a base type and an arrow type --
inductive typ : Type
  | base : typ
  | arrow : typ → typ → typ

-- Conveniance notations --
notation A"->"B => typ.arrow A B

-- We define terms in a recursive manner --
inductive term : Type
  | var : Nat → term            -- Each variables is identitifed by a natural number
  | abs : Nat → term → term    -- Lambda abstraction
  | app : term → term → term    -- Application

notation:max "$"n => term.var n
notation:max "λ["x"]."t => term.abs x t
notation:max t₀"{"t₁"}" => term.app t₀ t₁

def print_term : term → String := by
  intro t
  cases t
  case var k => exact toString k
  case abs n t₁ => exact "λ" ++ toString n ++"."++ (print_term t₁)
  case app u v => exact (print_term u) ++ "(" ++(print_term v)++")"


-- A context is a list of Natural number paired with a type that do not contain duplicates in names --
structure ctx_elem where
  name : Nat
  type : typ


-- Carefull, this is "\ :" and not just ":" in the following notation
notation n"∶"t => ctx_elem.mk n t
@[simp]
theorem eq_ctx_elem : (c.name∶c.type) = c := rfl

-- notation "ctx" => List ctx_elem

inductive ctx : Type
  | nil : ctx
  | cons : ctx_elem → ctx → ctx



notation:max "[]" => ctx.nil
notation:max c"::"Γ => ctx.cons c Γ


def concat : ctx → ctx → ctx := by
  intro Γ Δ
  cases Γ
  case nil => exact Δ
  case cons c₀ Γ₀ => exact c₀ :: (concat Γ₀ Δ)
notation:max Γ"++"Δ => concat Γ Δ

@[simp]
theorem concat_empty_middle {Γ : ctx} {c : ctx_elem}: ((c :: []) ++ Γ) = (c :: Γ) := by rfl
@[simp]
theorem concat_empty_head {Γ : ctx}: ([] ++ Γ) = Γ := by rfl
@[simp]
theorem concat_empty_tail {Γ : ctx}: (Γ ++ []) = Γ := by
  induction Γ
  case nil => simp
  case cons c Γ₀ iH₀ =>
    have : ((c::Γ₀)++[]) = (c::(Γ₀++[])) := by rfl
    rw [this]
    rw [iH₀]

theorem concat_assoc_elem : ((c::Γ) ++ Δ) = (c ::(Γ ++ Δ)) := by rfl

theorem concat_assoc :(Γ Δ Λ : ctx) → (Γ ++ Δ ++ Λ) = ((Γ ++ Δ ) ++ Λ) := by
  intro Γ
  induction Γ
  case nil => simp
  case cons c₀ Γ₀ iH₀ =>
    intro Δ Λ
    have : ((c₀::Γ₀)++Δ++Λ) = (c₀::(Γ₀++Δ++Λ)) := concat_assoc_elem
    rw [this]
    have this₀ : (Γ₀++Δ++Λ) = (Γ₀++Δ)++Λ := iH₀ Δ Λ
    rw [this₀]
    rfl

theorem concat_assoc_full :(Δ₀ Γ Δ₁ Λ : ctx) → (Γ ++ Δ₀ ++ Δ₁ ++ Λ) = (Γ ++ (Δ₀ ++ Δ₁) ++ Λ) := by
  intro Δ₀
  induction Δ₀
  case nil =>
    intro Γ Δ₁ Λ
    simp
  case cons c₀ Δ₀₀ iH₀ =>
    intro Γ Δ₁ Λ
    have : ((c₀::Δ₀₀)++Δ₁++Λ) = (c₀::(Δ₀₀++Δ₁++Λ)) := concat_assoc_elem
    rw [this]
    sorry





inductive in_list : ctx_elem → ctx → Type
  | head : in_list c (c :: L)
  | tail : in_list c L₀ → in_list c (p :: L₀)
notation:max c"∈⋆"L => in_list c L
notation:max c"∉⋆"L => (in_list c L) → false

inductive subset : ctx → ctx → Type
  | cons {c : ctx_elem} : (c ∈⋆ Δ) → subset Γ Δ → subset (c :: Γ) Δ
notation:max Γ "⊆" Δ => subset Γ Δ

theorem subset_ex (Γ : ctx) (c₁ c₀ : ctx_elem) (Δ : ctx):
                    ((Γ ++ c₀ :: c₁ :: Δ) ⊆ Λ) → (Γ ++ c₁ :: c₀ :: Δ) ⊆ Λ := by
  intro H
  induction Γ
  case nil =>
    simp ; simp at H
    apply subset.cons
    case a => cases H ; case cons H₁ H₂ => cases H₂ ; assumption
    case a =>
      apply subset.cons
      case a => cases H ; assumption
      case a => cases H ; case cons H₁ H₂ => cases H₂ ; assumption
  case cons c Γ₀ iH₀ =>
    apply subset.cons
    case a => cases H ; assumption
    case a => apply iH₀ ; cases H ; case cons H₂ H₃ => assumption

/-  Inductive type inhabited whenever Γ : ctx is valid
    i.e does not contain any duplicates in the strong sense (context elements not just variable
    name )
-/
inductive valid : ctx → Type
  | nil : valid []
  | cons : valid Γ → (c ∉⋆ Γ) → valid c :: Γ

/-  Lemma for valid_comm
    Invert the constructor of valid context. Show that if c::Γ is a valid context,
    Then Γ was valid all along
-/
theorem valid_forget : valid (c :: Γ) → valid Γ := by
  intro H
  cases H
  assumption

/-  Lemma for valid_comm
    Invert the constructor of valid context. Show that if c::Γ is a valid context,
    Then c is not present in Γ
-/
theorem no_dup_in_valid_ctx : valid (c :: Γ) → c ∉⋆ Γ := by
  intro H₀
  cases H₀
  assumption

/-  Lemma for valid_comm
    Show that if an element c is in a context Γ then it remains there whenever we permute
    entries in Γ
-/
theorem in_ctx_comm : (c ∈⋆ (Γ ++ c₀ :: c₁ :: Δ)) → c ∈⋆ (Γ ++ c₁ :: c₀ :: Δ) := by
  intro H
  induction Γ
  case nil =>
    simp ; simp at H
    cases H
    case head => exact in_list.tail in_list.head
    case tail H₁ =>
      cases H₁
      case head => apply in_list.head
      case tail H₂ => exact in_list.tail (in_list.tail H₂)
  case cons c₂ Γ₀ iH₀ =>
    cases H
    case head => apply in_list.head
    case tail H₂ => exact in_list.tail (iH₀ H₂)


/-  Show that a context remains valid when an exchange is performed.
    This amount to show that if a context has no duplicates, then permuting two elements
    preserves this property
-/
theorem valid_comm {Γ : ctx} {c₁ c₀ : ctx_elem} {Δ : ctx}:
                    valid (Γ ++ c₀ :: c₁ :: Δ) → valid (Γ ++ c₁ :: c₀ :: Δ) := by
  intro H
  induction Γ
  case nil =>
    simp at H ; simp
    apply valid.cons
    case a =>
      cases H
      case cons H₁ H₂ =>
        apply valid.cons
        case a => exact valid_forget H₁
        case a =>
          intro H₃
          exact H₂ (in_list.tail H₃)
    case a =>
      intro H₁
      cases H₁
      case head =>
        cases H
        case cons H₂ H₃ => exact H₃ in_list.head
      case tail H₂ => exact (no_dup_in_valid_ctx (valid_forget H)) H₂
  case cons c₂ Γ₀ iH₀ =>
    apply valid.cons
    exact iH₀ (valid_forget H)
    intro H₁ ; exact (no_dup_in_valid_ctx H) (in_ctx_comm H₁)





def fresh_var : term → Nat := by
  intro t
  cases t
  case var k => exact k + 1
  case abs n₀ t₀ => exact n₀ + fresh_var t₀ + 1
  case app t₀ t₁ => exact fresh_var t₀ + fresh_var t₁

@[simp]
theorem fresh_var_var_case: fresh_var ($ n) = n + 1 := rfl

inductive in_context : Nat → ctx → Prop
  | init (n : Nat) (c : ctx_elem) (Γ : ctx) : n = c.name → in_context n (c :: Γ)
  | next (n : Nat) (t : ctx_elem) (Γ : ctx) : in_context n Γ → in_context n (t :: Γ)

notation c"∈ₚ"Γ => in_context c Γ
notation c"∉ₚ"Γ => ¬ in_context c Γ

-- Swap natural numbers --
def swap_nats ( n m : Nat) : Nat → Nat := by
  intro k
  exact if k = n then m else (if k = m then n else k)

-- We start by defining variable swap --
def var_swap ( n m : Nat) : term → term := by
  intro t
  cases t
  case var k => exact if k = n then ($ m) else (if k = m then ($ n) else ($ k))
  case abs k u =>  exact λ[swap_nats n m k].(var_swap n m u)
  case app u v => exact (var_swap n m u){var_swap n m v}

def rename : Nat → term → term := λ n => λ t => var_swap n (fresh_var t) t

def t₀ : term := λ[0].($ 0){$ 1}
#eval print_term (rename 0 t₀)

def fv : term → List Nat := by
  intro t
  cases t
  case var k => exact [k]
  case abs n₀ t₀ => exact List.erase (fv t₀) n₀
  case app t₀ t₁ => exact List.append (fv t₀) (fv t₁)

-- We define substitution of the term u for the variable named n in the term t --
def subst : Nat → term → term → term := by
  intros n t u
  cases t
  case var k => exact if k = n then u else $ k
  case abs x q => exact if (x ∉ (fv u)) ∧ x ≠ n then λ[x].(subst n q u) else λ[x].q
  case app t₀ t₁ => exact (subst n t₀ u){subst n t₁ u}

notation t"[" u "//" n"]" => subst n t u

-- Typing relation --
inductive TR : ctx → term → typ → Type
  | var : (valid (n∶T) :: Γ) → TR ((n∶T) :: Γ) ($ n) T
  | ex (Γ : ctx) (y x : Nat) (Δ : ctx) : TR (Γ ++ (x∶A) :: (y∶B) :: Δ) t C →  TR (Γ ++ (y∶B) :: (x∶A) :: Δ) t C
  | abs : (A B : typ) → (n:Nat) → (Γ : ctx ) → (t : term) → TR ((n∶A) :: Γ) t B → TR Γ (λ[n].t) (A -> B)
  | app : (A B : typ) → (Γ : ctx) → (t₀ t₁ : term) →  TR Γ t₀ (A -> B) → TR Γ t₁ A → TR Γ t₀{t₁} B

notation Γ"⊢"t"∶∶"A => TR Γ t A




theorem app_type_inference :      (Γ ⊢ v ∶∶ A)
                                → (t₀ t₁ : term)
                                → (v = t₀{t₁})
                                → (Σ B Γ' , Γ' ⊢ t₀ ∶∶ B -> A) := by
  intro d₀
  induction d₀
  case app A₀ B₀ Γ' t₃ t₄ iH₂ iH₃ iH₄ iH₅=>
    intro t₀ t₁ p
    injection p with H₀ H₁
    rw [H₀] at iH₂
    exact Sigma.mk A₀ (Sigma.mk Γ' iH₂)
  <;> intros <;> contradiction

/-  This Lemma proves that if an element is in a valid context, then the deduction remain
    unchanged when we swap the element with a subcontext, ie Δ,c,Γ,Λ ⊢ t iff Δ,Γ,c,Λ ⊢ t
    This is needed to prove the more general statement that any two subcontext commute
-/
theorem ctx_elem_ex :   (Γ Δ Λ : ctx) → (c : ctx_elem)
                        → ((Δ ++ (c::(Γ ++ Λ))) ⊢ t ∶∶ A) → (Δ ++ Γ ++ c :: Λ) ⊢ t ∶∶ A := by
  intro Γ
  induction Γ
  case nil =>
    intro Δ Λ c H
    assumption
  case cons c₀ Γ₀ iH₀ =>
    intro Δ Λ c H
    -- We need to take care of the associativity of the context before apply the IH
    have this₀: ((c₀::[])++Γ₀++c::Λ) = ((c₀::Γ₀)++c::Λ) := by apply concat_empty_middle
    have this : (Δ++(c₀::Γ₀)++c::Λ) = ((Δ++c₀::[])++Γ₀++c::Λ) := by
      rw[←this₀]
      apply concat_assoc
    rw [this]
    -- Induction Hypothesis
    apply iH₀ (Δ++ c₀::[]) Λ c
    -- We need to use the exchange deduction rule here
    have this₁ : (Δ++((c₀::[])++c::Γ₀++Λ)) = ((Δ++c₀::[])++c::Γ₀++Λ) := by apply concat_assoc
    rw [←this₁]
    apply TR.ex Δ c₀.name c.name (Γ₀++Λ)
    exact H

theorem ctx_ex : (Δ₀ Δ₁ Γ Λ : ctx) → ((Γ ++ Δ₀ ++ Δ₁ ++ Λ) ⊢ t ∶∶ A) → ((Γ ++ Δ₁ ++ Δ₀ ++ Λ) ⊢ t ∶∶ A) := by
  intro Δ₀
  induction Δ₀
  case nil =>
    intro Δ₁ Γ Λ H
    assumption
  case cons c₀ Δ₀₀ iH₀ =>
    intro Δ₁ Γ Λ H
    have this₀ : (c₀::[]++Δ₀₀++Λ) = ((c₀::Δ₀₀)++Λ) := by
      apply concat_assoc (c₀::[]) Δ₀₀ Λ
    rw [←this₀]
    have this₁ : (Γ++(Δ₁++c₀::[])++Δ₀₀++Λ)⊢t∶∶A := by
      apply iH₀ (Δ₁++c₀::[]) Γ Λ
      have this₂ :   (Γ++Δ₀₀++(Δ₁++c₀::[])++Λ)= (Γ++Δ₀₀)++(Δ₁++c₀::[])++Λ := by sorry
      have this₃ : ((Γ++Δ₀₀)++(Δ₁++c₀::[])++Λ) = ((Γ++Δ₀₀)++Δ₁++c₀::[]++Λ) := by sorry
      rw [this₂]
      rw [this₃]
      apply ctx_elem_ex Δ₁ (Γ ++ Δ₀₀) Λ c₀
      have this₄ : ((Γ++Δ₀₀)++c₀::Δ₁++Λ) = (Γ++Δ₀₀++c₀::Δ₁++Λ) := by sorry
      rw [this₄]
      apply ctx_elem_ex Δ₀₀ Γ (Δ₁++Λ) c₀
      have this₅ : (Γ++c₀::Δ₀₀++Δ₁++Λ) = (Γ++(c₀::Δ₀₀)++Δ₁++Λ) := by sorry
      rw [this₅]
      exact H
    have this₆ : (Γ++(Δ₁++c₀::[])++Δ₀₀++Λ) = (Γ++Δ₁++c₀::Δ₀₀++Λ) := by sorry
    simp
    rw[← this₆]
    exact this₁












-- Weakening is admissible --
theorem weakening_is_admissible : (Γ ⊢ t ∶∶ A) → valid Δ → (Γ ⊆ Δ) → (Δ ⊢ t ∶∶ A) := by
  intro H₀ v H₁
  induction H₀
  case var n₀ A₀ Γ₀ H₂ =>
    induction Δ
    case nil => contradiction
    case cons c Γ₁ iH₀ =>
      cases H₁
      case cons H₃ H₄ =>
        cases H₃
        case head =>
          apply TR.var
          exact v
        case tail H₅ =>
          induction H₅
          case head Γ₁ =>
            apply TR.ex [] c.name n₀ Γ₁
            apply TR.var
            simp
            apply @valid_comm [] (n₀∶A₀) c Γ₁
            exact v
          case tail Γ₂ c₁ H₆ iH₁ =>
            sorry

  case ex A₀ B₀ t₀ C₀ Γ₀ n₀ n₁ Δ₀ H₂ iH₀ =>
    apply iH₀
    induction Γ₀
    case nil => apply subset_ex [] (n₁∶A₀) (n₀∶B₀) Δ₀ H₁
    case cons c₀ Γ₀ iH₁ => apply subset_ex ; exact H₁
  case abs A₀ B₀ n₀ Γ₀ t₀ H₂ iH₀ =>
    apply TR.abs
    sorry

  case app A₀ B₀ Γ₀ t₀ t₁ H₂ H₃ iH₀ iH₁ =>
    apply TR.app
    case A => exact A₀
    case a => exact iH₀ H₁
    case a => exact iH₁ H₁













-- We define the α equivalence here, two terms are equivalent up to renaming of the bound variables --



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
  | cons : βr (λ[x].t){s} (t [ s // x ])

notation:max t "▸" q => βr t q

theorem β_preservation₀ : (Γ ⊢ t ∶∶ A) → (q : term) → (t ▸ q) → (Γ ⊢ q ∶∶ A) := by
  intro d
  induction d
  case var n₀ A₀ =>
    intro t₀ H₀
    contradiction
  case abs A₀ B₀ n₀ Γ₀ t₀ iH₀ iH₁ =>
    intro q H₀
    contradiction
  case app A₀ B₀ Γ₀ t₀ t₁ d₀ d₁ iH₀ iH₁ =>
    intro q H₀
    sorry


-- One step reduction --
inductive β₁ : term → term → Type
  | incl : (t ▸ q) → β₁ t q
  | app₁ : β₁ t  q → β₁ t{u} q{u}
  | app₂ : β₁ t  q → β₁ u{t} u{q}
  | abs : β₁ t  q → β₁ (λ[x].t) (λ[x].q)

notation:max t "▸₁" q => β₁ t q


theorem β_preservation₁ : (Γ ⊢ t ∶∶ A) → (q : term) → (t ▸₁ q) → (Γ ⊢ q ∶∶ A) := by
  intro H₀ q H₁
  induction H₁
  case incl t₀ t₁ iH₀ => exact β_preservation₀ H₀ t₁ iH₀
  case app₁ t₀ q₀ u₀ H₂ iH₀ => sorry









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


theorem β₁_preservation : (t ▸₁ q)
                          → (Σ A Γ , (Γ ⊢ t ∶∶ A))
                          → (Σ Δ , (Δ ⊢ q ∶∶ A)) := by
  intro c p
  induction c
  case incl t₀ t₁ p₀ =>
    cases p₀
    case cons n₀ q₀ q₁ =>
      apply Sigma.mk
      case fst => exact (n₀ ∶ p.fst) , p.snd.fst
      case snd =>

      case a => sorry -- Inversion of abs
  case app₁ t₀ t₁ t₂ p₀ iH₀ =>

  case app₂ => sorry
  case abs => sorry



theorem β₂_preservation : (t ▸β q) → (Γ ⊢ t ∶∶ A) → (Γ ⊢ q ∶∶ A) := by
  intro c p
  induction c
  case incl t₀ t₁ iH => sorry -- exact β₁_preservation
  case trans t₀ t₁ t₂ iH₀ iH₁ iH₂ iH₃=>
    apply iH₃
    apply iH₂
    assumption


-- The full beta reduction preservation theorem --
theorem β_preservation : (t ≅β q) → (Γ ⊢ t ∶∶ A) → (Γ ⊢ q ∶∶ A) := by
  intros c p
  induction c
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
  case comm  r₀ r₁ iH₀ iH₁ => sorry

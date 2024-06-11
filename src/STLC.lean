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

def fresh_var : ctx → Nat := by
  intro Γ
  cases Γ
  case nil => exact 0
  case append elem Γ => exact elem.name + 1 + fresh_var Γ

inductive in_context : Nat → ctx → Prop
  | init (n : Nat) (c : ctx_elem) (Γ : ctx) : n = c.name → in_context n (c , Γ)
  | next (n : Nat) (t : ctx_elem) (Γ : ctx) : in_context n Γ → in_context n (t , Γ)

-- Count the number of elements in the context sharing the same name --
inductive count : Nat → Nat → ctx → Prop
  | nil   (c : Nat) : count 0 c []
  | next_yes  : count n m Γ → m = c.name → count (n+1) m (c ,Γ)
  | next_no  :  count n m Γ → m ≠ c.name → count n m (c ,Γ)

notation c"∈"Γ => in_context c Γ
notation c"∉"Γ => ¬ in_context c Γ

example : count 0 3 [] := by apply count.nil
example : count 1 3 ((3∶typ.base) , []) := by
  apply count.next_yes
  apply count.nil
  rfl
example : count 1 3 ((4∶typ.base) , ((3∶typ.base) , [])) := by
  apply count.next_no
  case a =>
    apply count.next_yes
    apply count.nil
    rfl
  case a =>
    intro p
    contradiction
example : 3 ∈ ((3∶typ.base) , []) := by
  apply in_context.init 3
  rfl


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
  | var : (n:Nat) → (T : typ) → TR ((n∶T) , []) ($ n) T
  | weak : TR Γ t T → TR (((fresh_var Γ)∶T₀) , Γ) t T
  | abs : (A B : typ) → (n:Nat) → (Γ : ctx ) → (t : term) → TR ((n∶A) , Γ) t B → TR Γ (term.abs ($ n) t) (A -> B)
  | app : (A B : typ) → (Γ : ctx) → (t₀ t₁ : term) →  TR Γ t₀ (A -> B) → TR Γ t₁ A → TR Γ (term.app t₀ t₁) B
  | sub : (A : typ) → (n:Nat) → (t u : term) → TR Γ t A → TR Γ (t[u // n]) A

notation Γ"⊢"t"∶∶"A => TR Γ t A

theorem fresh_var_not_in_ctx (v : Nat) (Γ : ctx): (v = fresh_var Γ) → v ∉ Γ := by
  intro h₀ h₁
  induction h₁
  case init n₁ Γ₁ p =>
    have this : fresh_var (n₁ , Γ₁) = n₁.name + 1 + (fresh_var Γ₁) := by rfl
    rw [p] at this
    have this₁ : 1 + fresh_var Γ₁ = 0 := by
      apply @Nat.add_left_cancel n₁.name (1 + fresh_var Γ₁) 0
      simp
      rw [← Nat.add_assoc n₁.name 1 (fresh_var Γ₁)]
      assumption
    have this₂ : 1 = 0 ∧ (fresh_var Γ₁) = 0 := by
      apply (@Nat.add_eq_zero_iff 1 (fresh_var Γ₁)).mp this₁
    apply Nat.succ_ne_zero 0
    apply this₂.left
  case next n₁ Γ₁ p iH₁ => sorry
theorem in_compositve_ctx (c n : Nat) : (c ∈ ((n∶T) , Γ)) → (c = n) ∨ (c ∈ Γ) := by
  intro p
  cases p
  case init H =>
    apply Or.intro_left
    exact H
  case next H =>
    apply Or.intro_right
    exact H
theorem not_in_count (n : Nat ) ( Γ : ctx ) : (n ∉ Γ) → (count 0 n Γ) := by
  intro d₀
  induction Γ
  case nil =>
    apply count.nil
  case append c₀ Γ₀ iH₀ =>
    have : n ≠ c₀.name := by
      intro p
      apply d₀
      apply in_context.init
      assumption
    have this₀ : n ∉ Γ₀ := by
      intro p
      apply d₀
      apply in_context.next
      assumption
    have this₁ : count 0 n Γ₀ := iH₀ this₀
    apply count.next_no
    assumption
    assumption
theorem in_extended_ctx (n : Nat) (Γ : ctx) (c : ctx_elem): (n ∈ Γ) → (n ∈ (c , Γ)) := by
  sorry

-- The contexts are valid under the typing rules --
theorem no_duplicates_in_ctx :    (c : ctx_elem)
                                → (Γ : ctx)
                                → (c.name ∈ Γ)
                                → (Γ ⊢ t ∶∶ A)
                                → (count 1 c.name Γ) := by
  intros c Γ p d
  induction d
  case var n T =>
    apply count.next_yes
    apply count.nil
    cases p
    case a.init m => exact m
    case a.next q₀  => contradiction
  case weak Γ₀ t₀ T₀ T₁ iH₀ iH₁ =>
    have this₀ :  (c.name = (fresh_var Γ₀)) ∨ (c.name ∈ Γ₀) := in_compositve_ctx c.name (fresh_var Γ₀) p
    apply Or.elim this₀
    case left =>
      intro d₀
      apply count.next_yes
      have this₁ : c.name ∉ Γ₀ := fresh_var_not_in_ctx c.name Γ₀ d₀
      apply not_in_count
      assumption
      rw [d₀]
    case right =>
      intro d₀
      apply count.next_no
      case a => exact iH₁ d₀
      case a =>
        intro p₀
        apply fresh_var_not_in_ctx c.name Γ₀
        simp at p₀
        assumption
        assumption
  case abs A₀ B₀ n₀ Γ₀ t₀ iH₀ iH₁ =>
    have this₀ : (c.name∈(n₀∶A₀),Γ₀) := by
      apply in_context.next
      assumption
    have this₁ : count 1 c.name ((n₀∶A₀),Γ₀) := iH₁ this₀
    cases this₁
    case next_yes K₀ K₁ =>
      cases K₁
      case nil => contradiction
      case next_no Γ₂ m₁ Γ₁ iH₂=> sorry
    case next_no K₀ K₁ =>
      assumption
  case app A₀ B₀ Γ₀ t₀ t₁ iH₁ iH₂ iH₃ iH₄ =>
    apply iH₃
    assumption
  case sub Γ₀ A₀ n₀ t₀ t₁ iH₁ iH₂ =>
    apply iH₂
    assumption


-- Weakening is admissible --
-- theorem weakening :


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

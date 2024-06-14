import Init.Data.Nat.Basic
import Init.Data.List.Basic


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

-- notation "ctx" => list ctx_elem
inductive ctx : Type
  | nil : ctx
  | append : ctx_elem → ctx → ctx

notation "[]" => ctx.nil
notation t","Γ => ctx.append t Γ

def fresh_var : term → Nat := by
  intro t
  cases t
  case var k => exact k + 1
  case abs n₀ t₀ => exact n₀ + fresh_var t₀ + 1
  case app t₀ t₁ => exact fresh_var t₀ + fresh_var t₁

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
  | var : (n:Nat) → (T : typ) → TR ((n∶T) , []) ($ n) T
  | weak (T₀ : typ) : TR Γ t T → TR (((fresh_var t)∶T₀) , Γ) t T
  | abs : (A B : typ) → (n:Nat) → (Γ : ctx ) → (t : term) → TR ((n∶A) , Γ) t B → TR Γ (λ[n].t) (A -> B)
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
  case weak Γ₀ t₂ A₀ A₁ iH₁ iH₂ => exact iH₂
  case  var => sorry
  case abs => sorry

theorem abs_app_type_inference : (Γ ⊢ t{s} ∶∶ A) → (x t' : term) → (t = (λ[x].t')) → (Σ Γ' , Γ' ⊢ t' ∶∶ A) := by
  intro d
  have : (Σ P Γ' , (Γ' ⊢ t ∶∶ P)) := app_type_inference d t s rfl
  intro x t' p
  apply Sigma.mk
  case fst => exact Γ
  case snd =>
    cases this.snd.snd
  sorry

-- the fresh_var function always return a variable that is not present in the context --
theorem fresh_var_not_in_ctx (Γ : ctx) : (fresh_var Γ) ∉ Γ := by
  intro p
  induction Γ
  case nil => contradiction
  case append c₀ Γ₀ iH =>
    cases p
    case init r =>
      simp at r
      have this₀ : 1 + fresh_var Γ₀ = 0 := by
        apply @Nat.add_left_cancel c₀.name (1 + fresh_var Γ₀) 0
        simp
        rw [← Nat.add_assoc c₀.name 1 (fresh_var Γ₀)]
        assumption
      have this₂ : 1 = 0 ∧ (fresh_var Γ₀) = 0 := by
        apply (@Nat.add_eq_zero_iff 1 (fresh_var Γ₀)).mp this₀
      apply Nat.succ_ne_zero 0
      apply this₂.left
    case next r => sorry


theorem in_compositve_ctx (c n : Nat) : (c ∈ ((n∶T) , Γ)) → (c = n) ∨ (c ∈ Γ) := by
  intro p
  cases p
  case init H =>
    apply Or.intro_left
    exact H
  case next H =>
    apply Or.intro_right
    exact H

theorem not_to_count (n : Nat ) ( Γ : ctx ) : (n ∉ Γ) → (count 0 n Γ) := by
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

theorem count_to_not (k n : Nat) (Γ : ctx): (count k n Γ) → (k = 0) → (n ∉ Γ) := by
  intro d d₀
  induction d
  case nil =>
    intro p
    contradiction
  case next_no k₀ k₁ Γ₀ c₀ _ H₁ H₂ =>
    intro p
    cases p
    case init H₃ => contradiction
    case next H₃ =>
      have : ¬ k₁ ∈ Γ₀ := H₂ d₀
      exact this H₃
  case next_yes k₀ k₁ Γ₀ c₀ _ _ _ =>
    intro
    have this₂ : k₀ = 0 ∧ 1 = 0 := (@Nat.add_eq_zero_iff k₀ 1).mp d₀
    apply Nat.succ_ne_zero 0
    apply this₂.right

theorem in_extended_ctx (n : Nat) (Γ : ctx) (c : ctx_elem): (n ∈ Γ) → (n ∈ (c , Γ)) := by
  intro p
  apply in_context.next
  assumption

-- The contexts are valid under the typing rules --
theorem no_duplicates_in_ctx :    (c : ctx_elem)
                                → (Γ : ctx)
                                → (c.name ∈ Γ)
                                → (Γ ⊢ t ∶∶ A)
                                → (count 1 c.name Γ) := by
  intros c Γ p d
  induction d
  case var n T =>
    apply count.next_yes ; apply count.nil
    cases p
    case a.init m => exact m
    case a.next q₀  => contradiction
  case weak Γ₀ _ _ T₁ _ iH₁ =>
    have this₀ :  (c.name = (fresh_var Γ₀)) ∨ (c.name ∈ Γ₀) := in_compositve_ctx c.name (fresh_var Γ₀) p
    apply Or.elim this₀
    case left =>
      intro d₀
      apply count.next_yes
      have this₂ : (fresh_var Γ₀) ∉ Γ₀ := fresh_var_not_in_ctx Γ₀
      apply not_to_count
      rw [←d₀] at this₂
      assumption
      rw [d₀]
    case right =>
      intro d₀
      apply count.next_no
      case a => exact iH₁ d₀
      case a =>
        intro p₀
        apply fresh_var_not_in_ctx Γ₀
        simp at p₀
        rw [p₀] at d₀
        assumption
  case abs A₀ _ n₀ Γ₀ _ _ iH₁ =>
    have this₀ : (c.name∈(n₀∶A₀),Γ₀) :=  in_context.next c.name (n₀∶A₀) Γ₀ p
    have this₁ : count 1 c.name ((n₀∶A₀),Γ₀) := iH₁ this₀
    cases this₁
    case next_yes K₀ K₁ =>
      have this₂ : c.name ∉ Γ₀ := count_to_not 0 c.name Γ₀ K₁ rfl
      contradiction
    case next_no K₀ K₁ => assumption
  case app _ B₀ _ _ _ _ _ iH₃ => exact iH₃ p
  case sub Γ₀ _ _ _ _ _ iH₂ => exact iH₂ p


-- Weakening is admissible --
-- theorem weakening :


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
  | cons : βr (λ[$ x].t){s} (t [ s // x ])

notation t "▸" q => βr t q

-- One step reduction --
inductive β₁ : term → term → Type
  | incl : (t ▸ q) → β₁ t q
  | app₁ : β₁ t  q → β₁ t{u} q{u}
  | app₂ : β₁ t  q → β₁ u{t} u{q}
  | abs : β₁ t  q → β₁ (λ[$ x].t) (λ[$ x].q)

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

theorem uniqueness_of_types : (Γ ⊢ t ∶∶ A) → (Γ ⊢ t ∶∶ B) → (A = B) := by
  intro d₀ d₁
  induction d₀
  case var n₀ A₀ => sorry
  sorry
theorem types_from_app : (v = t₀{t₁}) →  (Γ ⊢ v ∶∶ B) → (Γ ⊢ t₁ ∶∶ A) → (Γ ⊢ t₀ ∶∶ A -> B) := by
  intro p d₀ d₁
  induction d₀
  case var n => contradiction
  case weak Γ₀ t₃ A₀ B₀ iH₃ iH₄ =>
    apply TR.weak
    apply iH₄
    exact p
  case abs A₀ B₀ n₀ Γ₀ t₃ iH₁ iH₂ =>
    contradiction
  case app A₀ B₀ Γ₀ t₃ t₄ iH₂ iH₃ iH₄ iH₅ =>
    injection p with h₁ h₂
    rw [h₂] at iH₃
    have : A = A₀ := uniqueness_of_types d₁ iH₃
    rw [this]
    rw [h₁] at iH₂
    assumption
  case sub Γ₀ A₀ t₃ t₄ t₅ iH₂ iH₃ => sorry


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

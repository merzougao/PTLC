import Init.Data.Nat.Basic

--Presorts--
-- Those are lists of natural numbers
inductive pre_sort : Type
  | nil : pre_sort
  | append : (n : nat) → (l: pre_sort) → pre_sort

-- Lists --
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

-- Some test for lists of integers --
---------------------------------------------------------
def list₀ : list Nat := (0 , (1 , []))

-- Proof that there is no duplicates in list₀ --
example : no_duplicates Nat list₀ := by
  unfold list₀
  apply no_duplicates.head
  unfold not_in
  intro p
  cases p
  case a.cons r =>
    injection r

--------------------------------------------------------

structure Dep (l : list T) where
  src : T
  dest : T

def well_formed_dep : Dep l → Prop := λd => (in_list d.src l) ∧ (in_list d.dest l)

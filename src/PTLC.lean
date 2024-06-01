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

inductive not_in (t : T) : list T → Prop
  | nil : not_in t []
  | next : (t ≠ t₀) → not_in t l → not_in t (t₀ , l)

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
  apply not_in.next
  simp
  apply not_in.nil
--------------------------------------------------------

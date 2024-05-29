-- Definition of the lambda cube --

-- Nat --
inductive nat : Type
  | zero : nat
  | succ : nat → nat

--Sorts--
inductive sort : Type
  | nil : sort
  | append : sort → sort → sort
  | ▵ : Type

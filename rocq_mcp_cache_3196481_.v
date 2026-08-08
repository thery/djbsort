From mathcomp Require Import all_boot order perm.
Section T.
Variable m : nat.
Definition oord (i : nat) : option 'I_m :=
  (if i < m as b return (i < m) = b -> option 'I_m
   then fun E => Some (Ordinal E) else fun _ => None) (erefl (i < m)).

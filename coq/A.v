From Here Require Import Sub.
From Stdlib Require Import Lia.
Print imported.

Locate Here.Sub.T.



Definition m := 0.


Module Import notations M <: T.
  Definition n := m.
End M.


Module Import N := M.

Import M.

Goal bob = 0.
unfold n. unfold m. exact eq_refl.


















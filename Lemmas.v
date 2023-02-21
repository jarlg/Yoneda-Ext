From HoTT Require Import Basics Types Pointed ExactSequence.

Definition isexact_homotopic_if n {F X Y : pType}
  {i i' : F ->* X} (h : i' ==* i)
  {f f' : X ->* Y} (k : f' ==* f)
  `{IsExact n F X Y i f}
  : IsExact n i' f'.
Proof.
  refine (isexact_homotopic_i n h _).
  exact (isexact_homotopic_f n _ k).
Defined.

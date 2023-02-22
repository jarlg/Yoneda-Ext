From HoTT Require Import Basics Types Pointed WildCat
  ExactSequence AbGroups AbSES.

(** This should be placed in Homotopy.ExactSequence. *)
Definition isexact_homotopic_if n {F X Y : pType}
  {i i' : F ->* X} (h : i' ==* i)
  {f f' : X ->* Y} (k : f' ==* f)
  `{IsExact n F X Y i f}
  : IsExact n i' f'.
Proof.
  refine (isexact_homotopic_i n h _).
  exact (isexact_homotopic_f n _ k).
Defined.

(** This should be placed in AbSES.Pullback. *)
Definition abses_pullback_trivial_factors_projection `{Univalence}
  {B B' A : AbGroup} {g : B' $-> B} {E : AbSES B A}
  : pt = abses_pullback g E -> exists phi, g = projection E $o phi.
Proof.
  equiv_intros (equiv_path_abses (E:=pt) (F:=abses_pullback g E)) p.
  destruct p as [phi [p q]].
  exists (grp_pullback_pr1 _ _ $o phi $o ab_biprod_inr).
  apply equiv_path_grouphomomorphism; intro b'; symmetry.
  refine (right_square (abses_pullback_morphism E g) _ @ _).
  exact (ap g (q _)^).
Defined.

From HoTT Require Import Basics Types Pointed HSet HFiber Truncations
  Limits.Pullback WildCat AbGroups AbSES Homotopy.ExactSequence.

(** * The six-term exact sequences related to Ext *)

(** The contravariant case has been merged into AbSES.SixTerm. *)

(** ** The covariant case *)

(** Place in AbSES.Pullback or AbSES.SixTerm. *)
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

(** Towards exactness of [Hom G B -> Ext1 G A -> Ext1 G E]. *)
Definition isexact_ext_cov_sixterm_iv `{Univalence}
  {B A G : AbGroup} (E : AbSES B A)
  (F : AbSES G A) (p : abses_pushout (inclusion E) F = pt)
  : G $-> B.
Proof.
  (* we start by assuming that [G] is literally the cokernel of [inclusion F] *)
  pose (phi := equiv_path_abgroup
                 (abses_cokernel_iso (inclusion F) (projection F))).
  induction phi.
  (* now we can easily construct a map out of the cokernel *)
  apply equiv_quotient_abgroup_ump.
  pose (p' := equiv_path_abses^-1 p);
    destruct p' as [p' [pl pr]].
  exists (projection E $o ab_biprod_pr1 $o p' $o ab_pushout_inr).
  (* since we're proving a proposition, we may choose an actual preimage *)
  intros f; apply Trunc_rec; intros [a []]; clear f.
  refine (ap (projection E o ab_biprod_pr1 o p') _ @ _).
  1: exact (left_square (abses_pushout_morphism F _) a)^.
  refine (ap (projection E o ab_biprod_pr1) (pl _) @ _); cbn.
  apply isexact_inclusion_projection.
Defined.

Definition abses_sixterm3 `{Univalence} {A B C: AbGroup}
  (E : AbSES C B)
  : IsExact (Tr (-1))
      (abses_pushout_ext E)
      (fmap (pTr 0) (abses_pullback_pmap (A:=A) (projection E))).
Abort.


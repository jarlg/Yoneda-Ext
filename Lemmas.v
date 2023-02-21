From HoTT Require Import Basics Types Pointed WildCat
  ExactSequence AbGroups AbSES.

(* Place in Homotopy.ExactSequence. *)
Definition isexact_homotopic_if n {F X Y : pType}
  {i i' : F ->* X} (h : i' ==* i)
  {f f' : X ->* Y} (k : f' ==* f)
  `{IsExact n F X Y i f}
  : IsExact n i' f'.
Proof.
  refine (isexact_homotopic_i n h _).
  exact (isexact_homotopic_f n _ k).
Defined.

(* Place in AbSES.Pullback. *)
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

(** ** [loops_abses] is a group isomorphism *)

(** The functorial action of [abses_pullback_pmap] on loops. *)
Definition abses_loops_pullback_data `{Univalence} {B B' A : AbGroup} (g : B $-> B')
  : forall p, fmap loops (abses_pullback_pmap (A:=A) g) p
         = equiv_path_abses_iso
             ((abses_pullback_point' g)^$
                $@ (fmap (abses_pullback g) (equiv_path_abses_iso^-1 p)
                      $@ abses_pullback_point' g)).
Proof.
  intro p.
  refine (_ @ abses_path_data_compose_beta _ _).
  refine (_ @ ap011 _ (abses_path_data_V _) (abses_path_data_compose_beta _ _)).
  apply whiskerL.
  apply whiskerR.
  apply ap_abses_pullback.
Defined.

(** Loop spaces of a 1-truncated type are automatically groups. *)
Definition loops_1trunc (X : pType) `{IsTrunc 1 X} : Group.
Proof.
  nrefine (Build_Group (loops X) concat idpath inverse _).
  nrapply Build_IsGroup; repeat split.
  - by apply istrunc_paths.
  - rapply concat_p_pp.
  - rapply concat_1p.
  - rapply concat_p1.
  - rapply concat_Vp.
  - rapply concat_pV.
Defined.

Definition iso_loops_abses `{Univalence} {A B : AbGroup}
  : GroupIsomorphism (ab_hom B A)
      (loops_1trunc (AbSES B A)).
Proof.
  srapply Build_GroupIsomorphism'.
  1: apply loops_abses.
  intros phi psi.
  snrapply (equiv_ap_inv' equiv_path_abses).
  apply path_sigma_hprop.
  apply equiv_path_grouphomomorphism; intros [a b].
  unfold loops_abses.
  rewrite (eissect equiv_path_abses (abses_endomorphism_trivial^-1 (sg_op phi psi))).
  unfold equiv_path_abses.
  nrefine (_ @ ap (fun x => (equiv_path_abses^-1 x).1 _) _).
  2: exact (abses_path_data_compose_beta _ _)^.
  rewrite (equiv_inverse_compose _ _ _).
  nrefine (_ @ ap (fun x => ((equiv_path_abses_data _ _)^-1 x).1 _) _^).
  2: apply eissect.
  cbn.
  apply path_prod'.
  - rewrite grp_unit_l.
    apply associativity.
  - exact (grp_unit_l _)^.
Defined.

(** The inverse of [loops_abses]. *)
Definition loops_abses_inv `{Univalence} {A B : AbGroup}
  : loops (AbSES B A) <~> (B $-> A)
  := abses_endomorphism_trivial oE equiv_path_abses^-1.

(** Under the equivalence [loops_abses], [fmap loops (abses_pullback g)] corresponds to precomposition by [g]. It's easiest to show this using [loops_abses_inv]. *)
Definition abses_loops_pullback_inv `{Univalence} {B B' A : AbGroup} (g : B $-> B')
  : Square (IsGraph0:=isgraph_type) loops_abses_inv loops_abses_inv
      (fmap loops (abses_pullback_pmap (A:=A) g)) (fun f => f $o g).
Proof.
  intro phi; unfold loops_abses_inv.
  refine (ap abses_endomorphism_trivial _
            (x:=equiv_path_abses^-1%equiv (fmap loops _ phi))
            @ _).
  { refine (ap _ (abses_loops_pullback_data _ _) @ _).
    refine (equiv_inverse_compose _ _ _ @ _).
    exact (ap _ (eissect _ _)). }
  by apply equiv_path_grouphomomorphism.
Defined.

Definition abses_loops_pullback `{Univalence} {B B' A : AbGroup} (g : B $-> B')
  : Square (IsGraph0:=isgraph_type) loops_abses loops_abses
      (fun f => f $o g) (fmap loops (abses_pullback_pmap (A:=A) g)).
Proof.
  intro phi.
  rapply moveR_equiv_M'.
  nrefine (_ @ (abses_loops_pullback_inv g (loops_abses phi))^).
  refine (ap (fun f => f $o g) (x:=phi) _^).
  unfold loops_abses_inv, loops_abses.
  refine (ap _ (eissect equiv_path_abses _) @ _).
  apply eisretr.
Defined.

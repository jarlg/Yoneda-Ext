From HoTT Require Import Basics Types WildCat Pointed Truncations
  ExactSequence AbGroups AbSES AbSES.SixTerm.

Require Import Lemmas EquivalenceRelation Ext ES HigherExt XII_5.

Local Open Scope pointed_scope.
Local Open Scope type_scope.


(** * The long exact sequence of Ext groups *)

(** Currently [Ext n] is only a pointed set, but the notion of exactness abelian groups is the same. *)

(** Exactness at the domain of the connecting map, for all n. *)
Global Instance isexact_extn_inclusion_splice `{Univalence} {n : nat}
  {B A G : AbGroup} (E : ES 1 B A)
  : IsExact (Tr (-1))
      (ext_pullback (n:=n) (A:=G) (inclusion E))
      (abses_ext_splice E).
Proof.
  destruct n as [|n].
  (* The case [n=0] follows from [isexact_ext_contra_sixterm_iii]. *)
  { rapply isexact_homotopic_f.
    by apply phomotopy_homotopy_hset. }
  unshelve econstructor.
  { hnf.
    refine (splice_pullback_to_pushout_phomotopy _ _ @* _).
    rewrite abses_pushout_inclusion.
    apply abses_ext_splice_pt. }
  intros [S p]; revert dependent S.
  (** TODO make a tactic for the following. *)
  destruct n.
  1: rapply Trunc_ind; intros S p;
       rapply contr_inhabited_hprop;
       pose proof (K := snd (ext_XII_5_5 (S : ES 1 A G) E) p^).
  2: rapply Quotient_ind_hprop; intros S p;
       rapply contr_inhabited_hprop;
       pose proof (K := snd (ext_XII_5_5 S E) p^).
  all: strip_truncations; destruct K as [K q];
    refine (tr (K; _));
    apply path_sigma_hprop;
    exact q.
Defined.

(** Exactness at the domain of the connecting map, for all n. *)
(** The proof writes out the first part of Lemma XII.5.2. *)
Global Instance isexact_extn_splice_pullback `{Univalence} {n : nat}
  {B A G : AbGroup} (E : AbSES B A)
  : IsExact (Tr (-1))
      (abses_ext_splice (n:=n) (M:=G) E)
      (ext_pullback (projection E)).
Proof.
  destruct n as [|n].
  { rapply isexact_homotopic_if.
    all: by apply phomotopy_homotopy_hset. }
  srapply Build_IsExact.
  { refine (splice_pullback_commute _ _ @* _).
    rewrite <- abses_pullback_projection.
    apply abses_ext_splice_pt. }
  hnf.
  intros [S p]; revert dependent S.
  rapply Quotient_ind_hprop; intros [C [T F]] p.
  rapply contr_inhabited_hprop.
  pose (Fs := abses_pullback (projection E) F).
  assert (U : merely (hfiber (ext_pullback (inclusion Fs)) (es_in T))).
  { rapply isexact_preimage.
    1: apply isexact_extn_inclusion_splice.
    refine ((splice_pullback_commute _ _ _)^ @ _).
    destruct n; exact p. }
  strip_truncations; destruct U as [U q].
  pose (F' := abses_pushout (inclusion Fs) F).
  assert (alpha : merely (hfiber (abses_pushout_ext E)
                            (es_in (F' : ES 1 B Fs)))).
  { rapply (isexact_preimage _ (abses_pushout_ext E)).
    (* TODO Why do we have to specify the map above? *)
    apply (ap tr).
    refine ((abses_pushout_pullback_reorder _ _ _)^ @ _).
    apply abses_pushout_inclusion. }
  strip_truncations; destruct alpha as [alpha r].
  pose proof (r' := (equiv_path_Tr _ _)^-1 r);
    strip_truncations.
  refine (tr (ext_pullback alpha U; _)).
  apply path_sigma_hprop.
  unfold cxfib, Build_pMap, pointed_fun, pr1.
  refine (splice_pullback_to_pushout _ _ _ @ _).
  refine (ap (ext_abses_splice U) r' @ _); clear r'.
  unfold F'.
  refine ((splice_pullback_to_pushout _ _ _)^ @ _).
  rewrite q.
  destruct n; reflexivity.
Defined.

(** Exactness at the middle term, for n > 0. The zeroth level is covered by [isexact_ext_sixterm_ii]. *)
Global Instance isexact_extn_pullback_pullback `{Univalence} {n : nat}
  {B A G : AbGroup} (E : AbSES B A)
  : IsExact (Tr (-1))
      (ext_pullback (n:=n.+1) (A:=G) (projection E))
      (ext_pullback (inclusion E)).
Proof.
  destruct n.
  { rapply isexact_homotopic_if.
    all: by apply phomotopy_homotopy_hset. }
  srapply Build_IsExact.
  { apply phomotopy_homotopy_hset.
    rapply Quotient_ind_hprop; intro F.
    apply qglue.
    refine (transport (fun X => es_meqrel X pt) _^ _).
    { refine (es_pullback_compose _ _ _ @ _).
      refine (es_pullback_homotopic _ _ (f':=grp_homo_const)).
      intro; apply isexact_inclusion_projection. }
    apply zag_to_meqrel.
    apply es_pullback_const_zig. }
  hnf.
  intros [S p]; revert dependent S.
  rapply Quotient_ind_hprop; intros [C [T F]] p.
  rapply contr_inhabited_hprop.
  pose (Fs := abses_pullback (inclusion E) F).
  assert (U : merely (hfiber (ext_pullback (inclusion Fs)) (es_in T))).
  { rapply isexact_preimage.
    1: apply isexact_extn_inclusion_splice.
    refine ((splice_pullback_commute _ _ _)^ @ _).
    destruct n; exact p. }
  strip_truncations; destruct U as [U q].
  pose (iF := abses_pushout (inclusion Fs) F).
  assert (F' : (hfiber
                  (abses_pullback_pmap (projection E))
                  iF)).
  { (* Uses [isexact_abses_pullback]. *)
    rapply (isexact_preimage _ (abses_pullback_pmap (projection E))).
    refine ((abses_pushout_pullback_reorder _ _ _)^ @ _).
    exact (abses_pushout_inclusion Fs). }
  destruct F' as [F' r].
  refine (tr (ext_abses_splice U F'; _)).
  apply path_sigma_hprop.
  unfold cxfib, Build_pMap, pointed_fun, pr1.
  refine (splice_pullback_commute F' (projection E) U @ _).
  refine (ap (fun X => abses_ext_splice X U) r @ _).
  refine ((splice_pullback_to_pushout _ _ _)^ @ _).
  refine (ap (abses_ext_splice F) q @ _).
  destruct n; reflexivity.
Defined.

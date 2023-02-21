From HoTT Require Import Basics Types WildCat Pointed Truncations
  ExactSequence AbGroups AbSES AbSES.SixTerm.

Require Import Lemmas EqRel Ext ES HigherExt.

Local Open Scope pointed_scope.
Local Open Scope type_scope.

(** * The long exact sequence of Ext groups *)

(** We start with the contravariant case, in which the degree-wise maps are given by pulling back and the connecting maps are given by pushing out (or splicing). *)

(** Notes about the underlying complex: 
    1. the complex at one point easily follows from [es_pullback_compose] and [es_pullback_homotopic] -- even though these don't give pointed homotopies, they suffice when mapping into a set  
    2. 

*)

(** Exactness at the domain of the connecting map, for all n. *)
Global Instance isexact_extn_inclusion_splice `{Univalence} {n : nat}
  {C B A : AbGroup} (F : ES 1 C B)
  : IsExact (Tr (-1))
      (ext_pullback (n:=n) (A:=A) (inclusion F))
      (abses_ext_splice F).
Proof.
  destruct n as [|n].
  (* The case [n=0] follow from [isexact_ext_contra_sixterm_iii]. *)
  { rapply isexact_homotopic_f.
    by apply phomotopy_homotopy_hset. }
  unshelve econstructor.
  { refine (abses_ext_splice_reorder _ _ @* _).
    rewrite abses_pushout_inclusion.
    apply abses_ext_splice_pt. }
  intros [E p]; revert dependent E.
  destruct n. (* TODO Make a general tactic for this. *)
  1: rapply Trunc_ind; intros E p;
       rapply contr_inhabited_hprop;
       pose proof (G := snd (ext_XII_5_5 (E : ES 1 B A) F) p^).
  2: rapply Quotient_ind_hprop; intros E p;
  rapply contr_inhabited_hprop;
  pose proof (G := snd (ext_XII_5_5 E F) p^).
  all:  strip_truncations; destruct G as [G q];
    refine (tr (G; _));
    apply path_sigma_hprop;
       exact q.
Defined.

(** Exactness at the domain of the connecting map, for all n. *)
(** The proof writes out the first part of Lemma XII 5.2. *)
Global Instance isexact_extn_splice_pullback `{Univalence} {n : nat}
  {B A M : AbGroup} (E : AbSES B A)
  : IsExact (Tr (-1))
      (abses_ext_splice (n:=n) (M:=M) E)
      (ext_pullback (projection E)).
Proof.
  destruct n as [|n].
  { rapply isexact_homotopic_if.
    all: by apply phomotopy_homotopy_hset. }
  srapply Build_IsExact.
  { refine (abses_ext_splice_reorder' _ _ @* _).
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
    refine ((abses_ext_splice_reorder' _ _ _)^ @ _).
    destruct n; exact p. }
  strip_truncations; destruct U as [U q].
  pose (F' := abses_pushout (inclusion Fs) F).
  assert (alpha : merely (hfiber (abses_pushout_ext E)
                            (es_in (F' : ES 1 B Fs)))).
  { rapply (isexact_preimage _ (abses_pushout_ext E)).
    (* TODO Why do we have to specify the map? *)
    apply (ap tr).
    refine ((abses_pushout_pullback_reorder _ _ _)^ @ _).
    apply abses_pushout_inclusion. }
  strip_truncations; destruct alpha as [alpha r].
  pose proof (r' := (equiv_path_Tr _ _)^-1 r);
    strip_truncations.
  refine (tr (ext_pullback alpha U; _)).
  apply path_sigma_hprop.
  unfold cxfib, Build_pMap, pointed_fun, pr1.
  refine (abses_ext_splice_reorder'' _ _ _ @ _).
  refine (ap (ext_abses_splice U) r' @ _); clear r'.
  unfold F'.
  refine ((abses_ext_splice_reorder'' _ _ _)^ @ _).
  rewrite q.
  destruct n; reflexivity.
Defined.

(** Exactness at the middle term, for n > 0. The zeroth level is covered by [isexact_ext_sixterm_ii]. *)
Global Instance isexact_extn_pullback_pullback `{Univalence} {n : nat}
  {B A M : AbGroup} (E : AbSES B A)
  : IsExact (Tr (-1))
      (ext_pullback (n:=n.+1) (A:=M) (projection E))
      (ext_pullback (inclusion E)).
Proof.
  destruct n.
  { rapply isexact_homotopic_if.
    all: by apply phomotopy_homotopy_hset. }
  srapply Build_IsExact.
  { apply phomotopy_homotopy_hset.
    rapply Quotient_ind_hprop; intro F.
    apply qglue.
    refine (transport (fun X => es_mere_relation X pt) _^ _).
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
    refine ((abses_ext_splice_reorder' _ _ _)^ @ _).
    destruct n; exact p. }
  strip_truncations; destruct U as [U q].
  pose (iF := abses_pushout (inclusion Fs) F).
  (* assert (F' : merely (hfiber
                         (fmap (pTr 0) (abses_pullback_pmap (projection E)))
                         (tr iF))).
  { rapply isexact_preimage. (* [isexact_ext_contra_sixterm_v] *)
    apply (ap tr); cbn.
    refine ((abses_pushout_pullback_reorder _ _ _)^ @ _).
    exact (abses_pushout_inclusion Fs). } *)
  assert (F' : (hfiber
                  (abses_pullback_pmap (projection E))
                  iF)).
  { rapply (isexact_preimage _ (abses_pullback_pmap (projection E))).
    (* Uses [isexact_abses_pullback]. *)
    refine ((abses_pushout_pullback_reorder _ _ _)^ @ _).
    exact (abses_pushout_inclusion Fs). }
  destruct F' as [F' r].
  refine (tr (ext_abses_splice U F'; _)).
  apply path_sigma_hprop.
  unfold cxfib, Build_pMap, pointed_fun, pr1.
  refine (abses_ext_splice_reorder' F' (projection E) U @ _).
  refine (ap (fun X => abses_ext_splice X U) r @ _).
  refine ((abses_ext_splice_reorder _ _ _)^ @ _).
  refine (ap (abses_ext_splice F) q @ _).
  destruct n; reflexivity.
Defined.

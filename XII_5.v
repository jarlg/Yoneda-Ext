From HoTT Require Import Basics Types Spaces.Nat WildCat Pointed
  Truncations HProp HSet HFiber Limits.Pullback ExactSequence
  AbGroups AbSES.


Require Import Lemmas EquivalenceRelation ES HigherExt.

Local Open Scope pointed_scope.
Local Open Scope type_scope.

(** We prove Lemma XII.5.3, Lemma XII.5.4, and Lemma XII.5.5 in Mac Lane's "Homology". Using these, we deduce the long exact sequence in LES.v. The statements are named [XII_5_3], [XII_5_4], and [XII_5_5], respectively. We do the proof on the level of [ES n] as opposed to the quotient [Ext n], since it's simpler to express things before truncating. Afterwards we show that analogous statements hold for [Ext n] in HigherExt.v. *)

(** Since we'll be proving several goals of the form "the following 3 statements are equivalent" we make a helper structure: *)

Definition TFAE3 (P Q R : Type) := (P -> Q) * (Q -> R) * (R -> P).

Definition TFAE3_merely (P Q R : Type)
  : TFAE3 P Q R -> TFAE3 (merely P) (merely Q) (merely R).
Proof.
  intros [[PQ QR] RP]; repeat split;
    apply Trunc_functor; assumption.
Defined.

Definition iff_TFAE3 {P P' Q Q' R R' : Type}
  (p : P <-> P') (q : Q <-> Q') (r : R <-> R')
  : TFAE3 P Q R -> TFAE3 P' Q' R'.
Proof.
  intros [[PQ QR] RP]; repeat split.
  - exact (fst q o PQ o snd p).
  - exact (fst r o QR o snd q).
  - exact (fst p o RP o snd r).
Defined.


(** * Lemma XII.5.3 *)

(** Given two short exact sequences [F] and [E] which can be spliced, the following are logically equivalent:
    a) F is in the image of of pullback along [inclusion E]
    b) E is in the image of pushout along [projection F]
    c) [es_splice F E] is trivial
**)

(** We start by showing that (a) <-> (b), which we need in order to show that (c) is equivalent to either. *)

Definition abses_spliceable_hfiber_inclusion_to_hfiber_projection
  `{Univalence} {C B A : AbGroup} (F : AbSES B A) (E : AbSES C B)
  : hfiber (abses_pullback (inclusion E)) F
    -> hfiber (abses_pushout (projection F)) E.
Proof.
  (* By inducting on the path, we assume definitionally that
     [F = abses_pullback (inclusion F) G]
     for some [G]. *)
  intros [G []].
  (* We construct the sequence [K] then show it lies in the fiber. *)
  srefine (let K:=_ in (K; _)).
  { srapply (Build_AbSES G).
    1: apply grp_pullback_pr1.
    1: exact (projection E $o projection G).
    1: rapply istruncmap_mapinO_tr.
    1: exact _.
    snrapply Build_IsExact.
    { apply phomotopy_homotopy_hset; intros [g [b q]]; cbn.
      refine (ap _ q @ _).
      apply isexact_inclusion_projection. }
    intros [g q]; rapply contr_inhabited_hprop; cbn.
    assert (b : Tr (-1) (hfiber (inclusion E) (projection G g))).
    1: exact (isexact_preimage _ _ (projection E) _ q).
    strip_truncations; apply tr.
    srefine ((g; b.1; _); _); cbn.
    1: exact b.2^.
    by apply equiv_path_sigma_hprop. }
  (* We construct a morphism which exhibits [K] as the pullback of [F]: *)
  snrefine (abses_pushout_component3_id
              (Build_AbSESMorphism _ _ grp_homo_id _ _)
              (fun _ => idpath)).
  1: exact (projection G).
  - intros [g [b q]]; cbn.
    exact q^.
  - reflexivity.
Defined.

Definition abses_spliceable_hfiber_projection_to_hfiber_inclusion
  `{U : Univalence} {C B A : AbGroup} (F : AbSES B A) (E : AbSES C B)
  : hfiber (abses_pushout (projection F)) E
    -> hfiber (abses_pullback (inclusion E)) F.
Proof.
  (* We assume that [H] is definitionally a pushout by inducting on the path. *)
  intros [H []].
  (* We first construct a sequence [K], afterwards we show that it's in the fibre. *)
  srefine (let K:=_ in (K; _)).
  { srapply (Build_AbSES H).
    1: exact (inclusion H $o inclusion F).
    1: apply ab_pushout_inr.
    1: exact _.
    1: rapply ab_pushout_surjection_inr.
    srapply Build_IsExact.
    { apply phomotopy_homotopy_hset; intro a.
      refine ((ab_pushout_commsq _)^ @ _).
      refine (ap ab_pushout_inl _ @ _).
      1: apply isexact_inclusion_projection.
      apply grp_homo_unit. }
    intros [h p]; rapply contr_inhabited_hprop.
    (* since [h] is in the kernel of [projection H], we can lift it to [e : E] *)
    assert (e : merely (hfiber (inclusion H) h)).
    { rapply (isexact_preimage (Tr (-1)) (inclusion H)).
      refine ((right_square (abses_pushout_morphism H (projection F)) h)^ @ _);
        unfold abses_pushout_morphism, component2.
      refine (ap _ p @ _).
      apply grp_homo_unit. }
    strip_truncations.
    (* since [inclusion F] is a mono, [e] is in the kernel of [projection E] *)
    assert (q : projection F e.1 = pt).
    { rapply (isinj_embedding (inclusion (abses_pushout (projection F) H))).
      refine (ab_pushout_commsq e.1 @ _ @ (grp_homo_unit _)^).
      exact (ap ab_pushout_inr e.2 @ p). }
    (* by exactness of [E] we get a preimage [a : A] of [e : E] *)
    pose (a := isexact_preimage (Tr (-1)) (inclusion F) _ _ q).
    generalize a; clear a. apply Trunc_functor; intro a.
    exists a.1.
    apply path_sigma_hprop; cbn.
    exact (ap (inclusion H) a.2 @ e.2). }
  snrefine (abses_pullback_component1_id
             (Build_AbSESMorphism grp_homo_id _ _ _ _)
             (fun _ => idpath))^.
  - exact (inclusion H).
  - reflexivity.
  - exact (fun x => (ab_pushout_commsq x)^).
Defined.

(** Lemma XII.5.3 (a) iff (b) *)
Definition iff_abses_spliceable_hfiber_projection_inclusion `{Univalence}
  {C B A : AbGroup} (F : AbSES B A) (E : AbSES C B)
  : hfiber (abses_pullback (inclusion E)) F
    <-> hfiber (abses_pushout (projection F)) E
  := (abses_spliceable_hfiber_inclusion_to_hfiber_projection F E,
       abses_spliceable_hfiber_projection_to_hfiber_inclusion F E).

(** To show that (c) is equivalent to (a) and (b), we construct implications *)
(** We construct maps between fibres which are needed for the proof. *)
Definition es2_zag_fiber_inclusion `{Univalence} {C B B' A : AbGroup}
  {F : ES 1 B A} {E : ES 1 C B} {F' : ES 1 B' A} {E' : ES 1 C B'}
  (zag : es_zig (es_splice F' E') (es_splice F E))
  : hfiber (abses_pullback (inclusion E)) F
    -> hfiber (abses_pullback (inclusion E')) F'.
Proof.
  intros [G p]; induction p.
  destruct zag as [phi [p q]]; cbn in phi, p, q.
  pose (phi' := abses_path_pushout_inclusion_commsq phi _ _ q).
  destruct phi' as [phi' r].
  exists (abses_pullback phi' G).
  refine (abses_pullback_compose _ _ _ @ _).
  refine (abses_pullback_homotopic _ (inclusion E $o phi) _ _ @ _).
  1: symmetry; exact r.
  exact ((abses_pullback_compose _ _ _)^ @ p^).
Defined.

Definition es2_zig_fiber_projection `{Univalence} {C B B' A : AbGroup}
  {F : ES 1 B A} {E : ES 1 C B} {F' : ES 1 B' A} {E' : ES 1 C B'}
  (zig : es_zig (es_splice F E) (es_splice F' E'))
  : hfiber (abses_pushout (projection F)) E
    -> hfiber (abses_pushout (projection F')) E'.
Proof.
  intros [G p]; induction p.
  destruct zig as [phi [p q]]; cbn in phi, p, q.
  pose (phi' := abses_path_pullback_projection_commsq phi _ _ p^).
  destruct phi' as [phi' r].
  exists (abses_pushout phi' G).
  refine ((abses_pushout_compose _ _ _)^ @ _).
  refine (abses_pushout_homotopic _ (grp_homo_compose phi (projection F)) _ _ @ _).
  1: exact r.
  exact (abses_pushout_compose _ _ _ @ q).
Defined.

Lemma XII_5_3 `{Univalence} {C B A : AbGroup} (F : ES 1 B A) (E : ES 1 C B)
  : TFAE3 (hfiber (abses_pullback (inclusion E)) F)
      (hfiber (abses_pushout (projection F)) E)
      (pt ~ (es_splice F E)).
Proof.
  repeat split.
  - apply abses_spliceable_hfiber_inclusion_to_hfiber_projection.
  - (* (b) -> (c)  can be shown directly *)
    intros [G p]; induction p.
    exists 2%nat. (* pt <- (E (projection E) <> F) -> E <> (projection E) F *)
    refine (_; (_, inl (es_morphism_abses_zig _ _ _))).
    refine (pt; (idpath, inr _)).
    exists grp_homo_const; split; cbn.
    + refine (_ @ (abses_pullback_point _)^).
      exact (abses_pullback_projection F)^.
    + exact (abses_pushout_const G).
  - (* for (c) -> (a) we need to use that we know (a) <-> (b) *)
    intros [n zzs].
    revert dependent B.
    induction n as [|n IH]; intros.
    + (* the base case can be shown directly *)
      cbn in zzs.
      apply (transport (fun X : ES 2 C A =>
                          hfiber (abses_pullback (inclusion (snd X.2)))
                            (fst X.2)) zzs); cbn.
      exists pt.
      apply abses_pullback_point.
    + destruct zzs as [[D [X0 X1]] [zzs [zig|zag]]].
      (* note: X is definitionally in the image of es_splice *)
      * apply abses_spliceable_hfiber_projection_to_hfiber_inclusion.
        apply (es2_zig_fiber_projection zig).
        apply abses_spliceable_hfiber_inclusion_to_hfiber_projection.
        exact (IH _ X0 X1 zzs).
      * apply (es2_zag_fiber_inclusion zag).
        by apply IH.
Defined.


(** * Lemma XII.5.4 *)

(** Lemma XII.5.4 gives an equivalent condition to (b) in Lemma XII.5.3 which generalises to [ES n]. The condition is that the following type is inhabited: *)
Definition es_ii_family `{Univalence} {n : nat} {C B A : AbGroup}
  : ES n.+1 B A -> ES 1 C B -> Type
  := fun E F => { alpha : { B' : AbGroup & B' $-> B }
                       & (pt ~ es_pullback alpha.2 E)
                         * (hfiber (abses_pushout alpha.2) F) }.

(** The logical equivalence with condition (b) above. *)
Lemma XII_5_4 `{Univalence} {C B A : AbGroup} (F : ES 1 B A) (E : ES 1 C B)
  : hfiber (abses_pushout (projection F)) E <-> es_ii_family F E.
Proof.
  split.
  - intros [G p]; induction p.
    exists (middle F; projection F); split.
    + apply abses_pullback_projection.
    + cbn. exact (G; idpath).
  - intros [[B' alpha] [p [G q]]]; cbn in *.
    pose (phi := abses_pullback_trivial_factors_projection p).
    destruct phi as [phi gamma].
    exists (abses_pushout phi G).
    refine ((abses_pushout_compose _ _ _)^ @ _).
    refine (abses_pushout_homotopic _ _ _ _ @ _).
    1: exact (equiv_path_grouphomomorphism^-1 gamma^).
    assumption.
Defined.

(** We rephrase Lemma XII.5.3 in general terms for later use. *)
Theorem XII_5_3' `{Univalence} {C B A : AbGroup} (E : ES 1 B A) (F : ES 1 C B)
  : TFAE3 (rfiber es_zig (es_pullback (inclusion F)) E)
      (es_ii_family E F)
      (pt ~ (es_splice E F)).
Proof.
  repeat split.
  - refine (_ o _).
    + apply XII_5_4.
    + apply XII_5_3.
  - refine (_ o _).
    + apply XII_5_3.
    + apply XII_5_4.
  - apply XII_5_3.
Defined.


(** * Lemma XII.5.5 *)

(** For [S : ES n.+1 B A] and [E : ES 1 C B], the following are equivalent:
 a) S is in the image of pullback along [inclusion E]
 b) [es_ii_family S E] holds
 c) [es_splice S E] is trivial
**)

(** The proof is structurally similar to Lemma XII.5.3; we need to know that (a) iff (b) in order to show the equivalence with (c). *)

Definition es_zag_fiber_inclusion `{Univalence} {n : nat} {C B B' A : AbGroup}
  {S : ES n.+1 B A} {F : ES 1 C B} {S' : ES n.+1 B' A} {F' : ES 1 C B'}
  (zag : es_zig (es_abses_splice S' F') (es_abses_splice S F))
  : rfiber es_eqrel (es_pullback (inclusion F)) S
    -> rfiber es_eqrel (es_pullback (inclusion F')) S'.
Proof.
  destruct n.
  1: by apply es2_zag_fiber_inclusion.
  intros [G zz].
  destruct zag as [phi [p q]]; cbn in phi, q; unfold es_abses_splice in p.
  pose (phi' := abses_path_pushout_inclusion_commsq phi _ _ q).
  destruct phi' as [phi' r].
  exists (es_pullback phi' G).
  transitivity (es_pullback phi S).
  2: exact (zag_to_eqrel _ p).
  refine (transport (fun X => X ~ _) _ _).
  { refine (_ @ (es_pullback_compose _ _ _)^).
    refine (_ @ es_pullback_homotopic (f:=inclusion F $o phi) _ _).
    2: exact r.
    exact (es_pullback_compose _ _ _). }
  apply rap_pullback.
  exact zz.
Defined.

Definition es_zig_fiber_projection `{Univalence} {n : nat} {C B B' A : AbGroup}
  {S : ES n.+1 B A} {F : ES 1 C B} {S' : ES n.+1 B' A} {F' : ES 1 C B'}
  (zig : es_zig (es_abses_splice S F) (es_abses_splice S' F'))
  : es_ii_family S F -> es_ii_family S' F'.
Proof.
  intros [[B'' alpha] [zz [G p]]]; induction p.
  unfold pr2 in zz, zig; unfold pr1 in G.
  destruct zig as [phi [p q]]; cbn in phi, q; unfold es_abses_splice in p.
  exists (B''; grp_homo_compose phi alpha); split; unfold pr2.
  2: exact (G; abses_pushout_compose _ _ _ @ q).
  rewrite <- es_pullback_compose.
  etransitivity.
  2: { apply rap_pullback.
       destruct n.
       + by induction p.
       + exact (zig_to_eqrel _ p). }
  assumption.
Defined.

(** Lemma XII.5.5 (i) -> (ii) *)
Definition es_spliceable_rfiber_inclusion_es_ii_family `{Univalence} {n : nat}
  {C B A : AbGroup} (S : ES n.+1 B A) (F : ES 1 C B)
  : rfiber es_eqrel (es_pullback (inclusion F)) S -> es_ii_family S F.
Proof.
  destruct n.
  1: intro; by apply XII_5_4, abses_spliceable_hfiber_inclusion_to_hfiber_projection.
  intros [[? [G0 G1]] p].
  pose (T := abses_pullback (inclusion F) G1).
  exists (middle T; projection T); split; unfold pr2.
  - etransitivity.
    2: exact (rap_pullback _ _ _ p).
    unfold es_pullback.
    rewrite <- abses_pullback_projection.
    apply zig_to_eqrel.
    nrapply es_splice_point_abses.
  - apply abses_spliceable_hfiber_inclusion_to_hfiber_projection.
    exact (G1; idpath).
Defined.

(** A preliminary result for Lemma XII.5.5: given Lemma XII.5.5 at level n, we deduce (i) iff (ii) on level n+1. *)
Lemma XII_5_5_prelim `{Univalence} {n : nat}
  : (forall {C B A : AbGroup} (E : ES n.+1 B A) (F : ES 1 C B),
    TFAE3 (rfiber es_eqrel (es_pullback (inclusion F)) E)
      (es_ii_family E F)
      (pt ~ (es_abses_splice E F)))
    -> (forall {C B A : AbGroup} (S : ES n.+2 B A) (E : ES 1 C B),
           (rfiber es_eqrel (es_pullback (inclusion E)) S)
           <-> es_ii_family S E).
Proof.
  intro IH; split.
  1: apply es_spliceable_rfiber_inclusion_es_ii_family.
  destruct S as [C' [T F]].
  intros [[B' alpha] [p [E' q]]]; unfold pr2 in p, q.
  assert (T' : rfiber es_eqrel
                (es_pullback (inclusion (abses_pullback alpha F))) T).
  1: apply IH; exact p.
  assert (F' : hfiber (abses_pullback (inclusion E))
                 (abses_pushout (inclusion (abses_pullback alpha F)) F)).
  { apply XII_5_3.
    induction q.
    etransitivity.
    2: nrapply es_morphism_abses_eqrel.
    unfold es_pullback.
    rewrite (abses_pushout_pullback_reorder F _ alpha)^.
    rewrite abses_pushout_inclusion.
    apply zag_to_eqrel.
    nrapply es_point_splice_abses. }
  destruct F' as [F' r], T' as [T' r'].
  exists (es_abses_splice T' F').
  unfold es_pullback, es_abses_splice.
  rewrite r.
  etransitivity.
  1: symmetry; nrapply es_morphism_abses_eqrel.
  exact (rap_splice _ _ _ r').
Defined.

(** It is useful to have a name for this family below. *)
Local Definition XII_5_5_family `{Univalence} {n : nat} {B A : AbGroup}
  : ES n.+2 B A -> Type.
Proof.
  intros [C [E F]].
  exact (rfiber es_eqrel (es_pullback (inclusion F)) E).
Defined.
  
Lemma XII_5_5 `{Univalence} {n : nat}
  : forall {C B A : AbGroup} (E : ES n.+1 B A) (F : ES 1 C B),
    TFAE3 (rfiber es_eqrel (es_pullback (inclusion F)) E)
      (es_ii_family E F)
      (pt ~ (es_abses_splice E F)).
Proof.
  induction n as [|n IHn]; intros.
  1: apply XII_5_3'.
  repeat split.
  - apply es_spliceable_rfiber_inclusion_es_ii_family.
  - intros [[B' alpha] [[m zzs] [G p]]]; induction p.
    unfold pr1, pr2 in *.
    etransitivity.
    2: nrapply es_morphism_abses_eqrel.
    etransitivity (es_abses_splice (pt : ES n.+2 B' A) G).
    2: { rapply rap_splice.
         exact (m; zzs). }
    apply zag_to_eqrel.
    apply es_point_splice_abses.
  - intros [m zzs].
    revert dependent B.
    induction m as [|m IHm]; intros.
    + nrapply (transport XII_5_5_family zzs).
      exists pt.
      exists (0%nat); rapply es_pullback_point.
    + destruct zzs as [[D [X0 X1]] [zzs [zig|zag]]].
      * apply (XII_5_5_prelim IHn).
        apply (es_zig_fiber_projection zig).
        apply (XII_5_5_prelim IHn).
        by apply IHm.
      * apply (es_zag_fiber_inclusion zag).
        by apply IHm.
Defined.


(** * Lemma XII.5.5 for [Ext n] *)

(** Relating condition (i) for ES and Ext. *)

Definition es_rfiber_to_ext_hfiber `{Univalence} {n : nat}
  {C B A : AbGroup} (E : ES n.+1 B A) (F : ES 1 C B)
  : rfiber es_eqrel (es_pullback (inclusion F)) E
    -> hfiber (ext_pullback (inclusion F)) (es_in E).
Proof.
  apply (functor_sigma es_in); intros G rho.
  destruct n.
  1: by destruct rho. (* path induction *)
  rapply path_quotient.
  exact (tr rho).
Defined.

Definition ext_hfiber_to_mere_es_rfiber `{Univalence} {n : nat}
  {C B A : AbGroup} (E : ES n.+1 B A) (F : ES 1 C B)
  : hfiber (ext_pullback (inclusion F)) (es_in E)
    -> merely (rfiber es_eqrel (es_pullback (inclusion F)) E).
Proof.
  intros [G p].
  (* First we choose a representative for G. *)
  assert (G' : Tr (-1) (hfiber es_in G)).
  1: destruct n; rapply center. (* both tr and class_of are surjective *)
  strip_truncations.
  destruct G' as [G' q]; induction q.
  (* by inducting on [q], [G'] is definitionally in the image of [tr] *)
  destruct n.
  - pose proof (q := (equiv_path_Tr _ _)^-1 p); strip_truncations.
    exact (tr (G'; q)).
  -pose proof (q := (path_quotient _ _ _)^-1 p); strip_truncations.
   exact (tr (G'; q)).
Defined.

Definition iff_es_rfiber_ext_hfiber `{Univalence} {n : nat}
  {C B A : AbGroup} (E : ES n.+1 B A) (F : ES 1 C B)
  : merely (rfiber es_eqrel (es_pullback (inclusion F)) E)
    <-> merely (hfiber (ext_pullback (inclusion F)) (es_in E)).
Proof.
  split.
  - apply Trunc_functor, es_rfiber_to_ext_hfiber.
  - apply Trunc_rec, ext_hfiber_to_mere_es_rfiber.
Defined.

(** Relating condition (ii) for ES and Ext. *)

Definition ext_ii_family `{Univalence} {n : nat} {C B A : AbGroup}
  : Ext n.+1 B A -> Ext 1 C B -> Type
  := fun E F => { bt : { B' : AbGroup & B' $-> B }
                    & (pt = ext_pullback bt.2 E :> Ext n.+1 bt.1 A)
                      * (hfiber (ext_pushout bt.2) F) }.

(** Condition (iii) for ES and Ext. *)

Lemma iff_iii `{Univalence} {n : nat} {C B A : AbGroup}
  (E : ES n.+1 B A) (F : ES 1 C B)
  : (es_meqrel pt (es_abses_splice E F)) <-> (pt = ext_abses_splice (es_in E) F).
Proof.
  apply (equiv_equiv_iff_hprop _ _)^-1.
  destruct n; rapply path_quotient.
Defined.

(** Now we show that [ext_ii_family] corresponds to the propositional truncation of [ii_family] from ES.v. *)

Lemma iff_es_ext_ii_family `{Univalence} {n : nat} {C B A : AbGroup}
  (E : ES n.+1 B A) (F : ES 1 C B)
  : merely (es_ii_family E F) <-> merely (ext_ii_family (es_in E) (es_in F)).
Proof.
  apply (equiv_equiv_iff_hprop _ _)^-1.
  refine (equiv_O_sigma_O _ _ oE _ oE (equiv_O_sigma_O _ _)^-1).
  apply Trunc_functor_equiv.
  apply equiv_functor_sigma_id; intros [B' alpha].
  refine ((equiv_O_prod_cmp _ _ _)^-1 oE _ oE equiv_O_prod_cmp _ _ _).
  apply equiv_functor_prod'.
  { destruct n.
    all: refine (equiv_tr _ _ oE _).
    - apply equiv_path_Tr.
    - rapply path_quotient. }
  refine (_ oE (equiv_O_sigma_O _ _)^-1).
  apply equiv_iff_hprop.
  - apply Trunc_functor.
    apply (functor_sigma tr); cbn; intro G.
    apply path_Tr.
  - apply Trunc_rec; cbn; intros [G p].
    revert p; strip_truncations; cbn.
    rapply (equiv_ind (equiv_path_Tr _ _)).
    apply Trunc_functor; intro p.
    exact (G; tr p).
Defined.

(** Now Lemma XII.5.5 follows for Ext as well. *)

Lemma ext_XII_5_5 `{Univalence} {n : nat} {C B A : AbGroup}
  (E : ES n.+1 B A) (F : ES 1 C B)
  : TFAE3 (merely (hfiber (ext_pullback (inclusion F)) (es_in E)))
      (merely (ext_ii_family (es_in E) (es_in F)))
      (pt = ext_abses_splice (es_in E) F).
Proof.
  rapply iff_TFAE3.
  - apply iff_es_rfiber_ext_hfiber.
  - apply iff_es_ext_ii_family.
  - apply iff_iii.
  - apply TFAE3_merely.
    apply XII_5_5.
Defined.

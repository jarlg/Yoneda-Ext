From HoTT Require Import Basics Types Pointed HSet HFiber Truncations
  Limits.Pullback WildCat AbGroups AbSES Homotopy.ExactSequence.

(** * Lemma XII.5.3 (i) iff (ii) *)

(** Given two short exact sequences [E] and [F] which can be spliced, the fibres [hfiber (abses_pullback (inclusion F)) E] and [hfiber (abses_pushout (projection E)) F] are logically equivalent, and this fact underlies Lemma XII.5.3 (i) iff (ii). We begin by showing (i) -> (ii). *)

(** Lemma XII.5.3 (i) -> (ii) *)
Definition abses_spliceable_hfiber_inclusion_to_hfiber_projection
  `{Univalence} {C B A : AbGroup} (E : AbSES B A) (F : AbSES C B)
  : hfiber (abses_pullback (inclusion F)) E
    -> hfiber (abses_pushout (projection E)) F.
Proof.
  (* By inducting on the path, we assume definitionally that
     [E = abses_pullback (inclusion F) G]
     for some [G]. *)
  intros [G []].
  (* We construct the sequence [K] then show it lies in the fiber. *)
  srefine (let K:=_ in (K; _)).
  { srapply (Build_AbSES G).
    1: apply grp_pullback_pr1.
    1: exact (projection F $o projection G).
    1: rapply istruncmap_mapinO_tr.
    1: exact _.
    snrapply Build_IsExact.
    { apply phomotopy_homotopy_hset; intros [g [b q]]; cbn.
      refine (ap _ q @ _).
      apply isexact_inclusion_projection. }
    intros [g q]; rapply contr_inhabited_hprop; cbn.
    assert (b : Tr (-1) (hfiber (inclusion F) (projection G g))).
    1: exact (isexact_preimage _ _ (projection F) _ q).
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

(** Lemma XII.5.3 (ii) -> (i) *)
Definition abses_spliceable_hfiber_projection_to_hfiber_inclusion `{U : Univalence}
  {C B A : AbGroup} (E : AbSES B A) (F : AbSES C B)
  : hfiber (abses_pushout (projection E)) F
    -> hfiber (abses_pullback (inclusion F)) E.
Proof.
  (* We assume that [H] is definitionally a pushout by inducting on the path. *)
  intros [H []].
  (* We first construct a sequence [K], afterwards we show that it's in the fibre. *)
  srefine (let K:=_ in (K; _)).
  { srapply (Build_AbSES H).
    1: exact (inclusion H $o inclusion E).
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
      refine ((right_square (abses_pushout_morphism H (projection E)) h)^ @ _);
        unfold abses_pushout_morphism, component2.
      refine (ap _ p @ _).
      apply grp_homo_unit. }
    strip_truncations.
    (* since [inclusion F] is a mono, [e] is in the kernel of [projection E] *)
    assert (q : projection E e.1 = pt).
    { rapply (isinj_embedding (inclusion (abses_pushout (projection E) H))).
      refine (ab_pushout_commsq e.1 @ _ @ (grp_homo_unit _)^).
      exact (ap ab_pushout_inr e.2 @ p). }
    (* by exactness of [E] we get a preimage [a : A] of [e : E] *)
    pose (a := isexact_preimage (Tr (-1)) (inclusion E) _ _ q).
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

(** Lemma XII.5.3 (ii) iff (i) *)
Definition iff_abses_spliceable_hfiber_projection_inclusion `{Univalence}
  {C B A : AbGroup} (E : AbSES B A) (F : AbSES C B)
  : hfiber (abses_pullback (inclusion F)) E
    <-> hfiber (abses_pushout (projection E)) F
  := (abses_spliceable_hfiber_inclusion_to_hfiber_projection E F,
       abses_spliceable_hfiber_projection_to_hfiber_inclusion E F).

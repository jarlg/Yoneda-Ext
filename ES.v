From HoTT Require Import Basics Types Pointed Spaces.Nat Truncations
  AbGroups AbSES AbSES.Pullback WildCat ExactSequence.

Require Import EqRel Ext SixTerm.

Local Open Scope pointed_scope.
Local Open Scope type_scope.

Global Instance ispointed_grouphom {G H : Group}
  : IsPointed (GroupHomomorphism G H)
  := grp_homo_const.

Global Instance ispointed_abgroup@{u v}
  : IsPointed@{v} AbGroup@{u} := abgroup_trivial@{u}.

Definition AbGroup := [AbGroup, _].
Definition AbSES : AbGroup^op -> AbGroup -> pType := AbSES.

(** * Length-n exact sequences *)

(** ** The type [ES n] of length [n] exact sequences *)

(** We define the type [ES n] of pairs of exact sequences that can be spliced (when n > 1), of which [Ext n] will be defined as a quotient (by "Mac Lane moves"). We could start the induction at n=1, but by starting at n=2 we get that [Pretext 1 B A] is definitionally [AbSES B A], which is preferable. *)
(* NB: [ES n] is not the real n-type of "length-n exact sequences," i.e., the classifying space of the category of such. Rather, it is an approximation which has the correct set-truncation. *)
Fixpoint ES' (n : nat) : AbGroup^op -> AbGroup -> Type
  := match n with
     | 0%nat => fun B A => GroupHomomorphism B A
     | 1%nat => AbSES
     | S n => fun C A => exists B, (ES' n B A) * (AbSES C B)
     end.

Global Instance ispointed_es' (n : nat)
  : forall B A, IsPointed (ES' n B A).
Proof.
  induction n as [| [|n] IH]; intros B A.
  - exact grp_homo_const.
  - exact pt.
  - exists abgroup_trivial.
    exact (IH _ _, point _).
Defined.

Definition ES (n : nat) : AbGroup^op -> AbGroup -> pType
  := fun B A => [ES' n B A, _].

(** *** Functoriality of [ES] *)

(** The covariant action on [es] by pushing out. *)
Definition es_pushout `{Univalence} {n : nat}
  : forall {B A A' : AbGroup} (f : A $-> A'), ES n B A -> ES n B A'.
(* We have to quantify in the conclusion to make the induction go through. *)
Proof.
  induction n as [| [|n] IH].
  - intros ? ? ? f g; exact (f $o g).
  - intros ? ? ? f E; exact (abses_pushout f E).
  - intros ? ? ? f [C [E F]].
    exact (C; (IH _ _ _ f E, F)).
Defined.

Lemma es_pushout_id `{Univalence} {n : nat}
  : forall {B A : AbGroup} (X : ES n B A), es_pushout grp_homo_id X = X.
Proof.
  induction n as [| [|n] IH]; intros.
  - cbn. by apply equiv_path_grouphomomorphism.
  - nrapply abses_pushout_id.
  - snrapply path_sigma.
    1: reflexivity.
    unfold transport. apply path_prod.
    + apply IH.
    + reflexivity.
Defined.

Lemma es_pushout_point `{Univalence} {n : nat}
  {B A A' : AbGroup} (g : A $-> A')
  : es_pushout g (pt : ES n B A) = pt.
Proof.
  induction n as [| [|n] IH].
  - nrapply equiv_path_grouphomomorphism; intro b; cbn.
    apply grp_homo_unit.
  - nrapply abses_pushout_point.
  - snrapply path_sigma; only 1: reflexivity.
    refine (path_prod' _ idpath).
Admitted.

(** The contravariant action on [es] by pulling back. *)
Definition es_pullback `{Univalence} {n : nat}
  {B B' A : AbGroup} (g : B' $-> B)
  : ES n B A -> ES n B' A.
Proof.
  destruct n as [|[|]] ; cbn.
  - exact (fun phi => grp_homo_compose phi g).
  - exact (abses_pullback g).
  - intros [C [E F]].
    exact (C; (E, abses_pullback g F)).
Defined.

Lemma es_pullback_id `{Univalence} {n : nat} {B A : AbGroup} (X : ES n B A)
  : es_pullback grp_homo_id X = X.
Proof.
  induction n as [| [|n] IH].
  - by nrapply equiv_path_grouphomomorphism.
  - nrapply abses_pullback_id.
  - destruct X as [C [E S]]; cbn.
    snrapply path_sigma.
    1: reflexivity.
    unfold transport, pr2.
    exact (path_prod' idpath (abses_pullback_id S)).
Defined.

Lemma es_pullback_point `{Univalence} {n : nat} {B B' A : AbGroup} (f : B' $-> B)
  : es_pullback f (pt : ES n B A) = pt.
Proof.
  destruct n as [|[|]].
  - cbn. by nrapply equiv_path_grouphomomorphism.
  - nrapply abses_pullback_point.
  - snrapply path_sigma; only 1: cbn.
    1: reflexivity.
    unfold transport, es_pullback, pr2.
    exact (path_prod' idpath (abses_pullback_point _)).
Defined
.

Definition es_pullback_compose `{Univalence} {n : nat}
  {B0 B1 B2 A : AbGroup} (f0 : B1 $-> B0) (f1 : B2 $-> B1)
  : es_pullback (n:=n) (A:=A) f1 o es_pullback f0 == es_pullback (f0 $o f1).
Proof.
  destruct n as [|[|]].
  - intro x; by nrapply equiv_path_grouphomomorphism.
  - cbn. nrapply abses_pullback_compose.
  - intros [C [E F]]; cbn.
    snrapply path_sigma.
    1: reflexivity.
    unfold transport, pr2.
    exact (path_prod' idpath (abses_pullback_compose _ _ _)).
Defined.

Definition es_pullback_homotopic `{Univalence} {n : nat} {B B' A : AbGroup}
  {f f' : B' $-> B} (h : f == f') : es_pullback (n:=n) (A:=A) f == es_pullback f'.
Proof.
  destruct n as [|[|]].
  - intro g; nrapply equiv_path_grouphomomorphism; intro b; cbn.
    exact (ap g (h b)).
  - cbn. by nrapply abses_pullback_homotopic.
  - intros [C [E F]]; cbn.
    snrapply path_sigma.
    1: reflexivity.
    apply path_prod'.
    + reflexivity.
    + by nrapply abses_pullback_homotopic.
Defined.

(** We can splice a longer exact sequence with a short exact sequence. *)
Definition es_abses_splice `{Univalence} {n : nat} {C B A : AbGroup}
  : ES n B A -> AbSES C B -> ES (S n) C A.
Proof.
  intros E F; destruct n.
  - exact (abses_pushout E F).
  - exact (B; (E, F)).
Defined.

Definition es_pushout_pullback_reorder `{Univalence} {n : nat}
  : forall {B B' A A' : AbGroup} (f : A $-> A') (g : B' $-> B) {E : ES n B A},
    es_pushout f (es_pullback g E) = es_pullback g (es_pushout f E).
Proof.
  induction n as [| [|n] IH]; intros.
  - by nrapply equiv_path_grouphomomorphism.
  - nrapply abses_pushout_pullback_reorder.
  - snrapply path_sigma.
    1: reflexivity.
    unfold transport.
    exact (path_prod' idpath idpath).
Defined.

(** We can splice arbitrary [ES]'s. When (n, m = 0) splicing reduces to composition of morphisms, and when (m = 0) it's given by [es_pullback]. *)
(* jarl: An issue that comes up is that splicing is not associative on the type level. Of course it's not associative on the term level, but in fact you can't even ask about associativity on the term level, since you don't have terms in the same types! *)
Definition es_splice `{Univalence} {n m : nat}
  : forall {C B A}, ES n B A -> ES m C B -> ES (add n m) C A.
Proof.
  induction m as [| [|m] IH]; intros ? ? ? E F.
  (* In the base case, we pull the left factor back. *)
  - rewrite <- nat_add_n_O.
    exact (es_pullback F E).
  - rewrite nat_add_comm. 
    exact (es_abses_splice E F).
  - rewrite <- nat_add_n_Sm.
    destruct F as [D [S T]].
    exact (es_abses_splice (IH _ _ _ E S) T).
Defined.


(** ** The relation on [ES] *)

(** We define a relation on [ES n] whose set-quotient will be defined to be [Ext n]. *)
Definition es_prerelation `{Univalence} {n : nat}
  : forall {B A : AbGroup}, Relation (ES n B A).
Proof.
  induction n as [|[|n] IH]; intros B A.
  1,2: exact paths.
  intros [C [E S]] [D [F T]].
  exact { f : C $-> D & (IH _ _ E (es_pullback f F)) * (abses_pushout f S = T) }.
Defined.
(* NB: On the inductive step, it might seem like we should have asked for an arbitrary zig-zag relating [E] and [es_pullback f F] above. However, such zig-zags on level [n] can be encoded as zig-zags on level [n+1]. Thus the generated equivalence relation [EqRel es_prerelation] will be the same. Working with a single zig is simpler, so we've chosen that. (As a sanity check, the function [zzap_splice] below shows that splicing respects the generated equivalence relation.) *)

(** [EqRel R] is only correct when [R] is reflexive, so we need to show that. *)
Local Instance reflexive_es_prerelation `{Univalence} {n : nat}
  : forall B A, Reflexive (@es_prerelation _ n B A).
Proof.
  induction n as [| [|n] IH]; intros.
  - exact _.
  - exact (fun _ => idpath).
  - intros [C [E S]].
    exists grp_homo_id; split.
    + rewrite es_pullback_id; nrapply IH.
    + nrapply abses_pushout_id.
Defined.

Local Instance transitive_es_prerelation `{Univalence} {n : nat}
  : forall B A, Transitive (@es_prerelation _ n B A).
Proof. Admitted.

(** The "Mac Lane move". *)
(* todo: do it with n on the RHS? *)
Definition es_morphism_abses_zig `{Univalence} {n : nat}
  {C B B' A : AbGroup} (E : ES n B' A) (phi : B $->  B') (F : ES 1 C B)
  : es_prerelation
      (es_abses_splice (es_pullback phi E) F)
      (es_abses_splice E (es_pushout phi F)).
Proof.
  destruct n as [|[|]]; only 1,2: cbn.
  - nrapply abses_pushout_compose.
  - exists phi; easy.
  - exists phi; destruct E as [D [E0 E1]].
    unfold es_pullback, es_abses_splice.
    nrefine (_, idpath).
    nrapply reflexive_es_prerelation.
Defined.

(** The equivalence relation generated by [es_prerelation]. *)
Definition es_relation `{Univalence} {n : nat} {B A : AbGroup}
  : Relation (ES n B A)
  := match n with
     | 0%nat => paths
     | 1%nat => paths
     | n => EqRel es_prerelation
     end.

Notation "E ~ F" := (es_relation E F) (at level 93).

Definition es_morphism_abses_relation `{Univalence} {n : nat}
  {C B B' A : AbGroup} (E : ES n.+1 B' A) (phi : B $->  B') (F : ES 1 C B)
  : es_abses_splice (es_pullback phi E) F ~
      es_abses_splice E (es_pushout phi F)
  := zig_to_eqrel _ (es_morphism_abses_zig E phi F).

(* todo: Can this be done better? *)
Global Instance reflexive_es_relation `{Univalence} {n : nat} {B A : AbGroup}
  : Reflexive (@es_relation _ n B A)
  := ltac:(destruct n as [|[|]]; exact _).

Global Instance symmetric_es_relation `{Univalence} {n : nat} {B A : AbGroup}
  : Symmetric (@es_relation _ n B A)
  := ltac:(destruct n as [|[|]]; exact _).

Global Instance transitive_es_relation `{Univalence} {n : nat} {B A : AbGroup}
  : Transitive (@es_relation _ n B A)
  := ltac:(destruct n as [|[|]]; exact _).

(** The mere equivalence relation generated by [es_prerelation]. *)
Definition es_mere_relation `{Univalence} {n : nat} {B A : AbGroup}
  : Relation (ES n B A)
  := match n with
     | 0%nat => paths
     | 1%nat => (fun A B => tr (n:=0) A = tr B)
     | n => MEqRel es_prerelation
     end.

(** *** Properties of the (pre)relation on [ES n]. *)

(** Pullback preserves [es_relation]. *)
(* jarl: "rap" is for "relation ap"... *)
Definition rap_pullback `{Univalence} {n : nat} {B B' A : AbGroup} (g : B' $-> B)
  : forall (E F : ES n B A), E ~ F -> es_pullback g E ~ es_pullback g F.
Proof.
  destruct n as [|[|]].
  1,2: by intros ? ? []. (* path induction *)
  nrapply eqrel_generator; intros E F [X [p q]].
  nrefine (X; (p, _)).
  nrefine (abses_pushout_pullback_reorder _ _ _ @ _).
  by nrapply (ap (abses_pullback g)).
Defined.

(** If you pull back along [grp_homo_const], you get a zig from [pt]. *)
Lemma es_pullback_const_zig `{Univalence} {n : nat}
  : forall {B B' A : AbGroup} (E : ES n B A),
    es_prerelation (pt : ES n B' A) (es_pullback grp_homo_const E).
Proof.
  induction n as [| [|n] IH]; intros.
  1: symmetry; nrapply equiv_path_grouphomomorphism; intro x; apply grp_homo_unit.
  1: nrapply abses_pullback_const.
  exists grp_homo_const; split.
  + nrapply IH.
  + cbn. exact (abses_pushout_point _ @ abses_pullback_const _).
Defined.

(** To show that pushout preserves the relation we first show, by induction, that it preserves the generating relation. *)
Definition rap_pushout_prerelation `{Univalence} {n : nat}
  : forall {B A A' : AbGroup} (f : A $-> A') (E F : ES n B A),
    es_prerelation E F -> es_prerelation (es_pushout f E) (es_pushout f F).
Proof.
  induction n as [| [|n] IH].
  1,2: by intros ? ? ? ? ? ? []. (* path induction *)
  intros ? ? ? f [? [E0 E1]] [? [F0 F1]] [phi [p q]].
  exists phi; split.
  2: exact q.
  nrefine (transport (fun X => es_prerelation (es_pushout f E0) X) _ _).
  1: exact (es_pushout_pullback_reorder f phi (E:=F0)).
  by apply IH.
Defined.

Definition rap_pushout `{Univalence} {n : nat} {B A A' : AbGroup}
  (f : A $-> A') (E F : ES n B A)
  : E ~ F -> es_pushout f E ~ es_pushout f F.
Proof.
  induction n as [| [|n] IH].
  1,2: by intros []. (* path induction *)
  apply eqrel_generator, rap_pushout_prerelation.
Defined.

(** Splicing respects the relation. *)
Definition rap_splice `{Univalence} {n : nat} {C B A : AbGroup}
  (E F : ES n B A) (S : AbSES C B)
  : E ~ F -> es_abses_splice E S ~ es_abses_splice F S.
Proof.
  destruct n as [|[|]].
  1,2: by intros []. (* path induction *)
  revert E F; apply eqrel_generator; intros E F zig.
  exists grp_homo_id; split; unfold es_abses_splice.
  - rewrite es_pullback_id; exact zig.
  - apply abses_pushout_id.
Defined.

Definition es_point_splice_abses `{Univalence} {n : nat} {C B A : AbGroup}
  (E : AbSES C B) : es_prerelation (es_abses_splice (pt : ES n B A) E) pt.
Proof.
  destruct n as [|].
  - cbn. apply abses_pushout_const.
  - exists grp_homo_const; split; unfold es_abses_splice.
    + apply es_pullback_const_zig.
    + apply abses_pushout_const.
Defined.

Definition es_splice_point_abses `{Univalence} {n : nat} {C B A : AbGroup}
  (E : ES n B A) : es_prerelation pt (es_abses_splice E (pt : AbSES C B)).
Proof.
  destruct n.
  - cbn; symmetry. apply abses_pushout_point.
  - exists grp_homo_const; split; unfold es_abses_splice.
    + nrapply es_pullback_const_zig.
    + apply abses_pushout_const.
Defined.


(** * Lemma XII.5.3 in Mac Lane *)

Definition es2_zag_fiber_inclusion `{Univalence} {C B B' A : AbGroup}
  {E : ES 1 B A} {F : ES 1 C B} {E' : ES 1 B' A} {F' : ES 1 C B'}
  (zag : es_prerelation (es_splice E' F') (es_splice E F))
  : hfiber (abses_pullback (inclusion F)) E
    -> hfiber (abses_pullback (inclusion F')) E'.
Proof.
  intros [G p]; induction p.
  destruct zag as [phi [p q]]; cbn in phi, p, q.
  pose (phi' := abses_path_pushout_inclusion_commsq phi _ _ q).
  destruct phi' as [phi' r].
  exists (abses_pullback phi' G).
  refine (abses_pullback_compose _ _ _ @ _).
  refine (abses_pullback_homotopic _ (inclusion F $o phi) _ _ @ _).
  1: symmetry; exact r.
  exact ((abses_pullback_compose _ _ _)^ @ p^).
Defined.

(* todo: try to unify this result with the previous one. *)
(** This statement works already on [es_prerelation]. *)
(* Definition es_zag_fiber_inclusion `{Univalence} {n : nat} {C B B' A : AbGroup}
  {E : ES n.+1 B A} {F : ES 1 C B} {E' : ES n.+1 B' A} {F' : ES 1 C B'}
  (zag : es_prerelation (es_abses_splice E' F') (es_abses_splice E F))
  : lfiber es_prerelation (es_pullback (inclusion F)) E
    -> lfiber es_prerelation (es_pullback (inclusion F')) E'.
Proof.
  destruct n.
  1: admit.
  (* { refine (_ o es2_zag_fiber_inclusion zag).
    apply equiv_functor_sigma_id; intro X.
    apply equiv_path_inverse. } *)
  intros [G zz].
  destruct zag as [phi [p q]]; cbn in phi, q; unfold es_abses_splice in p.
  pose (phi' := abses_path_pushout_inclusion_commsq phi _ _ q).
  destruct phi' as [phi' r].
  exists (es_pullback phi' G).
  refine (transport (fun X => es_prerelation E' X) _ _).
  { refine (_ @ (es_pullback_compose _ _ _)^).
    refine (_ @ es_pullback_homotopic (f:=inclusion F $o phi) _ _).
    2: exact r.
    exact (es_pullback_compose _ _ _). }
  etransitivity.
  1: exact p.
  apply 

  exact (zag_to_eqrel _ p).
  apply rap_pullback.
  exact zz.
Defined. *)

Definition es_zag_fiber_inclusion `{Univalence} {n : nat} {C B B' A : AbGroup}
  {E : ES n.+1 B A} {F : ES 1 C B} {E' : ES n.+1 B' A} {F' : ES 1 C B'}
  (zag : es_prerelation (es_abses_splice E' F') (es_abses_splice E F))
  : rfiber es_relation (es_pullback (inclusion F)) E
    -> rfiber es_relation (es_pullback (inclusion F')) E'.
Proof.
  destruct n.
  1: by apply es2_zag_fiber_inclusion.
  intros [G zz].
  destruct zag as [phi [p q]]; cbn in phi, q; unfold es_abses_splice in p.
  pose (phi' := abses_path_pushout_inclusion_commsq phi _ _ q).
  destruct phi' as [phi' r].
  exists (es_pullback phi' G).
  transitivity (es_pullback phi E).
  2: exact (zag_to_eqrel _ p).
  refine (transport (fun X => X ~ _) _ _).
  { refine (_ @ (es_pullback_compose _ _ _)^).
    refine (_ @ es_pullback_homotopic (f:=inclusion F $o phi) _ _).
    2: exact r.
    exact (es_pullback_compose _ _ _). }
  apply rap_pullback.
  exact zz.
Defined.

Definition es2_zig_fiber_projection `{Univalence} {C B B' A : AbGroup}
  {E : ES 1 B A} {F : ES 1 C B} {E' : ES 1 B' A} {F' : ES 1 C B'}
  (zig : es_prerelation (es_splice E F) (es_splice E' F'))
  : hfiber (abses_pushout (projection E)) F
    -> hfiber (abses_pushout (projection E')) F'.
Proof.
  intros [G p]; induction p.
  destruct zig as [phi [p q]]; cbn in phi, p, q.
  pose (phi' := abses_path_pullback_projection_commsq phi _ _ p^).
  destruct phi' as [phi' r].
  exists (abses_pushout phi' G).
  refine ((abses_pushout_compose _ _ _)^ @ _).
  refine (abses_pushout_homotopic _ (grp_homo_compose phi (projection E)) _ _ @ _).
  1: exact r.
  exact (abses_pushout_compose _ _ _ @ q).
Defined.

(** This is the family in (ii) of Lemma XII.5.3 *)
Definition es_ii_family `{Univalence} {n : nat} {C B A : AbGroup}
  : ES n.+1 B A -> ES 1 C B -> Type
  := fun E F => { alpha : { B' : AbGroup & B' $-> B }
                       & (pt ~ es_pullback alpha.2 E)
                         * (hfiber (abses_pushout alpha.2) F) }.

(* todo: try to unify this with [es2_zig_fiber_projection] *)
Definition es_zig_fiber_projection `{Univalence} {n : nat} {C B B' A : AbGroup}
  {E : ES n.+1 B A} {F : ES 1 C B} {E' : ES n.+1 B' A} {F' : ES 1 C B'}
  (zig : es_prerelation (es_abses_splice E F) (es_abses_splice E' F'))
  : es_ii_family E F -> es_ii_family E' F'.
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

(** Lemma XII.5.4 *)
Lemma XII_5_4 `{Univalence} {C B A : AbGroup} (E : ES 1 B A) (F : ES 1 C B)
  : hfiber (abses_pushout (projection E)) F <-> es_ii_family E F.
Proof.
  split.
  - intros [G p]; induction p.
    exists (middle E; projection E); split.
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

(** Lemma XII.5.5 (i) -> (ii) *)
Definition es_spliceable_rfiber_inclusion_es_ii_family `{Univalence} {n : nat}
  {C B A : AbGroup} (E : ES n.+1 B A) (F : ES 1 C B)
  : rfiber es_relation (es_pullback (inclusion F)) E -> es_ii_family E F.
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

(** Lemma XII.5.3 *)
Theorem XII_5_3 `{Univalence} {C B A : AbGroup} (E : ES 1 B A) (F : ES 1 C B)
  : TFAE3 (hfiber (abses_pullback (inclusion F)) E)
      (hfiber (abses_pushout (projection E)) F)
      (pt ~ (es_splice E F)).
Proof.
  repeat split.
  - apply abses_spliceable_hfiber_inclusion_to_hfiber_projection.
  - intros [G p]; induction p.
    exists 2%nat. (* pt <- (E (projection E) <> F) -> E <> (projection E) F *)
    refine (_; (_, inl (es_morphism_abses_zig _ _ _))).
    refine (pt; (idpath, inr _)).
    exists grp_homo_const; split; cbn.
    + refine (_ @ (abses_pullback_point _)^).
      exact (abses_pullback_projection E)^.
    + exact (abses_pushout_const G).
  - intros [n zzs].
    revert dependent B.
    induction n as [|n IH]; intros.
    + cbn in zzs.
      apply (transport (fun X : ES 2 C A =>
                          hfiber (abses_pullback (inclusion (snd X.2))) (fst X.2)) zzs); cbn.
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

(** Lemma XII.5.3 rephrased using Lemma XII.5.4. *)
Theorem XII_5_3' `{Univalence} {C B A : AbGroup} (E : ES 1 B A) (F : ES 1 C B)
  : TFAE3  (rfiber es_relation (es_pullback (inclusion F)) E)
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

Local Definition XII_5_5_family `{Univalence} {n : nat} {B A : AbGroup}
  : ES n.+2 B A -> Type.
Proof.
  intros [C [E F]].
  exact (rfiber es_relation (es_pullback (inclusion F)) E).
Defined.

(** A preliminary result for Lemma XII.5.5: given Lemma XII.5.5 at level n, we deduce (i) iff (ii) on level n+1. *)
Lemma XII_5_5_prelim `{Univalence} {n : nat}
  : (forall {C B A : AbGroup} (E : ES n.+1 B A) (F : ES 1 C B),
    TFAE3 (rfiber es_relation (es_pullback (inclusion F)) E)
      (es_ii_family E F)
      (pt ~ (es_abses_splice E F)))
    -> (forall {C B A : AbGroup} (S : ES n.+2 B A) (E : ES 1 C B),
           (rfiber es_relation (es_pullback (inclusion E)) S)
           <-> es_ii_family S E).
Proof.
  intro IH; split.
  1: apply es_spliceable_rfiber_inclusion_es_ii_family.
  destruct S as [C' [T F]].
  intros [[B' alpha] [p [E' q]]]; unfold pr2 in p, q.
  assert (T' : rfiber es_relation
                (es_pullback (inclusion (abses_pullback alpha F))) T).
  1: apply IH; exact p.
  assert (F' : hfiber (abses_pullback (inclusion E))
                 (abses_pushout (inclusion (abses_pullback alpha F)) F)).
  { apply XII_5_3.
    induction q.
    etransitivity.
    2: nrapply es_morphism_abses_relation.
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
  1: symmetry; nrapply es_morphism_abses_relation.
  exact (rap_splice _ _ _ r').
Defined.
  
Lemma XII_5_5 `{Univalence} {n : nat}
  : forall {C B A : AbGroup} (E : ES n.+1 B A) (F : ES 1 C B),
    TFAE3 (rfiber es_relation (es_pullback (inclusion F)) E)
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
    2: nrapply es_morphism_abses_relation.
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

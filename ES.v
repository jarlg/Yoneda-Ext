From HoTT Require Import Basics Types Spaces.Nat WildCat Pointed
                         AbGroups AbSES.

Require Import EquivalenceRelation.

Local Open Scope pointed_scope.
Local Open Scope type_scope.


(** * Length-n exact sequences *)

(** ** The type [ES n] of length [n] exact sequences *)

(** We define the type [ES n] of pairs of exact sequences that can be spliced (when n > 1), of which [Ext n] will be defined as a quotient by a certain equivalence relation. We could start the induction at n=1, but by starting at n=2 we get that [ES 1 B A] is definitionally [AbSES B A], which is preferable. *)
(* NB: [ES n] is not the real n-type of "length-n exact sequences," i.e., the classifying space of the category of such. Rather, it is an approximation which has the correct set-truncation. *)
Fixpoint ES' (n : nat) : AbGroup^op -> AbGroup -> Type
  := match n with
     | 0%nat => GroupHomomorphism
     | 1%nat => AbSES
     | S n => fun B A => exists M, (ES' n M A) * (AbSES B M)
     end.

Global Instance ispointed_es' (n : nat)
  : forall B A, IsPointed (ES' n B A).
Proof.
  induction n as [| [|n] IH].
  - intros; exact grp_homo_const.
  - intros; exact pt.
  - intros; exact (abgroup_trivial; (IH _ _, pt)).
Defined.

Definition ES (n : nat) : AbGroup^op -> AbGroup -> pType
  := fun B A => [ES' n B A, _].

(** *** Functoriality of [ES] *)

(** For proofs related to pushouts we have to quantify over the hypotheses to the right of [:] in order to make the induction go through. The proofs have similar structure, so an abstract approach (or tactic) is be warranted in the future. *)

(** The covariant action on [es] by pushing out. *)
Definition es_pushout `{Univalence} {n : nat}
  : forall {B A A' : AbGroup} (f : A $-> A'), ES n B A -> ES n B A'.
Proof.
  induction n as [| [|n] IH]; intros ? ? ? f.
  - exact (fun g => f $o g).
  - exact (abses_pushout f).
  - intros [M [F E]].
    exact (M; (IH _ _ _ f F, E)).
Defined.

Lemma es_pushout_id `{Univalence} {n : nat}
  : forall {B A : AbGroup} (F : ES n B A), es_pushout grp_homo_id F = F.
Proof.
  induction n as [| [|n] IH]; intros.
  - cbn. by apply equiv_path_grouphomomorphism.
  - nrapply abses_pushout_id.
  - snrapply path_sigma; only 1: reflexivity.
    (* the transport is trivial *)
    refine (path_prod' _ idpath).
    apply IH.
Defined.

Lemma es_pushout_point `{Univalence} {n : nat}
  : forall {B A A' : AbGroup} (g : A $-> A'),
    es_pushout g (pt : ES n B A) = pt.
Proof.
  induction n as [| [|n] IH]; intros ? ? ? g.
  - nrapply equiv_path_grouphomomorphism; intro b; cbn.
    apply grp_homo_unit.
  - nrapply abses_pushout_point.
  - snrapply path_sigma; only 1: reflexivity.
    refine (path_prod' _ idpath).
    apply IH.
Defined.

(** The contravariant action on [es] by pulling back. *)
Definition es_pullback `{Univalence} {n : nat}
  {B B' A : AbGroup} (g : B' $-> B)
  : ES n B A -> ES n B' A.
Proof.
  destruct n as [|[|]] ; cbn.
  - exact (fun phi => grp_homo_compose phi g).
  - exact (abses_pullback g).
  - intros [M [F E]].
    exact (M; (F, abses_pullback g E)).
Defined.

Lemma es_pullback_id `{Univalence} {n : nat}
  {B A : AbGroup} (F : ES n B A)
  : es_pullback grp_homo_id F = F.
Proof.
  induction n as [| [|n] IH].
  - by nrapply equiv_path_grouphomomorphism.
  - nrapply abses_pullback_id.
  - destruct F as [C [S E]]; cbn.
    snrapply path_sigma.
    1: reflexivity.
    unfold transport, pr2.
    exact (path_prod' idpath (abses_pullback_id E)).
Defined.

Lemma es_pullback_point `{Univalence} {n : nat}
  {B B' A : AbGroup} (f : B' $-> B)
  : es_pullback f (pt : ES n B A) = pt.
Proof.
  destruct n as [|[|]].
  - cbn. by nrapply equiv_path_grouphomomorphism.
  - nrapply abses_pullback_point.
  - snrapply path_sigma; only 1: cbn.
    1: reflexivity.
    unfold transport, es_pullback, pr2.
    exact (path_prod' idpath (abses_pullback_point _)).
Defined.

Definition es_pullback_compose `{Univalence} {n : nat}
  {B0 B1 B2 A : AbGroup} (f0 : B1 $-> B0) (f1 : B2 $-> B1)
  : es_pullback (n:=n) (A:=A) f1 o es_pullback f0 == es_pullback (f0 $o f1).
Proof.
  destruct n as [|[|]].
  - intro x; by nrapply equiv_path_grouphomomorphism.
  - cbn. nrapply abses_pullback_compose.
  - intros [M [F E]]; cbn.
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
  - intros [M [F E]]; cbn.
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
  intros F E; destruct n.
  - exact (abses_pushout F E).
  - exact (B; (F, E)).
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


(** ** The equivalence relation on [ES] *)

(** We define a relation on [ES n] whose set-quotient will be defined to be [Ext n]. *)

(** This is the relation which will generate the equivalence relation we want. *)
Definition es_zig `{Univalence} {n : nat}
  : forall {B A : AbGroup}, Relation (ES n B A).
Proof.
  induction n as [|[|n] IH]; intros B A.
  1,2: exact paths.
  intros [M [F E]] [N [Y X]].
  exact { f : M $-> N & (IH _ _ F (es_pullback f Y)) * (abses_pushout f E = X) }.
Defined.
(* NB: On the inductive step, it might seem like we should have asked for an arbitrary zig-zag relating [E] and [es_pullback f F] above. However, such zig-zags on level [n] can be encoded as zig-zags on level [n+1]. Thus the generated equivalence relation [EqRel es_zig] will be the same. Working with a single zig is simpler, so we've chosen that. (As a sanity check, the function [rap_splice] below shows that splicing respects the generated equivalence relation.) *)

Local Instance reflexive_es_zig `{Univalence} {n : nat}
  : forall B A, Reflexive (@es_zig _ n B A).
Proof.
  induction n as [| [|n] IH]; intros.
  - exact _.
  - exact (fun _ => idpath).
  - intros [M [F E]].
    exists grp_homo_id; split.
    + rewrite es_pullback_id; nrapply IH.
    + nrapply abses_pushout_id.
Defined.

(** [es_zig] is intended to assert exactly this relation. *)
Definition es_morphism_abses_zig `{Univalence} {n : nat}
  {C B B' A : AbGroup} (F : ES n B' A) (phi : B $->  B') (E : ES 1 C B)
  : es_zig
      (es_abses_splice (es_pullback phi F) E)
      (es_abses_splice F (es_pushout phi E)).
Proof.
  destruct n as [|[|]]; only 1,2: cbn.
  - nrapply abses_pushout_compose.
  - exists phi; easy.
  - exists phi.
    nrefine (_, idpath).
    nrapply reflexive_es_zig.
Defined.

(** The equivalence relation generated by [es_zig]. *)
Definition es_eqrel `{Univalence} {n : nat} {B A : AbGroup}
  : Relation (ES n B A)
  := match n with
     | 0%nat => paths
     | 1%nat => paths
     | n => EqRel es_zig
     end.

Notation "E ~ F" := (es_eqrel E F) (at level 93).

Definition es_morphism_abses_eqrel `{Univalence} {n : nat}
  {C B B' A : AbGroup} (E : ES n.+1 B' A) (phi : B $->  B') (F : ES 1 C B)
  : es_abses_splice (es_pullback phi E) F ~
      es_abses_splice E (es_pushout phi F)
  := zig_to_eqrel _ (es_morphism_abses_zig E phi F).

Global Instance reflexive_es_eqrel `{Univalence} {n : nat} {B A : AbGroup}
  : Reflexive (@es_eqrel _ n B A)
  := ltac:(destruct n as [|[|]]; exact _).

Global Instance symmetric_es_eqrel `{Univalence} {n : nat} {B A : AbGroup}
  : Symmetric (@es_eqrel _ n B A)
  := ltac:(destruct n as [|[|]]; exact _).

Global Instance transitive_es_eqrel `{Univalence} {n : nat} {B A : AbGroup}
  : Transitive (@es_eqrel _ n B A)
  := ltac:(destruct n as [|[|]]; exact _).

(** The mere equivalence relation generated by [es_zig]. *)
Definition es_meqrel `{Univalence} {n : nat} {B A : AbGroup}
  : Relation (ES n B A)
  := match n with
     | 0%nat => paths
     | 1%nat => (fun A B => tr (n:=0) A = tr B)
     | n => MEqRel es_zig
     end.

(** *** Properties of the relation [es_zig]. *)

(** Pullback preserves [es_zig]. ("rap" is for "relation ap".) *)
Definition rap_pullback `{Univalence} {n : nat} {B B' A : AbGroup} (g : B' $-> B)
  : forall (F Y : ES n B A), F ~ Y -> es_pullback g F ~ es_pullback g Y.
Proof.
  destruct n as [|[|]].
  1,2: by intros ? ? []. (* path induction *)
  nrapply eqrel_generator; intros F Y [phi [p q]].
  nrefine (phi; (p, _)).
  nrefine (abses_pushout_pullback_reorder _ _ _ @ _).
  by nrapply (ap (abses_pullback g)).
Defined.

(** If you pull back along [grp_homo_const], you get a zig from [pt]. *)
Lemma es_pullback_const_zig `{Univalence} {n : nat}
  : forall {B B' A : AbGroup} (E : ES n B A),
    es_zig (pt : ES n B' A) (es_pullback grp_homo_const E).
Proof.
  induction n as [| [|n] IH]; intros.
  1: symmetry; nrapply equiv_path_grouphomomorphism; intro x; apply grp_homo_unit.
  1: nrapply abses_pullback_const.
  exists grp_homo_const; split.
  + nrapply IH.
  + cbn. exact (abses_pushout_point _ @ abses_pullback_const _).
Defined.

(** To show that pushout preserves the relation we first show, by induction, that it preserves the generating relation. *)
Definition rap_pushout_zig `{Univalence} {n : nat}
  : forall {B A A' : AbGroup} (f : A $-> A') (F Y : ES n B A),
    es_zig F Y -> es_zig (es_pushout f F) (es_pushout f Y).
Proof.
  induction n as [| [|n] IH].
  1,2: by intros ? ? ? ? ? ? []. (* path induction *)
  intros ? ? ? f [? [F0 F1]] [? [Y0 Y1]] [phi [p q]].
  exists phi; split.
  2: exact q.
  nrefine (transport (fun E => es_zig (es_pushout f F0) E) _ _).
  1: exact (es_pushout_pullback_reorder f phi (E:=Y0)).
  by apply IH.
Defined.

Definition rap_pushout `{Univalence} {n : nat} {B A A' : AbGroup}
  (f : A $-> A') (F Y : ES n B A)
  : F ~ Y -> es_pushout f F ~ es_pushout f Y.
Proof.
  induction n as [| [|n] IH].
  1,2: by intros []. (* path induction *)
  apply eqrel_generator, rap_pushout_zig.
Defined.

(** Splicing respects the relation. *)
Definition rap_splice `{Univalence} {n : nat} {C B A : AbGroup}
  (F Y : ES n B A) (E : AbSES C B)
  : F ~ Y -> es_abses_splice F E ~ es_abses_splice Y E.
Proof.
  destruct n as [|[|]].
  1,2: by intros []. (* path induction *)
  revert F Y; apply eqrel_generator; intros F Y zig.
  exists grp_homo_id; split; unfold es_abses_splice.
  - rewrite es_pullback_id; exact zig.
  - apply abses_pushout_id.
Defined.

Definition es_point_splice_abses `{Univalence} {n : nat} {C B A : AbGroup}
  (E : AbSES C B) : es_zig (es_abses_splice (pt : ES n B A) E) pt.
Proof.
  destruct n as [|].
  - cbn. apply abses_pushout_const.
  - exists grp_homo_const; split; unfold es_abses_splice.
    + apply es_pullback_const_zig.
    + apply abses_pushout_const.
Defined.

Definition es_splice_point_abses `{Univalence} {n : nat} {C B A : AbGroup}
  (F : ES n B A) : es_zig pt (es_abses_splice F (pt : AbSES C B)).
Proof.
  destruct n.
  - cbn; symmetry. apply abses_pushout_point.
  - exists grp_homo_const; split; unfold es_abses_splice.
    + nrapply es_pullback_const_zig.
    + apply abses_pushout_const.
Defined.

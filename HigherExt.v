From HoTT Require Import Basics Types Pointed Spaces.Nat Truncations HProp
  AbGroups AbSES WildCat Modalities.ReflectiveSubuniverse
  Colimit TruncType ExactSequence.

Require Import EquivalenceRelation ES XII_5.

Local Open Scope pointed_scope.
Local Open Scope type_scope.

Definition Ext1 := Ext.
Definition Ext1' := Ext'.

(** * Higher Ext groups *)

(** The unpointed type. *)
Definition Ext' `{Univalence} (n : nat) (B A : AbGroup) : Type
  := match n with
     | 0%nat => GroupHomomorphism B A
     | 1%nat => Ext B A
     | n => Quotient (@es_meqrel _ n B A)
     end.

Global Instance ispointed_Ext' `{Univalence} (n : nat) (B A : AbGroup)
  : IsPointed (Ext' n B A)
  := match n with 0%nat => grp_homo_const | 1%nat => pt | _ => class_of _ pt end.

Global Instance ishset_Ext' `{Univalence} (n : nat) (B A : AbGroup)
  : IsHSet (Ext' n B A) := ltac:(destruct n as [|[|]]; exact _).

(** The definition of Ext as a pointed type. *)
Definition Ext `{Univalence} (n : nat) (B A : AbGroup) : pType
  := Build_pType (Ext' n B A) _.

(** The natural projection map from [ES n] to [Ext n]. *)
Definition es_in `{Univalence} {n : nat} {B A : AbGroup}
  : ES n B A -> Ext n B A
  := match n with 0%nat => idmap | 1%nat => tr | n => class_of _ end.

(** TODO use this throughout! *)
Definition es_zig_to_path `{Univalence} {n : nat}
  {B A : AbGroup} (E F : ES n B A)
  : es_zig E F -> (es_in E = es_in F).
Proof.
  destruct n as [|[|]].
  - exact idmap.
  - exact (ap tr).
  - intro rho; apply qglue.
    by apply zig_to_meqrel.
Defined.

Definition es_zag_to_path `{Univalence} {n : nat}
  {B A : AbGroup} (E F : ES n B A)
  : es_zig F E -> (es_in E = es_in F).
Proof.
  destruct n as [|[|]].
  - exact (equiv_path_inverse _ _).
  - intro p; by induction p.
  - intro rho; apply qglue.
    by apply zag_to_meqrel.
Defined.

(** *** Functoriality of [Ext n] *)

(** jarl: If we developed things in the generality of bifunctors then most things below could surely be made automatic. *)

(** The contravariant action on [Ext n] by pulling back. *)
Definition ext_pullback `{Univalence} {n : nat} {B B' A : AbGroup}
  (g : GroupHomomorphism B' B) : Ext n B A ->* Ext n B' A.
Proof.
  destruct n as [|[|]].
  - exact (fmap10 (A:=Group^op) ab_hom g A).
  - exact (fmap10 (A:=AbGroup^op) ab_ext g A).
  - srapply Build_pMap.
    { snrapply Quotient_functor.
      1: exact (es_pullback g).
      intros X Y; apply Trunc_functor.
      exact (rap_pullback g X Y). }
    apply qglue.
    by rewrite (es_pullback_point).
Defined.

Definition ext_pushout `{Univalence} {n : nat} {B A A' : AbGroup}
  (f : A $-> A') : Ext n B A ->* Ext n B A'.
Proof.
  destruct n as [|[|]].
  - exact (fmap01 (A:=Group^op) ab_hom B f).
  - exact (fmap01 (A:=AbGroup^op) ab_ext B f).
  - srapply Build_pMap.
    { snrapply Quotient_functor.
      1: exact (es_pushout f).
      intros X Y; apply Trunc_functor.
      exact (rap_pushout f X Y). }
    apply qglue.
    by rewrite (es_pushout_point f).
Defined.
  
(** We can splice with a short exact sequence. *)
Definition ext_abses_splice `{Univalence} {n : nat} {B A M : AbGroup}
  : Ext n A M -> AbSES B A -> Ext n.+1 B M.
Proof.
  destruct n.
  { intros phi E; apply tr.
    exact (fmap01 (AbSES' : AbGroup^op -> AbGroup -> Type) B phi E). }
  intros E S; revert E.
  destruct n.
  { apply Trunc_rec; intro E.
    exact (es_in (es_abses_splice (E : ES 1 A M) S)). }
  snrapply Quotient_functor.
  1: exact (fun E => (A; (E, S))).
  intros X Y; apply Trunc_functor.
  exact (rap_splice X Y S).
Defined.

(** The connecting map. *)
Definition abses_ext_splice `{Univalence} {n : nat}
  {B A M : AbGroup} (E : AbSES B A)
  : Ext n A M ->* Ext n.+1 B M.
Proof.
  srapply (Build_pMap _ _ (fun S => ext_abses_splice S E)).
  destruct n as [|[|]].
  { apply (ap tr); cbn.
    apply abses_pushout_const. }
  all: apply qglue;
    apply zig_to_meqrel;
    exact (es_point_splice_abses E).
Defined.

Definition abses_ext_splice_pt `{Univalence} {n : nat}
  {B A M : AbGroup}
  : abses_ext_splice (n:=n) (M:=M) (pt : AbSES B A) ==* pconst.
Proof.
  apply phomotopy_homotopy_hset.
  destruct n as [|[|]].
  1: intro.
  2: rapply Trunc_ind; intros.
  3: rapply Quotient_ind_hprop; intros.
  all: rapply es_zag_to_path;
    rapply es_splice_point_abses.
Defined.

(* The mac lane move. *)
Definition abses_ext_splice_reorder'' `{Univalence} {n : nat}
  {C B B' A : AbGroup} (E : Ext n B' A)
  (phi : B $->  B') (F : ES 1 C B)
  : ext_abses_splice (ext_pullback phi E) F
    = ext_abses_splice E (abses_pushout phi F).
Proof.
  destruct n as [|[|]].
  1: cbn; apply ap, abses_pushout_compose.
  1,2: revert E.
  1: rapply Trunc_ind; intros.
  2: rapply Quotient_ind_hprop; intros.
  all: rapply es_zig_to_path;
    nrapply es_morphism_abses_zig.
Defined.

Definition abses_ext_splice_reorder `{Univalence} {n : nat}
  {B A A' M : AbGroup} (E : AbSES B A) (f : A $-> A')
  : abses_ext_splice (n:=n) (M:=M) E o* ext_pullback f
    ==* abses_ext_splice (abses_pushout f E).
Proof.
  apply phomotopy_homotopy_hset.
  intro; apply abses_ext_splice_reorder''.
Defined. (** TODO Clean up *)

(** Isn't this pretty much definitional? *)
Definition abses_ext_splice_reorder' `{Univalence} {n : nat}
  {B B' A M : AbGroup} (E : AbSES B A) (g : B' $-> B)
  : (ext_pullback g o* abses_ext_splice (n:=n) (M:=M) E)
      ==* abses_ext_splice (abses_pullback g E).
Proof.
  apply phomotopy_homotopy_hset.
  destruct n as [|[|]].
  { intro; cbn. apply ap.
    symmetry; apply abses_pushout_pullback_reorder. }
  1: { rapply Trunc_ind; intro.
       rapply es_zig_to_path.
       cbn. (* trivial. *)
Admitted.
                                    

(** Towards Lemma XII.5.5 *)

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

(** Now we can show Lemma XII.5.5 for Ext as well. *)

(* todo: let [E] be an extension *)
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

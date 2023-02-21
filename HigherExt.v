From HoTT Require Import Basics Types Pointed Spaces.Nat Truncations
                         AbGroups AbSES WildCat.

Require Import EquivalenceRelation ES.

Local Open Scope pointed_scope.
Local Open Scope type_scope.

Definition Ext1 := Ext.
Definition Ext1' := Ext'.

(** * Higher Ext groups *)

(** We define [Ext n] as the quotient of [ES n] by [es_meqrel]. *)
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

Definition es_zig_to_path `{Univalence} {n : nat}
  {B A : AbGroup} (F Y : ES n B A)
  : es_zig F Y -> (es_in F = es_in Y).
Proof.
  destruct n as [|[|]].
  - exact idmap.
  - exact (ap tr).
  - intro rho; apply qglue.
    by apply zig_to_meqrel.
Defined.

Definition es_zag_to_path `{Univalence} {n : nat}
  {B A : AbGroup} (F Y : ES n B A)
  : es_zig Y F -> (es_in F = es_in Y).
Proof.
  destruct n as [|[|]].
  - exact (equiv_path_inverse _ _).
  - intro p; by induction p.
  - intro rho; apply qglue.
    by apply zag_to_meqrel.
Defined.

(** *** Functoriality of [Ext n] *)

(** We descend the operations we need from [ES n] to [Ext n]. *)

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
  
(** Splicing with aa short exact sequence. *)
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

(** This is the connecting map in the long exact sequence. It's [ext_abses_splice] with the arguments reversed, but we also need that it's a pointed map. *)
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

(** By definition of [es_zig], we can move a pullback to a pushout across a splice. *)
Definition splice_pullback_to_pushout `{Univalence} {n : nat}
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

Definition splice_pullback_to_pushout_phomotopy `{Univalence} {n : nat}
  {B A A' M : AbGroup} (E : AbSES B A) (f : A $-> A')
  : abses_ext_splice (n:=n) (M:=M) E o* ext_pullback f
    ==* abses_ext_splice (abses_pushout f E).
Proof.
  apply phomotopy_homotopy_hset.
  intro; apply splice_pullback_to_pushout.
Defined.

(** Splicing commutes with with pullbacks. *)
Definition splice_pullback_commute `{Univalence} {n : nat}
  {B B' A M : AbGroup} (E : AbSES B A) (g : B' $-> B)
  : (ext_pullback g o* abses_ext_splice (n:=n) (M:=M) E)
      ==* abses_ext_splice (abses_pullback g E).
Proof.
  apply phomotopy_homotopy_hset.
  destruct n as [|[|]].
  { intro; cbn. apply ap.
    symmetry; apply abses_pushout_pullback_reorder. }
  - by rapply Trunc_ind.
  - by rapply Quotient_ind_hprop.
Defined.


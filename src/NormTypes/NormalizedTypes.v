Require Import NormTypes.irreleventQuantifiers.
(* A normalizeed type is the image of a type A by a function nf: A ->
   B. nf is not supposed to beinjective so this defines a quotient on
   A. *)
Section Norm.
  Context {A B:Type}.
  Variable nf: A -> B.
  Definition Norm := { b | irr (iexists a, b = nf a) }. (* irrelevant existential proof. *)
  (* Given a:A, its equivalence class is given by (nf a). *)
  Definition class (a:A):Norm := isig_intro _ (nf a) (iex_intro _ a eq_refl).

  Definition extract (x:Norm): B :=
    match x with
    | isig_intro _ res _ => res
    end.

  Definition lift (X:Type) (f:B -> X): Norm -> X := fun a:Norm => f (extract a).

  Definition liftR:= fun (R:B -> B -> Prop) => fun a b:Norm => R (extract a) (extract b).

  (* Lemma facile (P:B -> Prop):     forall b: B, P b -> forall a:A, nf a = b -> lift _ P (class a). *)
  Lemma facile: forall (C:Type) (f:B -> C),
    forall b: B, forall a:Norm, extract a = b -> lift _ f a = f b.
  Proof.
    intros C f b a H. 
    unfold lift.
    rewrite H.
    reflexivity.
  Qed.

  Lemma facile2C (C:Type) (f:B -> B -> C):
    forall b b': B, forall a a':Norm, extract a = b ->
                                      extract a' = b'
                                      -> lift _ ((lift _ f a)) a' = f b b'.
  Proof.
    intros b b' a a' H H0. 
    erewrite facile.
    2:eassumption.
    erewrite facile.
    2:eassumption.
    reflexivity.
  Qed.


  Lemma facile2 (P:B -> B -> Prop):
    forall b b': B, P b b' -> forall a a':Norm, extract a = b ->
                                                extract a' = b'
                                                -> lift _ ((lift _ P a)) a'.
  Proof.
    intros b b' H a a' H0 H1. 
    erewrite facile2C;eauto.
  Qed.


  Definition eqS := (liftR eq).

  Lemma eqS_eq: forall x y, eqS x y -> eq x y.
  Proof.
    intros x y H.
    unfold eqS,liftR in *.
    destruct x;destruct y.
    simpl in *.
    subst.
    reflexivity.
  Qed.

End Norm.



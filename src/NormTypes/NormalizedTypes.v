Require Import NormTypes.irreleventQuantifiers.
(* A normalizeed type is the image of a type A by a function nf: A ->
   B. nf is not supposed to beinjective so this defines a quotient on
   A. *)
Section Norm.
  Context {A B:Type}.
  Variable nf: A -> B.
  Definition Norm := { b | ! (exists a, ! b = nf a) }. (* irrelevant existential proof. *)
  (* Given a:A, its equivalence class is given by (nf a). *)
  Definition class (a:A):Norm := isig_intro _ (nf a) (iex_intro _ a eq_refl).

  Definition extract (x:Norm): B :=
    match x with
    | isig_intro _ res _ => res
    end.

  Definition lift (X:Type) (f:B -> X): Norm -> X := fun a:Norm => f (extract a).

  Definition liftR:= fun (R:B -> B -> Prop) => fun a b:Norm => R (extract a) (extract b).

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



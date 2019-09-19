Require Import NormTypes.NormalizedTypes.
Require Import NormTypes.irreleventQuantifiers.
Require Import NPeano Omega.

Module Mod3_byHand.
  Definition mod3 (n:nat) := (Nat.modulo n 3).

  (* Notation "'class' nf a" := (isig_intro _ (nf a) (iex_intro _ a eq_refl)) (at level 100). *)
  Check (class mod3 3).
  Check (class mod3 0).

  Notation "'[[' x ']N/3N]'" := (class mod3 x) (at level 200).
  Notation "'N/3N'" := (Norm mod3) (at level 200).
  Check [[3]N/3N].
  Check [[0]N/3N].


  Lemma eq_3_0: [[3]N/3N] = [[0]N/3N].
  Proof.
    reflexivity.
  Qed.

  Lemma eq_3_x: forall x , [[x]N/3N] = [[3+x]N/3N].
  Proof.
    intros x. 
    apply eqS_eq.
    simpl.
    unfold class.
    unfold eqS, liftR.
    simpl.
    replace (S (S (S x))) with (x+1*3);try omega.
    unfold mod3.
    rewrite (Nat.mod_add x 1 3);auto.
  Qed.

  Lemma eq_3_mult_x: forall x , [[0]N/3N] = [[3*x]N/3N].
  Proof.
    intros x.
    apply eqS_eq.
    simpl.
    unfold class.
    unfold eqS, liftR.
    simpl.
    replace (x + (x + (x + 0))) with (0+x*3);try omega.
    unfold mod3.

    rewrite (Nat.mod_add 0 x 3);auto.
  Qed.

  Definition add1:= @lift _ _ mod3 _ (fun x:nat => [[ x +1 ]N/3N]).
  Eval compute in (add1 ([[3]N/3N])).

  Notation "[[ x ]]" := (isig_intro _ x _) (only printing, at level 200).
  Eval compute in (add1 ([[3]N/3N])).
  Eval compute in (add1 ([[4]N/3N])).

  Definition add:=
    @lift _ _ mod3 _ (fun n:nat =>
                            @lift _ _ mod3 _ (fun x:nat => [[ x + n ]N/3N])).

  Eval compute in (add ([[2]N/3N]) ([[2]N/3N])).

  (* Definition toint (x:N/3N):nat := extract _ x. *)
  (* Definition fromint (x:nat):N/3N := class _ x. *)

End Mod3_byHand.


Module Mod3_usingLibMod.

  Definition mod3 (n:nat) := (Nat.modulo n 3).
  Definition NMod3 := Norm mod3.

  Check (class mod3 3).
  Check (class mod3 0).

  Notation "'[[' x ']Z/3Z]'" := (class mod3 x) (at level 200).
  Notation "A == B" := (@eqS _ _ mod3 A B) (at level 200).
  Check [[3]Z/3Z].
  Check [[0]Z/3Z].


  Lemma eq_3_0: [[3]Z/3Z] = [[0]Z/3Z].
  Proof.
    reflexivity.
  Qed.


  Lemma eq_3_x: forall x , [[x]Z/3Z] = [[3+x]Z/3Z].
  Proof.
    intros x.
    apply eqS_eq.
    simpl.
    unfold class.
    unfold eqS, liftR.
    simpl.
    replace (S (S (S x))) with (x+1*3);try omega.
    unfold mod3.
    rewrite (Nat.mod_add x 1 3);auto.
  Qed.

End Mod3_usingLibMod.

(* Example: Z/3Z. *)
Require Import ZArith.

Module Mod3Z.

  Open Scope Z_scope.

  Definition mod3Z (z:Z) := (Z.modulo z 3%Z).
  Definition NMod3Z := Norm mod3Z.

  Check (class mod3Z 3).
  Check (class mod3Z 0).

  Notation "'[[' x ']Z/3Z]'" := (class mod3Z x) (at level 200).
  Check [[3]Z/3Z].
  Check [[0]Z/3Z].


  Lemma eq_3_0Z: [[3]Z/3Z] = [[0]Z/3Z].
  Proof.
    reflexivity.
  Qed.

  Lemma eq_3_x: forall x , [[x]Z/3Z] = [[3+x]Z/3Z].
  Proof.
    intros x.
    apply eqS_eq.
    lazy beta delta -[Z.add Z.modulo] iota.
    replace (3+x) with (x+1*3);try omega.
    rewrite (Z.mod_add x 1 3);auto.
    omega.
  Qed.
End Mod3Z.


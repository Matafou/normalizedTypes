Require Import NormTypes.NormalizedTypes.
Require Import NPeano Omega.

Module Mod3_byHand.
  Fixpoint mod3 (n:nat) :=
    match n with
    | S (S (S n')) => mod3 n'
    | _ => n
    end.
  Definition NMod3 := Norm mod3.

  Check (class mod3 3).
  Check (class mod3 0).

  Notation "'[[' x ']Z/3Z]'" := (class mod3 x) (at level 200).
  Check [[3]Z/3Z].
  Check [[0]Z/3Z].


  Lemma eq_3_0: [[3]Z/3Z] = [[0]Z/3Z].
  Proof.
    reflexivity.
  Qed.

  Lemma eq_3_x: forall x , [[x]Z/3Z] = [[3+x]Z/3Z].
  Proof.
    simpl.
    reflexivity.
  Qed.
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

Module Mod3Z.

  (* Example: Z/3Z. *)
  Require Import ZArith.
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


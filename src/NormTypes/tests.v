Require Import NormTypes.NormalizedTypes.
Require Import NPeano Omega.
(* Example: nat/3nat. *)
(* Definition mod3 (n:nat) := (Nat.modulo n 3). *)

(*
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

Import irreleventQuantifiers.
Inductive SFalse: SProp:=.

Goal iex IsSucc -> SFalse.
  intro.
  destruct H.

*)



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








Lemma foo:
  exist
    (fun b : nat =>
     ex
       (fun a : nat =>
        b = match snd (Nat.divmod a 2 0 2) with
            | 0 => 2
            | 1 => 1
            | S (S _) => 0
            end)) 0
    (ex_intro
       (fun a : nat =>
        0 = match snd (Nat.divmod a 2 0 2) with
            | 0 => 2
            | 1 => 1
            | S (S _) => 0
            end) 3 eq_refl)
  =
  exist
    (fun b : nat =>
     ex
       (fun a : nat =>
        b = match snd (Nat.divmod a 2 0 2) with
            | 0 => 2
            | 1 => 1
            | S (S _) => 0
            end)) 0
    (ex_intro
       (fun a : nat =>
        0 = match snd (Nat.divmod a 2 0 2) with
            | 0 => 2
            | 1 => 1
            | S (S _) => 0
            end) 0 eq_refl).
  simpl.
Abort.


Lemma eq_3_0: [[3]Z/3Z] = [[0]Z/3Z].
Proof.
  unfold class.
  unfold mod3.
  simpl.
  reflexivity.
Qed.
Lemma eq_3_x: forall x , [[x]Z/3Z] = [[3+x]Z/3Z].
Proof.
  intro.
  
  simpl.
  unfold class.
Check ((irreleventQuantifiers.iex_intro (fun a : nat => mod3 x = mod3 a) x eq_refl)=
      (irreleventQuantifiers.iex_intro (fun a : nat => mod3 (S (S (S x))) = mod3 a)
       (S (S (S x))) eq_refl)).

Check  (fun x => irreleventQuantifiers.iex (fun a : nat => mod3 (S (S (S x))) = mod3 a)
       ,fun x => irreleventQuantifiers.iex (fun a : nat => mod3 x = mod3 a)).
Check  ((fun x => ex (fun a : nat => mod3 (S (S (S x))) = mod3 a))
        = (fun x => ex (fun a : nat => mod3 x = mod3 a))).



Axiom f_equal2_dep :
  forall (A1 A2 B : Type) (f : A1 -> A2 -> B) (x1 y1 : A1) (x2 y2 : A2),
    x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.

Lemma eq_3_x: forall x , [[x]Z/3Z] = [[3+x]Z/3Z].
Proof.
  intro.
  
  simpl.
  unfold class.

Check ((irreleventQuantifiers.iex_intro (fun a : nat => mod3 x = mod3 a) x eq_refl)
       = (irreleventQuantifiers.iex_intro (fun a : nat => mod3 (S (S (S x))) = mod3 a)
                                          (S (S (S x))) eq_refl)).

  exact
    (@f_equal2
       _ _ (@Norm nat nat mod3) (@irreleventQuantifiers.isig_intro nat (fun b : nat => @irreleventQuantifiers.iex nat (fun a : nat => @eq nat b (mod3 a))))

        (mod3 x)
        (mod3 (S (S (S x))))
        (@irreleventQuantifiers.iex_intro nat (fun a : nat => @eq nat (mod3 x) (mod3 a))
          x (@eq_refl nat (mod3 x)))
        (@irreleventQuantifiers.iex_intro nat
          (fun a : nat => @eq nat (mod3 (S (S (S x)))) (mod3 a))
          (S (S (S x))) (@eq_refl nat (mod3 (S (S (S x))))))).

  eapply f_equal3.
  replace (S (S (S x))) with (3 + x).
  2: auto.
  replace (3+x) with (x+1*3);try omega.
  (* change ((x + 1 * 3) mod 3) with (x mod 3). *)
  rewrite (Nat.mod_add x 1 3).

  eapply f_equal.
  simpl.
  induction x.
  - reflexivity.
  - 
Qed.


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



Require Import Recdef.
Function plus3 n :=
  match n with
  | S(S(S n')) => plus3 n'
  | _ => n
  end.

Lemma eq_3plusx_x: forall x, [[3 + x]Z/3Z] = [[x]Z/3Z].
Proof.
  intro x.
  simpl.
  
  induction x , (plus3 x) using plus3_ind.

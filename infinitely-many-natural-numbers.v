(*********************************************************)
(* Theorem: there exist infinitely many natural numbers. *)
(*********************************************************)

Require Import Arith Omega List.


(*******)
(* Sum *)
(*******)

Fixpoint sum (l : list nat) : nat :=
  match l with
    | nil => O
    | x::l' => x + sum l'
  end.

Lemma sum_le : forall l : list nat, forall x : nat, In x l -> x <= sum l.
Proof.
  intros l x Hin. induction l ; destruct Hin ; simpl.
  rewrite H. omega. apply IHl in H. omega.
Qed.


(***********)
(* Maximum *)
(***********)

Fixpoint maximum (l : list nat) : nat :=
  match l with
    | nil => O
    | x::l' => max x (maximum l')
  end.

Lemma maximum_le : forall l : list nat, forall x : nat, In x l -> x <= maximum l.
Proof.
  intros l x Hin. induction l ; destruct Hin.
  rewrite <- H ; simpl ; apply Max.le_max_l. simpl.
  apply IHl in H. assert (trans := Max.le_max_r a (maximum l)). omega.
Qed.


(***********)
(* Product *)
(***********)

Fixpoint product (l : list nat) : nat :=
  match l with
    | nil => 1
    | x::l' => match x with O => product l' | S _ => x * product l' end
  end.

Lemma product_lt_0 : forall l : list nat, product l > 0.
Proof.
  intro l. induction l ; simpl ; auto.
  destruct a. exact IHl. simpl.
  apply lt_le_trans with (n := 0) (m := product l) (p := product l + a * product l).
  exact IHl. auto with arith.
Qed.

Corollary product_lt_x : forall l : list nat, forall x : nat, x <= x * product l.
Proof.
  intros l x. rewrite <- (Nat.mul_1_r x) at 1. apply Nat.mul_le_mono_l. apply product_lt_0.
Qed.

Lemma product_le_x : forall l : list nat, forall x : nat, x <= product (x::l).
Proof.
  intros l x. destruct x. omega. simpl. rewrite Nat.add_comm.
  assert (foo := Nat.mul_succ_l x (product l)).
  rewrite <- foo. apply product_lt_x.
Qed.

Lemma product_le_l : forall l : list nat, forall x : nat, product l <= product (x::l).
Proof.
  intros l x. destruct x; simpl. omega. rewrite Nat.add_comm.
  rewrite <- (plus_O_n (product l)) at 1. apply plus_le_compat_r.
  rewrite <- (Nat.mul_0_l 1). apply Nat.mul_le_mono ; [omega | apply product_lt_0].
Qed.

Corollary product_max : forall l : list nat, forall x : nat, max x (product l) <= product (x::l).
Proof.
  intros l x. apply Nat.max_lub ; [apply product_le_x | apply product_le_l].
Qed.

Lemma product_le : forall l : list nat, forall x : nat, In x l -> x <= product l.
Proof.
  intros l x Hin. induction l. elim Hin. destruct x.
  exact (lt_le_weak 0 (product (a::l)) (product_lt_0 (a::l))). destruct Hin.
  rewrite H. apply Nat.max_lub_l with (n := S x) (m := product l) (p := product (S x::l)) ; exact (product_max l (S x)).
  apply le_trans with (n := S x) (m := product l) (p := product (a::l)). exact (IHl H).
  apply Nat.max_lub_r with (n := a) (m := product l) (p := product (a::l)) ; exact (product_max l (a)).
Qed.


(********************************************************************************)
(* Theorem: for all list l, there exists a natural integer N which is not in l. *)
(********************************************************************************)

Theorem exists_N_not_in_l : forall l : list nat, exists N : nat, ~In N l.
Proof.
  intro l.
  (* set (N := S (sum l)). exists N. intro.
  assert (absurd := sum_le l N H). *)
  (* set (N := S (product l)). exists N. intro.
  assert (absurd := product_le l N H). *)
  set (N := S (maximum l)). exists N. intro.
  assert (absurd := maximum_le l N H).
  unfold N in absurd. omega.
Qed.

(***********************************************************)
(* Corollary: there exist infinitely many natural numbers. *)
(***********************************************************)

(* Direct proof *)

Corollary infinitely_many_natural_numbers : ~(exists l : list nat, forall x : nat, In x l).
Proof.
  intro H ; destruct H as [l Hin].
  set (Hyp := exists_N_not_in_l l). destruct Hyp as [N N_not_in_l].
  apply N_not_in_l. exact (Hin N).
Qed.

(* Proof 2: application of a general fact *)

Lemma forall_not_exists : forall X Y : Set, forall R : Y -> X -> Prop, (forall x : X, exists y : Y, not (R y x)) -> not (exists x : X, forall y : Y, R y x).
Proof.
  intros. intro H0 ; destruct H0.
  set (foo := H x). destruct foo as [y H1]. exact (H1 (H0 y)).
Qed.

Corollary infinitely_many_natural_numbers_proof_2 : ~(exists l : list nat, forall x : nat, In x l).
Proof.
  exact (forall_not_exists (list nat) nat (In (A := nat)) exists_N_not_in_l).
Qed.


(*******************************************************)
(* Theorem: there exist infinitely many prime numbers. *)
(*******************************************************)
(* Euclid's proof *)
(******************)


Require Import Arith Omega.


(**********************************************)
(* Two lemmas about multiplication and order. *)
(**********************************************)

Lemma mult_gt_0 : forall x y : nat, x * y > 0 <-> x > 0 /\ y > 0.
Proof.
  intros x y. destruct x. omega. destruct y. omega.
  split. omega. intros _. simpl. apply gt_Sn_O.
Qed.

Lemma mult_le_r : forall x y : nat, y > 0 -> x <= x * y.
Proof.
  intros x y H. rewrite <- (mult_1_r x) at 1. apply mult_le_compat_l. exact H.
Qed.


(*****************)
(* Divisibility. *)
(*****************)

Definition div (x y : nat) := exists z : nat, y = x * z.

Notation "x & y" := (div x y) (at level 70).

(* Four lemmas about divisibility. *)

Lemma div_le : forall x y : nat, y > 0 -> x & y -> x <= y.
Proof.
  intros x y. intros Hy [z Hdiv].
  subst. apply mult_le_r. rewrite mult_gt_0 in Hy. tauto.
Qed.

Lemma div_mult_l : forall x y z : nat, x & y -> x & z * y.
Proof.
  intros x y z [z' Hdiv]. subst. exists (z * z'). ring.
Qed.

Lemma div_minus : forall x y z : nat, x & y -> x & z -> x & y - z.
Proof.
  intros x y z [z1 Hdiv_xy] [z2 Hdiv_xz]. subst. exists (z1 - z2).
  rewrite <- mult_minus_distr_l. reflexivity.
Qed.

Lemma div_trans : forall x y z : nat, x & y -> y & z -> x & z.
Proof.
  intros x y z [z1 Hdiv_xy] [z2 Hdiv_yz]. exists (z1 * z2). subst. ring.
Qed.


(*****************************************)
(* Product of a list of natural numbers. *)
(*****************************************)

Require Import List.

Fixpoint prod (l : list nat) : nat :=
  match l with
    | nil => 1
    | x::l' => x * prod l'
  end.

(* Three lemmas about product and order. *)

Lemma prod_gt_0 : forall l : list nat, ~In 0 l <-> prod l > 0.
Proof.
  induction l; simpl. omega. rewrite mult_gt_0. intuition.
Qed.

Lemma prod_div : forall l : list nat, forall x : nat, In x l -> x & prod l.
Proof.
  intros l x. induction l; simpl. tauto.
  intros [Ha|Hx]. subst. exists (prod l). reflexivity.
  destruct (IHl Hx) as [z Hdiv]. rewrite Hdiv. exists (a * z). ring.
Qed.

Corollary prod_le_x : forall l : list nat, forall x : nat, ~In 0 l -> In x l -> x <= prod l.
Proof.
  intros l x H0 Hx.
  apply prod_gt_0 in H0.
  exact (div_le x (prod l) H0 (prod_div l x Hx)).
Qed.


(******************)
(* Prime numbers. *)
(******************)

Definition prime (p : nat) := p >= 2 /\ (forall x : nat, x & p -> x = 1 \/ x = p).

Lemma zero_is_not_prime : ~prime 0.
Proof.
  unfold prime. omega.
Qed.

(* We use classical reasoning to simplify the proof a little bit. *)
Require Import Classical.

Lemma nontrivial_divisor : forall x : nat, x >= 2 -> ~prime x -> exists y, y >= 2 /\ y < x /\ y & x.
Proof.
  intros x x_le_2 x_is_not_prime.
  apply not_and_or in x_is_not_prime. intuition. apply not_all_ex_not in H.
  destruct H as [d Hd]. apply imply_to_and in Hd. destruct Hd as [H1 H2].
  apply not_or_and in H2.
  assert (p_lt_x : d < x). apply div_le in H1. omega. omega.
  assert (p_ge_2 : d >= 2). destruct H2 as [Hd_not_1 Hd_not_x].
  destruct (eq_nat_dec d 0). subst. destruct H1. omega. omega. clear H2.
  exists d. tauto.
Qed.

Lemma prime_divisor : forall x : nat, x >= 2 -> exists p, prime p /\ p & x.
Proof.
  intro x. pattern x. apply lt_wf_ind. clear x. intros n H n_le_2.
  (* Law of excluded middle: x is prime or x is not prime. *)
  destruct (classic (prime n)) as [n_is_prime | n_is_not_prime].
  (* n is prime *)
  exists n. split ; [assumption | exists 1 ; ring].
  (* n is not prime *)
  set (divisor := nontrivial_divisor n n_le_2 n_is_not_prime).
  destruct divisor as [d Hdiv]. destruct Hdiv as [d_le_2 [d_lt_n Hdn]].
  destruct (H d d_lt_n d_le_2) as [p Hyp].
  exists p. split. tauto. apply div_trans with (x := p) (y := d) (z := n) ; tauto.
Qed.

Theorem primes_are_infinite : ~ (exists l : list nat, forall x : nat, prime x <-> In x l).
Proof.
  intros [l all_primes_in_l]. set (n := S (prod l)).
  (* We prove that n is prime. *)
    assert (n_is_prime : prime n). split.
    (* n >= 2 *)
    apply le_n_S. apply lt_le_S. apply prod_gt_0.
    rewrite <- all_primes_in_l. apply zero_is_not_prime.
    (* We now prove that assuming that there is a divider a of n that is
    different from 1 and n leads to a contradiction. *)
    intros a a_div_n. destruct (eq_nat_dec a 1). tauto.
    right. destruct (eq_nat_dec a n). assumption. apply False_rec.
    (* We prove that a is >= 2. *)
    assert (a_ge_2 : a >= 2). destruct a_div_n as [q hn].
    destruct (eq_nat_dec a 0). subst. rewrite mult_0_l in hn. omega. omega.
    (* Hence, a has a prime divider p. *)
    destruct (prime_divisor a a_ge_2) as [p [p1 p2]].
    (* By transitivity, p divides n. *)
    generalize (div_trans p a n p2 a_div_n) ; intro p_div_n.
    (* Since all primes are in l, p is in l and p divides prod l. *)
    assert (p_in_l : In p l). rewrite <- all_primes_in_l. assumption.
    apply (prod_div l p) in p_in_l.
    (* Thus p divides n - (prod l) = 1. *)
    generalize (div_minus p n (prod l) p_div_n p_in_l).
    unfold n. rewrite <- minus_Sn_m, minus_diag. 2: reflexivity.
    (* Therefore p = 1 but 1 is not prime. Hence, n is prime. *)
    intro p_div_1. apply div_le in p_div_1. 2: omega. unfold prime in p1. omega.
  (* We now prove that n is not in l. *)
  rewrite all_primes_in_l in n_is_prime.
  assert (zero_not_in_l : ~In 0 l).
  rewrite <- all_primes_in_l. exact zero_is_not_prime.
  generalize (prod_le_x l n zero_not_in_l n_is_prime).
  unfold n. omega.
Qed.

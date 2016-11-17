(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*   Author: Yu Guo <aciclo@gmail.com>                                        *)
(*                                        Computer Science Department, USTC   *)
(*                                                                            *)
(*           Hui Zhang <sa512073@mail.ustc.edu.cn>                            *)
(*                                     School of Software Engineering, USTC   *)
(*                                                                            *)
(* ************************************************************************** *)


Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. auto. Qed.

Axiom FFF : False.
Ltac skip := destruct FFF.

Ltac inv H := inversion H; clear H; subst.

Ltac caseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

Lemma eq_sym : forall {A: Type} (n m : A), n = m -> m = n.
Proof.
  intros.
  subst; trivial.
Qed.
Implicit Arguments eq_sym [A n m].

(* deprecated, use "neq_sym" instead *)
Lemma neq_refl : forall n m : nat, n <> m -> m <> n.
Proof.
  intros.
  intro HF; subst; auto.
Qed.
Implicit Arguments neq_refl [n m].

Lemma neq_sym : forall {A: Type} (n m : A), n <> m -> m <> n.
Proof.
  intros.
  intro HF; subst; auto.
Qed.
Arguments neq_sym {A} {n} {m} _ _.


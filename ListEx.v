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

Require Import LibEx.
Require Import Lists.List.
Require Import Arith.
Require Import bnat.
Require Import Omega.

Set Implicit Arguments.
Unset Strict Implicit.

Fixpoint list_append {A: Set} (l: list A) (a: A) : list A :=
  match l with
    | nil => cons a nil
    | cons x l' => cons x (list_append l' a)
  end.

Fixpoint list_none_list {A: Set} (n: nat) : list (option A) :=
  match n with 
    | O => nil
    | S n => cons None (list_none_list n)
  end.

Fixpoint list_repeat_list {A: Set} (n : nat) (elem : A) : list A :=
  match n with
    | O => nil
    | S n' => cons elem (list_repeat_list n' elem)
  end.

Fixpoint list_get {A: Set} (l: list A) (i: nat) : option A :=
  match i, l with 
    | O, cons a l' => Some a
    | S i', cons a l' => list_get l' i'
    | _, _ => None
  end.

Fixpoint list_set {A: Set} (l: list A) (i: nat) (a: A): option (list A) :=
  match i, l with
    | O, cons a' l' => Some (cons a l')
    | S i', cons a' l' => 
      match list_set l' i' a with
        | None => None 
        | Some l'' => Some (cons a' l'')
      end
    | _, _ => None
  end.

Lemma list_get_list_set_eq : 
  forall {A: Set} (l: list A) (i: nat) (a: A) (l' : list A),
    list_set l i a = Some l'
    -> list_get l' i = Some a.
Proof.
  induction l.
    simpl; intros.
    destruct i.
      discriminate.
    discriminate.
  intros.
  destruct i.
  simpl in * .
  injection H.
  intro; subst l'.
  simpl.
  trivial.
  simpl in H.
  destruct (list_set l i a0) eqn:Hset; [| discriminate] .
  injection H.
  intro; subst l'.
  simpl.
  eapply IHl; eauto.
Qed.

Lemma list_get_list_set_neq : 
  forall {A: Set} (l: list A) (i i': nat) (a: A) (l' : list A),
    list_set l i a = Some l'
    -> i <> i'
    -> list_get l' i' = list_get l i'.
Proof.
  induction l.
    simpl; intros.
    destruct i.
      discriminate.
    discriminate.
  intros.
  simpl in * .
  destruct i;
    destruct i'.
    destruct (H0 (refl_equal _)).
    injection H.
    intro; subst l'.
    simpl.
    trivial.
    destruct (list_set l i a0) eqn:Hset.
    injection H.
     intro; subst l'.
    simpl.
    trivial.
    discriminate.
  destruct (list_set l i a0) eqn:Hset; [| discriminate].
  assert (Hi: i <> i').
    auto with arith.
  injection H.
  intro; subst l'.
  simpl.
  eapply IHl; eauto.
Qed.

Lemma list_get_list_set : 
  forall {A: Set} (l: list A) i (a a': A)  ,
    list_get l i = Some a
    -> exists l', list_set l i a' = Some l'.
Proof.
  induction l;  simpl; intros; auto.
    destruct i; discriminate.
  destruct i.
    exists (cons a' l).
    trivial.
  destruct (IHl i a0 a' H) as [l' Hl'].
  rewrite Hl'.
  exists (cons a l'); trivial.
Qed.

Lemma list_set_same : 
  forall {A: Set} (l: list A) i (a : A)  ,
    list_get l i = Some a
    -> list_set l i a = Some l.
Proof.
  induction l;  simpl; intros; auto.
    destruct i; discriminate.
  destruct i.
    injection H; intro; subst a0.
    trivial.
  rewrite (IHl _ _ H).
  trivial.
Qed.

Lemma list_set_list_get_rev : 
  forall {A: Set} (l: list A) (i: nat) (a: A) (l' : list A),
    list_set l i a = Some l'
    -> exists a', list_get l i = Some a'.
Proof.
  induction l.
    simpl; intros.
    destruct i.
      discriminate.
    discriminate.
  intros.
  destruct i.
  simpl in * .
  exists a; trivial.

  simpl in H.
  destruct (list_set l i a0) eqn:Hset; [| discriminate] .
  injection H.
  intro; subst l'.
  simpl.
  eapply IHl; eauto.
Qed.

Lemma list_get_list_repeat_list : 
  forall {A: Set} i (a: A) n,
    i < n
    -> list_get (list_repeat_list n a) i = Some a.
Proof.
  induction i; simpl; intros; trivial.
    destruct n.
      apply False_ind.
      apply (gt_irrefl _ H); trivial. 
    simpl. 
    trivial.
  destruct n.
    apply gt_asym in H.
    apply False_ind.
    apply H.
    apply gt_Sn_O; trivial.
  simpl.
  apply IHi; trivial.
  apply gt_S_n; trivial.
Qed.

Lemma list_get_list_repeat_list_none : 
  forall {A: Set} i (a: A) n,
    n <= i
    -> list_get (list_repeat_list n a) i = None.
Proof.
  induction i; simpl; intros; trivial.
    destruct n.
      simpl.
      trivial.
    apply False_ind.
    apply (le_Sn_0 _ H).
  destruct n.
    simpl; trivial.
  apply IHi; trivial.
  apply le_S_n; trivial. 
Qed.

Lemma list_get_list_repeat_list_some_elim : 
  forall {A: Set} i (a a' : A) n, 
    list_get (list_repeat_list n a) i = Some a'
    -> blt_nat i n = true /\ a = a'.
Proof.
  induction i; simpl; intros; trivial.
    destruct n.
      simpl in H.
      discriminate.
    simpl in H.
    injection H; intro; subst a'.
    split; trivial.
  destruct n.
    simpl in H.
    discriminate.
  apply (IHi a a' n).
  simpl in H.
  trivial.
Qed.

(* ************************************************************************** *)

Lemma list_set_length_preserv: 
  forall {A: Set} (l:list A) i l' (a: A),
    list_set l i a = Some l'
    -> length l' = length l.
Proof.
  induction l; destruct i; simpl; intros.
    discriminate.
    discriminate.
  destruct l' as [ | a' l'].
  discriminate.
  inversion H.
  subst a0 l'.
  simpl; trivial.
  destruct l' as [ | a' l'].
  destruct (list_set l i a0).
    inversion H.
    discriminate.
  simpl.
  destruct (list_set l i a0) eqn:Hset.
  inversion H; subst.
  assert (length l' = length l).
    eapply IHl; eauto.
  rewrite H0; trivial.
  discriminate.
Qed.                                    

Lemma length_elim: 
  forall {A: Set} (l: list A) len,
    length l = len 
    -> forall i, 
         (blt_nat i len = true -> exists a, list_get l i = Some a)
         /\ (blt_nat i len = false -> list_get l i = None).
Proof.
  induction l; simpl; intros; trivial.
    split.
      subst len.
      intros.
      simplbnat.
    subst len.
    intros.
    destruct i; trivial.
  destruct len.
    discriminate.
  injection H; intros.
  split.
    intros.
    destruct i.
      exists a; trivial.
    assert (blt_nat i len = true).
      simplbnat.
      trivial.
    destruct (IHl len H0 i) as [IH1 IH2].
    apply IH1; trivial.
  intros.
  destruct i.
    simplbnat.
  assert (blt_nat i len = false).
    simplbnat.
    trivial.
  destruct (IHl len H0 i) as [IH1 IH2].
  apply IH2; trivial.
Qed.

Lemma length_intro: 
  forall {A: Set} (l: list A) len,
    (forall i, 
         (blt_nat i len = true -> exists a, list_get l i = Some a)
         /\ (blt_nat i len = false -> list_get l i = None))
    -> length l = len.
Proof.
  induction l; simpl; intros; trivial.
    destruct (H 0) as [H1 H2].
    destruct len; trivial.
    assert (blt_nat 0 (S len) = true).
      simplbnat.
      trivial.
    destruct (H1 H0).
    discriminate.
  destruct len; trivial.
    destruct (H 0) as [H1 H2].
    assert (blt_nat 0 0 = false).
      simplbnat.
      trivial.
    discriminate (H2 H0).
  assert ((forall i : nat,
         (blt_nat i len = true -> exists a : A, list_get l i = Some a) /\
         (blt_nat i len = false -> list_get l i = None))).
    intros.
    split.
      intros.
      assert (blt_nat (S i) (S len) = true).
        simplbnat.
        trivial.
      destruct (H (S i)) as [Hx Hy].
      apply Hx; trivial.
    intros.
    assert (blt_nat (S i) (S len) = false).
      simplbnat.
      trivial.
    destruct (H (S i)) as [Hx Hy].
    apply Hy; trivial.
  rewrite (IHl len); trivial.
Qed.


(* ************************************************************************** *)

Fixpoint list_make_nat_list (i : nat) : list nat :=
  match i with
    | 0 => nil
    | S i' => list_append (list_make_nat_list i') i'
  end.

(* Eval compute in (list_make_nat_list 5). *)

Lemma list_get_list_append_some_elim :
  forall {A: Set} (l : list A) a a' i, 
    list_get (list_append l a) i = Some a'
    -> (blt_nat i (length l) = true -> list_get l i = Some a')
       /\ (blt_nat i (length l) = false -> list_get l i = None /\ i = length l /\ a = a').
Proof.
  induction l.
    simpl.
    intros.
    destruct i.
      injection H; intro; subst a'.
      split.
        intro HF. 
        simplbnat.
      intro Hx.
      split; trivial.
      split; trivial.
    destruct i; discriminate.
  simpl.
  intros ax a' i H.
  destruct i.
    injection H; intro; subst a'.
    split.
      intros; trivial.
    intros.
    simplbnat.
  simpl.
  split.
    intro Hx.
    destruct (IHl ax a' i H) as [H1 H2].
    apply H1; trivial.
  intro Hx.
  destruct (IHl ax a' i H) as [H1 H2].
  destruct (H2 Hx) as [H3 [H4 H5]].
  split; trivial.
  rewrite H4, H5.
  split; trivial.
Qed.

Lemma list_append_list_length :
  forall {A: Set} (l : list A) a,
    length (list_append l a) = S (length l).
Proof.
  induction l.
    simpl; trivial.
  intros.
  simpl.
  rewrite IHl.
  trivial.
Qed.

Lemma list_make_nat_list_length : 
  forall n, length (list_make_nat_list n) = n.
Proof.
  induction n.
    simpl; trivial.
  simpl.
  rewrite list_append_list_length.
  rewrite IHn.
  trivial.
Qed.

Lemma list_make_nat_list_get_some_elim : 
  forall n i a,
    list_get (list_make_nat_list n) i = Some a 
    -> blt_nat a n = true /\ i = a.
Proof.
  induction n; trivial.
    intros.
    destruct i.
      simpl in H.
      discriminate.
    simpl in H.
    discriminate.
  intros i a H.
  destruct i.
    simpl in H.
    destruct (@list_get_list_append_some_elim _ _ _ _ _ H) as [H1 H2].
    rewrite list_make_nat_list_length in H1.
    rewrite list_make_nat_list_length in H2.
    destruct (blt_nat 0 n) eqn:Hn.
      destruct (IHn 0 a (H1 (refl_equal _))).
      split; trivial.
      solvebnat.
    destruct (H2 (refl_equal _)) as [H3 [H4 H5]].
    subst.
    subst a.
    simpl; split; trivial.
  simpl in H.
  destruct (@list_get_list_append_some_elim _ _ _ _ _ H) as [H1 H2].
  rewrite list_make_nat_list_length in H1.
  rewrite list_make_nat_list_length in H2.
  destruct (blt_nat (S i) n) eqn:Hn.
    destruct (IHn (S i) a (H1 (refl_equal _))) as [Hx Hy].
    split; trivial.
    solvebnat.
  destruct (H2 (refl_equal _)) as [H3 [H4 H5]].
  subst n a.
  split.
    simpl.
    simplbnat.
    trivial.
  trivial.
Qed.

Lemma list_get_list_append_some_intro :
  forall {A: Set} (l : list A) a a' i, 
     (blt_nat i (length l) = true /\ list_get l i = Some a')
    \/ (beq_nat i (length l) = true /\ a = a')
    -> list_get (list_append l a) i = Some a'.
Proof.
  induction l.
    simpl.
    intros.
    destruct i.
      destruct H.
        destruct H; discriminate.
      destruct H; subst; trivial. 
    destruct H.
      destruct H; discriminate.
    destruct H; discriminate.
  simpl.
  intros ax a' i H.
  destruct i.
    destruct H.
      destruct H; trivial.
    destruct H.
    desbnat.
    discriminate.
  simplbnat.
  destruct H.
    apply IHl.
    left; trivial.
  apply IHl.
  right.
  destruct H.
  split; trivial.
Qed.

Lemma list_make_nat_list_get_some_intro : 
  forall n i, 
    blt_nat i n = true
    -> list_get (list_make_nat_list n) i = Some i.
Proof.
  induction n.
    intros.
    simplbnat.
  intros.
  simpl.
  apply list_get_list_append_some_intro.
  rewrite list_make_nat_list_length.
  destruct (blt_S_dec _ _ H) as [H1 | H2].
    left.
    split.
      solvebnat.
    apply IHn; trivial.
  right.
  split; trivial.
  rewrite (beq_true_eq _ _ H2).
  trivial.
Qed.                                                    

(* ************************************************************************** *)

Fixpoint list_find_rec {A: Set} (beq : A -> A -> bool) (l: list A) (a: A) (i: nat) : option nat :=
  match l with 
    | nil => None
    | cons a' l' => 
      match beq a a' with
        | true => Some i
        | false => list_find_rec beq l' a (S i) 
      end
  end.

Definition list_find {A: Set} (beq : A -> A -> bool) (l: list A) (a: A) : option nat :=
  list_find_rec beq l a O.

Fixpoint list_find_rev {A: Set} (beq : A -> A -> bool) (l: list A) (a: A) : option nat :=
  match l with 
    | nil => None
    | cons a' l' => match list_find_rev beq l' a with 
                      | Some i' => Some (S i')
                      | None => match beq a a' with
                                  | true => Some 0
                                  | false => None 
                                end
                    end
  end.

(* Section TEST. *)
(*   Let l := 1::2::3::4::4::5::2::nil. *)
(*   Eval compute in list_find_rev beq_nat l 9. *)
(* End TEST. *)

Lemma list_find_rev_list_get :
  forall {A: Set} (l: list A) (a : A) i beq,
    list_find_rev beq l a = Some i
    -> (forall a1 a2, beq a1 a2 = true -> a1 = a2)
    -> list_get l i = Some a.
Proof.
  induction l as [ | a' l']; simpl; intros; trivial.
    discriminate.
  destruct (list_find_rev beq l' a) eqn:Hfind; try discriminate.
    injection H; intro; subst i; clear H.
    apply (IHl' a n beq); auto.
  destruct (beq a a') eqn:Ha; try discriminate.
  injection H; intro; subst i; clear H.
  rewrite (H0 _ _ Ha); trivial.
Qed.

Lemma list_find_rev_mono_rev :
  forall {A: Set} (l: list A) (a a' : A) i beq,
    list_find_rev beq (a'::l) a = Some (S i)
    -> list_find_rev beq l a = Some i.
Proof.
  induction l as [ | a' l']; simpl; intros; trivial.
    destruct (beq a a'); discriminate.
  destruct (list_find_rev beq l' a) eqn:Hfind; try discriminate.
    injection H; intro; subst i; clear H.
    trivial.
  destruct (beq a a') eqn:Ha; try discriminate.
    injection H; intro; subst i; clear H.
    trivial.
  destruct (beq a a'0).
    discriminate.
  discriminate.
Qed.

Lemma list_find_rev_mono :
  forall {A: Set} (l: list A) (a a' : A) i beq,
    list_find_rev beq l a = Some i
    -> list_find_rev beq (a'::l) a = Some (S i).
Proof.
  intros; simpl; trivial.
  rewrite H.
  trivial.
Qed.

Lemma list_get_list_find_rev : 
  forall {A: Set} i (l: list A) (a : A) beq,
    list_get l i = Some a
  -> (forall i' a', i' > i
                 -> list_get l i' = Some a'
                 -> a <> a')
  -> (forall a1 a2, a1 = a2 -> beq a1 a2 = true)
  -> (forall a1 a2, beq a1 a2 = true -> a1 = a2)
  -> list_find_rev beq l a = Some i.
Proof.
  induction i; simpl; intros; trivial.
    destruct l as [ | a' l'].
      simpl in H.
      discriminate.
    simpl in H.
    injection H; intro; subst a'; clear H.
    simpl.
    rewrite (H1 a a (refl_equal _)).
    destruct (list_find_rev beq l' a) eqn:Hfind; trivial.
    assert (HF:= H0 (S n) a).
    assert (Hget:= list_find_rev_list_get Hfind H2).
    simpl in  HF.
    apply False_ind.
    apply HF; trivial.
    auto with arith.
  destruct l as [ | a' l' ].
    simpl in H.
    discriminate.
  simpl in H.
  apply list_find_rev_mono; trivial.
  apply IHi; eauto.
  intros.
  apply H0 with (S i'); auto.
  apply lt_n_S; trivial.
Qed.

Lemma list_set_list_find_rev_neq :
  forall {A:Set} (l l':list A) i a a' a'' beq, 
    list_get l i = Some a
    -> list_set l i a' = Some l'
    -> a'' <> a'
    -> a'' <> a
    -> (forall a1 a2, a1 <> a2 -> beq a1 a2 = false)
    -> (forall a1 a2, beq a1 a2 = false -> a1 <> a2)
    -> list_find_rev beq l' a'' = list_find_rev beq l a''.
Proof.
  induction l; simpl; intros; trivial.
    destruct i; discriminate.
  destruct i.
    injection H; intro; subst a0; clear H.
    injection H0; intro; subst l'; clear H0.
    simpl.
    destruct (list_find_rev beq l a'') eqn:Hfind; trivial.
    rewrite (H3 a'' a' H1).
    rewrite (H3 a'' a H2).
    trivial.
  destruct (list_set l i a') eqn:Hset; try discriminate.
  injection H0; intro; subst l'; clear H0.
  simpl.
  rewrite (IHl l0 i a0 a' a'' beq H Hset H1 H2 H3 H4).
  destruct (list_find_rev beq l a'') eqn:Hfind; trivial.
Qed.

(* ************************************************************************** *)

Fixpoint list_inb {A: Set} (beq : A -> A -> bool) (l: list A) (a : A) : bool :=
  match l with 
    | nil => false
    | cons a' l' => match beq a a' with
                      | true => true
                      | false => list_inb beq l' a 
                    end
  end.

Lemma list_inb_false_elim : 
  forall {A: Set} (l: list A) a beq,
    list_inb beq l a = false
    -> (forall a1 a2, beq a1 a2 = false -> a1 <> a2)
    -> (forall i' a',
          list_get l i' = Some a'
          -> a <> a'
       ).
Proof.
  induction l as [ | a' l'].
    simpl; intros.
    destruct i'; discriminate.
  simpl.
  intros a beq H Hbeq2 i' a2 Hgi'.
  destruct (beq a a') eqn: Hb; try discriminate.
  destruct i'.
    injection Hgi'; intro; subst a2.
    apply Hbeq2; trivial.
  apply IHl' with beq i'; trivial.
Qed.


Lemma list_inb_true_elim : 
  forall {A: Set} (l: list A) a beq,
    list_inb beq l a = true
    -> (forall a1 a2, beq a1 a2 = true -> a1 = a2)
    -> exists i',
         list_get l i' = Some a.
Proof.
  induction l as [ | a' l'].
    simpl; intros.
    discriminate.
  simpl.
  intros a beq H Hbeq .
  destruct (beq a a') eqn: Hb.
    exists 0.
    rewrite (Hbeq a a' Hb).
    trivial.
  destruct (IHl' a beq H Hbeq) as [i' Hi'].
  exists (S i').
  trivial.
Qed.


Lemma list_inb_true_intro : 
  forall {A: Set} (l: list A) a beq i,
    list_get l i = Some a
    -> (forall a1 a2, beq a1 a2 = false -> a1 <> a2)
    -> list_inb beq l a = true.
Proof.
  induction l as [ | a' l'].
    simpl; intros.
    destruct i; discriminate.
  simpl.
  intros a beq i H Hbeq2 .
  destruct (beq a a') eqn: Hb; trivial.
  destruct i.
    injection H; intro; subst a'.
    destruct (Hbeq2 _ _ Hb (refl_equal _)).
  apply IHl' with i; trivial.
Qed.


(* ************************************************************************** *)

Fixpoint list_unique {A: Set} (beq : A -> A -> bool) (l : list A) : bool := 
  match l with 
    | nil => true 
    | cons a' l' => match list_inb beq l' a' with 
                 | true => false 
                 | false => list_unique beq l'
               end
  end.


Lemma list_unique_elim : 
  forall {A: Set} (l: list A) beq,
    list_unique beq l = true
    -> (forall a1 a2, beq a1 a2 = false -> a1 <> a2)
    -> (forall i i' a a',
          i <> i'
          -> list_get l i = Some a
          -> list_get l i' = Some a'
          -> a <> a'
       ).
Proof.
  induction l as [ | a' l'].
    simpl; intros.
    destruct i; discriminate.
  simpl.
  intros beq H Hbeq i1 i2 a1 a2 Hneq Hgi1 Hgi2.
  destruct i1.
    injection Hgi1; intro; subst a'.
    destruct (list_inb beq l' a1) eqn:Hinb; try discriminate.
    destruct i2.
      destruct (Hneq (refl_equal _)).
    apply (list_inb_false_elim Hinb Hbeq Hgi2).
  destruct i2.
    injection Hgi2; intro; subst a'.
    destruct (list_inb beq l' a2) eqn:Hinb; try discriminate.
    apply neq_sym.
    apply (list_inb_false_elim Hinb Hbeq Hgi1).
  destruct (list_inb beq l' a') eqn:Hinb; try discriminate.
  apply IHl' with beq i1 i2; trivial.
  intro HF; subst i1.
  destruct (Hneq (refl_equal _)).
Qed.

Lemma list_unique_intro : 
  forall {A: Set} (l: list A) beq,
    (forall a1 a2, beq a1 a2 = false -> a1 <> a2)
    -> (forall a1 a2, beq a1 a2 = true -> a1 = a2)
    -> (forall i i' a a',
          i <> i'
          -> list_get l i = Some a
          -> list_get l i' = Some a'
          -> a <> a'
       )
    -> list_unique beq l = true.
Proof.
  induction l as [ | a' l'].
    simpl; intros.
    trivial.
  simpl.
  intros beq Hbeq1 Hbeq2 H.
  destruct (list_inb beq l' a') eqn:Hinb.
    destruct (list_inb_true_elim Hinb Hbeq2) as [ix Hix].
    assert (Hx := H 0 (S ix) a' a').
    simpl in Hx.
    apply False_ind.
    apply Hx; trivial.
  apply IHl'; trivial.
  intros i1 i2 a1 a2 Hneq Ha1 Ha2.
  apply (H (S i1) (S i2) _ _); trivial.
  auto with arith.
Qed.

(* ************************************************************************** *)

Fixpoint list_remove {A:Set} (beq: A -> A -> bool) (x : A) (l : list A) : list A :=
  match l with
    | nil => nil
    | y::tl => if (beq x y) then list_remove beq x tl else y::(list_remove beq x tl)
  end.


Lemma list_inb_list_remove_neq : 
  forall {A: Set} (l: list A) (a a' : A) beq, 
    a' <> a
    -> (forall a1 a2, beq a1 a2 = true -> a1 = a2)
    -> list_inb beq (list_remove beq a' l) a = list_inb beq l a.
Proof.
  induction l; simpl; intros; trivial.
  destruct (beq a' a) eqn:Ha1.
    destruct (beq a0 a) eqn:Ha2.
      rewrite (H0 _ _ Ha1) in H.
      rewrite (H0 _ _ Ha2) in H.
      destruct (H (refl_equal _)).
    assert (a' = a).
      apply H0; trivial.
    subst a'.
    rewrite IHl; trivial.
  simpl.
  destruct (beq a0 a) eqn:Ha2.
    trivial.
  rewrite IHl; trivial.
Qed.

Lemma list_remove_preserv_list_unique : 
  forall {A:Set} (l l' : list A) a beq,
    list_unique beq l = true
    -> (forall a1 a2, beq a1 a2 = false -> a1 <> a2)
    -> (forall a1 a2, beq a1 a2 = true -> a1 = a2)
    -> l' =  list_remove beq a l
    -> list_unique beq l' = true.
Proof.
  induction l; simpl; intros.
    subst; simpl; trivial.
  destruct (list_inb beq l a) eqn:Hinb; try discriminate.
  destruct (beq a0 a) eqn:Hbeq.
    assert (a0 = a).
    apply H1; trivial.
    subst a0.
    apply IHl with a; trivial.
  rewrite H2.
  simpl.
  destruct (list_inb beq (list_remove beq a0 l) a) eqn:Hx.
    assert (a0 <> a).
      apply H0; trivial.
    rewrite list_inb_list_remove_neq in Hx; trivial.
    rewrite Hx in Hinb.
    discriminate.
  apply IHl with a0; trivial.
Qed.

Lemma list_inb_false_list_remove :
  forall {A:Set} (l : list A) a beq, 
    list_inb beq l a = false
    -> l = list_remove beq a l.
Proof.
  induction l as [ | a' l'].
    simpl; intros.
    trivial.
  intros a beq Hinb.
  simpl in * .
  destruct (beq a a') eqn:Hneq; try discriminate.
  rewrite (IHl' a beq Hinb) at 1; trivial.
Qed.   

Lemma list_length_subone_after_list_remove : 
  forall {A:Set} (l l': list A) a beq,
    list_unique beq l = true
    -> list_inb beq l a = true
    -> l' = list_remove beq a l
    -> (forall a1 a2, beq a1 a2 = false -> a1 <> a2)
    -> (forall a1 a2, beq a1 a2 = true -> a1 = a2)
    -> S (length l') = length l.
Proof.
  induction l as [ | a l].
    simpl; intros.
    discriminate.
  intros l' a' beq Hlu Hinb Hl' Hbeqfe Hbeqte.
  simpl in * .
  destruct (beq a' a) eqn:Hbeq.
    destruct (list_inb beq l a) eqn:Hinb2; try discriminate.
    assert (a' = a).
      apply Hbeqte; trivial.
    subst a'.
    rewrite Hl'.
    rewrite <- list_inb_false_list_remove; trivial.
  rewrite Hl'.
  simpl.
  destruct (list_inb beq l a) eqn:Hinb2; try discriminate.
  assert (Hx := IHl (list_remove beq a' l) a' beq Hlu Hinb (refl_equal _) Hbeqfe Hbeqte).
  rewrite Hx.
  trivial.
Qed.


Lemma list_remove_list_inb_false : 
  forall {A:Set} (l l': list A) a beq,
    l' = list_remove beq a l
    -> list_inb beq l' a = false.
Proof.
  induction l as [ | a l ].
    simpl; intros.
    subst l'.
    simpl.
    trivial.
  intros l' a' beq Hl'.
  simpl in Hl'.
  destruct (beq a' a) eqn:Hbeq.
    rewrite IHl; trivial.
  rewrite Hl'.
  simpl.
  rewrite Hbeq.
  rewrite IHl; auto.
Qed.

(* ************************************************************************** *)

Fixpoint list_filter {A: Set} (l : list A) (f: A -> bool) : list A := 
  match l with 
    | nil => nil 
    | cons a' l' => match f a' with 
                 | true => a' :: list_filter l' f
                 | false => list_filter l' f
               end
  end.

Fixpoint list_filter_domain {A: Set} (l : list A) (f: A -> bool) (i: nat): list nat := 
  match l with 
    | nil => nil 
    | cons a' l' => match f a' with 
                 | true => i :: list_filter_domain l' f (S i)
                 | false => list_filter_domain l' f (S i)
               end
  end.

Lemma list_filter_domain_is_greater_equal_than_base :
  forall {A: Set} (l:list A) i base f beq,
    i < base
    -> (forall a1 a2, a1 <> a2 -> beq a1 a2 = false)
    -> list_inb beq (list_filter_domain l f base) i = false .
Proof.
  induction l.
    simpl; trivial.
  intros i base f beq Hi Hbeqnf.
  simpl.
  destruct (f a) eqn: Hf.
    simpl.
    assert (beq i base = false).
      apply Hbeqnf.
      clear - Hi.
      omega.
    rewrite H.
    apply IHl; trivial. 
    auto with arith.
  apply IHl.
  omega.
  trivial.
Qed.    

Lemma list_filter_domain_elim :
  forall {A: Set} (l:list A) i base f beq,
    list_inb beq (list_filter_domain l f base) (base + i) = true 
    -> (forall a1 a2, a1 <> a2 -> beq a1 a2 = false)
    -> (forall a1 a2, beq a1 a2 = true -> a1 = a2)
    -> exists a, list_get l i = Some a
                 /\ f a = true.
Proof.
  induction l.
    simpl; intros.
    discriminate.
  simpl.
  intros i base f beq Hinb Hbeqnf Hbeqte.
  assert (forall i j, i + S j = S i + j).
    clear.
    intros; omega.
  destruct (f a) eqn: Hf.
    destruct i.
      simpl in * .
      exists a; split; trivial.
    simpl in Hinb.
    destruct (beq (base + S i) base) eqn:Hbase.
      assert (forall i j, i + S j <> i).
        clear.
        intros.
        omega.
      rewrite (Hbeqnf _ _ (H0 base i)) in Hbase.
      discriminate.
    apply IHl with (S base) beq; trivial.
    rewrite H in Hinb.
    trivial.
  destruct i.
    rewrite (list_filter_domain_is_greater_equal_than_base) in Hinb; trivial.  
    discriminate. 
    clear.
    omega.
  apply IHl with (S base) beq; trivial.
  rewrite H in Hinb.
  trivial.
Qed.

Lemma list_unique_list_filter_domain :
  forall {A: Set} (l : list A) f base, 
    (* (forall a1 a2, beq a1 a2 = true -> a1 = a2) *)
    list_unique beq_nat (list_filter_domain l f base) = true.
Proof.
  induction l.
    simpl.
    trivial.
  simpl.
  intros f base.
  destruct (f a) eqn: Hf.
    simpl.
    rewrite list_filter_domain_is_greater_equal_than_base; trivial.
    omega.
    apply neq_beq_false.
  rewrite IHl with f (S base).
  trivial.
Qed.

Lemma list_filter_domain_intro :
  forall {A: Set} (l:list A) i base f beq ,
    forall a, 
      list_get l i = Some a
      -> f a = true
      -> (forall a1 a2, a1 <> a2 -> beq a1 a2 = false)
      -> (forall a1 a2, a1 = a2 -> beq a1 a2 = true)
      -> list_inb beq (list_filter_domain l f base) (base + i) = true.
Proof.
  induction l.
    simpl; intros.
    destruct i; discriminate.
  simpl.
  intros i base f beq ax Hg Hf Hbeqnf Hbeqet.
  (* assert (forall i j, i + S j = S i + j). *)
  (*   clear. *)
  (*   intros; omega. *)
  destruct (f a) eqn: Hfa.
    destruct i.
      simpl.
      assert (beq (base + 0) base = true).
      apply Hbeqet.
      omega.
      rewrite H.
      trivial.
    simpl.
    assert (beq (base + S i) base = false).
      apply Hbeqnf.
      omega.
    rewrite H.
    assert (base + S i = S base + i).
      omega.
      rewrite H0.
    apply (IHl i (S base) f beq ax); trivial.
  destruct i.
    injection Hg; intro; subst ax; clear Hg.
    rewrite Hfa in Hf.
    discriminate.
  assert (base + S i = S base + i).
    omega.
    rewrite H.
  apply (IHl i (S base) f beq ax); trivial.
Qed.

(* ************************************************************************** *)

Fixpoint list_opt_dual_filter {A: Set} (l : list (prod (option A) (option A))) (f: A -> bool) : list A := 
  match l with 
    | nil => nil 
    | cons (Some a1, Some a2) l' => 
               match (f a1, f a2) with 
                 | (true, true) => a1 :: a2 :: list_opt_dual_filter l' f
                 | (true, false) => a1 :: list_opt_dual_filter l' f 
                 | (false, true) => a2 :: list_opt_dual_filter l' f 
                 | (false, false) => list_opt_dual_filter l' f
               end

    | cons (Some a1, None) l' => 
               match (f a1) with 
                 | true => a1 :: list_opt_dual_filter l' f 
                 | false => list_opt_dual_filter l' f
               end

    | cons (None, Some a2) l' => 
               match (f a2) with 
                 | true => a2 :: list_opt_dual_filter l' f 
                 | false => list_opt_dual_filter l' f
               end

    | cons (None, None) l' =>  list_opt_dual_filter l' f
  end.


(* ************************************************************************** *)

Lemma list_length_after_permutation: 
  forall {A:Set} (l l': list A) beq,
    list_unique beq l = true
    -> list_unique beq l' = true
    -> (forall i a, list_get l i = Some a 
       -> list_inb beq l' a = true)
    -> (forall i a, list_get l' i = Some a 
       -> list_inb beq l a = true)
    -> (forall a1 a2, beq a1 a2 = false -> a1 <> a2)
    -> (forall a1 a2, beq a1 a2 = true -> a1 = a2)
    -> length l = length l'.
Proof.
  induction l as [ | a l].
    simpl; intros.
    destruct l' as [ | a' l'].
      simpl; trivial.
    assert (Hx : list_get (a' :: l') 0 = Some a').
      simpl; trivial.
    discriminate (H2 _ _ Hx).
  intros l' beq Hlu Hlu' Hsub Hsub' Hbeqfe Hbeqte.
  set (lx := list_remove beq a l').
  assert (list_unique beq l = true).
    simpl in Hlu.
    destruct (list_inb beq l a) eqn:Hinb; try discriminate.
    trivial.
  assert (list_unique beq lx = true).
    apply list_remove_preserv_list_unique with l' a; trivial.
  assert (length l = length lx).
    apply IHl with beq; trivial.

    intros i ax Hax.
    assert (Hneq : a <> ax).
      intro HF.
      subst ax.
      simpl in Hlu.
      destruct (list_inb beq l a) eqn:Hinb; try discriminate.
      assert (Hx := list_inb_false_elim Hinb Hbeqfe).
      apply (Hx i a); trivial.
    assert (Hx := Hsub (S i) ax).
    simpl in Hx.
    apply Hx in Hax.
    subst lx.
    rewrite (list_inb_list_remove_neq _ Hneq Hbeqte); trivial.
    
    intros i ax Hax.
    assert (Hneq : a <> ax).
      intro HF.
      subst ax.
      assert (Hx := @list_remove_list_inb_false _ l' lx a beq (refl_equal _)). 
      assert (Hy := @list_inb_false_elim _ _ _ _ Hx Hbeqfe i a Hax).
      apply Hy; trivial.
    assert (Hx : list_inb beq l' ax = true).
      rewrite <- (@list_inb_list_remove_neq _ _ _ _ _ Hneq Hbeqte); trivial.
      subst lx.
      apply list_inb_true_intro with i; trivial.
    destruct (@list_inb_true_elim _ _ _ _ Hx Hbeqte) as [ix Hgx].
    assert (Hy := Hsub' ix ax Hgx).
    simpl in Hy.
    destruct (beq ax a) eqn:Hax2.
      destruct ((neq_sym Hneq) (Hbeqte _ _ Hax2)).
    trivial.
  simpl.
  rewrite H1.
  assert (list_inb beq l' a = true).
    apply Hsub with 0.
    simpl; trivial.
  rewrite (@list_length_subone_after_list_remove _ _ _ _ _ Hlu' H2 ); trivial.
Qed.

Unset Implicit Arguments.

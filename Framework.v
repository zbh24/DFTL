(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*   Author: Yu Guo <guoyu@ustc.edu.cn>                                       *)
(*                          School of Computer Science and Technology, USTC   *)
(*                                                                            *)
(*           Bihong Zhang <sa614257@mail.ustc.edu.cn>                         *)
(*                                     School of Software Engineering, USTC   *)
(*                                                                            *)
(*           Yishuai Li <lyishuai@mail.ustc.edu.cn>                           *)
(*                                         School of the Gifted Young, USTC   *)
(*                                                                            *)
(* ************************************************************************** *)

Require Import List.
Require Import ListEx.
Require Import Params.
Require Export bnat.
Require Import NPeano.

Require Import Monad.
Require Import Data.

Require Import Nand.
Require Import Dftl2.

(* ************* *********** *** *)
(* magnetic hard disk device interface *)

Definition sector_no := nat. 

Definition bvalid_sector_no (sec: sector_no) := blt_nat sec NUM_OF_SECTORS.

Definition valid_sector_no (sec: sector_no) : Prop := 
  bvalid_sector_no sec = true.

Definition hard_disk := list data.

Definition hdd_read (hdd: hard_disk) (sec: sector_no) : option data  := 
  test (bvalid_sector_no sec);
  do d <-- list_get hdd sec;
  ret d.

Definition hdd_write (hdd: hard_disk) (sec: sector_no) (d: data): option hard_disk := 
  test (bvalid_sector_no sec);
  do hdd' <-- list_set hdd sec d;
  ret hdd'.

Definition hdd_init : hard_disk :=
  list_repeat_list NUM_OF_SECTORS (zero_data SECTOR_DATA_SIZE).

Inductive command : Set :=
  | cmd_read (sec: sector_no)
  | cmd_write (sec: sector_no) (d: data).

Inductive behav : Set :=
  | bh_void 
  | bh_value (d: data).

Definition behavior : Set := list behav.

Inductive hdd_run : hard_disk -> command -> hard_disk -> behav -> Prop :=
  | hdd_run_read (hdd: hard_disk) 
                (lpn: sector_no) 
                (d: data)
                (Hdr: hdd_read hdd lpn = Some d) : hdd_run hdd (cmd_read lpn) hdd (bh_value d)
  | hdd_run_write (hdd: hard_disk) 
                 (hdd': hard_disk)
                 (lpn: sector_no) 
                 (d: data)
                 (Hdw: hdd_write hdd lpn d = Some hdd') : hdd_run hdd (cmd_write lpn d) hdd' (bh_void).

Fixpoint hdd_run_cmd_list (hdd: hard_disk) (cl: list command) (hdd': hard_disk) (B: behavior) := 
  match cl, B with
    | nil, nil => hdd = hdd'
    | c :: cl', bh :: B' => exists hdd'', hdd_run hdd c hdd'' bh /\ hdd_run_cmd_list hdd'' cl' hdd' B'
    | _, _ => False 
  end.

Lemma hdd_read_write_at_same_addr : 
  forall hdd addr v hdd',
    hdd_write hdd addr v = Some hdd'
    -> hdd_read hdd' addr = Some v.
Proof.
  unfold hdd_write, hdd_read.
  intros hdd addr v hdd' Hw.
  destruct (bvalid_sector_no addr) eqn:Hva; [ | discriminate].


  destruct (list_set hdd addr v) eqn:Hl; [ | discriminate].
  injection Hw.
  intro; subst hdd'.
  rewrite (list_get_list_set_eq Hl).
  trivial.
Qed.

Lemma hdd_read_write_not_same_addr : 
  forall hdd addr addr' v hdd',
    addr <> addr' 
    -> hdd_write hdd addr v = Some hdd'
    -> hdd_read hdd' addr' = hdd_read hdd addr'.
Proof.
  unfold hdd_write, hdd_read.
  intros hdd addr addr' v hdd' Hneq Hw.
  destruct (bvalid_sector_no addr) eqn:Ha.
    destruct (bvalid_sector_no addr') eqn:Ha'.
    destruct (list_set hdd addr v) eqn:Hl; [ | discriminate].
    injection Hw; intro; subst l.
    rewrite (list_get_list_set_neq Hl Hneq).
    trivial.
    trivial.
  discriminate.
Qed.

Lemma hdd_write_some_implies_valid_addr :
  forall hdd sec d hdd',
    hdd_write hdd sec d = Some hdd'
    -> valid_sector_no sec.
Proof.
  intros.
  unfold hdd_write in H.
  destruct (bvalid_sector_no sec) eqn:Hs;[| discriminate].
  trivial.
Qed.

(* ************* *********** *** *)
(* flash device interface *)

Definition bvalid_logical_block_no (lbn: block_no) := blt_nat lbn MAX_LOGICAL_BLOCKS.

Definition lbn_off_to_lpn (lbn: block_no) (off: page_off) : nat := 
  lbn * PAGES_PER_BLOCK + off.

(* Eval compute  in (10 /3 ). *)

Definition lpn_to_lbn_off (lpn: nat) : prod block_no page_off :=
  (lpn /  PAGES_PER_BLOCK, lpn mod PAGES_PER_BLOCK).

Lemma addr_neq_trans_implies_neq :
  forall addr addr' lbn off lbn' off',
    addr <> addr'
    -> lpn_to_lbn_off addr = (lbn, off)
    -> lpn_to_lbn_off addr' = (lbn', off')
    -> lbn <> lbn' \/ ((lbn = lbn') /\ off <> off').
Proof.
  intros.
  destruct (beq_nat lbn lbn') eqn:Hlbn.
  - apply beq_true_eq in Hlbn.
    right; split; auto; intro.
    apply H.
    rewrite div_mod with (y := PAGES_PER_BLOCK);
      try (intro Heq; inversion Heq).
    replace lbn with (addr / PAGES_PER_BLOCK) in *;
      try (inversion H0; subst; reflexivity).
    replace off with (addr mod PAGES_PER_BLOCK) in *;
      try (inversion H0; subst; reflexivity).
    replace lbn' with (addr' / PAGES_PER_BLOCK) in *;
      try (inversion H1; subst; reflexivity).
    replace off' with (addr' mod PAGES_PER_BLOCK) in *;
      try (inversion H1; subst; reflexivity).
    rewrite <- Hlbn.
    rewrite <- H2.
    apply div_mod.
    intro.
    inversion H3.
  - left.
    apply beq_false_neq.
    assumption.
Qed.

Lemma valid_lpn_implies_valid_off :
  forall addr lbn off,
    bvalid_sector_no addr = true
    -> lpn_to_lbn_off addr = (lbn, off)
    -> bvalid_page_off off = true.
Proof.
  intros.
  replace off with (addr mod PAGES_PER_BLOCK).
  - apply lt_blt_true.
    apply Nat.mod_small_iff;
      try (intro Heq; inversion Heq).
    apply Nat.mod_mod;
      try (intro Heq; inversion Heq).
  - inversion H0; auto.
Qed.

Lemma valid_lpn_implies_valid_lbn :
  forall addr lbn off,
    bvalid_sector_no addr = true
    -> lpn_to_lbn_off addr = (lbn, off)
    -> bvalid_logical_block_no lbn = true.
Proof.
  intros.
  replace lbn with (addr / PAGES_PER_BLOCK).
  - apply lt_blt_true.
    apply Nat.div_lt_upper_bound;
      try (intro Heq; inversion Heq).
    apply blt_true_lt.
    rewrite Nat.mul_comm.
    unfold bvalid_sector_no in H.
    unfold NUM_OF_SECTORS in H.
    assumption.
  - inversion H0; auto.
Qed.

Lemma invalid_lpn_implies_valid_off :
  forall addr lbn off,
    bvalid_sector_no addr = false
    -> lpn_to_lbn_off addr = (lbn, off)
    -> bvalid_page_off off = true.
Proof.
  intros.
  replace off with (addr mod PAGES_PER_BLOCK).
  - apply lt_blt_true.
    apply Nat.mod_small_iff;
      try (intro Heq; inversion Heq).
    apply Nat.mod_mod;
      try (intro Heq; inversion Heq).
  - inversion H0; auto.
Qed.

Lemma invalid_lpn_implies_invalid_lbn :
  forall addr lbn off,
    bvalid_sector_no addr = false
    -> lpn_to_lbn_off addr = (lbn, off)
    -> bvalid_logical_block_no lbn = false.
Proof.
  intros.
  replace lbn with (addr / PAGES_PER_BLOCK).
  - unfold bvalid_logical_block_no.
    apply le_blt_false.
    apply Nat.div_le_lower_bound;
      try (intro Heq; inversion Heq).
    apply blt_false_le.
    rewrite Nat.mul_comm.
    unfold bvalid_sector_no in H.
    unfold NUM_OF_SECTORS in H.
    assumption.
  - inversion H0; auto.
Qed.

Definition flash_device := prod chip FTL.

Definition fld_read (fld: flash_device) (lpn: nat) : option data := 
  let (c, f) := fld in
  do [d,_] <-- FTL_read c f lpn;
  ret d.

Definition fld_write (fld: flash_device) (lpn: nat) (d: data) : option flash_device := 
  let (c, f) := fld in
  do [c',f'] <-- FTL_write c f lpn d;
  ret (c',f').

(* Definition fld_init : flash_device := (nand_init, ftl_init). *)

(* Definition fld_run (fld: flash_device) (cmd: command) (fld': flash_device) (bh: behav) : Prop := *)
(*   match cmd with  *)
(*     | cmd_read lpn => exists d, fld_read fld lpn = Some d /\ bh = bh_value d /\ fld' = fld *)
(*     | cmd_write lpn d =>  *)
(* fld_write fld lpn d = Some fld' /\ bh = bh_void *)
(*   end. *)

Definition fld_run (fld: flash_device) (cmd: command) (fld': flash_device) (bh: behav) : Prop :=
  match cmd with 
    | cmd_read lpn => exists d, fld_read fld lpn = Some d /\ bh = bh_value d
    | cmd_write lpn d => 
fld_write fld lpn d = Some fld' /\ bh = bh_void
  end.

Fixpoint fld_run_cmd_list (fld: flash_device) (cl: list command) (fld': flash_device) (B: behavior) := 
  match cl, B with
    | nil, nil => fld = fld'
    | c :: cl', bh :: B' => exists fld'', fld_run fld c fld'' bh /\ fld_run_cmd_list fld'' cl' fld' B'
    | _, _ => False 
  end.

(* ************************************************************************** *)

(* The binary relation to prove the refinement                                *)

Definition R (hdd: hard_disk) (fld: flash_device) : Prop :=
  forall sec, 
    hdd_read hdd sec = fld_read fld sec.

(* ************************************************************************** *)

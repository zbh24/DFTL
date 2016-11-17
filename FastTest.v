(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*   Author: Yu Guo <guoyu@ustc.edu.cn>                                       *)
(*                          School of Computer Science and Technology, USTC   *)
(*                                                                            *)
(*           Yishuai Li <lyishuai@mail.ustc.edu.cn>                           *)
(*                                         School of the Gifted Young, USTC   *)
(*                                                                            *)
(* ************************************************************************** *)

Require Import ListEx.
Require Import Monad.

Require Import Params.
Require Import Nand.
Require Import Data.
Require Import FtlFast.

Open Scope list_scope.

Definition write_command : Set := (block_no * page_off * char) %type.

Import NewNand.
Import NandData.

(* Test NAND *)

Fixpoint nand_write_batch (c: chip) (wl : list write_command) 
  : op_result chip :=
  match wl with 
    | nil => ret c
    | cons wr wl' => 
      let (pn, char) := wr in
      let (b, off) := pn in
      do c' <== nand_write_page c b off (mkdata_chars (char::nil)) mkoob_empty;
      nand_write_batch c' wl'
  end.

Compute ( 
  let wl := (0,0,c_a) :: nil in
  do c0 <-- Some nand_init;
  do c <== nand_write_batch c0 wl;
  ret c).

Compute ( 
  let wl := (0,0,c_a) :: (0,1,c_a) :: nil in
  do c0 <-- Some nand_init;
  do c <== nand_write_batch c0 wl;
  ret c).

Compute ( 
  let wl := (0,0,c_a) :: (0,1,c_a) :: nil in
  do c0 <-- Some nand_init;
  do c <== nand_write_batch c0 wl;
  do c'<== nand_erase_block c 0;
  ret c').

(* Test NAND *)

Fixpoint ftl_write_batch (c: chip)(f: FTL) (wl : list write_command) 
  : op_result (chip * FTL) :=
  match wl with 
    | nil => ret (c, f)
    | cons wr wl' => 
      let (pn, char) := wr in
      let (b, off) := pn in
      do [c', f'] <== ftl_write c f b off (mkdata_chars (char::nil));
      ftl_write_batch c' f' wl'
  end.

Let c0 := nand_init.
Let f0 := ftl_init.

Compute ( 
  let wl := (0,0,c_a) :: nil in
  do [c, f] <== ftl_write_batch c0 f0 wl;
  ret (c, f)).

Compute ( 
  let wl := (0,0,c_a)::(0,1,c_b)::(0,0,c_c)::(0,0,c_d)::
nil in
  do c0 <-- Some nand_init;
  do f0 <-- Some ftl_init;
  do [c, f] <== ftl_write_batch c0 f0 wl;
  ret (c, f)).

(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*   Author: Yu Guo <guoyu@ustc.edu.cn>                                       *)
(*                          School of Computer Science and Technology, USTC   *)
(*                                                                            *)
(*           Hui Zhang <sa512073@mail.ustc.edu.cn>                            *)
(*                                     School of Software Engineering, USTC   *)
(*                                                                            *)
(*           Bihong Zhang <sa614257@mail.ustc.edu.cn>                         *)
(*                                     School of Software Engineering, USTC   *)
(* ************************************************************************** *)

Require Import String.
Require Import ListEx.

(* A temporary definition of chars. *)
Inductive char : Type :=
| c_null : char
| c_a : char
| c_b : char 
| c_c : char
| c_d : char
| c_e : char
| c_f : char
| c_g : char
| c_h : char
| c_0 : char
| c_1 : char
| c_2 : char
| c_3 : char
| c_4 : char
| c_5 : char
| c_6 : char
| c_7 : char
| c_info : string -> char
| c_ff : char
.

Notation "'0xA'" := (c_a).
Notation "'0xNN'" := (c_null).
Notation "'0xFF'" := (c_ff).
Notation "<< s >>" := (c_info s).

Definition byte := char.

Definition bytelist := list byte.
(*transrecord:lpn ppn*)
Inductive trans_record: Type :=
  | trans_empty
  | trans_data(lpn:nat)(pbn:nat)(offset:nat).

Definition meta_trans_record_list := list trans_record.

Inductive  data : Type := 
  | metabyte:  bytelist->data
  | metarecord: meta_trans_record_list->data.

Definition zero_data (sz: nat) : data :=
  metabyte (list_repeat_list sz c_null).

(* Definition ff_data (sz: nat) : data := *)
(*   list_repeat_list sz c_ff.i *)
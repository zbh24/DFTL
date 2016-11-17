(* ************************************************************************** *)
(*                                                                            *)
(* Verified Flash Translation Layer                                           *)
(*                                                                            *)
(*                                                                            *)
(*   Author: Yu Guo <guoyu@ustc.edu.cn>                                       *)
(*                          School of Computer Science and Technology, USTC   *)
(*                                                                            *)
(*           Bihong Zhang  <sa614257@mail.ustc.edu.cn>                        *)
(*                                       School of Software Engeering, USTC   *)
(*                                                                            *)
(* ************************************************************************** *)

Require Import ListEx.
Require Import Monad.

Require Import Params.
Require Import Nand.
Require Import Data.
Require Import Dftl0.

Open Scope list_scope.


Fixpoint write_command_batch(c:chip) (f:FTL) (num:nat) (lpn:page_no): option (prod chip FTL) :=
  match num with
      | O => ret (c,f)
      | S i => do data <-- Some (metabyte (cons c_h (cons c_b  nil) ) );
               do [c',f'] <-- FTL_write  c f lpn  data;
               write_command_batch  c' f' i lpn
 end.



(* Definition test_write_read : option chip  := *)
(*   do c <-- Some nand_init; *)
(*   do f <-- ftl_init; *)
(*   do data <-- Some (metabyte (cons c_h (cons c_b  nil) ) ); *)
(*   do [c',f'] <-- FTL_write c f 0 data; *)
(*   ret c'. *)

(* Compute test_write_read. *)

(* Definition test_write_read : option FTL  := *)
(*   do c <-- Some nand_init; *)
(*   do f <-- ftl_init; *)
(*   do data <-- Some (metabyte (cons c_h (cons c_b  nil) ) ); *)
(*   do [c',f'] <-- FTL_write c f 0 data; *)
(*   ret f'. *)

(* Compute test_write_read. *)

(* Definition test_write_read : option (prod chip FTL)  := *)
(*   do c <-- Some nand_init; *)
(*   do f <-- ftl_init; *)
(*   do data <-- Some (metabyte (cons c_h (cons c_b  nil) ) ); *)
(*   do [c',f'] <-- FTL_write c f 0 data; *)
(*   do [d,cf] <-- FTL_read c' f' 0; *)
(*   do [c'',f''] <-- Some cf; *)
(*   ret (c'',f''). *)

(* Compute test_write_read. *)


(* Definition test_write_read : option data  := *)
(*   do c <-- Some nand_init; *)
(*   do f <-- ftl_init; *)
(*   do data <-- Some (metabyte (cons c_h (cons c_b  nil) ) ); *)
(*   do [c',f'] <-- FTL_write c f 0 data; *)
(*   do [d,cf] <-- FTL_read c' f' 0; *)
(*   do [c'',f''] <-- Some cf; *)
(*   ret d. *)

(* Compute test_write_read. *)


(* Definition test_write_read : option (prod data FTL)  := *)
(*   do c <-- Some nand_init; *)
(*   do f <-- ftl_init; *)
(*   do data <-- Some (metabyte (cons c_h (cons c_b  nil) ) ); *)
(*   do [c',f'] <-- FTL_write c f 83 data; *)
(*   do [d,cf] <-- FTL_read c' f' 83; *)
(*   do [c'',f''] <-- Some cf; *)
(*   do [d,cf'] <-- FTL_read c'' f'' 83; *)
(*   do [c''',f'''] <-- Some cf'; *)
(*   ret (d,f'''). *)

(* Compute test_write_read. *)

(* It is wrong ,because the offset is beyond the 16 *)
(* Definition test_write_read : option (prod data FTL)  := *)
(*   do c <-- Some nand_init; *)
(*   do f <-- ftl_init; *)
(*   do data <-- Some (metabyte (cons c_h (cons c_b  nil) ) ); *)
(*   do [c',f'] <-- FTL_write c f 16 data; *)
(*   do [d,cf] <-- FTL_read c' f' 16; *)
(*   do [c'',f''] <-- Some cf; *)
(*   ret (d,f''). *)

(* Compute test_write_read. *)

(* Definition test_write_read : option (prod data FTL)  := *)
(*   do c <-- Some nand_init; *)
(*   do f <-- ftl_init; *)
(*   do data <-- Some (metabyte (cons c_h (cons c_b  nil) ) ); *)
(*   do [c',f'] <-- FTL_write c f 0 data; *)
(*   do [c'',f''] <-- FTL_write c' f' 15 data; *)
(*   do [d,cf] <-- FTL_read c'' f'' 0; *)
(*   do [c''',f'''] <-- Some cf; *)
(*   ret (d,f'''). *)

(* Compute test_write_read. *)

(* Definition test_write_read : option chip  := *)
(*   do c <-- Some nand_init; *)
(*   do f <-- ftl_init; *)
(*   do data <-- Some (metabyte (cons c_h (cons c_b  nil) ) ); *)
(*   do [c',f'] <-- FTL_write c f 0 data; *)
(*   do [c'',f''] <-- FTL_write c' f' 0 15 data; *)
(*   do [d,cf] <-- FTL_read c'' f'' 0; *)
(*   do [c''',f'''] <-- Some cf; *)
(*   ret c'''. *)

(* Compute test_write_read. *)


(* ---------------------------------------------------------------- *)

(* Definition test_write_read : option (prod data FTL)  := *)
(*   do c <-- Some nand_init; *)
(*   do f <-- ftl_init; *)
(*   do data <-- Some (metabyte (cons c_h (cons c_b  nil) ) ); *)
(*   do [c',f'] <-- write_command_batch c f 31 0; *)
(*   do [d,cf] <-- FTL_read c' f' 0; *)
(*   do [c'',f''] <-- Some cf; *)
(*   ret (d,f''). *)

(* Compute test_write_read. *)

(* Definition test_write_read : option (prod data (prod chip FTL) )  := *)
(*   do c <-- Some nand_init; *)
(*   do f <-- ftl_init; *)
(*   do data <-- Some (metabyte (cons c_h (cons c_b  nil) ) ); *)
(*   do [c',f'] <-- write_command_batch c f 45 0;  *)
(*   do [d,cf] <-- FTL_read c' f' 0; *)
(*   do [c'',f''] <-- Some cf; *)
(*   ret (d,(c'',f'') ). *)

(* Compute test_write_read. *)

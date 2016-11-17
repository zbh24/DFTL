
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

Require Export bnat.
Require Import LibEx.
Require Import ListEx.
Require Import Monad.
Require Import Data.
Require Import Params.

(* NAND hardware interface *)

(* Definition oob := list int. *)

Definition page_off := nat.

Definition block_no := nat.

Definition page_off_of_nat (n: nat) : page_off := n.

(* Definition page_no := prod block_no page_off. *)

Definition page_no := nat.

Definition page_oob_nat := option (prod nat nat).

Inductive page_status : Set :=
  | ps_free
  | ps_programmed.

Inductive block_status : Set :=
  | bs_free
  | bs_programmed.

Record page : Set := 
  mkpage {
      page_data : data;
      page_oob :  page_oob_nat;
      page_state : page_status
      (* data_size: length (page_data) = PAGE_DATA_SIZE; *)
      (* oob_size: length (page_data) = PAGE_SPAREAREA_SIZE *)
    }.

Record block : Set := 
  mkblock {
      block_pages : list page;
      next_page : page_off;
      block_erase_count: nat;
      block_state : block_status
      (* pages_size: length block_pages = PAGES_PER_BLOCK *)
    }.

Record chip : Set := 
  mkchip {
      chip_blocks: list block
      (* blocks_size : length chip_blocks = BLOCKS *)
    }. 

(********* Initialization of the Nand Chip ****************)

(*Just init single page's content,including the page content and oob*)
Definition init_page_data : data :=
  metabyte (list_repeat_list PAGE_DATA_SIZE c_ff).

(* Definition init_page_oob : data := *)
(*   metabyte (list_repeat_list PAGE_SPARE_AREA_SIZE c_ff). *)

(*The Initialization oob is 0 *)
Definition init_page : page :=
  mkpage init_page_data None  ps_free.

Definition init_block : block :=
  mkblock (list_repeat_list PAGES_PER_BLOCK init_page) 0 0 bs_free.

Definition erased_block (ec: nat): block :=
  mkblock (list_repeat_list PAGES_PER_BLOCK init_page) 0 (S ec) bs_free.

Definition bvalid_block_no (pbn: block_no) : bool := 
  (blt_nat pbn BLOCKS).

Definition bvalid_page_no (ppn:page_no) : bool :=
  (blt_nat ppn (BLOCKS * PAGES_PER_BLOCK)).

Definition bvalid_page_off (off: page_off) : bool := 
  (blt_nat off PAGES_PER_BLOCK).

(********* Nand chip Operations ***************)
Definition nand_init : chip :=
  mkchip (list_repeat_list BLOCKS init_block). 

(* written by zhanghui, generate the content of 'oob' according to the
data stored in this page. *)
(* TEMP: now just return a list of null *)
(* Definition make_oob (d : data) : data := *)
(*   list_repeat_list PAGE_SPARE_AREA_SIZE c_null. *)

Definition page_set__oob (p:page)(oob:page_oob_nat) :=
  ret (mkpage (page_data p) oob (page_state p) ).

Definition page_get_oob (p:page) :page_oob_nat :=
  page_oob p.

Definition chip_get_block (c: chip) (pbn: block_no): option block :=
  list_get (chip_blocks c) pbn.

Definition chip_set_block (c: chip) (pbn: block_no) (b: block) : option chip :=
  test bvalid_block_no pbn;
  do nbl <-- list_set (chip_blocks c) pbn b;
  ret (mkchip nbl).

Definition block_get_page (b: block) (off: page_off) : option page :=
  test (bvalid_page_off off);
  do p <-- (list_get (block_pages b) off);
  ret p.
 
Definition block_set_page (b: block) (off: page_off) (p: page) : option block :=
  test bvalid_page_off off;
  do npl <-- list_set (block_pages b) off p;
  ret (mkblock npl (next_page b) (block_erase_count b) bs_programmed).

Definition block_set_next_page (b: block) (off: page_off) : option block :=
  ret (mkblock (block_pages b) (off) (block_erase_count b) (block_state b)).

Definition chip_get_page (c: chip) (bln: block_no) (poff: page_off) : option page :=
  match chip_get_block c bln with
    | None => None
    | Some b =>
      block_get_page b poff
  end.

Definition page_get_data (p: page) : option data :=
  match page_state p with
    | ps_free => None (* This is an empty page, no data. *)
    | ps_programmed => Some (page_data p)
  end.

Definition check_page_state_is_free (ps : page_status) : bool :=
  match ps with
    | ps_free => true
    | _ => false
  end.

(*It donesn't need a state,if it is invaild,it will be set to trans_empty.*)
Definition data_get_record_list(pagedata:data)(lpn:page_no) : option meta_trans_record_list :=
  match pagedata with
      | metabyte _  => None
      | metarecord l => Some l
  end.

Fixpoint recordlist_get_record(l:meta_trans_record_list)(lpn:page_no) :option trans_record :=
  match l with
      | nil => None
      | cons a l' =>match a with 
                        | trans_empty => recordlist_get_record l' lpn
                        | trans_data lpn' ppn' offset => if beq_nat lpn lpn' then Some a else recordlist_get_record l' lpn 
                    end
end.

(*It's can't exist,because the page must write in once*)

(* Fixpoint recordlist_set_record(l:meta_trans_record_list)(lpn:page_no) :option meta_trans_record_list := *)
(*   match l with *)
(*       | nil => None *)
(*       | cons a l' =>match a with  *)
(*                         | trans_empty => recordlist_get_record l' lpn *)
(*                         | trans_data lpn' ppn'=> if beq_nat lpn lpn' then Some a else recordlist_get_record l' lpn  *)
(*                     end *)
(* end. *)
 
(********* Nand chip Operations ***************)
Definition nand_read_page (c: chip) (pbn: block_no) (poff: page_off) : option (prod data page_oob_nat) :=
  test (bvalid_block_no pbn);
  do b <-- chip_get_block c pbn;
  test (bvalid_page_off poff);
  do p <-- block_get_page b poff;
  ret (page_data p, page_oob p).

Definition nand_write_page (c: chip) (pbn: block_no) (off: page_off) (d: data) (oob: page_oob_nat): option chip :=
  test (bvalid_block_no pbn);
  do b <-- chip_get_block c pbn;
  test (bvalid_page_off off);
  test (ble_nat (next_page b) off);
  do p <-- block_get_page b off;
  test (check_page_state_is_free (page_state p));
  do b' <-- block_set_page b off (mkpage d oob ps_programmed);
  do b'' <-- block_set_next_page b' (S off);
  do c' <-- chip_set_block c pbn b'';
  ret c'.
                 
Definition nand_erase_block (c: chip) (pbn: block_no) : option chip :=
  test (bvalid_block_no pbn);
  do b <-- chip_get_block c pbn;
  let b' := erased_block (block_erase_count b) in 
  do c' <-- chip_set_block c pbn b';
  ret c'.

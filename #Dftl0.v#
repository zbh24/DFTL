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
(* ************************************************************************** *)

(* 

*)

(* ************* ************************************* *****)
(* ftl interface *)

Require Import ListEx.
Require Import Monad.
Require Import Data.
Require Import Params.
Require Import Nand.


(*
Cache mapping table

The cmt_record is (lpn,ppn,flag,time).The init cmt is all the cmt_empty.
*)

Inductive flag :Set := 
 | dirty:flag 
 | clean:flag.

Inductive cmt_record: Set := 
| cmt_empty
| cmt_trans(lpn:page_no)(pbn:block_no)(offset:nat)(is_dirty:flag).


Definition cache_mapping_table := list cmt_record.

Fixpoint  find_empty_cmt(cmt:cache_mapping_table) (i:nat): option nat := 
  match cmt with
  | nil => None
  | cons a cmt' => match a with
                     | cmt_empty => Some i
                     | _ => find_empty_cmt cmt' (S i)
                   end
end.

Definition cmt_get(cmt : cache_mapping_table) (loc: nat) : option cmt_record :=
  list_get cmt loc.

Definition cmt_set(cmt: cache_mapping_table) (loc: nat) (newrecord:cmt_record): option cache_mapping_table :=
  list_set cmt loc newrecord.

Definition cmt_get_trans(record:cmt_record) : option (prod (prod block_no page_no) flag)  :=
  match record with
      | cmt_empty => None
      | cmt_trans lpn pbn off f => ret((pbn,off),f)
end.

Fixpoint cmt_in (cmt:cache_mapping_table) (lpn:page_no) :bool :=
  match cmt with
      | nil => false
      | cons a cmt' => match a with
                           | (cmt_trans lpn' _ _ _) => if beq_nat lpn lpn' then true else cmt_in cmt' lpn
                           | _ => cmt_in cmt' lpn
                       end
  end.

Fixpoint find_cmtrecord(cmt:cache_mapping_table)(lpn:page_no)(i:nat) : option nat :=
  match cmt with
    | nil => None
    | cons a cmt' => match a with 
                         |(cmt_trans lpn' _ _ _) =>if beq_nat lpn' lpn then Some i else find_cmtrecord cmt' lpn (S i)  
                         | _ => find_cmtrecord cmt' lpn (S i)
                     end
end.

Fixpoint remove_cmt(cmt:cache_mapping_table) (lpn:page_no):  cache_mapping_table :=
  match cmt with
    | nil => nil
    | cons a cmt' => match a with 
                         |(cmt_trans lpn' _  _ _) =>if beq_nat lpn' lpn then cmt' else cons a (remove_cmt cmt' lpn)
                         | _ => cons a (remove_cmt cmt' lpn)
                     end
end.

Fixpoint insert_cmt (cmt:cache_mapping_table) (record:cmt_record) (num:nat) :cache_mapping_table :=
  match num with
      | O => cons record cmt
      | S i => match cmt with
                 | nil => nil
                 | cons a cmt' => (cons a (insert_cmt cmt' record i ) )
                end
   end.

Definition remove_head(cmt:cache_mapping_table) : option cache_mapping_table :=
  match cmt with
      | nil => None
      | cons a cmt' => Some cmt'
end.

Fixpoint append_tail(cmt:cache_mapping_table)(newrecord:cmt_record) : cache_mapping_table :=
  match cmt with 
      | nil => cons newrecord nil
      | cons a nil => cons a (cons newrecord nil)
      | cons a cmt' => cons a (append_tail cmt' newrecord)
end.

(*Init the cache mapping table *)
Fixpoint init_cmt(cmt:cache_mapping_table)(i:nat): option cache_mapping_table :=
  match i with
|  O => None
|  S O => Some cmt
|  S i' => init_cmt (list_append cmt cmt_empty) i'
end.

Definition blank_cmt : cache_mapping_table :=
  list_repeat_list CMT_LENGTH cmt_empty.

(*
Global translation table

The length of the gtd is fixed.The record is(index,ppn).
*)

Inductive gtd_record: Set := 
| gtd_empty
| gtd_trans (pbn:block_no) (offset:nat ).


Definition global_mapping_directory := list gtd_record.

(* Definition gtd_len(gtd:global_mapping_directory) : nat :=  *)
(*   length gtd. *)

Definition gtd_get(gtd:global_mapping_directory)(loc: nat) : option gtd_record :=
  list_get gtd loc.

Definition gtd_set(gtd:global_mapping_directory) (loc: nat) (newrecord:gtd_record): option global_mapping_directory :=
  list_set gtd loc newrecord.

(* SearchAbout andb. *)
Fixpoint gtd_look_by_record(gtd:global_mapping_directory)(lbn:block_no) (off:nat) (num:nat) : option nat :=
  match gtd with
      | nil  => None
      | cons record' gtd' => match record' with
                                 | gtd_empty => gtd_look_by_record gtd' lbn off (S num)
                                 | gtd_trans lbn' off' => if andb (beq_nat lbn lbn') (beq_nat off off')  then Some num else gtd_look_by_record gtd' lbn off (S num) 

                             end
end.

Fixpoint gtd_look_by_lpn (gtd:global_mapping_directory) (lpn:page_no) (num:nat):option nat :=
  match gtd with
      | nil => None
      | cons record' l => if ble_nat lpn (pred ((S num) * RECORD_PER_TRANS)) then Some num else gtd_look_by_lpn l lpn (S num)
 end.

Definition  gtd_get_trans_by_lpn(gtd:global_mapping_directory)(lpn:page_no):option (prod nat nat) :=
  do gtd_loc <-- gtd_look_by_lpn gtd lpn 0;
  do record <-- gtd_get gtd gtd_loc;
  match record with
      | gtd_empty => None
      | gtd_trans pbn off => ret (pbn,off)
end.

Fixpoint init_gtd(gtd:global_mapping_directory)(i:nat): option global_mapping_directory :=
  match i with
|  O => None
|  S O => Some gtd
|  S i' => init_gtd (list_append gtd gtd_empty) i'
end.

Definition blank_gtd : global_mapping_directory :=
  list_repeat_list GTD_LENGTH gtd_empty.

(* Compute ( *)
(*  do gtd <-- Some blank_gtd; *)
(*  do i <-- gtd_look_by_lpn gtd 7 0; *)
(*  ret i *)
(* ). *)
(*
Trans_page data

The data of trans_page is (lpn,ppn)
*)

(* Inductive trans_record: Set := *)
(*   | trans_empty *)
(*   | trans_data(lpn:page_no)(ppn:page_no). *)

(* Definition trans_page := list trans_record. *)

(* Definition trans_len(trans:trans_page) : nat :=  *)
(*   length trans. *)

(* Definition trans_get(trans:trans_page)(loc: nat) : option trans_record := *)
(*   list_get trans loc. *)

(* Definition trans_set(trans:trans_page) (loc: nat) (newrecord:trans_record): option trans_page := *)
(*   list_set trans loc newrecord. *)


(*
FTL block state
*)

Inductive ftl_block_state : Set :=
  | bs_invalid
  | bs_erased
  | bs_data
  | bs_trans.

Inductive ftl_page_state : Set :=
  | ps_invalid
  | ps_erased
  | ps_data  (lpn:page_no)
  | ps_trans (gtd_loc:nat).

Definition page_state_table := list ftl_page_state.

Definition pst_get(pst:page_state_table)(loc: nat) : option ftl_page_state :=
  list_get pst loc.

Definition pst_set(pst:page_state_table) (loc: nat) (newstate:ftl_page_state): option page_state_table :=
  list_set pst loc newstate.

Definition pst_set_all (state:ftl_page_state):page_state_table  :=
  list_repeat_list  PAGES_PER_BLOCK state.

(*
Block_info_table
*)

Record block_info : Set := 
  mk_bi {
      bi_state: ftl_block_state;
      bi_used_pages: nat;
      bi_erase_count: nat;
      bi_page_state: page_state_table
    }.

Definition block_info_table :=  list block_info.

Definition bi_set_state (bi : block_info) (bi_state : ftl_block_state) : block_info :=
  mk_bi bi_state (bi_used_pages bi) (bi_erase_count bi) (bi_page_state bi).

(* set both the block and page state *)
Definition pi_set_state (bi : block_info) (bi_state : ftl_block_state) (bi_page_state:page_state_table) : block_info :=
  mk_bi bi_state (bi_used_pages bi) (bi_erase_count bi) bi_page_state.

Definition bit_get (bit: block_info_table) (b: block_no) 
     : option block_info := 
  list_get bit b.

Definition bit_update (bit: block_info_table) (b: block_no) (bi: block_info)
      : option block_info_table := 
  list_set bit b bi.

(* In FTL, a block is initialized to be 'bs_invalid' *)
Definition blank_bi : block_info := 
  mk_bi bs_erased 0 0 (pst_set_all ps_erased).

(*
Free block queue

Free blocks are those not used, and each of them can be invalid or
erased (filled with \og{0xFF}). All the free blocks are put into a 
queue, where a new allocated block is get from the head.
*)

Definition block_queue := list block_no.

Definition fbq_enq (fbq : block_queue) (b : block_no) : option (block_queue) :=
  Some (list_append fbq b).

Definition fbq_deq (fbq : block_queue) : option (prod block_no (block_queue)) := 
  match fbq with
    | nil => None
    | cons b fbq' => Some (b, fbq')
  end.

Definition fbq_in (fbq: list block_no) (pbn: block_no) : bool := list_inb beq_nat fbq pbn.

Definition fbq_get (fbq: list block_no) (i: nat) : option block_no := list_get fbq i.

Definition check_block_is_full (bi: block_info) : bool :=
  match blt_nat (bi_used_pages bi) PAGES_PER_BLOCK with 
    | true => false
    | false => true
  end.

(*

Currnt data/translation block

*)

(* Definition current_data_block := block_no. *)

(* Definition current_trans_block := block_no. *)

(*
FTL structure
*)

Record FTL : Set := 
  mk_FTL {
      ftl_bi_table: block_info_table;
      ftl_free_blocks: block_queue;
      ftl_cmt_table:cache_mapping_table;
      ftl_gtd_table:global_mapping_directory;
      current_data_block:block_no;
      current_trans_block:block_no
    }.

Definition ftl_update_bit (f: FTL) (bit: block_info_table) : option FTL :=
  ret mk_FTL bit (ftl_free_blocks f) (ftl_cmt_table f) (ftl_gtd_table f) (current_data_block f) (current_trans_block f).

Definition ftl_update_fbq (f: FTL) (fbq: block_queue) : option FTL :=
  ret mk_FTL (ftl_bi_table f) fbq  (ftl_cmt_table f) (ftl_gtd_table f) (current_data_block f) (current_trans_block f).

Definition ftl_update_cmt (f: FTL) (cmt: cache_mapping_table) : option FTL :=
  ret mk_FTL (ftl_bi_table f)  (ftl_free_blocks f) cmt (ftl_gtd_table f) (current_data_block f) (current_trans_block f).

Inductive freebq_state : Set :=
  | fbqs_abundant
  (* | fbqs_needgc *)
  | fbqs_scarce.

(* IMPORTANT !!! *)
Definition check_freebq_count (freebq: block_queue): freebq_state :=
  match (ble_nat MIN_FREE_BLOCKS (length freebq)) with
    | false => fbqs_scarce
    | true => fbqs_abundant
  end.


(* **************************************************** 

   * ReadBlock/WriteBlock Operations
*)

Definition read_block (c: chip) (pbn: block_no) (off: page_off) : option data :=
  (* read the page from "off" in pbn_data *)
  do [d, o] <-- (nand_read_page c pbn off);

  (* return the data in the page *)
  ret d.

Definition read_block_oob (c: chip) (pbn: block_no) (off: page_off) : option (prod data page_oob_nat) :=
  (* read the page from "off" in pbn_data *)
  do [d, o] <-- (nand_read_page c pbn off);
  ret (d,o).


Definition write_data_block (c: chip) (pbn_bi: block_info) (pbn: block_no) 
           (loc: page_off) (d: data) (oob:page_oob_nat)(page_state:ftl_page_state): option (prod chip block_info) := 
  (* write the data to "pbn#loc", return c' *)
  let pst := bi_page_state pbn_bi in
  do c' <-- (nand_write_page c pbn loc d oob);
  do pst' <-- pst_set pst loc page_state;
  (* return bi := <bi_state, used+1, ec> *)
  let bi' := mk_bi (bi_state pbn_bi) ((bi_used_pages pbn_bi)+1) (bi_erase_count pbn_bi) pst' in

  ret  (c', bi').

(* Definition read_trans_block (c: chip) (bi: block_info) (pbn_log: block_no) (off: page_off) : option data := *)
(*   (* find the lastest log page for "poff" in 'bk' , return the log-location *) *)
(*   do loc <-- (find_page_in_log_block bi off); *)

(*   (* read the page from "loc" in pbn_log *) *)
(*   do [d, o] <-- (nand_read_page c pbn_log loc);  *)

(*   (* return the data in the page *) *)
(*   ret d. *)

(* Definition write_trans_block *)

(*
FTL read algorithm

*)

(* **************************************************** 
* Alloc_Block 

Allocation block routine, no GC yet. But I believe that it will be 
not difficult to add a simple GC. 

*)

Definition alloc_block (c: chip) (f: FTL) : option (prod block_no (prod chip FTL)) :=
  let bit := ftl_bi_table f in
  let fbq := ftl_free_blocks f in
  match (check_freebq_count fbq) with
    | fbqs_abundant =>
        do [b, fbq'] <-- fbq_deq fbq; 
        do bi_free <-- bit_get bit b;
        match bi_state bi_free with
          | bs_erased => 
              (* TODO:  we don't need to update bit. No,we need,we set the used_pages and pages_state *)
              do bit' <-- bit_update bit b (mk_bi bs_erased 0 (bi_erase_count bi_free) (pst_set_all ps_erased));
              ret (b, (c, (mk_FTL bit'  fbq' (ftl_cmt_table f) (ftl_gtd_table f) (current_data_block f) (current_trans_block f) )))
          | bs_invalid => 
              do c' <-- nand_erase_block c b;
              do bit' <-- bit_update bit b (mk_bi bs_erased 0 (1 + bi_erase_count bi_free) (pst_set_all ps_erased));
              ret (b, (c',(mk_FTL bit' fbq' (ftl_cmt_table f) (ftl_gtd_table f) (current_data_block f) (current_trans_block f) )))

          | bs_data => None

          | bs_trans => None
        end 
  
    | _ => None
  end.

Definition bit_set_state (bit: block_info_table) (pbn: block_no) (st: ftl_block_state) (pst:page_state_table) 
  : option block_info_table :=
  do bi <-- bit_get bit pbn;
  do bi' <-- Some (mk_bi st (bi_used_pages bi) (bi_erase_count bi) pst);
  do bit' <-- bit_update bit pbn bi';
  ret bit'.

Definition bit_get_bstate (f: FTL) (pbn: block_no) : option ftl_block_state := 
  do bi <-- bit_get (ftl_bi_table f) pbn;
  ret (bi_state bi).

(* **************************************************** 
* Auxiliary Routines for update Meta-Data 
*)

Definition free_block (bit: block_info_table) (fbq: block_queue) (pbn: block_no)
  : option (prod block_info_table block_queue) :=
  do bi <-- bit_get bit pbn;
  do pst <-- Some (pst_set_all ps_invalid);
  do bi' <-- Some (mk_bi bs_invalid (bi_used_pages bi) (bi_erase_count bi) pst);
  do bit' <-- bit_update bit pbn bi';
  do fbq' <-- fbq_enq fbq pbn;
  ret (bit', fbq').

Definition zero_page := (zero_data PAGE_DATA_SIZE).

(*
* Check the current_data_block and current_trans_block
*)

Definition check_current_block(bit:block_info_table) (pbn: block_no):option bool :=
  do bi <-- bit_get bit pbn; 
  match check_block_is_full bi with
     | false => Some false
     | true => Some true
  end.

Fixpoint find_trans_in_metatrans(l:meta_trans_record_list) (lpn:page_off) : option (prod nat nat) :=
  match l with
      | nil => None
      | cons record l' =>match record with
                             | trans_empty => find_trans_in_metatrans l' lpn
                             | trans_data lpn' pbn' off' => if beq_nat lpn lpn' then Some (pbn',off') else find_trans_in_metatrans l' lpn 
                          end
end.

(* Definition div (n1:nat)(n2:nat):nat := 1. *)

(* Definition mod (n1:nat)(n2:nat):nat := 1. *)
 
Definition check_block_full(bi:block_info): bool :=
  do num <<-- (bi_used_pages bi); 
  match blt_nat num PAGES_PER_BLOCK with
      | true =>  false
      | false => true
 end.

(**********************************************************************)

(*
Init the ftl and nand
*)
Definition bit_init : block_info_table :=
  list_repeat_list BLOCKS blank_bi.

Definition cmt_init :cache_mapping_table := blank_cmt.

Definition gtd_init_empty : global_mapping_directory := blank_gtd.

Definition fbq_init : block_queue :=
  list_make_nat_list BLOCKS.

Definition bit_init_current:option block_info_table :=
  do bit <-- Some bit_init;
  do bit' <-- bit_update bit 0 (mk_bi bs_data 0 0 (pst_set_all ps_erased) );
  do bit'' <-- bit_update bit' 1 (mk_bi bs_trans 0 0  (pst_set_all ps_erased) );
  ret bit''.

Definition fbq_init_current:option block_queue :=
  do [_,fbq'] <-- fbq_deq fbq_init;
  do [_,fbq''] <-- fbq_deq fbq';
  ret fbq''.

Definition ftl_init : option FTL :=
   do bit <-- bit_init_current;
   do fbq <-- fbq_init_current;
   ret (mk_FTL bit fbq cmt_init gtd_init_empty 0 1).

(* Fixpoint gtd_init_trans(c:chip) (f:FTL) (gtd:global_mapping_table) (num:nat):option FTL := *)
(*   match num with *)
(*       | O => ret f *)
(*       | S i => do cur_trans <-- Some (current_trans_block f); *)
(*                do bit <-- ftl_bi_table f; *)
(*                do cur_trans_bi <-- bit_get bit cur_trans; *)
(*                match  check_block_full cur_trans_bi with *)
(*                    | false => do off <-- Some (bi_used_pages cur_trans_bi); *)
(*                               do gtd' <-- gtd_set gtd (minus 32 num) (gtd_trans cur_trans off); *)
(*                               do bit' <-- bit_update bit'; *)
(*                               do f' <-- (mk_FTL ( *)

(*
The meta_trans_data Definition && Operations

*)
Definition data_metatrans_get(dmt : meta_trans_record_list) (loc: nat) : option trans_record :=
  list_get dmt loc.

Definition data_metatrans_set(dmt: meta_trans_record_list) (loc: nat) (newrecord:trans_record): option meta_trans_record_list :=
  list_set dmt loc newrecord.

Definition blank_dmt :meta_trans_record_list  :=
  list_repeat_list RECORD_PER_TRANS trans_empty.

Fixpoint find_meta_trans_record(l:meta_trans_record_list)(lpn:page_no)(i:nat) :option nat :=
  match l with
      | nil =>None
      | cons record l' =>  match record with
                           | trans_empty => find_meta_trans_record l' lpn (S i)
                           | trans_data lpn' _ _ => if beq_nat lpn lpn' then Some i else find_meta_trans_record l' lpn (S i)
                          end
end.

Fixpoint find_meta_trans_empty(l:meta_trans_record_list)(lpn:page_no)(i:nat) :option nat :=
  match l with
      | nil =>None
      | cons record l' =>  match record with
                           | trans_empty => Some i
                           | trans_data lpn' _ _ => find_meta_trans_empty l' lpn (S i)
                          end
end.

Fixpoint get_meta_trans_record (l:meta_trans_record_list)(lpn:page_no)(i:nat) : option (prod block_no page_no) :=
  (* do i <-- find_meta_trans_record l lpn 0; *)
  do record <-- data_metatrans_get l i;
  match record with
      | trans_data lpn pbn off => ret (pbn,off)
      | _ => None
  end.

Fixpoint copy_data_trans(l:meta_trans_record_list) (lpn:page_no) (newrecord:trans_record) : option meta_trans_record_list :=
  match find_meta_trans_record l lpn 0 with
      | Some loc => do l' <-- data_metatrans_set l loc newrecord;
                    ret l'                   
      | None => do empty_loc <-- find_meta_trans_empty l lpn 0;
                do l' <-- data_metatrans_set l empty_loc newrecord;
                ret l' 
   end.

(*
Invalid the block page
*)
Definition invalid_old_page(bit:block_info_table)(pbn:block_no)(off:nat) :option block_info_table :=
  do bi <-- bit_get bit pbn;
  do pst <-- Some (bi_page_state bi);
  do pst' <--  pst_set pst off ps_invalid;
  do bi' <-- Some (pi_set_state bi (bi_state bi) pst');
  do bit' <-- bit_update bit pbn bi';
  ret bit'.

(*
copy the trans_page_data(trans_pbn,trans_off) to current block  page or new allock page 
for updating the pbn off
*)

Definition copy_trans_page(c:chip)(f:FTL)(lpn:page_no)(trans_pbn:block_no)(trans_off:nat)(pbn:block_no)(off:nat): option (prod chip FTL) :=
  let bit := ftl_bi_table f in
  let fbq := ftl_free_blocks f in
  let cmt := ftl_cmt_table f in
  let gtd := ftl_gtd_table f in
  let cur_trans := current_trans_block f in
  let cur_data := current_data_block f in
  do d <-- read_block c trans_pbn trans_off;
  match d with
    | metabyte _ => None
    | metarecord meta_list => do new_list <-- copy_data_trans meta_list lpn (trans_data lpn pbn off); 
                              do cur_bi <-- bit_get bit cur_trans;
                              do gtd_loc <-- gtd_look_by_lpn gtd lpn 0;
                              match check_block_full cur_bi with
                                | true =>(* If it is full *) 
                                         do [new_trans,cfx] <-- alloc_block c f;
                                         do [c',f'] <-- Some cfx;
                                         do bi <-- bit_get (ftl_bi_table f') new_trans;
                                         do bi' <-- Some (bi_set_state bi bs_trans);
                                         (* Repeat *)
                                         do [c'',bi''] <-- write_data_block c' bi' new_trans 0 (metarecord new_list) (Some (gtd_loc, 0)) (ps_trans gtd_loc);
                                         do bit' <-- bit_update (ftl_bi_table f') new_trans bi'';
                                         (*Invalidate the old trans one*)
                                         do bit'' <-- invalid_old_page bit' trans_pbn trans_off;
                                         (*Invalidate the old data one*)
                                         match find_meta_trans_record meta_list lpn 0 with
                                             | None =>  (* update the gtd *)
                                                        do gtd' <-- gtd_set gtd gtd_loc (gtd_trans new_trans 0) ;
                                                        ret(c'',(mk_FTL bit'' (ftl_free_blocks f') (ftl_cmt_table f') gtd' cur_data new_trans) )
                                                           
                                             | Some i => do [old_data,old_off] <--  get_meta_trans_record meta_list lpn i;
                                                         do bit''' <-- invalid_old_page bit'' old_data old_off;
                                                         do gtd' <-- gtd_set gtd gtd_loc (gtd_trans new_trans 0) ;
                                                         ret(c'',(mk_FTL bit''' (ftl_free_blocks f') (ftl_cmt_table f') gtd' cur_data new_trans) )
                                        end
                                                        
                                | false => 
                                           do cur_off <-- Some (bi_used_pages cur_bi);
                                           do [c',bi'] <-- write_data_block c cur_bi cur_trans cur_off (metarecord new_list) (Some(gtd_loc, 0)) (ps_trans gtd_loc);
                                           do bit' <-- bit_update bit cur_trans bi';
                                           (*Invalide the old trans page*)
                                           do bit'' <-- invalid_old_page bit' trans_pbn trans_off;
                                           (*Invalidate the old data one*)
                                           match find_meta_trans_record meta_list lpn 0 with
                                             | None =>  (* update the gtd,find the gtd_loc *)
                                                        do gtd' <-- gtd_set gtd gtd_loc (gtd_trans cur_trans cur_off);
                                                        ret (c',(mk_FTL bit'' fbq cmt  gtd' cur_data cur_trans ) )

                                             | Some i => do [old_data,old_off] <--  get_meta_trans_record meta_list lpn i;
                                                         do bit''' <-- invalid_old_page bit'' old_data old_off;
                                                         (* update the gtd,find the gtd_loc *)
                                                         do gtd' <-- gtd_set gtd gtd_loc (gtd_trans cur_trans cur_off);
                                                         ret (c',(mk_FTL bit''' fbq cmt  gtd' cur_data cur_trans ) )
                                            end
                               end
end.
   
Definition write_trans_page(c:chip)(f:FTL)(lpn:page_no) (pbn:block_no)(off:nat): option (prod chip FTL) :=
  let bit := ftl_bi_table f in
  let fbq := ftl_free_blocks f in
  let cmt := ftl_cmt_table f in
  let gtd := ftl_gtd_table f in
  let cur_trans := current_trans_block f in
  let cur_data := current_data_block f in
  do meta_list <-- Some (blank_dmt);
  do new_list <-- copy_data_trans meta_list lpn (trans_data lpn pbn off); 
  do cur_bi <-- bit_get bit cur_trans;
  do gtd_loc <-- gtd_look_by_lpn gtd lpn 0;
  match check_block_full cur_bi with
       | true =>(* If it is full *) 
             do [new_trans,cfx] <-- alloc_block c f;
             do [c',f'] <-- Some cfx;
             do bi <-- bit_get (ftl_bi_table f') new_trans;
             do bi' <-- Some (bi_set_state bi bs_trans);
             (* Repeat *)
             do [c'',bi''] <-- write_data_block c' bi' new_trans 0 (metarecord new_list) (Some (gtd_loc, 0)) (ps_trans gtd_loc);
             do bit' <-- bit_update (ftl_bi_table f') new_trans bi'';
             do gtd' <-- gtd_set gtd gtd_loc (gtd_trans new_trans 0) ;
             ret(c'',(mk_FTL bit' (ftl_free_blocks f') (ftl_cmt_table f') gtd' cur_data new_trans) )
                                        
                                                        
       | false => 
            do cur_off <-- Some (bi_used_pages cur_bi);
            do [c',bi'] <-- write_data_block c cur_bi cur_trans cur_off (metarecord new_list) (Some (gtd_loc, 0)) (ps_trans gtd_loc);
            do bit' <-- bit_update bit cur_trans bi';
            do gtd' <-- gtd_set gtd gtd_loc (gtd_trans cur_trans cur_off);
            ret (c',(mk_FTL bit' fbq cmt  gtd' cur_data cur_trans ) )                     
end.
                                                                                 
Definition FTL_read(c:chip)(f:FTL)(lpn:page_no) : option (prod data (prod chip FTL) ) :=
  let bit := ftl_bi_table f in
  let fbq := ftl_free_blocks f in
  let cmt := ftl_cmt_table f in
  let gtd := ftl_gtd_table f in
  (* test valid_page_off off; *)
  (* If the lpn in the cmt *)
  match find_cmtrecord cmt lpn 0 with
      | Some num =>
                  (* Do the read change the priitoty *)
                  do record <-- cmt_get cmt num;
                  match record with
                   | cmt_empty => None
                   | cmt_trans lpn' pbn' off' flag' =>  
                                              match find_empty_cmt cmt 0 with
                                                  | None =>  do cmt' <-- Some (remove_cmt cmt lpn);
                                                             do cmt'' <-- Some (append_tail cmt' record);
                                                             do d <-- read_block c pbn' off';
                                                             ret (d,(c,mk_FTL (ftl_bi_table f) (ftl_free_blocks f) cmt'' (ftl_gtd_table f) (current_data_block f) (current_trans_block f) ) )
                                                  | Some i => do cmt' <-- Some (remove_cmt cmt lpn);
                                                              do cmt'' <-- Some (insert_cmt cmt' record (pred i) );
                                                              do d <-- read_block c pbn' off';
                                                              ret (d,(c,mk_FTL (ftl_bi_table f) (ftl_free_blocks f) cmt'' (ftl_gtd_table f) (current_data_block f) (current_trans_block f) ) )
                                               end                                                            
                  end
      | None => do gtd_loc <-- gtd_look_by_lpn gtd lpn 0;
                do gtd_record <-- gtd_get gtd gtd_loc;
                match gtd_record with
                   | gtd_empty => None
                   | gtd_trans trans_lbn trans_offset =>
                             do [data,oob] <-- nand_read_page c trans_lbn trans_offset;
                             match data with
                                   | metabyte _ => None
                                   | metarecord meta_trans_list =>do [data_pbn,data_off] <-- find_trans_in_metatrans meta_trans_list lpn;
                                                                  match find_empty_cmt cmt 0 with
                                                                    | Some i =>(* Thec cmt is not full ,still have empty location *) 
                                                                               (* If find the empty the empty must in the end,cmt_set and append_tail is both ok *)
                                                                               do newcmt <-- cmt_set cmt i (cmt_trans lpn data_pbn data_off clean);
                                                                               do d <-- read_block c data_pbn data_off;
                                                                               ret (d,(c,mk_FTL (ftl_bi_table f) (ftl_free_blocks f) newcmt (ftl_gtd_table f) (current_data_block f) (current_trans_block f)))
                                                                    
                                                                    | None =>  (*If it doesn't find the empty,the cmt is full *)
                                                                               do head <-- cmt_get cmt 0;
                                                                               match head with 
                                                                                | cmt_trans h_lpn h_pbn h_off flag'' => 
                                                                                     match flag'' with 
                                                                                       | clean =>
                                                                                                 do newcmt' <-- remove_head cmt;
                                                                                                 do newcmt'' <-- Some (append_tail newcmt' (cmt_trans lpn data_pbn data_off clean) );
                                                                                                 do d <-- read_block c data_pbn data_off;
                                                                                                 ret (d,(c,mk_FTL (ftl_bi_table f) (ftl_free_blocks f) newcmt'' (ftl_gtd_table f) (current_data_block f) (current_trans_block f))) 
                                                                                       | drity => 
                                                                                                 (* it is dirty *)
                                                                                                 (*find the the trans_page for h_lpn *)
                                                                                                 do newcmt' <-- remove_head cmt;
                                                                                                 do newcmt'' <-- Some (append_tail newcmt' (cmt_trans lpn data_pbn data_off clean) );
                                                                                                 do newf <-- ftl_update_cmt f newcmt''; 
                                                                                                 do d <-- read_block c data_pbn data_off;
                                                                                                 match gtd_get_trans_by_lpn gtd h_lpn with
                                                                                                     | Some _ =>
                                                                                                          do [h_trans_pbn,h_trans_off] <-- gtd_get_trans_by_lpn gtd h_lpn;
                                                                                                          do [c',f'] <-- copy_trans_page c newf h_lpn h_trans_pbn h_trans_off h_pbn h_off;
                                                                                                          ret (d,(c', f'))
                                                                                                     | None => 
                                                                                                          do [c',f'] <-- write_trans_page c newf h_lpn h_pbn h_off;
                                                                                                          ret (d,(c',f'))
                                                                                                  end
                                                                                         end
                                                                                | cmt_empty => None
                                                                               end
      
                                                                    end
                                                                                          
                                end
                  end
end.                         

(* Definition gtd_set_trans(c:chip) (f:FTL) (lpn:nat) :option (prod FTL) := *)
(*   let bit := ftl_bi_table f in *)
(*   let fbq := ftl_free_blocks f in *)
(*   let cmt := ftl_cmt_table f in *)
(*   let gtd := ftl_gtd_table f in *)
(*   let cur_trans := current_trans_block f in *)
(*   let cur_data := current_data_block f in *)
(*   do loc <-- gtd_look_by_lpn gtd lpn;  *)
(*   do cur_trans_bi <-- bit_get bit cur_trans; *)
(*   match check_block_full cur_trans_bi with *)
(*       | false => do off <-- Some (bi_used_pages cur_trans_bi); *)
(*                  do gtd'<-- gtd_set gtd loc (gtd_trans cur_trans off); *)
(*                  do pst <-- Some (bi_page_state cur_trans_bi); *)
(*                  do pst' <-- pst_set pst off (ps_trans loc); *)
(*                  do new_bi <-- Some (mk_bi (bi_state cur_trans) ((bi_used_pages cur_trans) + 1) (bi_erase_count cur_trans) pst'); *)
(*                  do bit' <-- bit_update bit cur_trans new_bi; *)
(*                  ret (mk_FTL bit' fbq cmt gtd' cur_data cur_trans); *)
      
(*       | true => do [c',f'] <-- alloc c f; *)

                
Definition cmt_update_when_ftl_write(c:chip) (f:FTL) (lbn:block_no) (loff:nat):option (prod chip FTL) :=
  let bit := ftl_bi_table f in
  let fbq := ftl_free_blocks f in
  let cmt := ftl_cmt_table f in
  let gtd := ftl_gtd_table f in
  let cur_trans := current_trans_block f in
  let cur_data := current_data_block f in
  let lpn := lbn * PAGES_PER_BLOCK + loff in
  do bi <-- bit_get bit cur_data;
  do poff <-- Some (pred (bi_used_pages bi) );
  match find_cmtrecord cmt lpn 0 with
                     (* The cmt don't have the record *)
                     | None =>
                           match find_empty_cmt cmt 0 with
                                (* find the cmt is not full *)
                               | Some i => do cmt' <-- cmt_set cmt i (cmt_trans lpn cur_data poff dirty);
                                           ret (c,mk_FTL bit fbq cmt' gtd cur_data cur_trans)
                               | None  =>  do record <-- cmt_get cmt 0;
                                           match record with
                                               | cmt_empty => None
                                               | cmt_trans h_lpn h_pbn h_off h_flag =>
                                                       do cmt' <-- remove_head cmt;
                                                       do cmt'' <-- Some (append_tail cmt' (cmt_trans lpn cur_data poff dirty) );
                                                       match h_flag with
                                                           | clean =>  ret (c,mk_FTL bit fbq cmt'' gtd cur_data cur_trans)
                                                           | dirty =>  (*TO DO-->Done,This is not the invalid data*)
                                                                      match gtd_get_trans_by_lpn gtd h_lpn with
                                                                          | Some _ =>
                                                                                 do [h_trans_pbn,h_trans_off] <-- gtd_get_trans_by_lpn gtd h_lpn;
                                                                                 do new_f <-- Some (mk_FTL bit fbq cmt'' gtd cur_data cur_trans);
                                                                                 do [c'',new_f'] <-- copy_trans_page c new_f  h_lpn h_trans_pbn h_trans_off h_pbn h_off;
                                                                                 ret (c'',new_f')
                                                                          | None => (* The gtd loc is empty *)
                                                                                 do f' <-- ftl_update_cmt f cmt''; 
                                                                                 do [c',f''] <-- write_trans_page c f' h_lpn h_pbn h_off;  
                                                                                 ret (c',f'')
                                                                       end
                                                       end
                                           end
                                     
                           end
                     (* It is in the cmt *)                             
                     | Some i => do record <-- cmt_get cmt i;
                                 do [old_pbn_off,f] <-- cmt_get_trans record;
                                 (* The old data_one *)
                                 do [old_pbn,old_off] <-- Some old_pbn_off;
                                 (* do cmt' <-- cmt_set cmt i (cmt_trans lpn cur_data poff dirty); *)
                                 match find_empty_cmt cmt 0 with
                                     | None => do cmt' <-- Some (remove_cmt cmt lpn);
                                               do cmt'' <-- Some (append_tail cmt' (cmt_trans lpn cur_data poff dirty) );
                                               match f with
                                                 | dirty => do bit' <-- invalid_old_page bit old_pbn old_off;
                                                           do new_f <-- Some (mk_FTL bit' fbq cmt'' gtd cur_data cur_trans);
                                                           ret (c,new_f)
                                                 | clean => (*TO DO-->Done,invalid is lazy*)
                                                            do new_f <-- Some (mk_FTL bit fbq cmt'' gtd cur_data cur_trans);
                                                            ret(c,new_f)
                                               end
                                    | Some empty_loc =>  do cmt' <-- Some (remove_cmt cmt  lpn);
                                                         do cmt'' <-- Some (insert_cmt cmt' (cmt_trans lpn cur_data poff dirty) (pred empty_loc) );
                                                          match f with
                                                            | dirty => do bit' <-- invalid_old_page bit old_pbn old_off;
                                                                      do new_f <-- Some (mk_FTL bit' fbq cmt'' gtd cur_data cur_trans);
                                                                      ret (c,new_f)
                                                            | clean => (*TO DO-->Done,invalid is lazy*)
                                                                      do new_f <-- Some (mk_FTL bit fbq cmt'' gtd cur_data cur_trans);
                                                                      ret(c,new_f)
                                                           end
                                 end
                                                 
    end.

Fixpoint get_lbnandoff_by_lpn (lpn:page_no) (num:nat) : option (prod nat nat) :=
 match num with
      | O  => None
      | S i'  => if ble_nat (i' * PAGES_PER_BLOCK) lpn then Some (i',(minus lpn (i' * PAGES_PER_BLOCK) ) ) else get_lbnandoff_by_lpn lpn i'
 end.

Definition FTL_write (c:chip) (f:FTL) (lpn:page_no) (d:data):option (prod chip FTL) :=
  let bit := ftl_bi_table f in
  let fbq := ftl_free_blocks f in
  let cmt := ftl_cmt_table f in
  let gtd := ftl_gtd_table f in
  let cur_trans := current_trans_block f in
  let cur_data := current_data_block f in
  (* let lpn := lbn * PAGES_PER_BLOCK + loff in *)
  do [lbn,loff] <-- get_lbnandoff_by_lpn lpn BLOCKS;
  do bi <-- bit_get bit cur_data;
  do poff <-- Some (bi_used_pages bi);
  match check_block_is_full bi with
      (*It is not full*)
      | false => do [c',bi'] <-- write_data_block c bi cur_data poff d (Some (lbn,loff)) (ps_data lpn);
                 (* update the page_state in the bit *)
                 do bit' <-- bit_update bit cur_data bi';
                 do new_f <-- ftl_update_bit f bit';
                 do [new_c',new_f'] <-- cmt_update_when_ftl_write c' new_f lbn loff;
                 ret (new_c',new_f')
      | true  =>  do [new_data,cfx] <-- alloc_block c f;
                  do [c',f'] <-- Some cfx;
                  do bi' <-- bit_get (ftl_bi_table f') new_data;
                  do bi'' <-- Some (bi_set_state bi' bs_data);
                  do [c'',bi'''] <-- write_data_block c' bi'' new_data 0 d (Some (lbn, loff)) (ps_data lpn);
                  do bit' <-- bit_update (ftl_bi_table f') new_data bi''';
                  do new_f <-- Some (mk_FTL bit' (ftl_free_blocks f') (ftl_cmt_table f') (ftl_gtd_table f') new_data (current_trans_block f') );
                  (* update the cmt *)
                  do [new_c',new_f'] <-- cmt_update_when_ftl_write c'' new_f lbn loff;
                  ret (new_c',new_f')                                               
 end.
                
(*

The Garbge Collection
 
*)

Definition gc_copy_trans_page (c:chip) (f:FTL) (pbn:block_no) (off:nat)(gtd_loc:nat) : option (prod chip FTL) :=
  let bit := ftl_bi_table f in
  let gtd := ftl_gtd_table f in
  let fbq := ftl_free_blocks f in
  let cur_trans := current_trans_block f in
  let cur_data := current_data_block f in
  let cmt := ftl_cmt_table f in
  let gtd := ftl_gtd_table f in
  do cur_trans_info <-- bit_get bit cur_trans; 
  do cur_trans_off <-- Some (bi_used_pages cur_trans_info); 
  do [trans_d,oob] <-- read_block_oob c pbn off;
  (* Also it can look from the page_status *)
  (* do gtd_loc <-- gtd_look_by_record gtd pbn off 0; *)
  match check_block_full cur_trans_info with
     | false  => do [c',cur_bi'] <-- write_data_block c cur_trans_info cur_trans cur_trans_off trans_d oob (ps_trans gtd_loc) ;
                 do bit' <-- bit_update bit cur_trans cur_bi';
                 (* update the gtd *)
                 do gtd' <-- gtd_set gtd gtd_loc (gtd_trans cur_trans cur_trans_off);
                 do new_f <-- Some (mk_FTL bit'  fbq cmt gtd' cur_data cur_trans);
                 ret(c',new_f)
     
     | true =>  do [new_trans,cfx] <-- alloc_block c f;
                do [c',f'] <-- Some cfx;
                do new_trans_info <-- bit_get (ftl_bi_table f') new_trans;
                do [c',cur_bi'] <-- write_data_block c' new_trans_info new_trans 0 trans_d oob (ps_trans gtd_loc);
                do bit' <-- bit_update bit new_trans cur_bi';
                (* update the gtd *)
                do gtd' <-- gtd_set gtd gtd_loc (gtd_trans new_trans 0);
                do new_f <-- Some (mk_FTL bit' (ftl_free_blocks f') cmt gtd' cur_data new_trans);
                ret(c',new_f)
 end.

Definition invalid_old_block(bit:block_info_table)(pbn:block_no) :option block_info_table :=
  do bi <-- bit_get bit pbn;
  do pst <-- Some (pst_set_all ps_invalid);
  do bi' <-- Some (pi_set_state bi (bs_invalid) pst);
  do bit' <-- bit_update bit pbn bi';
  ret bit'.
                                                     
Fixpoint  gc_trans(c:chip) (f:FTL) (pbn:block_no) (i:nat) :option (prod chip FTL) :=
  let bit := ftl_bi_table f in
  let fbq := ftl_free_blocks f in
  let cmt := ftl_cmt_table f in
  let gtd := ftl_gtd_table f in
  let cur_trans := current_trans_block f in
  let cur_data := current_data_block f in
  do bi <-- bit_get bit pbn;
  do pst <-- Some ( bi_page_state bi );
  do ps <-- pst_get pst i;
  match i with
      | O => (* free_block also will do this *)
             do bit' <-- invalid_old_block bit pbn;
             ret(c,(mk_FTL bit' fbq cmt gtd cur_data cur_trans) )
              
      | S i' =>  match ps with
                    | ps_trans gtd_loc =>  do [c',f'] <-- gc_copy_trans_page c f pbn i' gtd_loc;
                                           gc_trans c' f' pbn i'
                                                 
                    | _ =>  gc_trans c f pbn i'
                            
                 end
   end.

(*
TO DO Invalid the old_data,but copy_trans_page do this
*)

Definition gc_copy_data_page (c:chip) (f:FTL) (pbn:block_no) (off:nat) (lpn:page_no): option (prod (prod nat  nat) (prod chip FTL) ) :=
  let bit := ftl_bi_table f in
  let gtd := ftl_gtd_table f in
  let fbq := ftl_free_blocks f in
  let cur_trans := current_trans_block f in
  let cur_data := current_data_block f in
  let cmt := ftl_cmt_table f in
  let gtd := ftl_gtd_table f in
  do cur_data_info <-- bit_get bit cur_data; 
  do cur_data_off <-- Some (bi_used_pages cur_data_info); 
  do [data_d,oob] <-- read_block_oob c pbn off;
  match check_block_full cur_data_info with
     | false  => do [c',cur_bi'] <-- write_data_block c cur_data_info cur_data cur_data_off data_d oob (ps_data lpn) ;
                 do bit' <-- bit_update bit cur_data cur_bi';
                 do new_f <-- Some (mk_FTL bit'  fbq cmt gtd cur_data cur_trans);
                 ret((cur_data,cur_data_off),(c',new_f))
     
     | true =>  do [new_data,cfx] <-- alloc_block c f;
                do [c',f'] <-- Some cfx;
                do new_data_info <-- bit_get (ftl_bi_table f') new_data;
                do [c',cur_bi'] <-- write_data_block c' new_data_info new_data 0 data_d oob (ps_data lpn);
                do bit' <-- bit_update bit new_data cur_bi';
                do new_f <-- Some (mk_FTL bit' (ftl_free_blocks f') cmt gtd new_data cur_trans);
                ret((new_data,0),(c',new_f))
     
 end.

Definition gc_data_copy_and_update (c:chip) (f:FTL) (pbn:block_no) (off:nat) (lpn:page_no): option (prod chip FTL) :=
  let gtd := ftl_gtd_table f in
  let cmt := ftl_cmt_table f in
  do [old_trans,old_off] <-- gtd_get_trans_by_lpn gtd lpn;
  do [pbn_off,cf] <-- gc_copy_data_page c f pbn off lpn;
  do [c',f'] <-- Some cf;
  do [new_data,new_off] <-- Some pbn_off;
  (*update the corrsponding trans_page and gtd *)
  do [c'',f''] <-- copy_trans_page c' f' lpn old_trans old_off new_data new_off;
  (* update the cmt *)
  do cmt <-- Some (ftl_cmt_table f'');
  match cmt_in cmt lpn with
      | false =>   ret (c'',f'')
      | true => do loc <-- find_cmtrecord cmt lpn 0;
                do cmt' <-- cmt_set cmt loc (cmt_trans lpn new_data new_off clean);
                do f''' <-- (ftl_update_cmt f'' cmt');
                ret (c'',f''')
   end.
                                                                                           
Fixpoint  gc_data(c:chip) (f:FTL) (pbn:block_no) (i:nat) :option (prod chip FTL) :=
  let bit := ftl_bi_table f in
  let fbq := ftl_free_blocks f in
  let cmt := ftl_cmt_table f in
  let gtd := ftl_gtd_table f in
  let cur_trans := current_trans_block f in
  let cur_data := current_data_block f in
  do bi <-- bit_get bit pbn;
  do pst <-- Some ( bi_page_state bi );
  do ps <-- pst_get pst i;
  match i with
      | O => do bit' <-- invalid_old_block bit pbn;
             ret(c,(mk_FTL bit fbq cmt gtd cur_data cur_trans) )
              
      | S i' =>  match ps with
                    | ps_data lpn =>  do [c',f'] <-- gc_data_copy_and_update c f pbn i' lpn;
                                      gc_data c' f' pbn i'
                                                 
                    | _ =>  gc_data c f pbn i'
                            
                 end
   end.                                                                                                                              
(*

The GC Opertions

The pbn has 3 limits:

1)it can't be cur_trans

2)it can't be cur_data

3)it can't be in the fbq
 
*)

Definition gc(c:chip) (f:FTL) (pbn:block_no) :option (prod chip FTL) :=
  let bit := ftl_bi_table f in
  let fbq := ftl_free_blocks f in
  let cmt := ftl_cmt_table f in
  let gtd := ftl_gtd_table f in
  let cur_trans := current_trans_block f in
  let cur_data := current_data_block f in
  do bi <-- bit_get bit pbn;
  do bs <-- Some (bi_state bi);
  match bs with
      | bs_trans => do [c',f'] <-- gc_trans c f pbn PAGES_PER_BLOCK;
                    do [bit',fbq'] <-- free_block (ftl_bi_table f') (ftl_free_blocks f') pbn;
                    do f''<-- ftl_update_bit f' bit';
                    do f''' <-- ftl_update_fbq f'' fbq';
                    ret(c',f''')
      
      | bs_data =>  do [c',f'] <-- gc_data c f pbn PAGES_PER_BLOCK;
                    do [bit',fbq'] <-- free_block (ftl_bi_table f') (ftl_free_blocks f') pbn;
                    do f''<-- ftl_update_bit f' bit';
                    do f''' <-- ftl_update_fbq f'' fbq';
                    ret(c',f''')

      | bs_erased => None

      | bs_invalid => None
  end.
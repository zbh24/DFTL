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
(*           Bihong Zhang <sa614257@mail.ustc.edu.cn>                         *)
(*                          School of Software Engineering, USTC              *)
(* ************************************************************************** *)


Require Import ListEx.
Require Import Monad.
Require Import Data.

Require Import Params.
Require Import Nand.

(* 

       DFTL Flash Translation Layer (Version 0.1) 

*)

(*
* FTL Data Structures

** Cache mapping table
   Thec Cache mapping table is a cache of the translation page.And the mapping is the page-level.

*)

Definition beq_page (page1:page_no)(page2:page_no) :bool :=
 true.

Definition cmt_record := prod (page_no) (page_no).

Definition page_mapping_table := list cmt_record.

Fixpoint cmt_get (cmt: page_mapping_table) (lpn: page_no) : option page_no :=
  match cmt with
      nil => None
      | cons (pair d1 d2) cmt' => match beq_page d1 lpn with
                         true => Some d2
                         | false => cmt_get cmt' lpn
                         end
end.
                       
Definition cmt_update (bmt: cache_mapping_table) (lbn: page_no) (record : cmt_record)
     : option block_mapping_table :=
  match record with
    | (d, l) =>
      (list_set bmt lbn (d, l))
  end.

Definition bmt_len (bmt: block_mapping_table) : nat := 
  length bmt.

(* 
** block info table
  
*)

Inductive pmt_entry : Set :=
  | pmte_empty
  | pmte_trans (lpn:page_no)(ppn:page_no).

Definition cache_mapping_table := list pmt_entry.

Inductive ftl_block_state : Set :=
  | bs_invalid
  | bs_erased
  | bs_data 
  | bs_translation.

Inductive ftl_page_state : Set :=
  | bs_invalid
  | bs_erased
  | bs_data (lpn: page_no)
  | bs_translation (lbn: block_no) (pmt: page_mapping_table).

Definition pmt_len (pmt: page_mapping_table) : nat :=
  length pmt.

Definition pmt_get (pmt: page_mapping_table) (loc: page_off) : option pmt_entry :=
  list_get pmt loc.

Definition beq_pmt_entry (pe1 pe2: pmt_entry) : bool :=
  match pe1, pe2 with
    | pmte_empty, pmte_empty => true
    | pmte_log off1, pmte_log off2 => beq_nat off1 off2
    | _, _ => false
  end.

Definition pmt_find (pmt: page_mapping_table) (pe: pmt_entry) : option page_off := 
  list_find beq_pmt_entry pmt pe.

Definition pmt_find_rev (pmt: page_mapping_table) (pe: pmt_entry) : option page_off :=
  list_find_rev beq_pmt_entry pmt pe.

Definition pmt_update (pmt: page_mapping_table) (loc: page_off) (off: page_off)
   : option page_mapping_table :=
  list_set pmt loc (pmte_log off).

Definition blank_pmt : page_mapping_table := list_repeat_list PAGES_PER_BLOCK pmte_empty.

Record block_info : Set := 
  mk_bi {
      bi_state: ftl_block_state;
      bi_used_pages: nat;
      bi_erase_count: nat
    }.

Definition bi_set_state (bi : block_info) (bi_state : ftl_block_state) : block_info :=
  mk_bi bi_state (bi_used_pages bi) (bi_erase_count bi).

Definition block_info_table :=  list block_info.

Definition bit_get (bit: block_info_table) (b: block_no) 
     : option block_info := 
  list_get bit b.

Definition bit_update (bit: block_info_table) (b: block_no) (bi: block_info)
      : option block_info_table := 
  list_set bit b bi.

(* In FTL, a block is initialized to be 'bs_invalid' *)
Definition blank_bi : block_info := 
  mk_bi bs_erased 0 0.

(* 

** Free block queue

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

(* **************************************************************************************** *)

(* The define of the FTL algorithm  *)

Record FTL : Set := 
  mk_FTL {
      ftl_bi_table: block_info_table;
      ftl_bm_table: block_mapping_table;
      ftl_free_blocks: block_queue
    }.

Definition ftl_update_bit (f: FTL) (bit: block_info_table) : option FTL :=
  ret mk_FTL bit (ftl_bm_table f) (ftl_free_blocks f).

Definition ftl_update_fbq (f: FTL) (fbq: block_queue) : option FTL :=
  ret mk_FTL (ftl_bi_table f) (ftl_bm_table f) fbq.

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

Definition bit_init : block_info_table :=
  list_repeat_list BLOCKS blank_bi.

Definition bmt_init : block_mapping_table :=
  list_repeat_list MAX_LOGICAL_BLOCKS (None, None). 

 (* check_good_blocks (i : nat) : block_queue := *)
 (*  match i with *)
 (*    | 0 => nil *)
 (*    | S i' => cons i' (check_good_blocks i') (* we assume all blocks are flawless *) *)
 (*  end. *)

Definition fbq_init : block_queue :=
  list_make_nat_list BLOCKS.

Definition ftl_init : FTL :=
  mk_FTL bit_init bmt_init fbq_init.

(* 
errcode 2 : FTL inconsistent 
*)
(*

  global invariants:

  pre-condition: (1) 0 <= lbn < MAX_LOGICAL_BLOCKS 
                 (2) 0 <= poff < LOGICAL_PAGES_PER_BLOCK

*)

(* 
  bk: the log block 
  poff: the logical page address that we are looking for
  pgn: the next free page in the block 
 
  @return: the physical offset of the page we are looking for  

*)

(* Definition find_page_in_log_block (bi: block_info) (off: page_off) : option page_off := *)
(*   match (bi_state bi) with  *)
(*     | bs_log lbn pmt => (pmt_find_rev pmt (pmte_log off)) *)
(*     | _ => None *)
(*   end. *)

(* Definition find_empty_page_in_block (bi: block_info): option page_off := *)
(*   match blt_nat (bi_used_pages bi) PAGES_PER_BLOCK with  *)
(*     | true => Some (bi_used_pages bi) *)
(*     | false => None *)
(*   end. *)
  
(* **************************************************** 

   * ReadBlock/WriteBlock Operations
*)


Definition read_log_block (c: chip) (bi: block_info) (pbn_log: block_no) (off: page_off) : option data :=
  (* find the lastest log page for "poff" in 'bk' , return the log-location *)
  do loc <-- (find_page_in_log_block bi off);

  (* read the page from "loc" in pbn_log *)
  do [d, o] <-- (nand_read_page c pbn_log loc); 

  (* return the data in the page *)
  ret d.

Definition read_data_block (c: chip) (pbn_data: block_no) (off: page_off) : option data :=
  (* read the page from "off" in pbn_data *)
  do [d, o] <-- (nand_read_page c pbn_data off);

  (* return the data in the page *)
  ret d.

Definition write_data_block (c: chip) (pbn_bi: block_info) (pbn: block_no) 
           (loc: page_off) (d: data): option (prod chip block_info) := 
  (* write the data to "pbn#loc", return c' *)
  do c' <-- (nand_write_page c pbn loc d init_page_oob);

  (* return bi := <bi_state, used+1, ec> *)
  let bi' := mk_bi (bi_state pbn_bi) ((bi_used_pages pbn_bi)+1) (bi_erase_count pbn_bi)  in

  ret  (c', bi').

(* *)

Definition bi_lbn (bi: block_info) : option block_no :=
  match (bi_state bi) with
    | bs_log lbn pmt => Some lbn
    | bs_data lbn => Some lbn
    | _ => None
  end.

Definition bi_pm_table (bi: block_info) : option page_mapping_table :=
  match (bi_state bi) with
    | bs_log lbn pmt => Some pmt
    | _ => None
  end.

Definition write_log_block (c: chip) (pbn_bi: block_info) (pbn: block_no) 
           (off: page_off) (d: data) : option (prod chip block_info) := 
  do loc <-- (find_empty_page_in_block pbn_bi);
  
  do c' <-- (nand_write_page c pbn loc d init_page_oob);
  
  do pmt <-- bi_pm_table pbn_bi;

  (* update pm_table: {loc --> off } *)
  do pmt' <-- pmt_update pmt loc off;

  do lbn <-- bi_lbn pbn_bi;
    
  let bi' := mk_bi (bs_log lbn pmt') ((bi_used_pages pbn_bi)+1)  (bi_erase_count pbn_bi) in
  ret (c', bi').

(* **************************************************** 

* Alloc_Block 

Allocation block routine, no GC yet. But I believe that it will be 
not difficult to add a simple GC. 

*)

Definition alloc_block (c: chip) (f: FTL) : option (prod block_no (prod chip FTL)) :=
  let bmt := ftl_bm_table f in
  let bit := ftl_bi_table f in
  let fbq := ftl_free_blocks f in
  match (check_freebq_count fbq) with
    | fbqs_abundant =>
        do [b, fbq'] <-- fbq_deq fbq; 
        do bi_free <-- bit_get bit b;
        match bi_state bi_free with
          | bs_erased => 
              (* TODO:  we don't need to update bit. *)
              do bit' <-- bit_update bit b (mk_bi bs_erased 0 (bi_erase_count bi_free));
              ret (b, (c, (mk_FTL bit' bmt fbq')))
          | bs_invalid => 
              do c' <-- nand_erase_block c b;
              do bit' <-- bit_update bit b (mk_bi bs_erased 0 (1 + bi_erase_count bi_free));
              ret (b, (c', (mk_FTL bit' bmt fbq')))

          | bs_data _ => None

          | bs_log _ _ => None
        end 
  
    | _ => None
  end.

(* **************************************************** 

* Auxiliary Routines for update Meta-Data 

*)

(*  The function (bit_set_state bit pbn st) :  
      bit{pbn->bi},  bi' = bi{bs_state:=st},  bit'{pbn->bi'}
*)

Definition bit_set_state (bit: block_info_table) (pbn: block_no) (st: ftl_block_state) 
  : option block_info_table :=
  do bi <-- bit_get bit pbn;
  do bi' <-- Some (mk_bi st (bi_used_pages bi) (bi_erase_count bi));
  do bit' <-- bit_update bit pbn bi';
  ret bit'.

Definition bit_get_bstate (f: FTL) (pbn: block_no) : option ftl_block_state := 
  do bi <-- bit_get (ftl_bi_table f) pbn;
  ret (bi_state bi).

(* **************************************************** 

* Free_Block 
 
Free a unused block back to the free block queue. It doesn't erase the data until FTL
tries to write new data into it.

*)

Definition free_block (bit: block_info_table) (fbq: block_queue) (pbn: block_no)
  : option (prod block_info_table (block_queue)) :=
  do bi <-- bit_get bit pbn;
  do bi' <-- Some (mk_bi bs_invalid (bi_used_pages bi) (bi_erase_count bi));
  do bit' <-- bit_update bit pbn bi';
  do fbq' <-- fbq_enq fbq pbn;
  ret (bit', fbq').

Definition zero_page := (zero_data PAGE_DATA_SIZE).

Fixpoint merge_block_fix (c: chip) (pl_bi: block_info) (pf_bi: block_info) 
         (pd: option block_no) (pl: block_no) (pf: block_no) (* (D, L, F) *)
         (poi: nat) (* offset *) {struct poi} : option (prod chip block_info) := 
  match poi with
    | O => ret (c, pf_bi)

    | S poi' => 
           let off := poi' in
           (* firstly, write the pages with lower no *)
           do [c', pf_bi'] <-- (merge_block_fix c pl_bi pf_bi pd pl pf poi');
           match (read_log_block c' pl_bi pl off) with 
             | Some d => 
                 write_data_block c' pf_bi' pf off d
             | None => 
               (
                 match pd with
                   | None => 
                       do [c'', pf_bi''] <-- write_data_block c' pf_bi' pf off zero_page;
                       ret (c'', pf_bi'')
                   | Some pbn_data =>
                     do d <-- (read_data_block c' pbn_data off); (* by Inv ##11 *)
                     do [c'', pf_bi''] <-- write_data_block c' pf_bi' pf off d;  
                     ret (c'', pf_bi'')
                 end
               )
           end
  end.

Definition merge_block (c: chip) (f: FTL) (lbn : block_no) : option (chip * FTL) % type :=
  do bit <-- Some (ftl_bi_table f);
  do bmt <-- Some (ftl_bm_table f);
  do fbq <-- Some (ftl_free_blocks f);
  do entry_to_merge <-- bmt_get bmt lbn;
  match entry_to_merge with
    | (opt_bd, Some bl) =>
      do [bf, cfx] <-- alloc_block c f;
      do [c', f'] <-- Some cfx;
      do bit' <-- Some (ftl_bi_table f') ;
      do bmt' <-- Some (ftl_bm_table f');
      do fbq' <-- Some (ftl_free_blocks f');

      (* merge_block_fix *)
      do bi_log <-- bit_get bit' bl;
      do bi_free <-- bit_get bit' bf;
      do [c_m, bi_new_data] <-- merge_block_fix c' bi_log bi_free opt_bd bl bf PAGES_PER_BLOCK;
      do bmt_m <-- bmt_update bmt' lbn (Some bf, None);
      do bit_m <-- bit_update bit' bf 
                              (bi_set_state bi_new_data (bs_data lbn));

      (* free_block bl *)
      do [bit_f, fbq_f] <-- free_block bit_m fbq' bl;

      match opt_bd with
        | None => ret (c_m, (mk_FTL bit_f bmt_m fbq_f))
        | Some bd =>
          (* free_block bd *)
          do [bit_f2, fbq_f2] <-- free_block bit_f fbq_f bd;
          ret (c_m, (mk_FTL bit_f2 bmt_m fbq_f2))
      end
        
    | (_, _) => None

  end.

(* **************************************************** 

* FTL read rouine 

*)

Definition FTL_read (c: chip) (f: FTL) (lbn : block_no) (off: page_off) : option data := 
  let bit := ftl_bi_table f in 
  let bmt := ftl_bm_table f in 
  test bvalid_page_off off;
  do bmt_entry <-- bmt_get bmt lbn;
  match bmt_entry with
    | (Some pbn_data, Some pbn_log) => 
      do pbn_log_bi <-- (bit_get bit pbn_log);
      match (read_log_block (c: chip) pbn_log_bi (pbn_log: block_no) (off: page_off)) with
       | Some d => ret d
       | None =>  
        (
           do d <-- (read_data_block (c: chip) (pbn_data: block_no) off);
           ret d
        )
      end

    | (None, Some pbn_log) => 
      do pbn_log_bi <-- (bit_get bit pbn_log);
      match (read_log_block (c: chip) pbn_log_bi (pbn_log: block_no) (off: page_off)) with
       | Some d => ret d
       | None => ret zero_page
      end

    | (Some pbn_data, None) => 
       do d <-- (read_data_block (c: chip) (pbn_data: block_no) off);
       ret d
    | (None, None) => ret zero_page
  end.

Definition bmt_update_log (bmt: block_mapping_table) (lbn: block_no) (pbn: block_no) 
  : option block_mapping_table :=
  do bme <-- bmt_get bmt lbn;
  do [data, log] <-- Some bme;
  do bme' <-- Some (data, Some pbn);
  do bmt' <-- bmt_update bmt lbn bme';
  ret bmt'.

Definition bmt_update_data (bmt: block_mapping_table) (lbn: block_no) (pbn: block_no) 
  : option block_mapping_table :=
  do bme <-- bmt_get bmt lbn;
  do [data, log] <-- Some bme;
  do bme' <-- Some (Some pbn, log);
  do bmt' <-- bmt_update bmt lbn bme';
  ret bmt'.
  
(* **************************************************** 

* FTL write rouine 

*)

Definition FTL_write (c: chip) (f: FTL) (lbn : block_no) (poff: page_off) (d: data)
             : option (prod chip FTL) := 
  (* aux def *)
  test bvalid_page_off poff;
  let bit := ftl_bi_table f in
  let bmt := ftl_bm_table f in
  let fbq := ftl_free_blocks f in
  do bmt_entry <-- bmt_get bmt lbn;  (* by Inv #10. *)
  match bmt_entry with
    (* 1st case: {lbn -> _ ,  pbn_log}*)
    | (opt_pbn_data, Some pbn_log) => 
      do bi_log <-- bit_get bit pbn_log; (* by Inv #1 *)
      match (check_block_is_full bi_log) with 

        | true =>  
          (* the log block is full, so we have to merge data & log *)
          do [c', ftl'] <-- merge_block c f lbn;  (* merge preserves $1 $2 *)

          (* allocate another new block for the new log block *)
          do [pbn_log_new, pack'] <-- alloc_block c' ftl';  (* by Inv #9 *)
          let (c_a, f_a) := (pack' : prod chip FTL) in 
          do bi_log_new <-- bit_get (ftl_bi_table f_a) pbn_log_new; (* by Inv #9 *)
          do bi_log_new' <-- Some (bi_set_state bi_log_new (bs_log lbn blank_pmt)); (* trivial *)
          do [c_w, bi_log_new''] <-- write_log_block c_a bi_log_new' pbn_log_new poff d; (* *)
          do bmt_w <-- bmt_update_log (ftl_bm_table f_a) lbn pbn_log_new;
          do bit_w <-- bit_update (ftl_bi_table f_a) pbn_log_new bi_log_new'';
          ret (c_w, (mk_FTL bit_w bmt_w (ftl_free_blocks f_a)))

        (* the log block is not full, then we write the log block directly *)
        | false =>           
          do [c', bi_log'] <-- write_log_block c bi_log pbn_log poff d;
          do bit' <-- bit_update bit pbn_log bi_log';
          ret (c', (mk_FTL bit' bmt fbq))
      end

    (* 2nd case: {lbn -> _, X} *)
    | (_, None) =>
        do [pbn_log, pack] <-- alloc_block c f; 
        let (c_a, f_a) := (pack : prod chip FTL) in 
        let bmt_a := ftl_bm_table f_a in
        let bit_a := ftl_bi_table f_a in
        let fbq_a := ftl_free_blocks f_a in
        do bi_log <-- bit_get bit_a pbn_log;
        do bi_log' <-- Some (bi_set_state bi_log (bs_log lbn blank_pmt));
        do [c_w, bi_log''] <-- write_log_block c_a bi_log' pbn_log poff d;
        do bmt_w <-- bmt_update_log bmt lbn pbn_log; 
        do bit_w <-- bit_update bit_a pbn_log bi_log'';
        ret (c_w, (mk_FTL bit_w bmt_w fbq_a))
  end.

(*  -------------------------------------------------------------

  Definitions

*)

Definition check_data_block (bi: block_info) : bool :=
  match bi_state bi with
    | bs_data _ => true
    | _ => false
  end.

Definition check_log_block (bi: block_info) : bool :=
  match bi_state bi with
    | bs_log _ _ => true
    | _ => false
  end.

Definition check_used_block (bi: block_info) : bool :=
  match bi_state bi with
    | bs_data _ => true
    | bs_log _ _ => true
    | _ => false
  end.

(*  -------------------------------------------------------------

  Lemmas  

*)

Fact PBN_is_greater_than_2_LBN : 
    BLOCKS >= MIN_FREE_BLOCKS + 2 * MAX_LOGICAL_BLOCKS.
Proof.
  simpl.
  unfold BLOCKS.
  omega.
Qed.

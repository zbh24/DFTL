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
Require Import Dftl2.

Open Scope list_scope.

Definition nand_write_command : Set := (nat * nat  * data) %type.

(* Test NAND *)
Fixpoint nand_write_batch (c: chip) (wl : list nand_write_command) 
  : option chip :=
  match wl with 
    | nil => ret c
    | cons wr wl' => 
      let (pn, d) := wr in
      let (b,off) := pn in
      do c' <-- nand_write_page c b off d None;
      nand_write_batch c' wl'
  end.

Compute ( 
  let wl := (0,0,(metabyte (c_1::c_6::nil) ) ) :: nil in
  do c0 <-- Some nand_init;
  do c <-- nand_write_batch c0 wl;
  ret c).

Compute ( 
  let wl := (0,0,(metabyte (c_1::c_6::nil) )) :: (0,1,(metabyte (c_1::c_6::nil) )) :: nil in
  do c0 <-- Some nand_init;
  do c <-- nand_write_batch c0 wl;
  ret c).

Compute ( 
  let wl := (0,0,(metabyte (c_1::c_6::nil) )) :: (0,1,(metabyte (c_1::c_6::nil) )) :: nil in
  do c0 <-- Some nand_init;
  do c <-- nand_write_batch c0 wl;
  do c'<-- nand_erase_block c 0;
  ret c').

(************************************************************************)
(* -------------------------------------------------------------------- *)
(* -------------------------------------------------------------------- *)
(* Test DFTL *)

Definition ftl_write_command : Set := (nat  * bytelist) % type.

Fixpoint ftl_write_batch (c: chip) (f: FTL) (wl : list ftl_write_command) 
  : option (chip * FTL) :=
  match wl with 
    | nil => ret (c, f)
    | cons wr wl' => 
      let (lpn, d) := wr in
      do [c', f'] <-- FTL_write c f lpn (metabyte d);
      ftl_write_batch c' f' wl'
  end.

Fixpoint ftl_write_repeat (c: chip) (f: FTL) (wl : list ftl_write_command) (num:nat) 
  : option (chip * FTL) :=
  match num with 
   | O => ret (c, f)
   | S i => do [c',f'] <-- ftl_write_batch c f wl;
            ftl_write_repeat c' f' wl i
  end.

Definition ftl_read_command : Set := list nat.

Fixpoint ftl_read_batch (c: chip) (f: FTL) (rl:ftl_read_command)
  : option (chip * FTL) :=
  match rl with 
    | nil => ret (c, f)
    | cons lpn rl' => 
      do [d,cf] <-- FTL_read c f lpn;
      do [c',f'] <-- Some cf;
      ftl_read_batch c' f' rl'
  end.

Fixpoint ftl_read_repeat (c: chip) (f: FTL) (rl : ftl_read_command) (num:nat) 
  : option (chip * FTL) :=
  match num with 
   | O => ret (c, f)
   | S i => do [c',f'] <-- ftl_read_batch c f rl;
            ftl_read_repeat c' f' rl i
  end.

Let c0 := nand_init.

(*
Write and read the lpn:0
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: nil in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_batch c0 f0 wl;
  do [d,cf] <-- FTL_read c f 0;
  do [c',f'] <-- Some cf;
  ret (d,(c', f'))).

(*
Write and read the lpn:0,reapt 16 times 
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: nil in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 16;
  do [d,cf] <-- FTL_read c f 0;
  do [c',f'] <-- Some cf;
  ret (d,(c', f'))).

(*
Write and read the lpn:0,reapt 17 times 
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: nil in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 17;
  do [d,cf] <-- FTL_read c f 0;
  do [c',f'] <-- Some cf;
  ret (d,(c', f'))).

(*
Write and read the lpn:0,reapt random(61) times 
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: nil in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 61;
  do [d,cf] <-- FTL_read c f 0;
  do [c',f'] <-- Some cf;
  ret (d,(c', f') ) ).

(***********************************************************)

(*
write the sequence 16(0-15) different place 
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_5:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_6:: nil))::nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 1;
  do [d,cf] <-- FTL_read c f 5;
  do [c',f'] <-- Some cf;
  ret (d,(c', f') ) ).


(*
write the squence 17(0-16) different place,and repeat 6 times 
*)
Compute ( 
  let wl := (0,(c_1::c_2:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_6:: nil))::(16,(c_1::c_6:: nil))::nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 6;
  do [d,cf] <-- FTL_read c f 0;
  do [c',f'] <-- Some cf;
  ret (d,(c', f') ) ).

(*
write the squence 17(0-16) different place,and repeat 6 times and more(2)
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_2:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_6:: nil))::(16,(c_1::c_6:: nil))::nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 6;
  do wl' <-- Some ((0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil)) ::nil);
  do [c',f'] <-- ftl_write_repeat c f wl' 1;
  do [d,cf] <-- FTL_read c' f' 10;
  do [c'',f''] <-- Some cf;
  ret (d,(c'', f'') ) ).

(*
Test the gc(1):write the squence 17(0-16) different place,and repeat 6 times and more,

next write data pages and trans pages: (16,16),data block(0,2,3,5),bs_trans block (1,4,6)

and the cur_data block is 13,and current_trans_block is 11.
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_2:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_6:: nil))::(16,(c_1::c_6:: nil))::nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 6;
  do wl' <-- Some ((0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil)):: nil);
  do [c',f'] <-- ftl_write_repeat c f wl' 1;
  do cur_data <-- Some (current_data_block f');
  do d_bi <-- bit_get (ftl_bi_table f') cur_data;
  do cur_d_off <-- Some (bi_used_pages d_bi);
  do cur_trans <-- Some (current_trans_block f');
  do t_bi <-- bit_get (ftl_bi_table f') cur_trans;
  do cur_t_off <-- Some (bi_used_pages t_bi);
  do [c'',f''] <-- FTL_write c' f' 9 (metabyte (c_1::c_6::nil) );
  do [c''',f'''] <-- FTL_write c'' f'' 10 (metabyte (c_1::c_6::nil) );
  ret (c''',f''')).

(*
Test the gc(2):write the squence 17(0-16) different place,and repeat 6 times and more,

next write data pages and trans pages: (16,16),data block(0,2,3,5),bs_trans block (1,4,6)

and the cur_data block is 14,and current_trans_block is 15.

write to the the gc block 0 and test it.
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_2:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_6:: nil))::(16,(c_1::c_6:: nil))::nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 6;
  do wl' <-- Some ((0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil)):: (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(9,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(9,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil)):: nil);
  do [c',f'] <-- ftl_write_repeat c f wl' 1;
  do cur_data <-- Some (current_data_block f');
  do d_bi <-- bit_get (ftl_bi_table f') cur_data;
  do cur_d_off <-- Some (bi_used_pages d_bi);
  do cur_trans <-- Some (current_trans_block f');
  do t_bi <-- bit_get (ftl_bi_table f') cur_trans;
  do cur_t_off <-- Some (bi_used_pages t_bi);
  do [c'',f''] <-- FTL_write c' f' 9 (metabyte (c_1::c_6::nil) );
  do [c''',f'''] <-- FTL_write c'' f'' 10 (metabyte (c_1::c_6::nil) );  
  ret (c''',f''')).

(*
write the squence 17(0-16) different place and repeat 4 times.then read 12 and 1.
*)

Compute ( 
  let wl := (0,(c_1::c_0:: nil)) :: (1,(c_1::c_2:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_1:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_6:: nil))::
            (66,(c_1::c_6:: nil))::nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 4;
  do [d,cf] <-- FTL_read c f 0;
  do [c',f'] <-- Some cf;
  do [d1,cf'] <-- FTL_read c' f' 12;
  do [c'',f''] <-- Some cf';
  do [d2,cf''] <-- FTL_read c'' f'' 1;
  do [c''',f'''] <-- Some cf'';
  ret (d,(d1,(d2,(c''', f''') ) ) ) ).

(*
write the squence 17(0-16) different place and repeat 4 times.then read 12 and 1,then go on write and 2 ,compare the 2 before and after write.*)

Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_6:: nil))::
            (66,(c_1::c_6:: nil))::nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 2;
  do [d,cf] <-- FTL_read c f 0;
  do [c',f'] <-- Some cf;
  do [d1,cf'] <-- FTL_read c' f' 12;
  do [c'',f''] <-- Some cf';
  do [d2,cf''] <-- FTL_read c'' f'' 2;
  do [c''',f'''] <-- Some cf'';
  do wl' <-- Some ((2,(c_1::c_3::nil))::nil);
  do [c4,f4] <-- ftl_write_repeat c''' f''' wl' 1;
  do [d3,cf'''] <-- FTL_read c4 f4 2;
  do [c5,f5] <-- Some cf''';
  ret (d2,(d3,(c5, f5)))).

(*
write the squence 17(0-16) different place and repeat 4 times.then read 0,12 and 1,then go on write and 0 ,compare the 0 before and after write.
*)

Compute ( 
  let wl := (0,(c_1::c_1:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_6:: nil))::
            (66,(c_1::c_6:: nil))::nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 4;
  do [d,cf] <-- FTL_read c f 0;
  do [c',f'] <-- Some cf;
  do [d1,cf'] <-- FTL_read c' f' 12;
  do [c'',f''] <-- Some cf';
  do [d2,cf''] <-- FTL_read c'' f'' 1;
  do [c''',f'''] <-- Some cf'';
  do wl' <-- Some ((0,(c_1::c_3::nil))::nil);
  do [c4,f4] <-- ftl_write_repeat c''' f''' wl' 1;
  do [d3,cf'''] <-- FTL_read c4 f4 0;
  do [c5,f5] <-- Some cf''';
  ret (d,(d3,(c5, f5)))).

(*
The cmt have empty place,So the LRU insert the cmt in the fist empty,This case is for test the cmt.
*)

Compute ( 
  do f0 <-- ftl_init;
  do data <-- Some (metabyte (cons c_2 (cons c_b  nil) ) );
  do [c',f'] <-- FTL_write c0 f0 0 data;
  do [c'',f''] <-- FTL_write c' f' 15 data;
  do [d,cf] <-- FTL_read c'' f'' 0;
  do [c''',f'''] <-- Some cf;
  ret (c''',f''')).

(*
Write the length about two length of cmt,then read the 15 and 16
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_1:: nil))::
            nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 2;
  do wl' <-- Some  ((16,(c_1::c_2:: nil)) :: (17,(c_1::c_6:: nil))::(18,(c_1::c_6:: nil))::(19,(c_1::c_6:: nil))::
            (20,(c_1::c_6:: nil)) :: (21,(c_1::c_6:: nil))::(22,(c_1::c_6:: nil))::(23,(c_1::c_6:: nil))::
            (24,(c_1::c_6:: nil)) :: (25,(c_1::c_6:: nil))::(26,(c_1::c_6:: nil))::(27,(c_1::c_6:: nil))::
            (28,(c_1::c_6:: nil)) :: (29,(c_1::c_6:: nil))::(30,(c_1::c_6:: nil))::(31,(c_1::c_6:: nil))::
            nil);
  do [c',f'] <-- ftl_write_repeat c f wl' 3;
  do [d1,cf] <-- FTL_read c' f' 15;
  do [c'',f''] <-- Some cf;
  do [d2,cf'] <-- FTL_read c'' f'' 16;
  do [c''',f'''] <-- Some cf';
  ret (d1,(d2,(c''',f''')))).

(*
Write the length about two length of cmt,then run a read list,and then read 28.
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_5:: nil))::
            nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 2;
  do wl' <-- Some  ((16,(c_1::c_6:: nil)) :: (17,(c_1::c_6:: nil))::(18,(c_1::c_6:: nil))::(19,(c_1::c_6:: nil))::
            (20,(c_1::c_6:: nil)) :: (21,(c_1::c_6:: nil))::(22,(c_1::c_6:: nil))::(23,(c_1::c_6:: nil))::
            (24,(c_1::c_6:: nil)) :: (25,(c_1::c_6:: nil))::(26,(c_1::c_6:: nil))::(27,(c_1::c_6:: nil))::
            (28,(c_1::c_2:: nil)) :: (29,(c_1::c_6:: nil))::(30,(c_1::c_6:: nil))::(31,(c_1::c_6:: nil))::
            nil);
  do [c',f'] <-- ftl_write_repeat c f wl' 3;
  do rl <-- Some (15::14::13::12::13::11::10::9::8::7::6::5::4::3::2::1::0::nil);
  do [c'',f''] <-- ftl_read_repeat c' f' rl 2;
  do [d,cf'] <-- FTL_read c'' f'' 28;
  do [c''',f'''] <-- Some cf';
  ret(d,(c''',f'''))).

(*
Write the length about two length of cmt,then run a read list,and then read 28.
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_5:: nil)):: (16,(c_1::c_5:: nil))::
            nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 2;
  do wl' <-- Some ((17,(c_1::c_6:: nil))::(18,(c_1::c_6:: nil))::(19,(c_1::c_6:: nil))::
            (20,(c_1::c_6:: nil)) :: (21,(c_1::c_6:: nil))::(22,(c_1::c_6:: nil))::(23,(c_1::c_6:: nil))::
            (24,(c_1::c_6:: nil)) :: (25,(c_1::c_6:: nil))::(26,(c_1::c_6:: nil))::(27,(c_1::c_6:: nil))::
            (28,(c_1::c_2:: nil)) :: (29,(c_1::c_6:: nil))::(30,(c_1::c_6:: nil))::(31,(c_1::c_6:: nil))::
            (32,(c_1::c_6::nil))::nil);
  do [c',f'] <-- ftl_write_repeat c f wl' 3;
  do [c'', f''] <-- ftl_write_repeat c' f' wl 2;
  do rl <-- Some (15::14::13::12::11::10::9::8::7::6::5::4::3::2::1::0::nil);
  do [c''',f'''] <-- ftl_read_repeat c'' f'' rl 2;
  do [d,cf'] <-- FTL_read c''' f''' 28;
  do [c4,f4] <-- Some cf';
  do [c5,f5] <-- ftl_write_repeat c4 f4 ((0,(c_1::c_1::nil))::nil) 1;
  do rl' <-- Some (16::15::14::13::12::11::10::9::8::7::6::5::4::3::2::1::nil);
  do [c6,f6] <-- ftl_read_repeat c5 f5 rl' 1;
  do [c7,f7] <-- ftl_read_repeat c6 f6 (0::nil) 1;
  ret (d,(c7,f7))).

(*
Write the length about two length of cmt,then run a read list(15-0).
The right answer is return None.
Attention:I don't write the lpn 1.
*)

Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (0,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_5:: nil))::
            nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 2;
  do wl' <-- Some  ((16,(c_1::c_6:: nil)) :: (17,(c_1::c_6:: nil))::(18,(c_1::c_6:: nil))::(19,(c_1::c_6:: nil))::
            (20,(c_1::c_6:: nil)) :: (21,(c_1::c_6:: nil))::(22,(c_1::c_6:: nil))::(23,(c_1::c_6:: nil))::
            (24,(c_1::c_6:: nil)) :: (25,(c_1::c_6:: nil))::(26,(c_1::c_6:: nil))::(27,(c_1::c_6:: nil))::
            (28,(c_1::c_6:: nil)) :: (29,(c_1::c_6:: nil))::(30,(c_1::c_6:: nil))::(31,(c_1::c_6:: nil))::
            nil);
  do [c',f'] <-- ftl_write_repeat c f wl' 1;
  do rl <-- Some (15::14::13::12::11::10::9::8::7::6::5::4::3::2::1::0::nil);
  do [c'',f''] <-- ftl_read_repeat c' f' rl 2;
  ret (c'',f'')).


(*
Ftl_write, remove the head of cmt which the head one is clean.
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_1:: nil))::
            nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 2;
  do wl' <-- Some  ((16,(c_1::c_2:: nil)) :: (17,(c_1::c_6:: nil))::(18,(c_1::c_6:: nil))::(19,(c_1::c_6:: nil))::
            (20,(c_1::c_6:: nil)) :: (21,(c_1::c_6:: nil))::(22,(c_1::c_6:: nil))::(23,(c_1::c_6:: nil))::
            (24,(c_1::c_6:: nil)) :: (25,(c_1::c_6:: nil))::(26,(c_1::c_6:: nil))::(27,(c_1::c_6:: nil))::
            (28,(c_1::c_6:: nil)) :: (29,(c_1::c_6:: nil))::(30,(c_1::c_6:: nil))::(31,(c_1::c_6:: nil))::
            nil);
  do [c',f'] <-- ftl_write_repeat c f wl' 2;
  do rl <-- Some (15::14::13::12::11::10::9::8::7::6::5::4::3::2::1::0::nil);
  do [c'',f''] <-- ftl_read_repeat c' f' rl 1;
  do [c''',f'''] <-- FTL_write c'' f'' 20 (metabyte (c_1::c_6::nil) );
  ret (c''',f''')).

(*
Ftl_write, remove the head of cmt which the head one is dirty and which the gtd_loc is empty.
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_1:: nil))::
            nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 2;
  do wl' <-- Some  ((16,(c_1::c_2:: nil))::
            nil);
  do [c',f'] <-- ftl_write_repeat c f wl' 1;
  ret (c',f')).

(*
Ftl_write, remove the head of cmt which the head one is dirty and which the gtd_loc is not empty,and insert the translation.
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_1:: nil))::
            nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 2;
  do wl' <-- Some  ((16,(c_1::c_2:: nil))::(17,(c_1::c_2::nil))::
            nil);
  do [c',f'] <-- ftl_write_repeat c f wl' 1;
  ret (c',f')).

(*
Ftl_write, remove the head of cmt which the head one is dirty and which the gtd_loc is not empty,and update the translation in the trans.
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_1:: nil))::
            nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 2;
  do wl' <-- Some  ((16,(c_1::c_2:: nil)) :: (17,(c_1::c_6:: nil))::(18,(c_1::c_6:: nil))::(19,(c_1::c_6:: nil))::
            (20,(c_1::c_6:: nil)) :: (21,(c_1::c_6:: nil))::(22,(c_1::c_6:: nil))::(23,(c_1::c_6:: nil))::
            (24,(c_1::c_6:: nil)) :: (25,(c_1::c_6:: nil))::(26,(c_1::c_6:: nil))::(27,(c_1::c_6:: nil))::
            (28,(c_1::c_6:: nil)) :: (29,(c_1::c_6:: nil))::(30,(c_1::c_6:: nil))::(31,(c_1::c_6:: nil))::
            nil);
  do [c',f'] <-- ftl_write_repeat c f wl' 1;
  do [c'',f''] <-- ftl_write_repeat c' f' wl 1;
  do wl'' <-- Some  ((16,(c_1::c_2:: nil))::nil);
  do [c''',f'''] <-- ftl_write_repeat c'' f'' wl'' 1;
  ret (c''',f''')).

(*
Ftl_write,and the lpn is in the cmt and remove the clean one(the head one).
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_1:: nil))::
            nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 2;
  do wl' <-- Some  ((16,(c_1::c_2:: nil)) :: (17,(c_1::c_6:: nil))::(18,(c_1::c_6:: nil))::(19,(c_1::c_6:: nil))::
            (20,(c_1::c_6:: nil)) :: (21,(c_1::c_6:: nil))::(22,(c_1::c_6:: nil))::(23,(c_1::c_6:: nil))::
            (24,(c_1::c_6:: nil)) :: (25,(c_1::c_6:: nil))::(26,(c_1::c_6:: nil))::(27,(c_1::c_6:: nil))::
            (28,(c_1::c_6:: nil)) :: (29,(c_1::c_6:: nil))::(30,(c_1::c_6:: nil))::(31,(c_1::c_6:: nil))::
            nil);
  do [c',f'] <-- ftl_write_repeat c f wl' 2;
  do rl <-- Some (15::14::13::12::11::10::9::8::7::6::5::4::3::2::1::0::nil);
  do [c'',f''] <-- ftl_read_repeat c' f' rl 1;
  do wl'' <-- Some  ((10,(c_1::c_2:: nil))::(16,(c_1::c_2:: nil))::nil);
  do [c''',f'''] <-- ftl_write_repeat c'' f'' wl'' 1;
  ret (c''',f''')).
(* The above is FLT_WRITE testing,the FTL_WRITE testing is over *)
(* --------------------------------------------------------------*)


(* FTL_read: ftl_read the lpn,and the lpn in the cmt and the cmt have empty place *)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::
            nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 2;
  do rl <-- Some (3::nil);
  do [c',f'] <-- ftl_read_repeat c f rl 1;
  ret (c',f')).

(* FTL_read: ftl_read the lpn,and the lpn in the cmt and the cmt don't have empty place *)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_1:: nil))::
            nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 2;
  do rl <-- Some (3::nil);
  do [c',f'] <-- ftl_read_repeat c f rl 1;
  ret (c',f')).

(*
Ftl_read,and the lpn is not in the cmt and remove the clean one (the head one).
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_1:: nil))::
            nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 2;
  do wl' <-- Some  ((16,(c_1::c_2:: nil)) :: (17,(c_1::c_6:: nil))::(18,(c_1::c_6:: nil))::(19,(c_1::c_6:: nil))::
            (20,(c_1::c_6:: nil)) :: (21,(c_1::c_6:: nil))::(22,(c_1::c_6:: nil))::(23,(c_1::c_6:: nil))::
            (24,(c_1::c_6:: nil)) :: (25,(c_1::c_6:: nil))::(26,(c_1::c_6:: nil))::(27,(c_1::c_6:: nil))::
            (28,(c_1::c_6:: nil)) :: (29,(c_1::c_6:: nil))::(30,(c_1::c_6:: nil))::(31,(c_1::c_6:: nil))::
            nil);
  do [c',f'] <-- ftl_write_repeat c f wl' 2;
  do rl <-- Some (15::14::13::12::11::10::9::8::7::6::5::4::3::2::1::0::nil);
  do [c'',f''] <-- ftl_read_repeat c' f' rl 1;
  do wl'' <-- Some  ((16,(c_1::c_2:: nil))::nil);
  do [c''',f'''] <-- ftl_write_repeat c'' f'' wl'' 1;
  ret (c''',f''')).

(*
Ftl_read,and the lpn is not in the cmt and remove the dirty one (the head one),the remove one don't have the gtd_loc(in this case is lpn:8).
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_1:: nil))::
            (16,(c_1::c_2:: nil)) ::
            nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 1;
  do rl <-- Some (0::1::2::3::4::5::6::7::nil);
  do [c'',f''] <-- ftl_read_repeat c f rl 1;
  ret (c'',f'')).

(*
Ftl_read,and the lpn is not in the cmt and remove the dirty one (the head one),and have the gtd_loc.
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_1:: nil))::
            (16,(c_1::c_2::nil))::
            nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 1;
  do rl <-- Some (0::1::2::3::4::5::6::7::8::9::nil);
  do [c'',f''] <-- ftl_read_repeat c f rl 1;
  ret (c'',f'')).

(*
The synthetical testing
*)
Compute ( 
  let wl := (0,(c_1::c_6:: nil)) :: (1,(c_1::c_6:: nil))::(2,(c_1::c_6:: nil))::(3,(c_1::c_6:: nil))::
            (4,(c_1::c_6:: nil)) :: (5,(c_1::c_6:: nil))::(6,(c_1::c_6:: nil))::(7,(c_1::c_6:: nil))::
            (8,(c_1::c_6:: nil)) :: (9,(c_1::c_6:: nil))::(10,(c_1::c_6:: nil))::(11,(c_1::c_6:: nil))::
            (12,(c_1::c_6:: nil)) :: (13,(c_1::c_6:: nil))::(14,(c_1::c_6:: nil))::(15,(c_1::c_1:: nil))::
            (16,(c_1::c_2::nil))::
            nil
  in
  do f0 <-- ftl_init;
  do [c, f] <-- ftl_write_repeat c0 f0 wl 1;
  do rl <-- Some (0::1::2::3::4::5::6::7::8::9::nil);
  do [c'',f''] <-- ftl_read_repeat c f rl 1;
  do [c''',f'''] <-- FTL_write c'' f'' 8 (metabyte (c_1::c_6::nil) );
  do [c4,f4] <-- FTL_write c''' f''' 8 (metabyte (c_1::c_6::nil) ); 
  do wl' <-- Some  ((17,(c_1::c_6:: nil))::(18,(c_1::c_6:: nil))::(19,(c_1::c_6:: nil))::
            (20,(c_1::c_6:: nil)) :: (21,(c_1::c_6:: nil))::(22,(c_1::c_6:: nil))::(23,(c_1::c_6:: nil))::
            (24,(c_1::c_6:: nil)) :: (25,(c_1::c_6:: nil))::(26,(c_1::c_6:: nil))::(27,(c_1::c_6:: nil))::
            (28,(c_1::c_6:: nil)) :: (29,(c_1::c_6:: nil))::(30,(c_1::c_6:: nil))::(31,(c_1::c_6:: nil))::
            (32,(c_1::c_6:: nil))::nil);
 
  do [c5, f5] <-- ftl_write_repeat c4 f4 wl' 1;
  ret (c5,f5)).

(*---------------------------------------------------*)

(*---------------------------------------------------*)
(* The White box testing *)
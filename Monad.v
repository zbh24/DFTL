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

Notation "'do' x <-- A ; B" := 
  (match A with 
     | Some y => (fun x => B) y 
     | None => None end)
  (at level 200, x ident).

Notation "'do' x <<-- A ; B" := 
  (match A with 
     | y => (fun x => B) y end)
  (at level 200, x ident).

Notation "'do' '[' x1 ',' x2 ']' <-- o ; f" :=
  (match o with Some (y1, y2) => (fun x1 x2 => f) y1 y2 | None => None end)
  (at level 200).

Notation "'test' b ; f" :=
  (match b with false => None | true => f end)
  (at level 200).

Notation "'ret' x" := (Some x) (at level 200, only parsing).



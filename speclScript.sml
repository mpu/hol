open HolKernel boolLib bossLib arithmeticTheory;

(* Specification language, with extraction to C *)
val _ = new_theory "specl"

(* syntax *)
val bop_def = Datatype`bop = PLS | MNS | CLE | CEQ | CNE`
val exp_def = Datatype`exp
 = Num num
 | Var num
 | Bop bop exp exp
 `
val stm_def = Datatype`stm
 = Nop
 | Set num exp
 | Seq stm stm
 | Whl exp stm
 `

val block_def = Define`block = FOLDL Seq Nop`

(* semantics *)
val erun_def = Define`
  (erun st (Num n) = n) /\
  (erun st (Var n) = st n) /\
  (erun st (Bop op e1 e2) =
    case op of
      PLS => erun st e1 + erun st e2
    | MNS => erun st e1 - erun st e2
    | CLE => if erun st e1 <= erun st e2 then 1 else 0
    | CEQ => if erun st e1  = erun st e2 then 1 else 0
    | CNE => if erun st e1 <> erun st e2 then 1 else 0)`

(**************** reflection datatypes and helpers ****************)
datatype bop
  = oPLS | oMNS | oCLE | oCEQ | oCNE

datatype exp
  = eNum of int
  | eVar of int
  | eBop of bop * exp * exp

datatype stm
  = sSet of int * exp
  | sWhile of exp * blk
withtype blk = stm list

fun dest_bop tm =
  if tm ~~ ``PLS`` then oPLS else
  if tm ~~ ``MNS`` then oMNS else
  if tm ~~ ``CLE`` then oCLE else
  if tm ~~ ``CEQ`` then oCEQ else
  if tm ~~ ``CNE`` then oCNE else
  failwith "unsupported binary operator"

fun dest_exp tm = let 
    val hd = repeat rator tm
  in
    if hd ~~ ``Num`` then eNum (numSyntax.int_of_term (rand tm)) else
    if hd ~~ ``Var`` then eVar (numSyntax.int_of_term (rand tm)) else
    if hd ~~ ``Bop`` then let
      val bop = dest_bop (tm |> rator |> rator |> rand)
      val lhs = dest_exp (tm |> rator |> rand)
      val rhs = dest_exp (tm |> rand)
      in eBop (bop, lhs, rhs) end
    else failwith "unsupported expression"
  end

(**************** usage example ****************)
(* Computes the mean of v0 and v1, assuming
 * v0 < v1 initially, and their difference
 * is even.
 *)
val mean_prog = ``
  Whl (Bop CNE (Var 0) (Var 1)) (block [
    Set 1 (Bop MNS (Var 1) (Num 1));
    Set 0 (Bop PLS (Var 0) (Num 1));
  ])``

open HolKernel boolLib bossLib arithmeticTheory optionTheory;

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

val srun_def = Define`
  (srun n st Nop = SOME st) /\
  (srun n st (Set v e) = SOME ((v =+ erun st e) st)) /\
  (srun n st (Seq s1 s2) =
    case srun n st s1 of
      SOME st1 => srun n st1 s2
    | NONE => NONE) /\
  (srun (SUC n) st (Whl e s) =
    if erun st e = 0 then
      SOME st
    else
      srun n st (Seq s (Whl e s))) /\
  (srun 0 st (Whl e s) = NONE)`

(**************** Hoare program logic ****************)

val tri_ind_def = Define`tri_ind n PRE s PST
  = !st1 st2. PRE st1 /\ srun n st1 s = SOME st2 ==> PST st2`

val tri_def = Define`tri PRE s PST = !n. tri_ind n PRE s PST`

val srun_monotonic = Q.prove(
  `!n1 s st1 n2 st2.
     n1 < n2 /\ srun n1 st1 s = SOME st2 ==>
     srun n2 st1 s = SOME st2`,
  Induct >| [
    (* base *)
    Induct_on `s` >> rw[srun_def] >>
    Cases_on `srun 0 st1 s` >> fs[] >>
    RES_TAC >> rw[],
    (* induction *)
    Cases_on `n2`
    >- fs[]
    >> REWRITE_TAC [LESS_MONO_EQ] >>
       Induct_on `s` >> rw[srun_def] >| [
         (* seq *)
         Cases_on `srun (SUC n1) st1 s` >> fs[] >>
         RES_TAC >> rw[],
         (* whl *)
         Cases_on `srun n1 st1 s` >> fs[] >>
         RES_TAC >> rw[]
       ]
  ]
)

val tri_ind_monotonic = Q.prove(
  `!n1 n2 PRE s PST.
     n1 > n2 /\ tri_ind n1 PRE s PST ==>
     tri_ind n2 PRE s PST`,
  rw[tri_ind_def] >>
  first_x_assum irule >>
  qexists_tac `st1` >> rw[] >>
  irule srun_monotonic >>
  qexists_tac `n2` >> rw[]
)

Theorem hoare_set:
  !PST v e. tri (PST o \st. (v =+ erun st e) st) (Set v e) PST
Proof
  rw[tri_def, tri_ind_def, srun_def]
QED

Theorem hoare_seq:
  !PRE MID PST s1 s2. tri PRE s1 MID /\ tri MID s2 PST ==>
                      tri PRE (Seq s1 s2) PST
Proof
  rw[tri_def, tri_ind_def, srun_def] >>
  Cases_on `srun n st1 s1` >> fs[] >>
  first_x_assum (qspecl_then [`n`,`x`] match_mp_tac) >> rw[] >>
  first_x_assum (qspecl_then [`n`,`st1`] match_mp_tac) >> rw[]
QED

val whl_ind_lem = Q.prove (
  `!n INV e s.
    tri_ind n (\st. INV st /\ (erun st e <> 0)) s INV ==>
    tri_ind n INV (Whl e s) (\st. INV st /\ (erun st e = 0))`,
  Induct >> rpt strip_tac
  >- rw[tri_ind_def, srun_def]
  >> rewrite_tac [tri_ind_def] >> rpt strip_tac >>
     first_x_assum (assume_tac o REWRITE_RULE [srun_def]) >>
     `(erun st1 e = 0) \/ (erun st1 e <> 0)` by decide_tac >> fs[]
     >- rw[]
     >> Cases_on `srun n st1 s` >> fs[] >> RES_TAC >>
        last_x_assum (irule o SIMP_RULE pure_ss [tri_ind_def, SimpR ``$==>``]) >>
        qexists_tac `s` >> qexists_tac `x` >> rw[] >| [
          last_x_assum (match_mp_tac o REWRITE_RULE [tri_ind_def]) >>
          qexists_tac `st1` >> rw[] >>
          irule srun_monotonic >> qexists_tac `n` >> rw[],
          irule tri_ind_monotonic >> qexists_tac `SUC n` >> rw[]
        ]
)

Theorem hoare_whl:
  !INV e s.
    tri (\st. INV st /\ (erun st e <> 0)) s INV ==>
    tri INV (Whl e s) (\st. INV st /\ (erun st e = 0))
Proof
  rw[tri_def, whl_ind_lem]
QED

Theorem hoare_wkn:
  !PRE PST PRE' PST'.
    (!st. PRE' st ==> PRE st) /\
    (!st. PST st ==> PST' st) /\
    tri PRE s PST ==>
    tri PRE' s PST'
Proof
  rw[tri_def, tri_ind_def] >>
  first_x_assum (qspec_then `st2` match_mp_tac) >>
  first_x_assum (qspecl_then [`n`,`st1`,`st2`] match_mp_tac) >>
  rw[]
QED

(**************** reflection datatypes and helpers ****************)
datatype bop
  = oMUL | oPLS | oMNS | oCLE | oCEQ | oCNE

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

fun dest_blk tm = let
    val hd = repeat rator tm
  in
    if hd ~~ ``Whl`` then let
      val exp = dest_exp (tm |> rator |> rand)
      val blk = dest_blk (tm |> rand)
      in [sWhile (exp, blk)] end else
    if hd ~~ ``Set`` then let
      val var = numSyntax.int_of_term (tm |> rator |> rand)
      val exp = dest_exp (tm |> rand)
      in [sSet (var, exp)] end else
    if hd ~~ ``Seq`` then let
      val blk1 = dest_blk (tm |> rator |> rand)
      val blk2 = dest_blk (tm |> rand)
      in blk1 @ blk2 end else
    if hd ~~ ``block`` then
      fst (listSyntax.dest_list (rand tm))
      |> List.map dest_blk |> List.concat else
    failwith "unsupported statement"
  end

fun emit_C (*name*) vars = let
  fun prec_of_op bo =
    case bo of
         oMUL => 1
       | oPLS => 2 | oMNS => 2
       | oCLE => 3 | oCEQ => 3 | oCNE => 3
  fun emit_op bo =
    case bo of
         oMUL => " * "
       | oPLS => " + " | oMNS => " - "
       | oCLE => " < " | oCEQ => " == " | oCNE => " != "
  fun parens s = "(" ^ s ^ ")"
  fun emit_exp (pl, e) =
    case e of
         eVar v => List.nth (vars, v)
       | eNum n => Int.toString n
       | eBop (bo, el, er) => let
         val pl' = prec_of_op bo
         val str =
           emit_exp (pl', el)
           ^ emit_op bo
           ^ emit_exp (pl' - 1, er)
         in if pl' > pl then parens str else str end
  val emit_exp = fn e => emit_exp (100, e)
  fun emit_blk idnt blk =  let
    fun stm s = idnt ^ emit_stm idnt s ^ "\n"
    in String.concat (List.map stm blk) end
  and emit_stm idnt stm =
    case stm of
         sSet (v, e) =>
           List.nth (vars, v) ^ " = " ^ emit_exp e ^ ";"
       | sWhile (e, b) =>
           "while (" ^ emit_exp e ^ ") {\n" ^
           emit_blk ("\t" ^ idnt) b ^
           idnt ^ "}"
  in
    emit_blk "\t"
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

(*
  EVAL ``srun 10 (\n. case n of 0 => 1 | 1 => 11) ^mean_prog``
  -- the program ends with 6 in variables 0 and 1

  (print o emit_C ["i", "j"] o dest_blk) mean_prog
  -- prints the C body in the repl
*)

(* Prove the specification of the mean function *)
Theorem mean_prog_proof:
  !i j.
    tri (\st. (st 0 = i) /\ (st 1 = j))
        ^mean_prog
        (\st. st 0 = (j + i) DIV 2)
Proof
  ntac 2 strip_tac >>
  (* the loop invariant *)
  markerLib.ABBREV_TAC
    ``INV = \st. (st 1 < st 0) \/
                 ((st 1 + st 0) DIV 2 = (j + i) DIV 2)`` >>
  match_mp_tac (Q.SPEC `INV` hoare_wkn) >>
  Q.PAT_ABBREV_TAC `cnd = (Bop CNE _ _)` >>
  qexists_tac `\st. INV st /\ (erun st cnd = 0)` >>
  rpt conj_tac
  >- rw[Abbr `INV`]
  >- (rw[Abbr `INV`, Abbr `cnd`, erun_def] >>
      fs[ONCE_REWRITE_RULE [MULT_COMM] (EVAL_RULE (Q.SPEC `2` MULT_DIV))])
  >> match_mp_tac hoare_whl >>
     rw[Abbr `INV`, Abbr `cnd`, block_def,
        erun_def, tri_def, tri_ind_def, srun_def] >>
     pop_assum kall_tac >>
     EVAL_TAC >> rw[] >>
     `st 1 = 0 \/ st 1 > 0` by decide_tac >> rw[]
QED

(* Extract the mean function in a C file *)
val _ =
  let
    val mean_body = emit_C ["i", "j"] (dest_blk mean_prog)
    val mean_fun =
      "int mean(int i, int j)\n{\n" ^ mean_body ^ "\treturn i;\n}\n"
    (* https://stackoverflow.com/a/33606353 *)
    fun writeFile filename content =
      let val fd = TextIO.openOut filename
          val _ = TextIO.output (fd, content)
                  handle e => (TextIO.closeOut fd; raise e)
          val _ = TextIO.closeOut fd
      in () end
  in writeFile "mean.c" mean_fun end

val _ = export_theory ()

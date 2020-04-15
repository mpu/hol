needs "Library/words.ml";;

let word_int = new_definition
  `word_int (a:N word) b x = word_ule (word_sub x a) (word_sub b a)`;;

let WORD_INT = prove
  (`!(x:N word) a b. word_int x a b <=>
           (if val a <= val b
            then val a <= val x /\ val x <= val b
            else val a <= val x \/ val x <= val b)`,
   REPEAT GEN_TAC THEN
   MAP_EVERY (ASSUME_TAC o C SPEC VAL_BOUND)
     [`x:N word`;`a:N word`;`b:N word`] THEN
   REWRITE_TAC[word_int; WORD_ULE; VAL_WORD_SUB_CASES] THEN
   REPEAT (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
   ASM_ARITH_TAC);;

(*
let mod_range = new_definition
  `mod_range a b m = {x | ?i. x = (a + i) MOD m /\ i <= (b + m - a) MOD m}`;;
*)

let MOD_ADD_MODULUS = prove
  (`(!m n. (n + m) MOD m = n MOD m) /\
    (!m n. (m + n) MOD m = n MOD m)`,
   MESON_TAC[MOD_MULT_ADD;MULT_CLAUSES]);;

(* Sweet! First non-trivial theorem :) *)
let LT_SUC_MOD = prove
  (`!m x. x MOD m < SUC x MOD m <=> ~(SUC x MOD m = 0)`,
   GEN_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[MOD_ZERO] THEN ARITH_TAC; GEN_TAC] THEN
   ASM_CASES_TAC `SUC x MOD m = 0` THEN ASM_REWRITE_TAC[LT] THEN
   MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `SUC (x MOD m)` THEN
   REWRITE_TAC[LT] THEN MATCH_MP_TAC EQ_IMP_LE THEN
   CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_UNIQ THEN
   EXISTS_TAC `x DIV m` THEN CONJ_TAC THENL
   [MP_TAC (SPECL [`x:num`;`m:num`] DIVISION) THEN ASM_ARITH_TAC;
    REWRITE_TAC[LT_LE] THEN CONJ_TAC THENL
    [ASM_SIMP_TAC[LE_SUC_LT;DIVISION];
     DISCH_THEN (MP_TAC o AP_TERM `\x. x MOD m`) THEN
     CONV_TAC (DEPTH_CONV BETA_CONV THENC MOD_DOWN_CONV) THEN
     REWRITE_TAC[MOD_REFL] THEN POP_ASSUM ACCEPT_TAC]]);;

(* TODO: define mdist m (a,b) the modular distance from a to b *)

(*
   Forward provers:
     - MESON[thlist] `term`
     - AC ADD_AC `add ac term`
   Tac:
     - TRANS_TAC LE_TRANS `term`
   Lib:
     - el 2 (CONJUNCTS ...)
*)

(* we want to use pure_prove_recursive_function_exists followed
   by new_specification *)
let RANGE_EXISTS =
  let thm = pure_prove_recursive_function_exists
    `?f. !a b m. f a b m =
        if a = b \/ ~(a < m /\ b < m)
        then {}
        else a INSERT (f (SUC a MOD m) b m)`
  in
  let wf_thm = prove
    ((hd (hyp thm)),
     EXISTS_TAC `MEASURE (\(a,b,m). (b + m - a) MOD m)` THEN
     REWRITE_TAC[WF_MEASURE; MEASURE; DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
     SUBGOAL_THEN `(SUC a = m /\ SUC a MOD m = 0) \/
                   (SUC a < m /\ SUC a MOD m = SUC a)` MP_TAC THENL
     [SUBGOAL_THEN `SUC a = m \/ SUC a < m` DISJ_CASES_TAC THENL
       [ASM_ARITH_TAC;
        DISJ1_TAC THEN ASM_REWRITE_TAC[MOD_REFL];
        DISJ2_TAC THEN ASM_MESON_TAC[MOD_LT]];
      ALL_TAC] THEN
     DISCH_THEN (DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
      (* SUC a = m *)
     [POP_ASSUM SUBST1_TAC THEN
      ASM_SIMP_TAC[SUB; MOD_ADD_MODULUS; MOD_LT] THEN
      SUBGOAL_THEN `b + m - a = SUC b /\ SUC b < m` MP_TAC THENL
        [ASM_ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
      (* SUC a < m *)
      POP_ASSUM SUBST1_TAC THEN
      SUBGOAL_THEN `b + m - a = SUC (b + m - SUC a)` ASSUME_TAC THENL
        [ASM_ARITH_TAC; FIRST_ASSUM SUBST1_TAC] THEN
      POP_ASSUM (fun th -> REWRITE_TAC[LT_SUC_MOD; GSYM th]) THEN
      REWRITE_TAC[GSYM DIVIDES_MOD; divides; NOT_EXISTS_THM] THEN
      X_GEN_TAC `q:num` THEN
      DISJ_CASES_TAC (ARITH_RULE `q = 0 \/ q = 1 \/ 2 <= q`) THENL
      [ASM_REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC;
       POP_ASSUM DISJ_CASES_TAC THENL
       [ASM_REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC;
        STRIP_TAC THEN
        MP_TAC (SPECL [`m:num`;`2`;`q:num`] LE_MULT_LCANCEL) THEN
        ASM_REWRITE_TAC[ONCE_REWRITE_RULE [MULT_SYM] MULT_2] THEN
        POP_ASSUM (SUBST1_TAC o GSYM) THEN
        ASM_ARITH_TAC]]])
  in
  PROVE_HYP wf_thm thm;;

(* Nice recursive range function! *)
let RANGE = new_specification["range"] RANGE_EXISTS;;

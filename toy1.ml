let INT_SUB_1_REM = prove
  (`!m x. (x - &1) rem m = if x rem m = &0 then abs m - &1 else x rem m - &1`,
   REPEAT GEN_TAC THEN ASM_CASES_TAC `m = &0` THENL
     [ASM_REWRITE_TAC[INT_REM_0] THEN INT_ARITH_TAC; ALL_TAC] THEN
   COND_CASES_TAC THEN MATCH_MP_TAC INT_REM_UNIQ THENL
   [ EXISTS_TAC `x div m - int_sgn m` THEN
     POP_ASSUM MP_TAC THEN REWRITE_TAC[INT_REM_DIV] THEN
     STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ REWRITE_TAC[INT_SUB_RDISTRIB; INT_SGN_ABS_ALT] THEN ASM_INT_ARITH_TAC;
       ASM_INT_ARITH_TAC;
       INT_ARITH_TAC ];
     EXISTS_TAC `x div m` THEN
     STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ REWRITE_TAC[INT_REM_DIV] THEN INT_ARITH_TAC;
       POP_ASSUM MP_TAC THEN
       POP_ASSUM (fun th -> MP_TAC (SPEC `x:int`
         (MATCH_MP INT_REM_POS th))) THEN
       INT_ARITH_TAC;
       POP_ASSUM (K ALL_TAC) THEN
       POP_ASSUM (fun th -> MP_TAC (MATCH_MP INT_DIVISION th)) THEN
       DISCH_THEN (MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC `x:int`) THEN
       INT_ARITH_TAC ] ]);;

let MODSUB_ADD_1 = prove
  (`!m x y. ~(x == y) (mod m) ==> (x - (y + &1)) rem m = (x - y) rem m - &1`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[INT_ARITH `x - (y + &1) = x - y - &1`; INT_SUB_1_REM] THEN
   SUBGOAL_THEN `~((x - y) rem m = &0)` (fun th -> REWRITE_TAC[th]) THEN
   POP_ASSUM MP_TAC THEN REWRITE_TAC[CONTRAPOS_THM] THEN
   REWRITE_TAC[INT_REM_EQ_0; int_divides; int_congruent]);;

let MODLOOP_IND = prove
  (`!m y P.
      ~(m = 0) /\
      (!x. (x == y) (mod m) ==> P x) /\
      (!x. (~(x == y) (mod m) /\ P (SUC x)) ==> P x) ==>
      !x. P x`,
   REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
   SUBGOAL_THEN `WF (MEASURE (\x. num_of_int((&y - &x) rem &m)))` MP_TAC THENL
     [REWRITE_TAC[WF_MEASURE]; REWRITE_TAC[WF_IND]] THEN
   DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[MEASURE] THEN
   GEN_TAC THEN POP_ASSUM (CONJUNCTS_THEN (MP_TAC o SPEC `x:num`)) THEN
   ASM_CASES_TAC `(x == y) (mod m)` THEN ASM_SIMP_TAC[] THEN
   REWRITE_TAC[IMP_IMP] THEN DISCH_THEN (CONJUNCTS_THEN MATCH_MP_TAC) THEN
   ONCE_REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
   ASM_SIMP_TAC[INT_REM_POS; INT_OF_NUM_OF_INT; INT_OF_NUM_EQ] THEN
   REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN IMP_REWRITE_TAC[MODSUB_ADD_1] THEN
   CONJ_TAC THENL [INT_ARITH_TAC; ASM_MESON_TAC[num_congruent; CONG]]);;

(* --------- *)

let MODSEG = define
  `modseg3 m a b =
    {x | &x < &m /\ (&x - &a) rem &m <= (&b - &a) rem &m}`;;

(* Modular range *)
let MODRNG = new_definition
  `MODRNG0 m a b =
     {x | ?d. x = (a + d) MOD m /\
          !e. e < d ==> ~(b == a + e) (mod m)}`;;

let MODRNG_ZERO = prove
  (`!a b. MODRNG0 0 a b = if a <= b then a..b else {x | a <= x}`,
   REWRITE_TAC[MODRNG; CONG; MOD_ZERO] THEN REPEAT GEN_TAC THEN
   ASM_CASES_TAC `a <= b` THEN
   ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THENL
   [GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
    [FIRST_X_ASSUM (MP_TAC o SPEC `b - a`);
     EXISTS_TAC `x - a`] THEN ASM_ARITH_TAC;
    GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
    [ALL_TAC; EXISTS_TAC `x - a`] THEN
    ASM_ARITH_TAC]);;

let MODRNG_SUBSET_NUMSEG = prove
  (`!m a b. ~(m = 0) ==> MODRNG0 m a b SUBSET 0..m - 1`,
   REWRITE_TAC[SUBSET; IN_NUMSEG_0; MODRNG; IN_ELIM_THM] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
   DISCH_THEN (CHOOSE_THEN (SUBST1_TAC o CONJUNCT1)) THEN
   MP_TAC (SPECL[`a + d`;`m:num`] MOD_LT_EQ) THEN
   ASM_ARITH_TAC);;

let FINITE_MODRNG = prove
  (`!m a b. FINITE (MODRNG0 m a b) <=> (m = 0 /\ a <= b) \/ ~(m = 0)`,
   REPEAT GEN_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [POP_ASSUM (fun th -> REWRITE_TAC[th; MODRNG_ZERO; LT]) THEN
    BOOL_CASES_TAC `a <= b` THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    REWRITE_TAC[GSYM INFINITE; INFINITE_ENUMERATE_SUBSET] THEN
    EXISTS_TAC `\n. n + a` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `0..m - 1` THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; MODRNG_SUBSET_NUMSEG]]);;

let MODRNG_CONG = prove
  (`!m a b. (a == b) (mod m) ==> MODRNG0 m a b = {a MOD m}`,
   REWRITE_TAC[MODRNG; EXTENSION; IN_ELIM_THM; CONG] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THENL
   (* ==> *)
   [DISCH_THEN (CHOOSE_THEN MP_TAC) THEN
    DISJ_CASES_TAC (SPEC `d:num` num_CASES) THENL
    [ASM_REWRITE_TAC[ADD_CLAUSES; LT] THEN
     DISCH_THEN SUBST1_TAC THEN SET_TAC[];
     POP_ASSUM (CHOOSE_THEN SUBST1_TAC) THEN
     DISCH_THEN (MP_TAC o GSYM o SPEC `0` o CONJUNCT2) THEN
     ASM_REWRITE_TAC[LT_0; ADD_CLAUSES; CONG]];
   (* <== *)
    REWRITE_TAC[IN_SING] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; LT]]);;

let MODRNG_REFL = prove
  (`!m a. MODRNG0 m a a = {a MOD m}`,
   REPEAT GEN_TAC THEN MATCH_MP_TAC MODRNG_CONG THEN
   REWRITE_TAC[CONG]);;

let MODRNG_CONGL = prove
  (`!m a b c. (a == b) (mod m) ==> MODRNG0 m a c = MODRNG0 m b c`,
   REWRITE_TAC[CONG] THEN REPEAT GEN_TAC THEN
   SUBGOAL_THEN `!a b. a MOD m = b MOD m ==>
     (!x. MODRNG0 m a c x ==> MODRNG0 m b c x)` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[EXTENSION; IN] THEN MESON_TAC[]] THEN
   REWRITE_TAC[MODRNG; IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THEN EXISTS_TAC `d:num` THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_THEN (fun th ->
      POP_ASSUM (MP_TAC o C MATCH_MP th)) THEN
    POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [CONTRAPOS_THM; CONG] THEN
    DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ASM_REWRITE_TAC[]]);;

let MODRNG_MODL = prove
  (`!m a b. MODRNG0 m (a MOD m) b = MODRNG0 m a b`,
   MESON_TAC[MODRNG_CONGL; CONG; MOD_MOD_REFL]);;

let MODRNG_CONGR = prove
  (`!m a b c. (b == c) (mod m) ==> MODRNG0 m a b = MODRNG0 m a c`,
   REWRITE_TAC[CONG] THEN REPEAT GEN_TAC THEN
   SUBGOAL_THEN `!b c. b MOD m = c MOD m ==>
     (!x. MODRNG0 m a b x ==> MODRNG0 m a c x)` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[EXTENSION; IN] THEN MESON_TAC[]] THEN
   REWRITE_TAC[MODRNG; IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THEN EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN DISCH_THEN (fun th ->
     POP_ASSUM (MP_TAC o C MATCH_MP th)) THEN
   ASM_REWRITE_TAC [CONTRAPOS_THM; CONG]);;

let MODRNG_MODR = prove
  (`!m a b. MODRNG0 m a (b MOD m) = MODRNG0 m a b`,
   MESON_TAC[MODRNG_CONGR; CONG; MOD_MOD_REFL]);;

let MODRNG_THM = prove
  (`!m a b. MODRNG0 m a b =
      if (a == b) (mod m)
      then {a MOD m}
      else (a MOD m) INSERT MODRNG0 m (SUC a) b`,
   REPEAT GEN_TAC THEN ASM_CASES_TAC `(a == b) (mod m)` THEN
   ASM_SIMP_TAC[MODRNG_CONG] THEN
   REWRITE_TAC[MODRNG; EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
   GEN_TAC THEN EQ_TAC THENL
   (* ==> *)
   [DISCH_THEN (CHOOSE_THEN MP_TAC) THEN
    DISJ_CASES_TAC (SPEC `d:num` num_CASES) THENL
    [ASM_SIMP_TAC[ADD_CLAUSES]; ALL_TAC] THEN
    POP_ASSUM (X_CHOOSE_THEN `f:num` SUBST1_TAC) THEN
    STRIP_TAC THEN DISJ2_TAC THEN EXISTS_TAC `f:num` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
    GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `SUC e`) THEN
    ASM_REWRITE_TAC[LT_SUC; ADD_CLAUSES];
   (* <== *)
    DISCH_THEN DISJ_CASES_TAC THENL
    [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ADD_CLAUSES; LT];
     POP_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `SUC d` THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
     GEN_TAC THEN DISJ_CASES_TAC (SPEC `e:num` num_CASES) THENL
     [ASM_REWRITE_TAC [ADD_CLAUSES;
        MESON[CONG] `(b == a) (mod m) <=> (a == b) (mod m)`];
      POP_ASSUM (X_CHOOSE_THEN `f:num` ASSUME_TAC) THEN
      ASM_REWRITE_TAC[LT_SUC] THEN
      DISCH_THEN (fun th -> FIRST_X_ASSUM (MP_TAC o C MATCH_MP th)) THEN
      REWRITE_TAC[ADD_CLAUSES]]]]);;

let rec NUM_MODRNG_CONV term =
  (REWR_CONV MODRNG_THM THENC
   DEPTH_CONV (REWR_CONV CONG) THENC
   DEPTH_CONV NUM_RED_CONV THENC
   TRY_CONV (RAND_CONV NUM_MODRNG_CONV)) term;;

(* Some examples to try out:

   NUM_MODRNG_CONV `MODRNG0 5 4 2`;;
   NUM_MODRNG_CONV `MODRNG0 5 1 3`;;
*)

(* TODO:
   - uniformize to (a == b) (mod m) or a MOD m = b MOD m
*)

let MODSUB = define `MODSUB2 m a b = ((a + m) - b MOD m) MOD m`;;

let MODSUB_ZERO = prove
  (`!a b. MODSUB2 0 a b = a - b`,
   REWRITE_TAC[MODSUB; MOD_ZERO; ADD_CLAUSES]);;

let MODSUB_NOT_ZERO = prove
  (`!m a b. ~(m = 0) ==> MODSUB2 m a b = (a + m - b MOD m) MOD m`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[MODSUB] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   MP_TAC(SPECL[`b:num`;`m:num`] MOD_LT_EQ) THEN
   ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let MODSUB_ALT = prove
  (`!m a b. MODSUB2 m a b = if m = 0 then a - b else (a + m - b MOD m) MOD m`,
   MESON_TAC[MODSUB_ZERO; MODSUB_NOT_ZERO]);;

let MODSUB_LT_EQ = prove
  (`!m a b. MODSUB2 m a b < m <=> ~(m = 0)`,
   REWRITE_TAC[MODSUB; MOD_LT_EQ]);;

(* TODO: Contribute this to arith.ml *)
let DIV_MULT_MOD_0 = prove
  (`!a b. a DIV b * b = a <=> a MOD b = 0`,
   REPEAT GEN_TAC THEN ASM_CASES_TAC `b = 0` THENL
   [ASM_REWRITE_TAC[MOD_ZERO; DIV_ZERO; MULT; EQ_SYM_EQ];
    MP_TAC (SPECL[`a:num`;`b:num`] DIVISION) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* TODO: Contribute this to arith.ml *)
let MOD_ADD_MODULUS = prove
  (`(!x m. (x + m) MOD m = x MOD m) /\
    (!x m. (m + x) MOD m = x MOD m)`,
   MAP_EVERY (MP_TAC o SPEC `1`) (CONJUNCTS MOD_MULT_ADD) THEN
   SIMP_TAC[MULT_CLAUSES]);;

let MOD_MODSUB = prove
  (`!m a b. MODSUB2 m a b MOD m = MODSUB2 m a b`,
   REWRITE_TAC[MODSUB; MOD_MOD_REFL]);;

let MODSUB_ADDL = prove
  (`!m a b. ~(m = 0) ==> (b + MODSUB2 m a b) MOD m = a MOD m`,
   ONCE_REWRITE_TAC[GSYM (MOD_DOWN_CONV `(b MOD m MOD m + x) MOD m`)] THEN
   REPEAT STRIP_TAC THEN REWRITE_TAC[MODSUB; MOD_ADD_MOD] THEN
   MP_TAC (ARITH_RULE `b MOD m < m ==>
     b MOD m + (a + m) - b MOD m = a + m`) THEN
   ASM_SIMP_TAC[MOD_LT_EQ; MOD_ADD_MODULUS]);;

let MODSUB_ADDR = prove
  (`!m a b. ~(m = 0) ==> (MODSUB2 m a b + b) MOD m = a MOD m`,
   ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC MODSUB_ADDL);;

(* TODO: Contribute this to in int.ml *)
let CONG_LE_EQ = prove
  (`!x y m. x <= y /\ (x == y) (mod m) <=> ?k. y = x + k * m`,
   REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[CONG] THEN ASM_CASES_TAC `m = 0` THENL
      [ASM_SIMP_TAC[MOD_ZERO; MULT_CLAUSES; ADD_0]; STRIP_TAC] THEN
    MAP_EVERY (fun tm ->
      FIRST_ASSUM (SUBST1_TAC o CONJUNCT1 o MATCH_MP (SPEC tm DIVISION)))
      [`x:num`;`y:num`] THEN
    EXISTS_TAC `y DIV m - x DIV m` THEN
    SUBGOAL_THEN `x DIV m * m <= y DIV m * m` MP_TAC THENL
      [ASM_SIMP_TAC[LE_MULT_RCANCEL; DIV_MONO]; ALL_TAC] THEN
    REWRITE_TAC[RIGHT_SUB_DISTRIB] THEN ASM_ARITH_TAC;
    DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN CONJ_TAC THENL
      [ASM_ARITH_TAC; REWRITE_TAC[CONG; MOD_MULT_ADD]]]);;

let [MODSUB_MODL; MODSUB_MODR] = (CONJUNCTS o prove)
  (`(!m a b. MODSUB2 m (a MOD m) b = MODSUB2 m a b) /\
    (!m a b. MODSUB2 m a (b MOD m) = MODSUB2 m a b)`,
   REWRITE_TAC[MODSUB_ALT] THEN CONJ_TAC THEN GEN_TAC THEN
   CONV_TAC MOD_DOWN_CONV THEN ASM_CASES_TAC `m = 0` THEN
   ASM_REWRITE_TAC[MOD_ZERO]);;

let ADD_MODSUB2 = prove
  (`!m a b. ~(m = 0) ==> MODSUB2 m (a + b) a = b MOD m`,
   ONCE_REWRITE_TAC[MESON[MODSUB_MODL; MOD_ADD_MOD]
     `MODSUB2 m (a + b) a = MODSUB2 m (a MOD m + b MOD m) a`] THEN
   REWRITE_TAC[MODSUB] THEN REPEAT STRIP_TAC THEN
   MP_TAC (ARITH_RULE `a MOD m < m ==>
     ((a MOD m + b MOD m) + m) - a MOD m = b MOD m + m`) THEN
   ASM_SIMP_TAC[MOD_LT_EQ; MOD_ADD_MODULUS; MOD_MOD_REFL]);;

let MODSUB_EXISTS = prove
  (`!m a b s. a MOD m = (b + s) MOD m <=>
      (?k. s = MODSUB2 m a b + k * m) /\ (m = 0 ==> b <= a)`,
   REPEAT GEN_TAC THEN EQ_TAC THENL
   (* ==> *)
   [ASM_CASES_TAC `m = 0` THENL
      [ASM_REWRITE_TAC[MOD_ZERO; MODSUB_ZERO; MULT_CLAUSES; ADD_CLAUSES] THEN
       ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    ONCE_REWRITE_TAC[GSYM MODSUB_MODL] THEN
    DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC[GSYM (MOD_DOWN_CONV`(b MOD m + s) MOD m`)] THEN
    REWRITE_TAC[MODSUB_MODL; MODSUB] THEN
    REWRITE_TAC[MOD_ADD_MODULUS;
      ARITH_RULE `(((b MOD m) + s) + m) - b MOD m = s + m`] THEN
    ASM_MESON_TAC[DIVISION; ADD_SYM];
   (* <== *)
    STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
    REWRITE_TAC[ADD_ASSOC; MOD_MULT_ADD] THEN
    ASM_CASES_TAC `m = 0` THENL
    [ASM_REWRITE_TAC[MOD_ZERO; MODSUB_ZERO] THEN ASM_ARITH_TAC;
     ASM_SIMP_TAC[MODSUB_ADDL]]]);;

let MODSUB_UNIQ = prove
  (`!m a b s. a MOD m = (b + s) MOD m /\ s < m ==> MODSUB2 m a b = s`,
   REWRITE_TAC[MODSUB_EXISTS] THEN REPEAT STRIP_TAC THEN
   FIRST_ASSUM SUBST1_TAC THEN
   SUBGOAL_THEN `k = 0`
     (fun th -> REWRITE_TAC[th; MULT_CLAUSES; ADD_CLAUSES]) THEN
   POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
   ASM_REWRITE_TAC[NOT_LT] THEN
   DISJ_CASES_THEN2 SUBST1_TAC (CHOOSE_THEN SUBST1_TAC)
     (SPEC `k:num` num_CASES) THEN
   REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC);;

let MODSUB_SUC_LT = prove
  (`!m a b s. ~(m = 0) /\ ~(a == b) (mod m) ==>
      MODSUB2 m a (SUC b) < MODSUB2 m a b`,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC `m = 1` THENL [ASM_REWRITE_TAC[CONG; MOD_1]; STRIP_TAC] THEN
   SUBGOAL_THEN `MODSUB2 m a b = SUC (MODSUB2 m a (SUC b))` MP_TAC THENL
     [MATCH_MP_TAC MODSUB_UNIQ; ARITH_TAC] THEN
   ASM_SIMP_TAC[ARITH_RULE `x + SUC y = SUC x + y`; MODSUB_ADDL] THEN
   MATCH_MP_TAC(ARITH_RULE
     `!x. x < m /\ ~(x = m - 1) /\ ~(m = 0) ==> SUC x < m`) THEN
   ASM_REWRITE_TAC[MODSUB_LT_EQ] THEN
   POP_ASSUM MP_TAC THEN REWRITE_TAC[CONTRAPOS_THM; CONG] THEN STRIP_TAC THEN
   GEN_REWRITE_TAC RAND_CONV [GSYM (CONJUNCT1 MOD_ADD_MODULUS)] THEN
   FIRST_ASSUM (SUBST1_TAC o MATCH_MP (ARITH_RULE
     `~(m = 0) ==> b + m = SUC b + (m - 1)`)) THEN
   POP_ASSUM (SUBST1_TAC o GSYM) THEN
   ASM_SIMP_TAC[MODSUB_ADDL]);;

let MODRNG_MODSUB = prove
  (`!m a b. ~(m = 0) ==>
      MODRNG0 m a b = {x | x < m /\ MODSUB2 m x a <= MODSUB2 m b a}`,
   REWRITE_TAC[EXTENSION; MODRNG; IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THENL
   (* ==> *)
   [STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
    ASM_SIMP_TAC[MODSUB_MODL; ADD_MODSUB2; MOD_LT_EQ] THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_LE] THEN STRIP_TAC THEN CONV_TAC NNF_CONV THEN
    EXISTS_TAC `MODSUB2 m b a` THEN CONJ_TAC THENL
    [TRANS_TAC LTE_TRANS `d MOD m` THEN ASM_REWRITE_TAC[MOD_LE];
     ASM_SIMP_TAC[CONG; MODSUB_ADDL]];
   (* <== *)
    STRIP_TAC THEN EXISTS_TAC `MODSUB2 m x a` THEN CONJ_TAC THENL
    [MATCH_MP_TAC EQ_SYM THEN ASM_SIMP_TAC[MODSUB_ADDL; MOD_EQ_SELF];
     GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
     REWRITE_TAC[CONG; NOT_CLAUSES; NOT_LT; MODSUB_EXISTS] THEN
     DISCH_THEN (CONJUNCTS_THEN2 (CHOOSE_THEN SUBST1_TAC) (K ALL_TAC)) THEN
     ASM_ARITH_TAC]]);;

(* There ought to be a simpler proof of that! *)
let MODRNG_SUC_PSUBSET = prove
  (`!m a b. ~(a == b) (mod m) ==> MODRNG0 m (SUC a) b PSUBSET MODRNG0 m a b`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[PSUBSET_INSERT_SUBSET] THEN
   EXISTS_TAC `a MOD m` THEN
   GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [MODRNG_THM] THEN
   ASM_REWRITE_TAC[SUBSET_REFL] THEN
   POP_ASSUM MP_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[MODRNG_ZERO; MOD_ZERO; CONG] THEN
    COND_CASES_TAC THEN REWRITE_TAC[IN_NUMSEG; IN_ELIM_THM] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
   ASM_CASES_TAC `m = 1` THENL [ASM_REWRITE_TAC[CONG; MOD_1]; ALL_TAC] THEN
   (* We are now in the non-degenerate case where m > 1 *)
   REWRITE_TAC[CONG; MODRNG; IN_ELIM_THM] THEN STRIP_TAC THEN
   CONV_TAC NNF_CONV THEN GEN_TAC THEN
   ASM_CASES_TAC `?k. d = (m - 1) + k * m` THENL
   (* ?k. d = m - 1 + m * k *)
   [POP_ASSUM (CHOOSE_THEN SUBST1_TAC) THEN DISJ2_TAC THEN
    EXISTS_TAC `MODSUB2 m b (SUC a)` THEN CONJ_TAC THENL
    (* first conjunct *)
    [TRANS_TAC LTE_TRANS `m - 1` THEN
     CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
     MATCH_MP_TAC (ARITH_RULE
      `x < m /\ ~(x = m - 1) ==> x < m - 1`) THEN
     ASM_REWRITE_TAC[MODSUB_LT_EQ] THEN POP_ASSUM MP_TAC THEN
     REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_THEN (ASSUME_TAC o GSYM) THEN
     GEN_REWRITE_TAC LAND_CONV [(GSYM o CONJUNCT1) MOD_ADD_MODULUS] THEN
     FIRST_ASSUM (SUBST1_TAC o MATCH_MP
       (ARITH_RULE `~(m = 0) ==> a + m = SUC a + m - 1`)) THEN
     ASM_SIMP_TAC[MODSUB_ADDL];
    (* 2nd conjunct *)
     CONV_TAC MOD_DOWN_CONV THEN ASM_SIMP_TAC[MODSUB_ADDL]];
   (* ~(?k. d = m - 1 + m * k) *)
    DISJ1_TAC THEN POP_ASSUM MP_TAC THEN
    REWRITE_TAC[CONTRAPOS_THM; GSYM CONG] THEN
    MP_TAC (ARITH_RULE `a <= SUC a + d`) THEN
    REWRITE_TAC[GSYM IMP_CONJ; CONG_LE_EQ] THEN
    DISCH_THEN (CHOOSE_THEN MP_TAC) THEN
    DISJ_CASES_TAC (SPEC `k:num` num_CASES) THENL
      [POP_ASSUM SUBST1_TAC THEN ARITH_TAC; ALL_TAC] THEN
    POP_ASSUM (X_CHOOSE_THEN `l:num` SUBST1_TAC) THEN
    REWRITE_TAC[MULT_CLAUSES] THEN
    STRIP_TAC THEN EXISTS_TAC `l:num` THEN
    ASM_ARITH_TAC (* slow! *)]);;

(* ------------------------------------------------------------------------- *)
(* Induction principle for modular arithmetic.                               *)
(* ------------------------------------------------------------------------- *)

let MODLOOP_IND = prove
  (`!m y P.
      ~(m = 0) /\ (!x. (x == y) (mod m) \/ P (SUC x) ==> P x) ==> !x. P x`,
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   SUBGOAL_THEN `WF (MEASURE (\x. MODSUB2 m y x))` MP_TAC THENL
     [REWRITE_TAC[WF_MEASURE]; REWRITE_TAC[WF_IND]] THEN
   DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[MEASURE] THEN
   GEN_TAC THEN ASM_CASES_TAC `(x == y) (mod m)` THENL
   [DISCH_THEN (K ALL_TAC) THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN (fun th ->
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASSUME_TAC th) THEN
    DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC MODSUB_SUC_LT THEN
    ASM_MESON_TAC[CONG]]);;

(* ------------------------------------------------------------------------- *)
(* Linear probing hash tables.                                               *)
(* ------------------------------------------------------------------------- *)

(*
   A hash table has three components:
   - a hash function from the key space K to num
   - a table represented as a function from num to
     entries; NONE is used to represent free entries
     while SOME (k,v) represents a binding that maps
     the key k to the value v
   - a modulus; it is the max number of bindings in
     the table
*)

new_type_abbrev("hash",`:(K->num)#(num->(K#V)option)#num`);;

let hmod = new_definition `hmod (h:hash) = SND (SND h)`;;
let htbl = new_definition `htbl (h:hash) = FST (SND h)`;;
let hfun = new_definition `hfun (h:hash) = (\x. FST h x MOD hmod h)`;;

let HGET = prove
  (`hfun (f,t,m) = (\x. f x MOD m) /\
    htbl (f,t,m) = t /\
    hmod (f,t,m) = m`,
   SIMP_TAC[hfun; htbl; hmod]);;

let HFUN_LT_EQ = prove
  (`!h k. hfun h k < hmod h <=> ~(hmod h = 0)`,
   SIMP_TAC[FORALL_PAIR_THM; HGET; MOD_LT_EQ]);;

let hnext = new_definition `hnext (h:hash) p = SUC p MOD hmod h`;;

let FINDLOOP = define
  `FINDLOOP h k p =
     if htbl h p = NONE \/ (?v. htbl h p = SOME (k,v))
     then p
     else FINDLOOP h k (hnext h p)`;;

let FIND = new_definition
  `FIND h k = htbl h (FINDLOOP h k (hfun h k))`;;

let NOTFULL = new_definition
  `NOTFULL h = ?p. p < hmod h /\ htbl h p = NONE`;;

(* Describes the guts of a healthy hash table; we require
   that for any key k, value v, position p, if the table
   has the (k,v) binding at position p, then all entries
   from from `hfun h k` to `p - 1` are non-empty and do
   not bind the key `k` *)
let INV0 = define
  `INV0 h =
    !p k v. p < hmod h /\ htbl h p = SOME (k,v) ==>
    !q. q IN MODRNG0 (hmod h) (hfun h k) p /\ ~(q = p) ==>
    ?kq vq. htbl h q = SOME (kq,vq) /\ ~(kq = k)`;;

let hempty = define `hempty f m = (f,(\x. NONE),m)`;;

let INV0_HEMPTY = prove
  (`!f m. INV0 (hempty f m:hash)`,
   REWRITE_TAC[INV0; hempty; HGET; distinctness "option"]);;

(* If the invariant INV0 holds, then any binding (k,v) in the
   hash table can be fetched using HFIND h k *)
let INV0_FIND = prove
  (`!(h:hash) k v p.
      INV0 h /\ p < hmod h /\ htbl h p = SOME (k,v) ==>
      FIND h k = SOME (k,v)`,
   REPEAT GEN_TAC THEN DISCH_THEN ASSUME_TAC THEN
   REWRITE_TAC[FIND] THEN
   SUBGOAL_THEN `FINDLOOP (h:hash) k (hfun h k) = p`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
   POP_ASSUM (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
   REWRITE_TAC[INV0] THEN
   DISCH_THEN (fun th -> FIRST_ASSUM (MP_TAC o MATCH_MP th)) THEN

   (* add the MOD in the findloop argument; cleanup this crap! *)
   SUBGOAL_THEN `hfun (h:hash) k < hmod h` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[HFUN_LT_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   FIRST_ASSUM (MP_TAC o GSYM o MATCH_MP MOD_LT) THEN
   DISCH_THEN (fun th -> GEN_REWRITE_TAC (RAND_CONV o DEPTH_CONV) [th]) THEN
   POP_ASSUM (K ALL_TAC) THEN

   SPEC_TAC (`hfun (h:hash) k`,`c:num`) THEN
   MATCH_MP_TAC (SPECL[`hmod (h:hash)`;`p:num`] MODLOOP_IND) THEN
   CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   GEN_TAC THEN STRIP_TAC THENL
   (* base case *)
   [DISCH_THEN (K ALL_TAC) THEN
    POP_ASSUM MP_TAC THEN SIMP_TAC[CONG] THEN
    DISCH_THEN (K ALL_TAC) THEN
    ASM_SIMP_TAC[MOD_LT] THEN
    ONCE_REWRITE_TAC[FINDLOOP] THEN
    ASM_REWRITE_TAC[injectivity"option"; MESON[]`?v'. k,v = k,v'`];
   (* possibly recursive case *)
    CHEAT_TAC]);;

let f2 = new_definition
  `f2 n m = ((n + 1) * n) DIV 2 + m`;;

(* we will prove that b2 is a bijection from NxN to N *)
let b2 = new_definition
  `b2 a b = f2 (a + b) b`;;

let invlf2 = new_definition
  `invlf2 k = minimal n. k - ((n + 1) * n) DIV 2 <= n`;;

let BINOM_ADD_1 = prove
  (`!n. (((n + 1) + 1) * (n + 1)) DIV 2 = ((n + 1) * n) DIV 2 + (n + 1)`,
   GEN_TAC THEN IMP_REWRITE_TAC[DIV_MULT_ADD;
     ARITH_RULE`((n + 1) + 1) * (n + 1) =
                (n + 1) * n + 2 * (n + 1)`] THEN
   CONV_TAC (RAND_CONV NUM_REL_CONV) THEN REWRITE_TAC[]);;

let BINOM_MONO = prove
  (`!n m. n <= m ==> ((n + 1) * n) DIV 2 <= ((m + 1) * m) DIV 2`,
   IMP_REWRITE_TAC[DIV_MONO; LE_MULT2] THEN ARITH_TAC);;

let F2_INVL_LEMMA = prove
  (`!n m k. k = f2 n m /\ m <= n ==> n = invlf2 k`,
   REWRITE_TAC[f2; invlf2] THEN REPEAT STRIP_TAC THEN
   CONV_TAC SYM_CONV THEN MATCH_MP_TAC MINIMAL_UNIQUE THEN
   REWRITE_TAC[] THEN CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
   X_GEN_TAC `x:num` THEN STRIP_TAC THEN REWRITE_TAC[NOT_LE] THEN
   FIRST_X_ASSUM (SUBST1_TAC o check (is_eq o concl)) THEN
   SUBGOAL_THEN `n = PRE n + 1` SUBST1_TAC THEN TRY ASM_ARITH_TAC THEN
   REWRITE_TAC[BINOM_ADD_1; GSYM ADD_ASSOC] THEN
   IMP_REWRITE_TAC[ARITH_RULE`c <= a ==> (a + b) - c = a - c + b`] THEN
   CONJ_TAC THEN TRY ASM_ARITH_TAC THEN MATCH_MP_TAC BINOM_MONO THEN
   ASM_ARITH_TAC);;

let invrf2 = new_definition
  `invrf2 k = k - ((invlf2 k + 1) * invlf2 k) DIV 2`;;

let F2_INV = prove
  (`!n m k. k = f2 n m /\ m <= n ==> n = invlf2 k /\ m = invrf2 k`,
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   FIRST_ASSUM (MP_TAC o MATCH_MP F2_INVL_LEMMA) THEN
   SIMP_TAC[invrf2] THEN POP_ASSUM STRIP_ASSUME_TAC THEN
   STRIP_TAC THEN POP_ASSUM (SUBST1_TAC o SYM) THEN
   FIRST_ASSUM SUBST1_TAC THEN REWRITE_TAC[f2] THEN
   REWRITE_TAC[ADD_SUB2]);;

let B2_INJ = prove
  (`!a b a' b'. b2 a b = b2 a' b' ==> a = a' /\ b = b'`,
   REWRITE_TAC[b2] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ] F2_INV)) THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ] F2_INV) o SYM) THEN
   ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let INVL_DEFINED = prove
  (`!k. ?r. k - ((r + 1) * r) DIV 2 <= r`,
   INDUCT_TAC THENL
   [ EXISTS_TAC `0` THEN CONV_TAC (DEPTH_CONV NUM_RED_CONV);
     POP_ASSUM (CHOOSE_THEN(STRIP_ASSUME_TAC o
       MATCH_MP(ARITH_RULE`a <= b ==> a = b \/ a < b`))) THENL
     [ EXISTS_TAC `r + 1` THEN REWRITE_TAC[BINOM_ADD_1] THEN
       ASM_ARITH_TAC;
       EXISTS_TAC `r:num` THEN ASM_ARITH_TAC ] ]);;

let INVR_LE_INVL = prove
  (`!k. invrf2 k <= invlf2 k`,
   REWRITE_TAC[invrf2] THEN
   SIMP_TAC[REWRITE_RULE[GSYM invlf2; MINIMAL] INVL_DEFINED]);;

let INVR_DEFINED = prove
  (`!k. ((invlf2 k + 1) * invlf2 k) DIV 2 <= k`,
   GEN_TAC THEN DISJ_CASES_TAC(SPEC `invlf2 k` num_CASES) THENL
   [ POP_ASSUM SUBST1_TAC THEN CONV_TAC (DEPTH_CONV NUM_RED_CONV) THEN
     REWRITE_TAC[LE_0];
     POP_ASSUM STRIP_ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN
     MP_TAC (REWRITE_RULE[GSYM invlf2; MINIMAL] INVL_DEFINED) THEN
     DISCH_THEN (MP_TAC o CONJUNCT2 o SPEC `k:num`) THEN
     DISCH_THEN (MP_TAC o SPEC `n:num`) THEN
     ANTS_TAC THEN ASM_ARITH_TAC ]);;

let B2_SURJ = prove
  (`!k. ?a b. k = b2 a b`,
   GEN_TAC THEN REWRITE_TAC[b2] THEN
   EXISTS_TAC `invlf2 k - invrf2 k` THEN
   EXISTS_TAC `invrf2 k` THEN
   IMP_REWRITE_TAC[SUB_ADD; INVR_LE_INVL] THEN
   REWRITE_TAC[f2; invrf2] THEN
   MATCH_MP_TAC(ARITH_RULE`a <= b ==> b = a + b - a`) THEN
   REWRITE_TAC[INVR_DEFINED]);;

let B2_BIJ = prove
  (`BIJ (UNCURRY b2) (:num#num) (:num)`,
   REWRITE_TAC[BIJ; INJ; SURJ; IN_UNIV;
               FORALL_PAIR_THM; EXISTS_PAIR_THM; UNCURRY_DEF] THEN
   MESON_TAC[B2_INJ; B2_SURJ]);;

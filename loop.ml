needs "Library/iter.ml";;

let LOOP = new_definition
  `LOOP N B = \x y. ~B y /\ x = N y`;;

(*
search [`WF(<)`] (* WF_num *)
search [`x ==> WF(y)`]
*)

let MINIMAL_SUC = prove
  (`!P. (?n. P n) /\ ~(P 0) ==> (minimal) P = SUC ((minimal) (P o SUC))`,
   GEN_TAC THEN SUBST1_TAC (MESON [num_CASES; NOT_SUC]
       `(?n. P n) /\ ~(P 0) <=> (?n. (P (SUC n))) /\ ~(P 0)`) THEN
   REWRITE_TAC[REWRITE_RULE[o_THM] (SPEC `(P:num->bool) o SUC` MINIMAL)] THEN
   STRIP_TAC THEN MATCH_MP_TAC MINIMAL_UNIQUE THEN CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   GEN_TAC THEN DISJ_CASES_TAC (SPEC `m:num` num_CASES) THEN
   ASM_REWRITE_TAC[] THEN POP_ASSUM (CHOOSE_THEN SUBST1_TAC) THEN
   ASM_SIMP_TAC[LT_SUC]);;

let WF_LOOP = prove
  (`!N (B:A->bool). (!s. ~B s ==> ?n. B (ITER n N s)) ==> WF(LOOP N B)`,
   REPEAT STRIP_TAC THEN MATCH_MP_TAC WF_SUBSET THEN
   EXISTS_TAC `MEASURE (\s. minimal n. (B:A->bool) (ITER n N s))` THEN
   REWRITE_TAC[WF_MEASURE; MEASURE; LOOP] THEN REPEAT STRIP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN REWRITE_TAC[GSYM ITER_ALT] THEN
   MP_TAC(SPEC `\n. (B:A->bool) (ITER n N y)` MINIMAL_SUC) THEN
   ASM_SIMP_TAC[CONJUNCT1 ITER; o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[LT]);;

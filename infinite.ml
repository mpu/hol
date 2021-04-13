(* Theorem: we can inject N in all infinite sets.
   In fact being infinite is precisely equivalent
   to containing N. *)

(* A pretty classic function... *)
let numinj_DEF = define
  `numinj s i =
     match i with
       0 -> CHOICE s
     | SUC i -> numinj (s DIFF {CHOICE s}) i`;;

let NUMINJ_IN = prove
  (`!i (s:A->bool). INFINITE s ==> numinj s i IN s`,
   INDUCT_TAC THEN ONCE_REWRITE_TAC[numinj_DEF] THENL
   [ REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
     MATCH_MP_TAC CHOICE_DEF THEN
     MATCH_MP_TAC INFINITE_NONEMPTY THEN
     POP_ASSUM ACCEPT_TAC;
     REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
     MATCH_MP_TAC (SET_RULE
       `(x:A) IN (s DIFF {CHOICE s}) ==> x IN s`) THEN
     FIRST_ASSUM MATCH_MP_TAC THEN
     MATCH_MP_TAC INFINITE_DIFF_FINITE THEN
     ASM_REWRITE_TAC[FINITE_SING] ]);;

(* in more convenient form for the followup *)
let NUMINJ_IN =
  (REWRITE_RULE[RIGHT_FORALL_IMP_THM] o
   ONCE_REWRITE_RULE[SWAP_FORALL_THM]) NUMINJ_IN;;

(* the theorem we wanted to prove *)
let INFINITE_IMP_NUM_INJ = prove
  (`!s:A->bool. INFINITE s ==> ?f. INJ f (:num) s`,
   GEN_TAC THEN STRIP_TAC THEN
   EXISTS_TAC `(numinj s):num->A` THEN
   REWRITE_TAC[INJ; IN_UNIV] THEN STRIP_TAC THENL
   [ ASM_MESON_TAC[NUMINJ_IN];
     GEN_TAC THEN POP_ASSUM MP_TAC THEN
     MAP_EVERY (fun x -> SPEC_TAC(x,x)) [`s:A->bool`;`x:num`] THEN
     INDUCT_TAC THEN ONCE_REWRITE_TAC[numinj_DEF] THENL
     [ REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
       POP_ASSUM MP_TAC THEN MP_TAC (SPEC `y:num` num_CASES) THEN
       STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN REWRITE_TAC[] THEN
       MP_TAC (SPEC `s DIFF {CHOICE s:A}` NUMINJ_IN) THEN
       IMP_REWRITE_TAC[INFINITE_DIFF_FINITE; FINITE_SING] THEN
       SET_TAC[];
       REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
       POP_ASSUM MP_TAC THEN MP_TAC (SPEC `y:num` num_CASES) THEN
       STRIP_TAC THEN POP_ASSUM SUBST1_TAC THEN REWRITE_TAC[] THENL
       [ MP_TAC (SPEC `s DIFF {CHOICE s:A}` NUMINJ_IN) THEN
         IMP_REWRITE_TAC[INFINITE_DIFF_FINITE; FINITE_SING] THEN
         SET_TAC[];
         STRIP_TAC THEN REWRITE_TAC[injectivity"num"] THEN
         FIRST_X_ASSUM (MP_TAC o SPEC `s DIFF {CHOICE s:A}`) THEN
         IMP_REWRITE_TAC[INFINITE_DIFF_FINITE; FINITE_SING] ] ] ]);;

(* the equivalence holds, actually! *)
let INFINITE_NUM_INJ = prove
  (`!s:A->bool. INFINITE s <=> ?f. INJ f (:num) s`,
   GEN_TAC THEN EQ_TAC THENL
   [ MATCH_ACCEPT_TAC INFINITE_IMP_NUM_INJ;
     STRIP_TAC THEN MATCH_MP_TAC INFINITE_SUPERSET THEN
     EXISTS_TAC `IMAGE (f:num->A) (:num)` THEN
     POP_ASSUM MP_TAC THEN REWRITE_TAC[INJ] THEN
     IMP_REWRITE_TAC[INFINITE_IMAGE; num_INFINITE] THEN
     SET_TAC[] ]);;

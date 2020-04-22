(*
  - pure_prove_recursive_function_exists
  - new_inductive_definition
*)

needs "Library/iter.ml";;

let loop_RECURSION = prove
  (`!(e:A) c b i R. WF(R) /\ (!(s:S). ~b s ==> R (i s) s) ==>
      ?f. !s. f s = if b s then e else c s (f (i s))`,
  REWRITE_TAC[WF_IND] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `MINI = \s:S n.
    b (ITER n i s) /\ !m. m < n ==> ~b (ITER m i s)` THEN
  (* --- lemma 1: MINI existence *)
  SUBGOAL_THEN `!s:S. ?n:num. MINI s n` MP_TAC THENL
  [EXPAND_TAC "MINI" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `(b:S->bool) s` THENL
   [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ITER; LT]; ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `(i:S->S) s`) THEN
   ASM_SIMP_TAC[] THEN DISCH_THEN (CHOOSE_THEN STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `SUC n` THEN ASM_REWRITE_TAC[ITER_ALT] THEN GEN_TAC THEN
   DISJ_CASES_TAC (SPEC `m:num` num_CASES) THENL
   [ASM_REWRITE_TAC[ITER];
    POP_ASSUM (CHOOSE_THEN SUBST1_TAC) THEN
    ASM_SIMP_TAC[ITER_ALT; LT_SUC]]; ALL_TAC] THEN
  (* --- lemma 2: MINI unicity *)
  SUBGOAL_THEN `!s:S. !(k:num) l.
    MINI s k /\ MINI s l ==> k = l` ASSUME_TAC THENL
  [EXPAND_TAC "MINI" THEN REPEAT (POP_ASSUM (K ALL_TAC)) THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [ARITH_RULE `k = l <=> ~(k < l) /\ ~(l < k)`] THEN
   CONJ_TAC THEN DISCH_THEN(fun i -> FIRST_ASSUM(MP_TAC o C MATCH_MP i)) THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* --- main proof *)
  CHOOSE_THEN ASSUME_TAC (prove_general_recursive_function_exists
    `?G. (!s. G 0 (s:S) = (e:A)) /\
         (!n s. (G (SUC n) s = c s (G n (i s))))`) THEN
  STRIP_TAC THEN EXISTS_TAC `\s. (G:num->S->A) (@n. MINI s n) s` THEN
  BETA_TAC THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   (* case: b s *)
  [SUBGOAL_THEN `(@n:num. MINI (s:S) n) = 0`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
   FIRST_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `s:S` THEN CONV_TAC (DEPTH_CONV SELECT_CONV) THEN
   CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
   EXPAND_TAC "MINI" THEN ASM_REWRITE_TAC[ITER; LT];
   (* case: ~b s *)
   FIRST_ASSUM(fun asm -> REWRITE_TAC[GSYM(CONJUNCT2 asm)]) THEN
   (* --- lemma 3: MINI and SUC *)
   SUBGOAL_THEN `(@n:num. MINI (s:S) n) = SUC (@n. MINI (i s) n)`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
   FIRST_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s:S` THEN
   CONV_TAC (DEPTH_CONV SELECT_CONV) THEN
   CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `!n:num. MINI ((i:S->S) s) n <=> MINI s (SUC n)`
     (fun th -> REWRITE_TAC[th]) THENL
   [POP_ASSUM MP_TAC THEN EXPAND_TAC "MINI" THEN
    REPEAT (POP_ASSUM (K ALL_TAC)) THEN REPEAT STRIP_TAC THEN EQ_TAC THEN
    REWRITE_TAC[ITER_ALT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
    [GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP (
       MESON[num_CASES; LT_SUC]
        `(m < SUC n) ==> m = 0 \/ ?k. (m = SUC k /\ k < n)`)) THEN
     DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[ITER_ALT];
     GEN_TAC THEN STRIP_TAC THEN
     REWRITE_TAC[GSYM ITER_ALT] THEN FIRST_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[LT_SUC]]; ALL_TAC] THEN
   (* --- back to ~b s *)
   ONCE_REWRITE_TAC[GSYM o_THM] THEN
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM o_THM] THEN
   CONV_TAC SELECT_CONV THEN REWRITE_TAC[o_THM] THEN
   FIRST_X_ASSUM (CHOOSE_THEN MP_TAC o SPEC `s:S`) THEN
   DISJ_CASES_TAC (SPEC `n:num` num_CASES) THENL
   [POP_ASSUM SUBST1_TAC THEN EXPAND_TAC "MINI" THEN ASM_REWRITE_TAC[ITER];
    POP_ASSUM MP_TAC THEN MESON_TAC[]]]);;

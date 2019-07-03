open HolKernel boolLib bossLib arithmeticTheory logrootTheory;

val _ = new_theory "fastexp"

val FEXP_def = tDefine"FEXP"
  `FEXP b e =
    if e = 0 then
      1
    else if EVEN e then
      FEXP (b * b) (e DIV 2)
    else
      b * FEXP (b * b) (e DIV 2)`
  (WF_REL_TAC `measure SND` >> rw[DIV_LESS])

Theorem DIV2_INDUCTION:
  !P. P 0 /\ (!a. P (a DIV 2) ==> P a) ==> !a. P a
Proof
  CONV_TAC (BINDER_CONV RIGHT_IMP_FORALL_CONV
            THENC SWAP_FORALL_CONV)
  >> completeInduct_on `a` >> rpt strip_tac
  >> `(a = 0) \/ (0 < a)` by decide_tac
  >> rw[(EVAL_RULE o Q.SPECL [`a`, `2`]) DIV_LESS]
QED

Theorem FEXP_EXP:
  !e b. FEXP b e = b ** e
Proof
  recInduct DIV2_INDUCTION
  >> rpt strip_tac >> rw[Once FEXP_def, EXP_MUL]
  (* EVEN case *)
  >- (qspec_then `a` mp_tac EVEN_EXISTS >> rw[]
      >> rw[SIMP_RULE arith_ss [] (Q.SPEC `2` MULT_DIV)])
  (* ODD case *)
  >- (pop_assum (assume_tac o REWRITE_RULE [GSYM ODD_EVEN])
      >> qspec_then `a` mp_tac ODD_EXISTS >> rw[]
      >> rw[ADD1, SimpL ``$=``]
      >> rw[EXP, SIMP_RULE arith_ss [] (Q.SPECL [`2`, `1`] DIV_MULT)])
QED

val _ = export_theory()

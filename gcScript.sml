open HolKernel Tactic Tactical Conv Rewrite
     bossLib arithmeticTheory bitTheory;

val _ = new_theory "gc";

(* BITS gives a range of bits of a number *)
val BITS_EX1 = Q.prove (
  `BITS 0 0 3 = 1`,
  simp [BITS_THM]
)

val BITS_EX2 = Q.prove (
  `BITS 2 1 6 = 3`,
  simp [BITS_THM]
)

Theorem NOT_BIT_ANY_GT_TWOEXP:
  !i j n. n < 2 ** i /\ i <= j ==> ~BIT j n
Proof
  metis_tac [SIMP_CONV std_ss [] ``2 ** i <= 2 ** j``,
             LESS_LESS_EQ_TRANS, NOT_BIT_GT_TWOEXP]
QED

val TOY_EX1 = Q.prove(
  `!n. n <= n * n`,
  HO_MATCH_MP_TAC numTheory.INDUCTION >>
  RW_TAC std_ss []
)

(* Define the gray code successor relation *)
val GCREL_def = Define`
  GCREL a b = ?n. (BIT n a <> BIT n b) /\
                  !m. m <> n ==> (BIT m a = BIT m b)`;

val bit_ss = std_ss && [BIT_def, BITS_THM]

val GCREL_EX1 = Q.prove(
  `GCREL 11 15`,
  simp_tac pure_ss [GCREL_def]
  >> qexists_tac `2`
  >> conj_tac >| [rw_tac bit_ss [], rw[]]
  >> `(m = 0) \/ (m = 1) \/ (m = 3) \/ (4 <= m)` by decide_tac
    >| (fn t => [t,t,t,all_tac]) (rw_tac bit_ss [])
    >- rw [Q.SPEC `4` NOT_BIT_ANY_GT_TWOEXP]
)

val BIT0_MOD2_LEM = Q.prove(
  `!a b. (a MOD 2 = b MOD 2) <=> (BIT 0 a = BIT 0 b)`,
  rw_tac std_ss [BIT0_ODD, ODD_MOD2_LEM, MOD_2])

Theorem DIV2_INDUCTION:
  !P. P 0 /\ (!a. P (a DIV 2) ==> P a) ==> !a. P a
Proof
  CONV_TAC (BINDER_CONV RIGHT_IMP_FORALL_CONV
            THENC SWAP_FORALL_CONV)
  >> completeInduct_on `a` >> rpt strip_tac
  >> `(a = 0) \/ (0 < a)` by decide_tac
  >> rw[(EVAL_RULE o Q.SPECL [`a`, `2`]) DIV_LESS]
QED

Theorem ALL_BIT_EQ:
  !a b. (!n. BIT n a = BIT n b) ==> (a = b)
Proof
  recInduct DIV2_INDUCTION
  >> rw_tac bool_ss [] >| [
    (* a = 0, then show b is 0 by contradiction *)
    metis_tac [BIT_ZERO, BIT_LOG2],
    (* 0 < a, use a = a DIV 2 + a MOD 2 *)
    `a DIV 2 = b DIV 2` by full_simp_tac bool_ss [BIT_DIV2] >>
    `a MOD 2 = b MOD 2` by full_simp_tac bool_ss [BIT0_MOD2_LEM] >>
    metis_tac [(EVAL_RULE o Q.SPEC `2`) DIVISION]
  ]
QED

Theorem GCREL_DIV2:
  !a b. GCREL a b =
          (((ODD a <> ODD b) /\ (a DIV 2 = b DIV 2)) \/
          ((ODD a = ODD b) /\ GCREL (a DIV 2) (b DIV 2)))
Proof
  rpt gen_tac >> eq_tac >| [
    (* => *)
    (* CONV_TAC (LAND_CONV (REWR_CONV GCREL_def)) >> rpt strip_tac *)
    rw[GCREL_def, SimpL ``(==>)``]
    >> Cases_on `n` >| [
      (* Case where bit 0 differs *)
      disj1_tac >> fs[BIT0_ODD, BIT_DIV2, ALL_BIT_EQ],
      (* Case where some other bit differs *)
      disj2_tac >> conj_tac >| [
        fs [GSYM BIT0_ODD, DECIDE ``0 <> SUC n'``],
        simp [GCREL_def, BIT_DIV2]
        >> qexists_tac `n'` >> rw[]
      ]
    ],
    (* <= *)
    simp [GCREL_def] >> strip_tac >| [
      (* case where bit 0 differs *)
      qexists_tac `0` >> rw_tac bool_ss [BIT0_ODD]
      >> Cases_on `m` >> fs[GSYM BIT_DIV2],
      (* case where some other bit differs *)
      qexists_tac `SUC n` >> fs[BIT_DIV2]
      >> Cases_on `m` >> fs[BIT0_ODD]
    ]
  ]
QED

val XORREL_def = Define
  `XORREL a b c = !n. BIT n c = (BIT n a <> BIT n b)`

Theorem XOR_EXISTS:
  !a b. ?c. XORREL a b c
Proof
  recInduct DIV2_INDUCTION
  >> rw_tac bool_ss [XORREL_def] >| [
    (* base case a = 0, then the xor is b *)
    qexists_tac `b` >> full_simp_tac std_ss [BIT_ZERO],
    (* inductive P (a DIV 2) ==> P a *)
    first_x_assum (qspec_then `b DIV 2` mp_tac)
    >> rw_tac bool_ss []
    >> qexists_tac `c * 2 + if BIT 0 a <> BIT 0 b then 1 else 0`
    >> Cases >| [
      (* n is 0 *)
      pop_assum kall_tac
      >> rw_tac bit_ss [MOD_TIMES],
      (* n is SUCC n' *)
      rw_tac std_ss [GSYM BIT_DIV2, DIV_MULT]
    ]
  ]
QED

val XOR_def = new_specification(
  "XOR_def", ["XOR"],
  CONV_RULE (REWRITE_CONV [XORREL_def] THENC SKOLEM_CONV) XOR_EXISTS)

Theorem XOR_UNIQUE:
  !a b c. XORREL a b c ==> (c = XOR a b)
Proof
  rw[] >> irule ALL_BIT_EQ >> fs[XOR_def, XORREL_def]
QED

Theorem XOR_COMM:
  !a b. XOR a b = XOR b a
Proof
  rw[] >> irule ALL_BIT_EQ >> rw[] >> eq_tac
  >> simp_tac bool_ss [XOR_def, XORREL_def]
QED

Theorem XOR_ASSOC:
  !a b c. XOR a (XOR b c) = XOR (XOR a b) c
Proof
  rpt gen_tac >> irule ALL_BIT_EQ
  >> simp_tac pure_ss [XOR_def, XORREL_def]
  >> metis_tac[]
QED

val XOR_ss = simpLib.SSFRAG {name = SOME"XOR",
                             convs = [], rewrs = [], congs = [], filter = NONE,
                             dprocs = [], ac = [(XOR_ASSOC, XOR_COMM)]}

Theorem XOR_ZERO:
  !a. XOR 0 a = a
Proof
  gen_tac >> irule ALL_BIT_EQ
  >> rw_tac bool_ss [XOR_def, XORREL_def, BIT_ZERO]
QED

Theorem XOR_DIV2:
  !a b. XOR (a DIV 2) (b DIV 2) = (XOR a b) DIV 2
Proof
  rpt gen_tac >> irule ALL_BIT_EQ >> rw[XOR_def, BIT_DIV2]
QED

Theorem BIT_2EXP_MINUS1:
  !n m. BIT m (2 ** n - 1) <=> m < n
Proof
  Induct >| [
    Cases >> rw_tac bit_ss [GSYM BIT_DIV2, ZERO_LT_TWOEXP, ZERO_DIV],
    `2 ** SUC n - 1 = SUC (2 * (2 ** n - 1))` by
       rw_tac arith_ss
         [EXP, LEFT_SUB_DISTRIB, SUC_ONE_ADD, GSYM LESS_EQ_ADD_SUB]
    >> Cases >| [
      (* 0 *)
      asm_simp_tac arith_ss
        [GSYM ODD_MOD2_LEM, BIT0_ODD, ODD_DOUBLE],
      (* SUC *)
      rw_tac std_ss
        [EXP, GSYM BIT_DIV2, ADD1, Q.SPEC `2` MULT_COMM, DIV_MULT]
    ]
  ]
QED

Theorem TWO_EXP_MINUS_ONE_DIV2:
  !n. (2 ** SUC n - 1) DIV 2 = 2 ** n - 1
Proof
  gen_tac >> irule ALL_BIT_EQ >> rw[BIT_DIV2, BIT_2EXP_MINUS1]
QED

Theorem XOR_SUC_2EXP:
  !a. ?n. XOR a (SUC a) = 2 ** (SUC n) - 1
Proof
  `!a. ?n. !m. BIT m (XOR a (SUC a)) <=> m < SUC n`
    suffices_by metis_tac [ALL_BIT_EQ, BIT_2EXP_MINUS1] >>
  recInduct DIV2_INDUCTION >> rw[]
  >- (qexists_tac `0` >> rw_tac std_ss [XOR_ZERO, GSYM BIT_2EXP_MINUS1])
  >- (
    Cases_on `ODD a` >| [
      (* a is ODD *)
      qexists_tac `SUC n` >> Cases
      (* 0 *)
      >- rw_tac bit_ss [XOR_def, GSYM ODD_MOD2_LEM, ODD]
      (* SUC *)
      >- (
        `(SUC a) DIV 2 = SUC (a DIV 2)` by (
          pop_assum (mp_tac o REWRITE_RULE [ODD_EXISTS]) >> rw[] >>
          rewrite_tac [DECIDE ``SUC (2 * m) = m * 2 + 1``,
                       EVAL_RULE (Q.SPECL [`2`, `1`] DIV_MULT)] >>
          rewrite_tac [DECIDE ``SUC (m * 2 + 1) = (m + 1) * 2``,
                       EVAL_RULE (Q.SPEC `2` MULT_DIV)] >>
          rw[]
        ) >>
        rw_tac arith_ss [GSYM BIT_DIV2, GSYM XOR_DIV2]
      ),
      (* a is EVEN *)
      qexists_tac `0` >> Cases
      (* 0 *)
      >- (rw[XOR_def, BIT0_ODD, ODD] >> metis_tac[])
      (* SUC *)
      >- (
        pop_assum (mp_tac o REWRITE_RULE [GSYM EVEN_ODD, EVEN_EXISTS]) >>
        rw [GSYM BIT_DIV2, GSYM XOR_DIV2] >>
        rewrite_tac [DECIDE ``SUC (2 * m) = m * 2 + 1``,
                     EVAL_RULE (Q.SPECL [`2`, `1`] DIV_MULT)] >>
        rewrite_tac [DECIDE ``2 * m = m * 2``,
                     EVAL_RULE (Q.SPEC `2` MULT_DIV)] >>
        rw[XOR_def]
      )
    ])
QED

Theorem GCREL_XOR:
  !a b. GCREL a b = (?n. XOR a b = 2 ** n)
Proof
  rewrite_tac [GCREL_def] >> rpt strip_tac
  >> eq_tac >> rw[] >> qexists_tac `n`
  >- (irule ALL_BIT_EQ >> rw[]
      >> Cases_on `n' = n` >> fs[XOR_def])
  >- (pop_assum (fn th =>
       `!m. BIT m (XOR a b) = (m = n)` by rw[BIT_TWO_POW, th])
      >> pop_assum (assume_tac o REWRITE_RULE [XOR_def])
      >> metis_tac[])
QED

(* Rolling binary code *)
val RBC_def = Define`RBC i = XOR i (i DIV 2)`;

Theorem RBC_GCREL:
  !i. GCREL (RBC i) (RBC (SUC i))
Proof
  gen_tac >> simp[GCREL_XOR, RBC_def, XOR_DIV2]
  >> qmatch_abbrev_tac `?n. LHS = 2 ** n`
  >> `LHS = XOR (XOR i (SUC i)) (XOR i (SUC i) DIV 2)`
       by full_simp_tac (std_ss++XOR_ss) [XOR_DIV2]
  >> pop_assum (fn th => rewrite_tac [th])
  >> `?n. XOR i (SUC i) = 2 ** SUC n - 1` by rw[XOR_SUC_2EXP]
  >> qexists_tac `n` >> rw[]
  >> irule ALL_BIT_EQ
  >> rw[TWO_EXP_MINUS_ONE_DIV2, XOR_def, BIT_2EXP_MINUS1]
QED

(* There is probably a better way knowing that for some n
   we have ~BIT n a and if 0 < a, then there is a n such
   that BIT n a; maybe using WHILE? *)
Theorem NLO_EXISTS:
  !a. 0 < a ==> ?n. ~BIT n a /\ (!m. m < n ==> BIT m a)
Proof
  recInduct DIV2_INDUCTION >> rw[]
  >> `(a = 1) \/ 2 <= a` by decide_tac >| [
    (* a = 1 *)
    qexists_tac `1`
    >> rw_tac bit_ss [DECIDE ``m < 1 ==> (m = 0)``],
    (* 2 <= a *)
    fs [DIV_GT0] >> Cases_on `BIT 0 a` >| [
      (* a is odd *)
      qexists_tac `SUC n`
      >> fs [BIT_DIV2] >> rw[]
      >> Cases_on `m` >> rw[],
      (* a is even *)
      qexists_tac `0` >> rw[]
    ]
  ]
QED


(* ------------------- WORK IN PROGRESS

Theorem SUC_BIT:
  !a. ?n. !m.
       if m < n then BIT m a /\ ~BIT m (SUC a)
  else if m = n then ~BIT m a /\ BIT m (SUC a)
  else               BIT m a = ~BIT m (SUC a)
Proof
QED


Theorem XOR_SUC_2EXP:
  !a. ?n. XOR a (SUC a) = 2 ** n - 1
Proof
  gen_tac >> `(a = 0) \/ (0 < a)` by decide_tac
  (* case 0 *) qexists_tac `1` >> full_simp_tac std_ss [XOR_ZERO]
  (* interesting case, use the number of leading ones of a *)
  mp_tac (Q.SPEC `a` NLO_EXISTS) >> rw[]
  >> qexists_tac `n`
  >> irule ALL_BIT_EQ >> rw[XOR_def]

print_match [] ``BIT nn (2 ** xx)`` (* BIT_TWO_POW *)
print_match [] ``0 < xx DIV yy ``

LESS_EQ_EXISTS

*)

(* Experiments:

`(x = f y) ==> x < y`
  STRIP_TAC
  POP_ASSUM (fn th => SIMP_TAC bool_ss [th])

SIMP_CONV arith_ss []
 ``!x a. (x > 3*a) /\ (x < 3*a+2) ==> ?k. (x = 2 * k)``

SIMP_CONV arith_ss []
 ``!x a b. (x > 3*a) /\ (x < 3*a+2) /\ (a = 2*b) ==> (x = b * 6 + 1)``

*)

val _ = export_theory();

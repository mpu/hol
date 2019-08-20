(*experiments with coinductive lists*)
open HolKernel boolLib bossLib arithmeticTheory llistTheory;

val _ = new_theory"coind"

val nat0_def = new_specification
  ("nat0", ["nat0"],
  Q.prove (
    `?nat0. nat0 = 1 ::: LMAP SUC nat0`,
    (* Q.SPEC does not work, understand why *)
    strip_assume_tac (Q.ISPEC `\n. SOME (SUC n, n)` llist_Axiom) \\
    qexists_tac `g 1` \\
    once_rewrite_tac[LLIST_BISIMULATION] \\
    qexists_tac `\a b. ?n. a = g n /\ b = n ::: LMAP SUC (g n)` \\
    rw[] \\
    disj2_tac \\ rw[] \\
    qexists_tac `SUC n` \\ rw[] \\
    `!n. g n = n ::: g (SUC n)` by rw[LHDTL_EQ_SOME] \\
    pop_assum (qspec_then `n` mp_tac) \\ rw[]
  ))

val _ = export_theory()

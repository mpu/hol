open HolKernel boolLib bossLib arithmeticTheory listTheory;

val _ = new_theory "elang"

(* Simple arithmetic expressions language *)
val _ = Datatype`expr = NUM num | BOP (num -> num -> num) expr expr`

(* Evaluation of expresssions *)
val EEVAL_def = Define`
  (EEVAL (NUM n) = n) /\
  (EEVAL (BOP f e1 e2) = f (EEVAL e1) (EEVAL e2))`

(*
  type_of ``BOP $+ (NUM 41) (NUM 1)``
  EVAL ``EEVAL (BOP $+ (NUM 41) (NUM 1))``
*)

(* Instruction of a stack-based language *)
val _ = Datatype`ins = PUSH num | APP (num -> num -> num)`

(* Execute the stack language *)
val SRUN_def = Define`
  (SRUN [] [n] = n) /\
  (SRUN ((PUSH n) :: inss) vals = SRUN inss (n :: vals)) /\
  (SRUN ((APP f) :: inss) (x :: y :: vals) =
     SRUN inss (CONS (f x y) vals))`

(*
  EVAL ``SRUN [PUSH 2; PUSH 40; APP $+] []``
*)

val COMP_def = Define`
  COMP e =
    case e of
      NUM n => [PUSH n]
    | BOP f e1 e2 => COMP e2 ++ COMP e1 ++ [APP f]`

(*
  EVAL `` COMP (BOP $* (NUM 21) (NUM 2)) ``
    [] ⊢ COMP (BOP $* (NUM 21) (NUM 2)) = [PUSH 2; PUSH 21; APP $*]
*)

Theorem COMP_CORRECT:
  !e n k s. (EEVAL e = n) ==> (SRUN (COMP e ++ k) s = SRUN k (n :: s))
Proof
  Induct
  (* Literal *)
  >- (EVAL_TAC >> rw[])
  (* Binary operator *)
  >- (
    rw[Once COMP_def, EEVAL_def]
    >> CONV_TAC (DEPTH_CONV (REWRITE_CONV [GSYM APPEND_ASSOC]))
    >> fs[SRUN_def]
  )
QED

(* ⊢ ∀n e. (EEVAL e = n) ⇒ (SRUN (COMP e) [] = n) *)
val COMP_CORRECT = save_thm("COMP_CORRECT",
  (GEN_ALL
    o REWRITE_RULE [APPEND_NIL, CONJUNCT1 SRUN_def]
    o SPECL [``e: expr``, ``n: num``, ``[]: ins list``, ``[]: num list``]
  ) COMP_CORRECT)

val _ = export_theory()

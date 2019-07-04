open HolKernel boolLib bossLib arithmeticTheory listTheory;

val _ = new_theory "secd"

val trm_def = Datatype
  `trm = VAR num | LAM trm | APP trm trm`

val res_def = Datatype
  `res = CLO (res list) trm`

val dir_def = Datatype
  `dir = TRM trm | APL`

val NAPP = Prim_rec.prove_rec_fn_exists
  (TypeBase.axiom_of ``:trm``)
  ``(NAPP (VAR n) = 0) /\
    (NAPP (LAM t) = 0) /\
    (NAPP (APP t u) = 1 + NAPP t + NAPP u)``

val RUN_def = tDefine"RUN"
  `(RUN f [v] e NIL NIL = v) /\
   (RUN f s e (TRM (VAR v) :: c) d =
     RUN f (EL v e :: s) e c d) /\
   (RUN f s e (TRM (LAM t) :: c) d =
     RUN f (CLO e t :: s) e c d) /\
   (RUN f s e (TRM (APP t u) :: c) d =
     RUN f s e (TRM u :: TRM t :: APL :: c) d) /\
   (RUN (SUC f) (CLO et t :: ru :: s) e (APL :: c) d =
     RUN f [] (ru :: et) [TRM t] ((s, e, c) :: d)) /\
   (RUN f [v] e' NIL ((s, e, c) :: d) =
     RUN f (v :: s) e c d)`
  (strip_assume_tac NAPP >>
   qabbrev_tac `X = \t. case t of APL => 0 | TRM t => NAPP t` >>
   WF_REL_TAC `inv_image ($< LEX $< LEX $< LEX $<) (\(f,s,e,c,d).
                   (f, LENGTH d, (SUM o MAP X) c, LENGTH c))` >>
   rw[Abbr`X`])

val _ = export_theory()

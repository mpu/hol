open HolKernel boolLib bossLib arithmeticTheory listTheory optionTheory;

val _ = new_theory "secd"

val trm_def = Datatype
  `trm = VAR num | LAM trm | APP trm trm`

val SUBST_def = Define
  `(SUBST n (VAR m) t =
     if m < n then VAR m else
       case m of 0 => t | SUC m' => VAR m') /\
   (SUBST n (LAM u) t = LAM (SUBST (SUC n) u t)) /\
   (SUBST n (APP u v) t = APP (SUBST n u t) (SUBST n v t))`

(* Define is pretty smart and can figure out the termination
   of this call-by-value evaluation function. *)
val CBV_def = Define
  `(CBV 0 t = NONE) /\
   (CBV (SUC f) (VAR n) = SOME (VAR n)) /\ (* or NONE? *)
   (CBV (SUC f) (LAM t) = SOME (LAM t)) /\
   (CBV (SUC f) (APP t u) =
     case CBV (SUC f) u of
       SOME vu =>
         (case CBV (SUC f) t of
         | SOME (LAM lt) =>
             CBV f (SUBST 0 vu lt)
         | _ => NONE)
     | _ => NONE)`

val res_def = Datatype
  `res = CLO (res list) trm`

val dir_def = Datatype
  `dir = TRM trm | APL`

(* Helper function for the termination proof of SECD *)
val NAPP_LEM = Prim_rec.prove_rec_fn_exists
  (TypeBase.axiom_of ``:trm``)
  ``(NAPP (VAR n) = 0) /\
    (NAPP (LAM t) = 0) /\
    (NAPP (APP t u) = 1 + NAPP t + NAPP u)``

(* The SECD machine, with a fuel argument (the first) to
   ensure termination. *)
val SECD_def = tDefine"SECD"
  `(SECD f [r] e [] [] = r) /\
   (SECD f s e (TRM (VAR v) :: c) d =
     SECD f (EL v e :: s) e c d) /\
   (SECD f s e (TRM (LAM t) :: c) d =
     SECD f (CLO e t :: s) e c d) /\
   (SECD f s e (TRM (APP t u) :: c) d =
     SECD f s e (TRM u :: TRM t :: APL :: c) d) /\
   (SECD (SUC f) (CLO et t :: ru :: s) e (APL :: c) d =
     SECD f [] (ru :: et) [TRM t] ((s, e, c) :: d)) /\
   (SECD f [v] e' NIL ((s, e, c) :: d) =
     SECD f (v :: s) e c d)`
  (strip_assume_tac NAPP_LEM >>
   qabbrev_tac `X = \t. case t of APL => 0 | TRM t => NAPP t` >>
   WF_REL_TAC `inv_image ($< LEX $< LEX $< LEX $<) (\(f,s,e,c,d).
                   (f, LENGTH d, (SUM o MAP X) c, LENGTH c))` >>
   rw[Abbr`X`])

val RSEM_def = tDefine"RSEM"
  `(RSEM (CLO e t) = FOLDL (SUBST 0) t (MAP RSEM e))`
  (WF_REL_TAC `measure res_size` >>
   Induct_on `e` >> rw[MEM, definition "res_size_def"]
   >- rw_tac arith_ss []
   >- (first_x_assum (qspecl_then [`t`, `a`] mp_tac) >> rw[]))

(* Decompile and SECD state *)
val DEC = Define
  `(DEC (r :: s) e c d =
     DEC s e (TRM (RSEM r) :: c) d) /\
   (DEC [] e (TRM tu :: TRM tt :: APL :: c) d =
     DEC [] e (TRM (APP tt tu) :: c) d) /\
   (DEC [] e' [TRM t] ((s, e, c) :: d) =
     DEC (CLO e' t :: s) e c d) /\
   (DEC [] e [TRM t] [] = SOME t) /\
   (DEC [] e _ _ = NONE)`

(* Would like to show,
   if CBV f t = SOME t' then RUN f [] [] [TRM t] [] = v

   Plan: define a decompilation function that creates a lambda
   term from an secd state; then by induction on the relation
   used to prove that SECD terminates, show that:

     (DECOMP s e c d = SOME t) /\ (CBV f t = SOME t') ==>
       (RUN f s e c d = t')

   And Profit!
*)

(*
  REWRITE_RULE [REWRITE_RULE [relationTheory.WF_EQ_WFP] prim_recTheory.WF_LESS]
  (Q.ISPEC `$<` relationTheory.WFP_INDUCT)
*)

val _ = export_theory()

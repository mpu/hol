open HolKernel Parse arithmeticTheory;

(* val _ = new_theory "test"; *)

(* Questions:
  - difference between single and double quotations
  - difference between = and <=>
*)

val div_def = Define `divides a b = ?x. b = a * x`;
set_fixity "divides" (Infix(NONASSOC, 450));

val prime_def = Define `prime p = p <> 1 /\ !x. x divides p ==> (x=1) \/ (x=p)`;

(* the rewriter *)
rw;

(* Starts a goal stack *)
g `!x. x divides 0`;
e (rw[div_def]);
e (qexists_tac `0`);
e (rw[]);

restart();
e (rw[div_def] >> qexists_tac `0` >> rw[]);

restart();
e (metis_tac [div_def, MULT_CLAUSES]);

val DIVIDES_0 = top_thm();

drop(); (* drops the goal stack *)

g `!m n. m divides n ==> m <= n \/ (n = 0)`;
e (rw[div_def]);
  DB.match ["arithmetic"] ``m <= m * x``;
  DB.match ["arithmetic"] ``m * x = 0``;
e (rw[LE_MULT_CANCEL_LBARE]);

val DIVIDES_LE = top_thm();
drop();

val DIVIDES_LE = store_thm(
  "DIVIDES_LE",
  ``!m n. m divides n ==> m <= n \/ (n = 0)``,
  rw[div_def] >> rw[]
);

val DIV_RMULT =  store_thm(
  "DIV_RMULT",
  ``!a b c. a divides b ==> a divides (b*c)``,
  metis_tac[div_def, MULT_ASSOC]
);

g`!m n. 0 < m /\ m <= n ==> m divides (FACT n)`;

e (`!m p. 0 < m ==> m divides FACT(m + p)`
   suffices_by metis_tac[LESS_EQ_EXISTS]);
e (Induct_on `p`);
e (rw[div_def]);
e (Cases_on `m`);
(**) e (fs[]);
(**) e (rw[FACT]);

e (rw[ADD_CLAUSES, FACT]);

e (rw[DIV_RMULT]);


(* Rework the proof *)
e(
  `!m p. 0 < m ==> m divides FACT(m + p)`
     suffices_by metis_tac[LESS_EQ_EXISTS] >>
  Induct_on `p` >| [
    Cases_on `m` >> rw[div_def, FACT],
    rw[ADD_CLAUSES, FACT, DIV_RMULT]
  ]
);



g `!x. (x = T) \/ (x = F)`;
e (Cases_on `x`);
e (rewrite_tac [OR_INTRO_THM1]);
e (rewrite_tac [OR_INTRO_THM2]);
val BOOL_CASES = top_thm();

val ARB_BOOL = save_thm("ARB_BOOL", SPEC ``ARB: bool`` BOOL_CASES);

(* b(); backs up; or [b in vim *)



(* An elementary substitution *)
let val t = ``f: ('a -> bool) -> bool`` in
  SUBST [{redex = t, residue = FORALL_DEF}] ``^t = $!``
    (REFL ``$!``)
end;



(* val _ = export_theory (); *)

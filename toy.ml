(* Modular range *)
let MODRNG = new_definition
  `MODRNG0 m a b =
     {x | ?d. x = (a + d) MOD m /\
          !e. e < d ==> ~(b == a + e) (mod m)}`;;

let MODRNG_ZERO = prove
  (`!a b. MODRNG0 0 a b = if a <= b then a..b else {x | a <= x}`,
   REWRITE_TAC[MODRNG; CONG; MOD_ZERO] THEN REPEAT GEN_TAC THEN
   ASM_CASES_TAC `a <= b` THEN
   ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THENL
   [GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
    [FIRST_X_ASSUM (MP_TAC o SPEC `b - a`);
     EXISTS_TAC `x - a`] THEN ASM_ARITH_TAC;
    GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
    [ALL_TAC; EXISTS_TAC `x - a`] THEN
    ASM_ARITH_TAC]);;

let MODRNG_SUBSET_NUMSEG = prove
  (`!m a b. ~(m = 0) ==> MODRNG0 m a b SUBSET 0..m - 1`,
   REWRITE_TAC[SUBSET; IN_NUMSEG_0; MODRNG; IN_ELIM_THM] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
   DISCH_THEN (CHOOSE_THEN (SUBST1_TAC o CONJUNCT1)) THEN
   MP_TAC (SPECL[`a + d`;`m:num`] MOD_LT_EQ) THEN
   ASM_ARITH_TAC);;

let FINITE_MODRNG = prove
  (`!m a b. FINITE (MODRNG0 m a b) <=> (m = 0 /\ a <= b) \/ ~(m = 0)`,
   REPEAT GEN_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [POP_ASSUM (fun th -> REWRITE_TAC[th; MODRNG_ZERO; LT]) THEN
    BOOL_CASES_TAC `a <= b` THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    REWRITE_TAC[GSYM INFINITE; INFINITE_ENUMERATE_SUBSET] THEN
    EXISTS_TAC `\n. n + a` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `0..m - 1` THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; MODRNG_SUBSET_NUMSEG]]);;

let MODRNG_CONG = prove
  (`!m a b. (a == b) (mod m) ==> MODRNG0 m a b = {a MOD m}`,
   REWRITE_TAC[MODRNG; EXTENSION; IN_ELIM_THM; CONG] THEN
   REPEAT STRIP_TAC THEN EQ_TAC THENL
   (* ==> *)
   [DISCH_THEN (CHOOSE_THEN MP_TAC) THEN
    DISJ_CASES_TAC (SPEC `d:num` num_CASES) THENL
    [ASM_REWRITE_TAC[ADD_CLAUSES; LT] THEN
     DISCH_THEN SUBST1_TAC THEN SET_TAC[];
     POP_ASSUM (CHOOSE_THEN SUBST1_TAC) THEN
     DISCH_THEN (MP_TAC o GSYM o SPEC `0` o CONJUNCT2) THEN
     ASM_REWRITE_TAC[LT_0; ADD_CLAUSES; CONG]];
   (* <== *)
    REWRITE_TAC[IN_SING] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; LT]]);;

let MODRNG_REFL = prove
  (`!m a. MODRNG0 m a a = {a MOD m}`,
   REPEAT GEN_TAC THEN MATCH_MP_TAC MODRNG_CONG THEN
   REWRITE_TAC[CONG]);;

let MODRNG_CONGL = prove
  (`!m a b c. (a == b) (mod m) ==> MODRNG0 m a c = MODRNG0 m b c`,
   REWRITE_TAC[CONG] THEN REPEAT GEN_TAC THEN
   SUBGOAL_THEN `!a b. a MOD m = b MOD m ==>
     (!x. MODRNG0 m a c x ==> MODRNG0 m b c x)` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[EXTENSION; IN] THEN MESON_TAC[]] THEN
   REWRITE_TAC[MODRNG; IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THEN EXISTS_TAC `d:num` THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ASM_REWRITE_TAC[];
    GEN_TAC THEN DISCH_THEN (fun th ->
      POP_ASSUM (MP_TAC o C MATCH_MP th)) THEN
    POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [CONTRAPOS_THM; CONG] THEN
    DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    ASM_REWRITE_TAC[]]);;

let MODRNG_MODL = prove
  (`!m a b. MODRNG0 m (a MOD m) b = MODRNG0 m a b`,
   MESON_TAC[MODRNG_CONGL; CONG; MOD_MOD_REFL]);;

let MODRNG_CONGR = prove
  (`!m a b c. (b == c) (mod m) ==> MODRNG0 m a b = MODRNG0 m a c`,
   REWRITE_TAC[CONG] THEN REPEAT GEN_TAC THEN
   SUBGOAL_THEN `!b c. b MOD m = c MOD m ==>
     (!x. MODRNG0 m a b x ==> MODRNG0 m a c x)` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[EXTENSION; IN] THEN MESON_TAC[]] THEN
   REWRITE_TAC[MODRNG; IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THEN EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN DISCH_THEN (fun th ->
     POP_ASSUM (MP_TAC o C MATCH_MP th)) THEN
   ASM_REWRITE_TAC [CONTRAPOS_THM; CONG]);;

let MODRNG_MODR = prove
  (`!m a b. MODRNG0 m a (b MOD m) = MODRNG0 m a b`,
   MESON_TAC[MODRNG_CONGR; CONG; MOD_MOD_REFL]);;

let MODRNG_THM = prove
  (`!m a b. MODRNG0 m a b =
      if (a == b) (mod m)
      then {a MOD m}
      else (a MOD m) INSERT MODRNG0 m (SUC a) b`,
   REPEAT GEN_TAC THEN ASM_CASES_TAC `(a == b) (mod m)` THEN
   ASM_SIMP_TAC[MODRNG_CONG] THEN
   REWRITE_TAC[MODRNG; EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
   GEN_TAC THEN EQ_TAC THENL
   (* ==> *)
   [DISCH_THEN (CHOOSE_THEN MP_TAC) THEN
    DISJ_CASES_TAC (SPEC `d:num` num_CASES) THENL
    [ASM_SIMP_TAC[ADD_CLAUSES]; ALL_TAC] THEN
    POP_ASSUM (X_CHOOSE_THEN `f:num` SUBST1_TAC) THEN
    STRIP_TAC THEN DISJ2_TAC THEN EXISTS_TAC `f:num` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
    GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `SUC e`) THEN
    ASM_REWRITE_TAC[LT_SUC; ADD_CLAUSES];
   (* <== *)
    DISCH_THEN DISJ_CASES_TAC THENL
    [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ADD_CLAUSES; LT];
     POP_ASSUM (CHOOSE_THEN STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `SUC d` THEN
     CONJ_TAC THENL [ASM_REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
     GEN_TAC THEN DISJ_CASES_TAC (SPEC `e:num` num_CASES) THENL
     [ASM_REWRITE_TAC [ADD_CLAUSES;
        MESON[CONG] `(b == a) (mod m) <=> (a == b) (mod m)`];
      POP_ASSUM (X_CHOOSE_THEN `f:num` ASSUME_TAC) THEN
      ASM_REWRITE_TAC[LT_SUC] THEN
      DISCH_THEN (fun th -> FIRST_X_ASSUM (MP_TAC o C MATCH_MP th)) THEN
      REWRITE_TAC[ADD_CLAUSES]]]]);;

let rec NUM_MODRNG_CONV term =
  (REWR_CONV MODRNG_THM THENC
   DEPTH_CONV (REWR_CONV CONG) THENC
   DEPTH_CONV NUM_RED_CONV THENC
   TRY_CONV (RAND_CONV NUM_MODRNG_CONV)) term;;

(* Some examples to try out:

   NUM_MODRNG_CONV `MODRNG0 5 4 2`;;
   NUM_MODRNG_CONV `MODRNG0 5 1 3`;;
*)

(* ------------------------------------------------------------------------- *)
(* Linear probing hash tables.                                               *)
(* ------------------------------------------------------------------------- *)

(*
   A hash table has three components:
   - a hash function from the key space K to num
   - a table represented as a function from num to
     entries; NONE is used to represent free entries
     while SOME (k,v) represents a binding that maps
     the key k to the value v
   - a modulus; it is the max number of bindings in
     the table
*)

new_type_abbrev("hash",`:(K->num)#(num->(K#V)option)#num`);;

let hmod = new_definition `hmod (h:hash) = SND (SND h)`;;
let htbl = new_definition `htbl (h:hash) = FST (SND h)`;;
let hfun = new_definition `hfun (h:hash) = (\x. FST h x MOD hmod h)`;;

let HGET = prove
  (`hfun (f,t,m) = (\x. f x MOD m) /\
    htbl (f,t,m) = t /\
    hmod (f,t,m) = m`,
   SIMP_TAC[hfun; htbl; hmod]);;

let HFUN_LT_EQ = prove
  (`!h k. hfun h k < hmod h <=> ~(hmod h = 0)`,
   SIMP_TAC[FORALL_PAIR_THM; HGET; MOD_LT_EQ]);;

let hnext = new_definition `hnext (h:hash) p = SUC p MOD hmod h`;;

let FINDLOOP = define
  `FINDLOOP h k p =
     if htbl h p = NONE \/ (?v. htbl h p = SOME (k,v))
     then p
     else FINDLOOP h k (hnext h p)`;;

let FIND = new_definition
  `FIND h k = htbl h (FINDLOOP h k (hfun h k))`;;

let NOTFULL = new_definition
  `NOTFULL h = ?p. p < hmod h /\ htbl h p = NONE`;;

(* A potiential healthiness invariant *)
let INV0 = define
  `INV0 h =
    !p k v. p < hmod h /\ htbl h p = SOME (k,v) ==>
    !q. q IN MODRNG0 (hmod h) (hfun h k) p /\ ~(q = p) ==>
    ?kq vq. htbl h q = SOME (kq,vq) /\ ~(kq = k)`;;

let INV0_FIND = prove
  (`!(h:hash) k v p.
      INV0 h /\ p < hmod h /\ htbl h p = SOME (k,v) ==>
      FIND h k = SOME (k,v)`,
   REPEAT GEN_TAC THEN DISCH_THEN ASSUME_TAC THEN
   REWRITE_TAC[FIND] THEN
   SUBGOAL_THEN `FINDLOOP (h:hash) k (hfun h k) = p`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
   (* to prove that we need to perform an induction
      on the segment ploop -- p *)
   CHEAT_TAC);;

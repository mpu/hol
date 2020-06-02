(*****************************************************************************)
(* Modular segment                                                           *)
(*****************************************************************************)

let MODSEG_rules, MODSEG_induct, MODSEG_cases = new_inductive_definition
  `(!m a b. MODSEG m a b (a MOD m)) /\
   (!m a b x. ~(a MOD m = b MOD m) /\ MODSEG m (SUC a) b x ==>
              MODSEG m a b x)`;;

let MODSEG_REC = prove
  (`!m a b. MODSEG m a b =
      if a MOD m = b MOD m
      then {a MOD m}
      else (a MOD m) INSERT MODSEG m (SUC a) b`,
   REWRITE_TAC[EXTENSION] THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [IN] THEN
   ONCE_REWRITE_TAC[MODSEG_cases] THEN
   COND_CASES_TAC THEN REWRITE_TAC[IN_SING; IN_INSERT] THEN
   REWRITE_TAC[IN]);;

let LB_IN_MODSEG = prove
  (`!m a b. a MOD m IN MODSEG m a b`,
   REWRITE_TAC[IN; MODSEG_rules]);;

let CONG_SUC = prove
  (`!m a b. a MOD m = b MOD m ==> SUC a MOD m = SUC b MOD m`,
   GEN_TAC THEN
   ASM_CASES_TAC `m = 0` THENL
     [ASM_REWRITE_TAC[MOD_ZERO] THEN ARITH_TAC;
      ALL_TAC] THEN
   ASM_CASES_TAC `m = 1` THENL
     [ASM_REWRITE_TAC[MOD_1] THEN ARITH_TAC;
      ALL_TAC] THEN
   REPEAT GEN_TAC THEN REWRITE_TAC[ADD1] THEN
   ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
   IMP_REWRITE_TAC[MOD_ADD_CASES] THEN
   ASM_ARITH_TAC);;

let MODSEG_CONG_lemma = prove
  (`!m a1 b1 x. MODSEG m a1 b1 x ==>
      !a2 b2. a2 MOD m = a1 MOD m /\ b2 MOD m = b1 MOD m ==>
        MODSEG m a2 b2 x`,
   MATCH_MP_TAC MODSEG_induct THEN
   CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_THEN (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[MODSEG_rules];
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[MODSEG_cases] THEN
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    IMP_REWRITE_TAC[CONG_SUC]]);;

let MODSEG_CONG = prove
  (`!m a1 b1 a2 b2. a1 MOD m = a2 MOD m /\ b1 MOD m = b2 MOD m ==>
      MODSEG m a1 b1 = MODSEG m a2 b2`,
   REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[MODSEG_CONG_lemma]);;

let MODSEG_MODR = prove
  (`!m a b. MODSEG m a (b MOD m) = MODSEG m a b`,
   MESON_TAC[MODSEG_CONG; MOD_MOD_REFL]);;

let MODSEG_MODL = prove
  (`!m a b. MODSEG m (a MOD m) b = MODSEG m a b`,
   MESON_TAC[MODSEG_CONG; MOD_MOD_REFL]);;

(*****************************************************************************)
(* Modular distance and induction principle for loops in modular arithmetic  *)
(*****************************************************************************)

prioritize_int();;

let INT_SUB_1_REM = prove
  (`!m x. (x - &1) rem m = if x rem m = &0 then abs m - &1 else x rem m - &1`,
   REPEAT GEN_TAC THEN ASM_CASES_TAC `m = &0` THENL
     [ASM_REWRITE_TAC[INT_REM_0] THEN INT_ARITH_TAC; ALL_TAC] THEN
   COND_CASES_TAC THEN MATCH_MP_TAC INT_REM_UNIQ THENL
   [ EXISTS_TAC `x div m - int_sgn m` THEN
     POP_ASSUM MP_TAC THEN REWRITE_TAC[INT_REM_DIV] THEN
     STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ REWRITE_TAC[INT_SUB_RDISTRIB; INT_SGN_ABS_ALT] THEN ASM_INT_ARITH_TAC;
       ASM_INT_ARITH_TAC;
       INT_ARITH_TAC ];
     EXISTS_TAC `x div m` THEN
     STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ REWRITE_TAC[INT_REM_DIV] THEN INT_ARITH_TAC;
       POP_ASSUM MP_TAC THEN
       POP_ASSUM (MP_TAC o SPEC `x:int` o MATCH_MP INT_REM_POS) THEN
       INT_ARITH_TAC;
       POP_ASSUM (K ALL_TAC) THEN
       POP_ASSUM (MP_TAC o MATCH_MP INT_DIVISION) THEN
       DISCH_THEN (MP_TAC o CONJUNCT2 o CONJUNCT2 o SPEC `x:int`) THEN
       INT_ARITH_TAC ] ]);;

let MODSUB_ADD_1 = prove
  (`!m x y. ~(x == y) (mod m) ==> (x - (y + &1)) rem m = (x - y) rem m - &1`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC[INT_ARITH `x - (y + &1) = x - y - &1`; INT_SUB_1_REM] THEN
   SUBGOAL_THEN `~((x - y) rem m = &0)` (fun th -> REWRITE_TAC[th]) THEN
   POP_ASSUM MP_TAC THEN REWRITE_TAC[CONTRAPOS_THM] THEN
   REWRITE_TAC[INT_REM_EQ_0; int_divides; int_congruent]);;

prioritize_num();;

let MODLOOP_IND = prove
  (`!m y P.
      ~(m = 0) /\
      (!x. (x == y) (mod m) ==> P x) /\
      (!x. (~(x == y) (mod m) /\ P (SUC x)) ==> P x) ==>
      !x. P x`,
   REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
   SUBGOAL_THEN `WF (MEASURE (\x. num_of_int((&y - &x) rem &m)))` MP_TAC THENL
     [REWRITE_TAC[WF_MEASURE]; REWRITE_TAC[WF_IND]] THEN
   DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[MEASURE] THEN
   GEN_TAC THEN POP_ASSUM (CONJUNCTS_THEN (MP_TAC o SPEC `x:num`)) THEN
   ASM_CASES_TAC `(x == y) (mod m)` THEN ASM_SIMP_TAC[] THEN
   REWRITE_TAC[IMP_IMP] THEN DISCH_THEN (CONJUNCTS_THEN MATCH_MP_TAC) THEN
   ONCE_REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN
   ASM_SIMP_TAC[INT_REM_POS; INT_OF_NUM_OF_INT; INT_OF_NUM_EQ] THEN
   REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN IMP_REWRITE_TAC[MODSUB_ADD_1] THEN
   CONJ_TAC THENL [INT_ARITH_TAC; ASM_MESON_TAC[num_congruent; CONG]]);;

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

let CHAIN = define
  `CHAIN h k a b =
    !p. q IN MODSEG (hmod h) a b /\ ~(p = b) ==>
    ?kp vp. htbl h p = SOME (kp,vp) /\ ~(kp = k)`;;

(* Describes the guts of a healthy hash table; we require
   that for any key k, value v, position p, if the table
   has the (k,v) binding at position p, then all entries
   from from `hfun h k` to `p - 1` are non-empty and do
   not bind the key `k` *)
let INV = define
  `INV1 h = !p k v.
    p < hmod h /\ htbl h p = SOME (k,v) ==>
    CHAIN h k (hfun h k) p`;;

let hempty = define `hempty f m = (f,(\x. NONE),m)`;;

let FINDLOOP_SPEC = prove
  (`!(h:hash) k a.
      let b = FINDLOOP h k a in
      (htbl h b = NONE \/ ?v. htbl h b = SOME (k,v)) /\
      CHAIN h k a b`

let INV_HEMPTY = prove
  (`!f m. INV1 (hempty f m:hash)`,
   REWRITE_TAC[INV; hempty; HGET; distinctness "option"]);;

(* If the invariant INV holds, then any binding (k,v) in the
   hash table can be fetched using HFIND h k *)
let INV_FIND = prove
  (`!(h:hash) k v p.
      INV1 h /\ p < hmod h /\ htbl h p = SOME (k,v) ==>
      FIND h k = SOME (k,v)`,
   REPEAT GEN_TAC THEN DISCH_THEN ASSUME_TAC THEN
   REWRITE_TAC[FIND] THEN
   SUBGOAL_THEN `FINDLOOP (h:hash) k (hfun h k) = p`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
   (* from then on to the case analysis below we build an
      inductive invariant to put in front of FINDLOOP h k c = p *)
   POP_ASSUM (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
   REWRITE_TAC[INV] THEN
   DISCH_THEN (fun th -> FIRST_ASSUM (MP_TAC o MATCH_MP th)) THEN
   (* add the MOD in the findloop argument *)
   SUBGOAL_THEN `hfun (h:hash) k = hfun h k MOD hmod h` MP_TAC THENL
     [IMP_REWRITE_TAC[MOD_LT; HFUN_LT_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   DISCH_THEN (fun th -> GEN_REWRITE_TAC (RAND_CONV o DEPTH_CONV) [th]) THEN
   (* we are done crafting the invariant; we now turn to the induction *)
   SPEC_TAC (`hfun (h:hash) k`,`c:num`) THEN
   MATCH_MP_TAC (SPECL[`hmod (h:hash)`;`p:num`] MODLOOP_IND) THEN
   CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[CONG] THEN CONJ_TAC THENL
   (* base case *)
   [ ASM_MESON_TAC[FINDLOOP; injectivity "option"; MOD_LT];
   (* recursive case *)
     GEN_TAC THEN STRIP_TAC THEN
     STRIP_TAC THEN ONCE_REWRITE_TAC[FINDLOOP] THEN
     COND_CASES_TAC THENL
     (* we cannot get in the first branch at this point because
        so we derive a contradiction *)
     [ POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
       STRIP_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `c MOD hmod (h:hash)`) THEN
       ASM_REWRITE_TAC[LB_IN_MODSEG] THEN
       ASM_MESON_TAC[injectivity "option"; distinctness "option"; PAIR_EQ];
     (* in the recursive call use the induction hypothesis *)
       POP_ASSUM (K ALL_TAC) THEN
       REWRITE_TAC[hnext] THEN CONV_TAC MOD_DOWN_CONV THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       ASM_REWRITE_TAC[] THEN
       ONCE_REWRITE_TAC[MODSEG_REC] THEN
       SUBGOAL_THEN `~(c MOD hmod (h:hash) = p MOD hmod h)`
         ASSUME_TAC THEN ASM_REWRITE_TAC[IN_INSERT]
     ]
   ]);;

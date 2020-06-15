(*****************************************************************************)
(* An induction principle for loops in modular arithmetic.                   *)
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

(*****************************************************************************)
(* Modular segments.                                                         *)
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

let MODSEG_REFL = prove
  (`!m a b. a MOD m = b MOD m ==> MODSEG m a b = {a MOD m}`,
    ONCE_REWRITE_TAC[MODSEG_REC] THEN SIMP_TAC[]);;

let LB_IN_MODSEG = prove
  (`!m a b. a MOD m IN MODSEG m a b`,
   REWRITE_TAC[IN; MODSEG_rules]);;

let CONG_SUC = prove
  (`!m a b. SUC a MOD m = SUC b MOD m <=> a MOD m = b MOD m`,
   GEN_TAC THEN
   ASM_CASES_TAC `m = 0` THENL
     [ASM_REWRITE_TAC[MOD_ZERO] THEN ARITH_TAC; ALL_TAC] THEN
   ASM_CASES_TAC `m = 1` THENL
     [ASM_REWRITE_TAC[MOD_1] THEN ARITH_TAC; ALL_TAC] THEN
   REPEAT GEN_TAC THEN REWRITE_TAC[ADD1] THEN
   ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
   IMP_REWRITE_TAC[MOD_ADD_CASES] THEN
   SUBGOAL_THEN `a MOD m < m /\ b MOD m < m` MP_TAC THENL
     [ASM_REWRITE_TAC[MOD_LT_EQ]; ALL_TAC] THEN
   SUBGOAL_THEN `1 MOD m = 1` SUBST1_TAC THENL
     [REWRITE_TAC[MOD_EQ_SELF] THEN ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `1 < m` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   MAP_EVERY SPEC_TAC [(`a MOD m`,`A:num`);(`b MOD m`,`B:num`)] THEN
   SIMP_TAC[] THEN ARITH_TAC);;

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

(* valid, but let's see if we need it

let MODSEG_SUCR = prove
  (`!m a b. ~(m = 0) /\ ~(a MOD m = SUC b MOD m) ==>
      MODSEG m a (SUC b) = SUC b MOD m INSERT MODSEG m a b`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   SPEC_TAC (`a:num`,`a:num`) THEN
   MP_TAC (SPECL[`m:num`;`SUC b`] MODLOOP_IND) THEN
   FIRST_ASSUM (fun th -> REWRITE_TAC[th; CONG]) THEN
   DISCH_THEN MATCH_MP_TAC THEN 
   CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
   GEN_REWRITE_TAC LAND_CONV [MODSEG_REC] THEN
   ASM_SIMP_TAC[] THEN
   ASM_CASES_TAC `a MOD m = b MOD m` THENL
   [FIRST_X_ASSUM (K ALL_TAC o check (is_imp o concl)) THEN
    IMP_REWRITE_TAC[MODSEG_REFL] THEN
    FIRST_ASSUM (MP_TAC o ONCE_REWRITE_RULE[GSYM CONG_SUC]) THEN
    SET_TAC[];
    FIRST_ASSUM (MP_TAC o ONCE_REWRITE_RULE[GSYM CONG_SUC]) THEN
    DISCH_THEN (fun th -> FIRST_X_ASSUM (SUBST1_TAC o C MATCH_MP th)) THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [MODSEG_REC] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

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

let hset = new_definition
  `hset (h:hash) p bnd = 
    (FST h,(\q. if q = p then bnd else htbl h q),hmod h)`;;

let FINDLOOP = define
  `FINDLOOP h k p =
     if htbl h p = NONE \/ (?v. htbl h p = SOME (k,v))
     then p
     else FINDLOOP h k (SUC p MOD (hmod h))`;;

let FIND = new_definition
  `FIND h k = htbl h (FINDLOOP h k (hfun h k))`;;

let ADD = new_definition
  `ADD h k v =
    let p = FINDLOOP h k (hfun h k) in
    hset h p (SOME (k,v))`;;

let NOTFULL = new_definition
  `NOTFULL h = ?e. e < hmod h /\ htbl h e = NONE`;;

let CHAIN = define
  `CHAIN h k a b =
    !p. p IN MODSEG (hmod h) a b /\ ~(p = b) ==>
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

let NOTFULL_HFUN_LT = prove
  (`!h k. NOTFULL h ==> hfun h k < hmod h`,
   SIMP_TAC[FORALL_PAIR_THM; NOTFULL; hfun; hmod; MOD_LT_EQ] THEN
   ARITH_TAC);;

let HSET = prove
  (`(hfun (hset (h:hash) p bnd) = hfun h) /\
    (htbl (hset (h:hash) p bnd) =
      \q. if q = p then bnd else htbl h q) /\
    (hmod (hset (h:hash) p bnd) = hmod h)`,
   SPEC_TAC (`h:hash`,`h:hash`) THEN
   REWRITE_TAC[FORALL_PAIR_THM; hfun; htbl; hmod; hset]);;

let CHAIN_REFL = prove
  (`!h k a. a < hmod h ==> CHAIN h k a a`,
   REWRITE_TAC[CHAIN] THEN REPEAT GEN_TAC THEN
   DISCH_THEN (MP_TAC o MATCH_MP
     (MESON[MOD_EQ_SELF]`m < n ==> m MOD n = m`)) THEN
   IMP_REWRITE_TAC[MODSEG_REFL; IN_SING]);;

let CHAIN_REC = prove
  (`!(h:hash) k a b ka va.
      ~(a MOD hmod h = b MOD hmod h) /\
      CHAIN h k (SUC a MOD hmod h) b /\
      htbl h (a MOD hmod h) = SOME (ka,va) /\ ~(ka = k) ==>
      CHAIN h k (a MOD hmod h) b`,
   REWRITE_TAC[CHAIN; RIGHT_IMP_FORALL_THM] THEN
   REPEAT GEN_TAC THEN ASM_CASES_TAC `p = a MOD hmod (h:hash)` THENL
   [POP_ASSUM SUBST1_TAC THEN
    INTRO_TAC "_ _ a b; _" THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    REWRITE_TAC[injectivity"option"; PAIR_EQ] THEN
    ASM_MESON_TAC[];
    STRIP_TAC THEN
    ONCE_REWRITE_TAC[MODSEG_REC] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN
    ONCE_REWRITE_TAC[GSYM MODSEG_MODL] THEN
    CONV_TAC MOD_DOWN_CONV THEN
    DISCH_THEN (fun th ->
      FIRST_X_ASSUM (ACCEPT_TAC o C MATCH_MP th))]);;

let FINDLOOP_SPEC = prove
  (`!(h:hash) k a. NOTFULL h /\ a < hmod h ==>
      let b = FINDLOOP h k a in
      b < hmod h /\
      (htbl h b = NONE \/ ?v. htbl h b = SOME (k,v)) /\
      CHAIN h k a b`,
   REPEAT GEN_TAC THEN
   let mod_lemma = MESON[MOD_EQ_SELF] `m < n ==> m MOD n = m`
   in
   DISCH_THEN (CONJUNCTS_THEN2
     (STRIP_ASSUME_TAC o REWRITE_RULE[NOTFULL])
     (SUBST1_TAC o GSYM o MATCH_MP mod_lemma)) THEN
   FIRST_ASSUM (ASSUME_TAC o MATCH_MP (ARITH_RULE`a < b ==> ~(b = 0)`)) THEN
   REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
   MAP_EVERY (fun t -> SPEC_TAC (t,t)) [`b:num`;`a:num`] THEN
   MATCH_MP_TAC (SPECL[`hmod (h:hash)`;`e:num`] MODLOOP_IND) THEN
   ASM_REWRITE_TAC[CONG] THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   (* base case of the modular induction; we are
      on the empty cell given by NOTFULL *)
   [DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP mod_lemma) THEN
    ONCE_REWRITE_TAC[FINDLOOP] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CHAIN_REFL THEN FIRST_ASSUM ACCEPT_TAC;
   (* harder cases, we simply know that we are not on the
      empty cell given by NOTFULL *)
    DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
    REPEAT CONJ_TAC THENL
    (* b < hmod h *)
    [ONCE_REWRITE_TAC[FINDLOOP] THEN
     COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[MOD_LT_EQ];
      CONV_TAC MOD_DOWN_CONV THEN
      FIRST_ASSUM MATCH_ACCEPT_TAC];
    (* htbl h b *)
     ONCE_REWRITE_TAC[FINDLOOP] THEN
     COND_CASES_TAC THEN
     CONV_TAC MOD_DOWN_CONV THEN
     FIRST_ASSUM MATCH_ACCEPT_TAC;
    (* CHAIN *)
     ONCE_REWRITE_TAC[FINDLOOP] THEN
     COND_CASES_TAC THENL
       [IMP_REWRITE_TAC[CHAIN_REFL; MOD_LT_EQ]; ALL_TAC] THEN
     (* recursive call, assemble the two pieces
        of the chain *)
     (* turn the negated condition into something more
        usable *)
     SUBGOAL_THEN
       `!X. ~(X = NONE \/ ?(v:V). X = SOME ((k:K),v)) ==>
            (?ka va. X = SOME (ka,va) /\ ~(ka = k))`
       (fun th -> FIRST_ASSUM (CHOOSE_THEN (CHOOSE_THEN ASSUME_TAC) o
                  MATCH_MP th)) THENL
     [ POP_ASSUM_LIST (K ALL_TAC) THEN
       GEN_TAC THEN
       REWRITE_TAC[DE_MORGAN_THM] THEN
       DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
       POP_ASSUM (
        CHOOSE_THEN (CHOOSE_THEN SUBST1_TAC) o
        MATCH_MP (MESON[cases"option"; PAIR]
          `~(X = NONE) ==> ?kx vx. X = SOME (kx, vx)`)) THEN
       REWRITE_TAC[injectivity"option"; PAIR_EQ] THEN
       MESON_TAC[];
       ALL_TAC ] THEN
      MATCH_MP_TAC CHAIN_REC THEN
      MAP_EVERY EXISTS_TAC [`ka:K`; `va:V`] THEN
      CONV_TAC MOD_DOWN_CONV THEN
      ASM_SIMP_TAC[MOD_LT] THEN
      (* show that FINDLOOP h k (SUC a) cannot be a *)
      MAP_EVERY POP_ASSUM [K ALL_TAC; MP_TAC; K ALL_TAC] THEN
      REWRITE_TAC[CONTRAPOS_THM] THEN
      DISCH_THEN (fun th ->
        POP_ASSUM_LIST (MP_TAC o end_itlist CONJ o rev) THEN
        SUBST1_TAC (GSYM th) THEN
        DISCH_THEN (MAP_EVERY ASSUME_TAC o CONJUNCTS)) THEN
      POP_ASSUM MP_TAC THEN MESON_TAC[]]]);;

let INV_HEMPTY = prove
  (`!f m. INV1 (hempty f m:hash)`,
   REWRITE_TAC[INV; hempty; htbl; distinctness"option"]);;

let INV_FINDLOOP = prove
  (`!(h:hash) k v p.
      INV1 h /\ p < hmod h /\ htbl h p = SOME (k,v) ==>
      FINDLOOP h k (hfun h k) = p`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
   REWRITE_TAC[INV; CHAIN] THEN
   DISCH_THEN (fun th -> FIRST_ASSUM (MP_TAC o MATCH_MP th)) THEN
   (* add the MOD in the findloop argument *)
   SUBGOAL_THEN `hfun (h:hash) k = hfun h k MOD hmod h` MP_TAC THENL
     [REWRITE_TAC[hfun; MOD_MOD_REFL]; ALL_TAC] THEN
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
       CONV_TAC MOD_DOWN_CONV THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       ASM_REWRITE_TAC[] THEN
       ONCE_REWRITE_TAC[MODSEG_REC] THEN
       SUBGOAL_THEN `~(c MOD hmod (h:hash) = p MOD hmod h)`
         ASSUME_TAC THEN ASM_REWRITE_TAC[IN_INSERT]
     ]
   ]);;

(* If the invariant INV holds, then any binding (k,v) in the
   hash table can be fetched using HFIND h k *)
let INV_IN_FIND = prove
  (`!(h:hash) k v p.
      INV1 h /\ p < hmod h /\ htbl h p = SOME (k,v) ==>
      FIND h k = SOME (k,v)`,
   REPEAT GEN_TAC THEN DISCH_THEN ASSUME_TAC THEN
   REWRITE_TAC[FIND] THEN
   SUBGOAL_THEN `FINDLOOP (h:hash) k (hfun h k) = p`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
   ASM_MESON_TAC[INV_FINDLOOP]);;

let NOTFULL_FIND_IN = prove
  (`!(h:hash) k v.
      NOTFULL h /\ FIND h k = SOME (k,v) ==>
      ?p. p < hmod h /\ htbl h p = SOME (k,v)`,
   REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   MP_TAC (SPECL[`h:hash`;`k:K`;`hfun (h:hash) k`] FINDLOOP_SPEC) THEN
   ASM_SIMP_TAC[FIND; NOTFULL_HFUN_LT; LET_DEF; LET_END_DEF] THEN
   MESON_TAC[]);;

let CHAIN_SET_LAST = prove
  (`!(h:hash) k a b v.
      CHAIN h k a b ==> CHAIN (hset h b (SOME (k,v))) k a b`,
   SIMP_TAC[CHAIN; HSET]);;

let CHAIN_SET_OTHER = prove
  (`!(h:hash) p ka va k a b.
    ~(k = ka) /\ CHAIN h k a b ==> CHAIN (hset h p (SOME (ka,va))) k a b`,
   SIMP_TAC[CHAIN; HSET] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
   POP_ASSUM (fun th -> DISCH_THEN (MP_TAC o MATCH_MP th)) THEN
   STRIP_TAC THEN ASM_MESON_TAC[]);;

let ADD_INV = prove
  (`!(h:hash) ka va. NOTFULL h /\ INV1 h ==> INV1 (ADD h ka va)`,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ADD; INV; LET_DEF; LET_END_DEF; HSET] THEN
    REPEAT GEN_TAC THEN COND_CASES_TAC THENL
    (* we're looking at the updated pos *)
    (* the core argument is a lemma about setting the last
       position of a chain for k to SOME (k,v) *)
    [REWRITE_TAC[injectivity"option"; PAIR_EQ] THEN
     DISCH_THEN (MP_TAC o GSYM) THEN
     DISCH_THEN (CONJUNCTS_THEN ASSUME_TAC) THEN
     POP_ASSUM (CONJUNCTS_THEN SUBST1_TAC) THEN
     FIRST_ASSUM SUBST1_TAC THEN
     MATCH_MP_TAC CHAIN_SET_LAST THEN
     MP_TAC (SPECL[`h:hash`;`ka:K`;`(hfun (h:hash) ka)`] FINDLOOP_SPEC) THEN
     ASM_SIMP_TAC[NOTFULL_HFUN_LT; LET_DEF; LET_END_DEF];
    (* we're looking at something else *)
     POP_ASSUM (fun th -> POP_ASSUM MP_TAC THEN ASSUME_TAC th) THEN
     REWRITE_TAC[IMP_IMP] THEN
     ASM_CASES_TAC `(k:K) = ka` THENL
     [POP_ASSUM SUBST1_TAC THEN
      DISCH_THEN (MP_TAC o MATCH_MP INV_FINDLOOP) THEN
      POP_ASSUM (MP_TAC o GSYM) THEN SIMP_TAC[];
      DISCH_THEN (CONJUNCTS_THEN (ASSUME_TAC o REWRITE_RULE[INV])) THEN
      FIRST_X_ASSUM (fun th -> POP_ASSUM (MP_TAC o MATCH_MP th)) THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC[IMP_IMP] THEN
      MATCH_ACCEPT_TAC CHAIN_SET_OTHER]]);;

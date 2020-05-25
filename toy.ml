(* Linear probing hash table *)

(* Notes:
   - Theorem for inductive types:
     cases, injectivity, distinctness,
*)

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

let MODRNG_REFL = prove
  (`!m a. MODRNG0 m a a = {a MOD m}`,
   REWRITE_TAC[MODRNG; EXTENSION; IN_ELIM_THM] THEN
   REPEAT GEN_TAC THEN EQ_TAC THENL
   (* ==> *)
   [DISCH_THEN (CHOOSE_THEN MP_TAC) THEN
    DISJ_CASES_TAC (SPEC `d:num` num_CASES) THENL
    [ASM_REWRITE_TAC[ADD_CLAUSES; LT] THEN
     DISCH_THEN SUBST1_TAC THEN SET_TAC[];
     POP_ASSUM (CHOOSE_THEN SUBST1_TAC) THEN
     DISCH_THEN (MP_TAC o SPEC `0` o CONJUNCT2) THEN
     REWRITE_TAC[LT_0; ADD_CLAUSES; CONG]];
   (* <== *)
    REWRITE_TAC[IN_SING] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; LT]]);;

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

(*

let MODRNG0_THM = prove
  (`!m a b. MODRNG0 m a b =
      if (a == b) (mod m)
      then {a MOD m}
      else a MOD m INSERT MODRNG0 m (SUC a) b`,

*)

(* -------------------- *)

let MODRNG_MODR = prove
  (`!m a b. MODRNG0 m a (b MOD m) = MODRNG0 m a b`,
   MESON_TAC[MODRNG_CONGR; CONG; MOD_MOD_REFL]);;

let NUMSEG_TEST = prove
  (`0..0 = {0}`,
   REWRITE_TAC[numseg; LE; EXTENSION; IN_ELIM_THM] THEN
   GEN_TAC THEN EQ_TAC THEN SIMP_TAC[COMPONENT; IN_SING; LE]);;

new_type_abbrev("hash",`:(K->num)#(num->(K#V)option)#num`);;

let hmod = new_definition `hmod (h:hash) = SND (SND h)`;;
let htbl = new_definition `htbl (h:hash) = FST (SND h)`;;
let hfun = new_definition `hfun (h:hash) = (\x. FST h x MOD hmod h)`;;

let HGETTER = prove
  (`hfun (f,t,m) = (\x. f x MOD m) /\
    htbl (f,t,m) = t /\
    hmod (f,t,m) = m`,
   SIMP_TAC[hfun; htbl; hmod]);;

let hnext = new_definition `hnext (h:hash) p = SUC p MOD hmod h`;;

let HFINDLOOP = define
  `HFINDLOOP h k p =
     if htbl h p = NONE \/ (?v. htbl h p = SOME (k,v))
     then p
     else HFINDLOOP h k (hnext h p)`;;

let HFIND = new_definition
  `HFIND h k = htbl h (HFINDLOOP h k (hfun h k))`;;

let NFULL = new_definition
  `NFULL h = ?p. p < hmod h /\ htbl h p = NONE`;;

(* a -- b *)

(* modular range *)
let hrng = new_definition `hrng (h:hash) = RNG (hmod h)`;;

(* (hfun k) -- (k,v) is a full interval *)
let INV

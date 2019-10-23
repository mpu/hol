open HolKernel boolLib bossLib pred_setTheory listTheory

val _ = new_theory "constraint"

val atom_def = Datatype`atom = IDX num | PRP ('a set)`

val ct_def = Datatype`ct
 = EX ct
 | AL ct
 (* | CONJ ct ct  annoying at first because we need to shuffle quantifiers *)
 | FLOW (('a atom # 'a atom) list)`

val SEMA = Define`
  (SEMA e (IDX n) = EL n e) /\
  (SEMA e (PRP p) = p)`

val SEM = Define`
  (SEM e (EX c) = ?p. SEM (p :: e) c) /\
  (SEM e (AL c) = !p. SEM (p :: e) c) /\
  (SEM e (FLOW l) = EVERY (\p. SEMA e (FST p) SUBSET SEMA e (SND p)) l)`

(* examples *)
val ex0 = Q.prove
  (`SEM [] (AL (EX (FLOW [IDX 0, IDX 1]))) = T`,
  rw[SEM,SEMA] >>
  qexists_tac `p` >>
  rw[])

val ex1 = Q.prove
  (`SEM [x] (AL (FLOW [IDX 1, IDX 0])) <=> (x = {})`,
  rw[SEM,SEMA] >>
  eq_tac >| [rw[GSYM SUBSET_EMPTY], rw[]])

val ex2 = Q.prove
  (`SEM [x] (AL (FLOW [IDX 0, IDX 1])) <=> (x = univ(:'a))`,
  rw[SEM,SEMA] >>
  eq_tac >| [
    DISCH_THEN (qspec_then `univ(:'a)` mp_tac) >>
    REWRITE_TAC[UNIV_SUBSET],
    RW_TAC std_ss [SUBSET_UNIV]
  ])

(* Split a FLOW conjunction in pieces *)
val LBS = Define`
  LBS l = FILTER (\p. SND p = IDX 0 /\ FST p <> IDX 0) l`
val UBS = Define`
  UBS l = FILTER (\p. FST p = IDX 0 /\ SND p <> IDX 0) l`
val OTH = Define`
  OTH l = FILTER (\p. FST p <> IDX 0 /\ SND p <> IDX 0) l`

val SEM_LBS_UBS_lem = Q.prove(
  `!e x l. (SEM (x::e) (FLOW (LBS l)) <=>
            !y. MEM y (LBS l) ==> SEMA (x::e) (FST y) SUBSET x) /\
           (SEM (x::e) (FLOW (UBS l)) <=>
            !y. MEM y (UBS l) ==> x SUBSET SEMA (x::e) (SND y))`,
  simp_tac list_ss [LBS,UBS,MEM_FILTER,SEM,EVERY_MEM,SEMA])

val [SEM_LBS_lem, SEM_UBS_lem] =
  CONJUNCTS (CONV_RULE (DEPTH_CONV FORALL_AND_CONV) SEM_LBS_UBS_lem)

Theorem SPLIT_LBS_UBS_OTH:
  !l e. SEM e (FLOW l) <=>
        SEM e (FLOW (LBS l)) /\ SEM e (FLOW (UBS l)) /\ SEM e (FLOW (OTH l))
Proof
  Induct >| [
    rw[LBS,UBS,OTH],
    rpt strip_tac >>
    `!l. SEM e (FLOW (h::l)) <=>
         SEM e (FLOW l) /\ (SEMA e (FST h) SUBSET SEMA e (SND h))`
      by (rw[SEM] >> prove_tac[]) >>
    Cases_on `FST h = IDX 0` >>
    Cases_on `SND h = IDX 0` >> 
    (`LBS (h::l) = LBS l`    by rw[LBS] ORELSE
     `LBS (h::l) = h::LBS l` by rw[LBS]) >>
    (`UBS (h::l) = UBS l`    by rw[UBS] ORELSE
     `UBS (h::l) = h::UBS l` by rw[UBS]) >>
    (`OTH (h::l) = OTH l`    by rw[OTH] ORELSE
     `OTH (h::l) = h::OTH l` by rw[OTH]) >>
    rw[] >> prove_tac[]
  ]
QED

Theorem SEMA_NE_IDX0:
  !a. a <> IDX 0 ==> !e x1 x2. SEMA (x1::e) a = SEMA (x2::e) a
Proof
  Cases >> rewrite_tac[SEMA] >>
  Cases_on `n` >| [
    rewrite_tac[],
    rewrite_tac[EL,TL]
  ]
QED

Theorem LBS_UBS_OTH_NE_IDX0:
  !x l. (MEM x (LBS l) ==> FST x <> IDX 0) /\
        (MEM x (UBS l) ==> SND x <> IDX 0) /\
        (MEM x (OTH l) ==> FST x <> IDX 0 /\ SND x <> IDX 0)
Proof
  simp_tac std_ss [LBS,UBS,OTH,MEM_FILTER]
QED

(* Eliminate an existentially quantified variable *)
val EXELIM = Define`
  EXELIM l =
    OTH l ++ FLAT (MAP (\u. MAP (\l. (FST l, SND u)) (LBS l)) (UBS l))`

(* EXELIM is a semantics-preserving transformation on formulas *)
Theorem SEM_EXELIM:
  !e l. SEM e (EX (FLOW l)) = SEM e (EX (FLOW (EXELIM l)))
Proof
  rw[Once SEM, Once SPLIT_LBS_UBS_OTH] >>
  rw[SEM_LBS_lem,SEM_UBS_lem] >>
  rw[EXELIM,SEM,EVERY_FLAT,EVERY_MAP] >>
  rw[EVERY_MEM] >>
  eq_tac >> strip_tac >| [
    qexists_tac `p` >>
    rw[] >> prove_tac[SUBSET_TRANS],
    qexists_tac
      `BIGUNION (\x. ?z. MEM z (LBS l) /\ x = SEMA (X::e) (FST z))` >>
    rw[BIGUNION_SUBSET] >| [
      match_mp_tac SUBSET_BIGUNION_I >>
      rw[] >> qexists_tac `y` >>
      prove_tac[SEMA_NE_IDX0,LBS_UBS_OTH_NE_IDX0],
      prove_tac[SEMA_NE_IDX0,LBS_UBS_OTH_NE_IDX0],
      prove_tac[SEMA_NE_IDX0,LBS_UBS_OTH_NE_IDX0]
    ]
  ]
QED

val _ = export_theory ()

open HolKernel boolLib bossLib listTheory pred_setTheory arithmeticTheory
     pairTheory

val _ = new_theory "euler"

(* PAIRS x l z is the set of (oriented) edges used in a path
   from x to z going by vertices in l *)
Definition PAIRS_def[simp]:
  (PAIRS x [] z = {(x,z)}) /\
  (PAIRS x (y::l) z = (x,y) INSERT PAIRS y l z)
End

Theorem FINITE_PAIRS:
  !l x z. FINITE (PAIRS x l z)
Proof Induct \\ rw[]
QED

(* (x,y) INE G is true when (x,y) is an edge in the undirected
   graph G *)
Definition INE_def: INE (x,y) G = ((x,y) IN G \/ (y,x) IN G)
End
val _ = Parse.set_fixity "INE" (Parse.Infix(Parse.NONASSOC, 425))
(* use term_grammar () to print the current grammar *)

(* A circuit is a path that does not go twice by the same
   undirected edge *)
val (CIRCUIT_rules, CIRCUIT_ind, _) = Hol_reln`
  (CIRCUIT x [] z) /\
  (~((x,y) INE PAIRS y l z) /\ CIRCUIT y l z ==> CIRCUIT x (y::l) z)`

Definition NEIGHB_def: NEIGHB x G = {y | (x,y) INE G}
End

Theorem FINITE_NEIGHB:
  !x G. FINITE G ==> FINITE (NEIGHB x G)
Proof
  `!x G. NEIGHB x G = IMAGE SND (G INTER ({x} CROSS UNIV)) UNION
                      IMAGE FST (G INTER (UNIV CROSS {x}))` by
    (rw[NEIGHB_def,INE_def,EXTENSION]
     \\ metis_tac[PAIR,FST,SND])
  \\ rw[]
QED

Definition DEG_def:
  DEG x G = CARD (NEIGHB x G) + if (x,x) IN G then 1 else 0
End

Theorem DEG_SINGLETON:
  !x y z. DEG x {(y,z)} =
          if x <> y /\ x <> z then 0 else
          if y = z then 2 else 1
Proof rw[DEG_def, NEIGHB_def, INE_def] \\ rpt (fs[])
QED

Theorem INE_IN:
  !x E. (x,x) INE E <=> (x,x) IN E
Proof rw[INE_def]
QED

Theorem INE_INSERT:
  !x y u v E. (x,y) INE ((u,v) INSERT E) <=>
              (x,y) INE {(u,v)} \/ (x,y) INE E
Proof rw[INE_def] \\ metis_tac[]
QED

Theorem DEG_INSERT_ADD:
  !x y z E. FINITE E /\ ~((y,z) INE E) ==>
            DEG x ((y,z) INSERT E) = DEG x {(y,z)} + DEG x E
Proof
  simp[DEG_def]
  \\ rpt strip_tac
  \\ qmatch_abbrev_tac `CARD S0 + _ = CARD S1 + (CARD S2 + _)`
  \\ `S0 = S2 UNION S1` by
       (unabbrev_all_tac \\ rw[NEIGHB_def,Once INE_INSERT,UNION_DEF])
  \\ pop_assum (fn eq => rewrite_tac [eq])
  \\ `FINITE S1` by rw[Abbr`S1`,FINITE_NEIGHB]
  \\ `FINITE S2` by rw[Abbr`S2`,FINITE_NEIGHB]
  \\ `CARD (S2 INTER S1) = 0` by
       (rw[Abbr`S1`,Abbr`S2`,EXTENSION,NEIGHB_def]
        \\ fs[INE_def] \\ metis_tac[])
  \\ rw[CARD_UNION_EQN]
  \\ fs[INE_IN]
QED

Theorem EULER0:
  !x l z.
    CIRCUIT x l z ==>
    let G = PAIRS x l z in
    (!y. y <> x /\ y <> z ==> EVEN (DEG y G)) /\
    if x = z then EVEN (DEG x G) else ODD (DEG x G) /\ ODD (DEG z G)
Proof
  ho_match_mp_tac CIRCUIT_ind
  \\ conj_tac >| [
    (* empty list *)
    rw[DEG_SINGLETON],
    (* non-empty list *)
    qx_genl_tac [`l`,`x`,`y`,`z`]
    \\ strip_tac \\ pop_assum mp_tac
    \\ qspecl_then [`l`,`y`,`z`] assume_tac FINITE_PAIRS 
    \\ simp[ODD_EVEN,DEG_INSERT_ADD,EVEN_ADD]
    \\ rw[] \\ rw[DEG_SINGLETON,DEG_INSERT_ADD,EVEN_ADD] \\ rw[]
  ]
QED

Definition NODES_def:
  NODES G = IMAGE FST G UNION IMAGE SND G
End

Theorem NODES_INSERT:
  !G x y. NODES ((x,y) INSERT G) = x INSERT y INSERT NODES G
Proof
  rw[NODES_def] \\ metis_tac[INSERT_UNION_EQ,UNION_COMM]
QED

Theorem INE_NODES_INSERT:
  !G e. e INE G ==> NODES (e INSERT G) = NODES G
Proof
  Cases_on `e`
  \\ rw[NODES_INSERT,INE_def]
  \\ `q IN NODES G /\ r IN NODES G` by
       (rw[NODES_def] \\ metis_tac[FST,SND])
  \\ metis_tac[ABSORPTION]
QED

Theorem INE_DEG_INSERT:
  !G e. e INE G ==> !x. DEG x (e INSERT G) = DEG x G
Proof
  rpt strip_tac
  \\ `!x y. (x,y) INE e INSERT G <=> (x,y) INE G` by
       (Cases_on `e` \\ fs[INE_def] \\ metis_tac[])
  \\ rw[DEG_def,NEIGHB_def] \\ fs[INE_def]
QED

Theorem SUM_IMAGE_ADD:
  !f g s. FINITE s ==> SIGMA (\x. f x + g x) s = SIGMA f s + SIGMA g s
Proof
  ntac 2 gen_tac
  \\ ho_match_mp_tac FINITE_INDUCT
  \\ rw[SUM_IMAGE_THM,DELETE_NON_ELEMENT_RWT]
QED

Theorem SUM_IMAGE_INSERT:
  !f s. FINITE s ==> !x. SIGMA f (x INSERT s) =
                         if x IN s then SIGMA f s else f x + SIGMA f s
Proof
  rw[SUM_IMAGE_THM] \\ rw[]
  THEN1 (
    `s = x INSERT (s DELETE x)` by rw[INSERT_DELETE]
    \\ pop_assum (CONV_TAC o RHS_CONV o DEPTH_CONV o REWR_CONV)
    \\ rw[SUM_IMAGE_THM]
  )
  THEN1 rw[DELETE_NON_ELEMENT_RWT]
QED

Theorem DEG_NON_NODE:
  !G x. FINITE G ==> x NOTIN NODES G ==> DEG x G = 0
Proof
  rw[DEG_def]
  THEN1 (
    `G = (x,x) INSERT G` by metis_tac[ABSORPTION]
    \\ pop_assum SUBST1_TAC
    \\ rw[NODES_INSERT]
  )
  THEN1 (
    rw[FINITE_NEIGHB]
    \\ rw[NEIGHB_def,EXTENSION]
    \\ `(x,x') INE G ==> x IN NODES G` by
         metis_tac[INE_NODES_INSERT,NODES_INSERT,INE_def,IN_INSERT]
    \\ metis_tac[]
  )
QED

Theorem HANDSHAKE:
  !G. FINITE G ==> EVEN (SIGMA (\x. DEG x G) (NODES G))
Proof
  ho_match_mp_tac FINITE_INDUCT
  \\ conj_tac
  THEN1 rw[NODES_def,SUM_IMAGE_THM]
  THEN1 (
    rw[] \\ pop_assum kall_tac
    \\ Cases_on `e` \\ rename[`(x,y)`]
    \\ Cases_on `(x,y) INE G`
    THEN1 simp[INE_NODES_INSERT,INE_DEG_INSERT]
    THEN1 (
      `FINITE (NODES ((x,y) INSERT G))` by rw[NODES_def]
      \\ simp[DEG_INSERT_ADD,EVEN_ADD,SUM_IMAGE_ADD]
      \\ `EVEN (SIGMA (\x. DEG x G) (NODES ((x,y) INSERT G)))` by
           (fs[NODES_INSERT,SUM_IMAGE_INSERT]
            \\ rw[] \\ fs[] \\ rw[DEG_NON_NODE])
      \\ `FINITE (NODES G)` by rw[NODES_def] (* maybe extract as lemma *)
      \\ rw[NODES_INSERT,SUM_IMAGE_THM,DELETE_INSERT]
      THEN (
        rw[DEG_SINGLETON,EVEN_ADD]
        \\ `!n. n = 0 ==> EVEN n` by rw[]
        \\ pop_assum match_mp_tac
        \\ rw[SUM_IMAGE_ZERO]
      )
    )
  )
QED

Theorem IN_NODES:
  !G x. x IN NODES G ==> ?y. (x,y) INE G (* really <=> *)
Proof
  rw[NODES_def,INE_def]
  (* \\ eq_tac \\ rw[] *)
  \\ metis_tac[PAIR,SND,FST]
QED

Theorem DELETE_PSUBSET:
  !s x. x IN s ==> (s DELETE x) PSUBSET s
Proof
  rw[PSUBSET_DEF,DELETE_SUBSET,EXTENSION] \\ metis_tac[]
QED

Theorem CIRCUIT_OF_INSERT:
  !G x y z. ~((x,y) INE G) /\ (?l. CIRCUIT_OF G y l z) ==>
            ?l. CIRCUIT_OF ((x,y) INSERT G) x l z
Proof
  rw[CIRCUIT_OF_def]
  \\ qexists_tac `y::l`
  \\ conj_tac
  THEN1 (match_mp_tac (CONJUNCT2 CIRCUIT_rules) \\ rw[])
  THEN1 (
    Cases \\ rw[Once INE_INSERT]
    \\ rw[INE_def] \\ metis_tac[]
  )
QED
  
Definition CIRCUIT_OF_def:
  CIRCUIT_OF G x l z =
  (CIRCUIT x l z /\ (!e. e INE PAIRS x l z <=> e INE G))
End

(*
Theorem EULER1:
  !G. FINITE G ==>
  !x y. x IN NODES G /\ z IN NODES G /\
        (if x = z
         then (!v. EVEN (DEG v G))
         else (ODD (DEG x G) /\ ODD (DEG z G) /\
               (!v. v <> x /\ v <> z ==> EVEN (DEG v G)))) ==>
        ?l. CIRCUIT_OF G x l z
Proof
  ho_match_mp_tac FINITE_COMPLETE_INDUCTION
  \\ rw[]
  \\ Cases_on `x = z`
  THEN1 ( (* cycle *)
    rw[] \\ qpat_x_assum `x IN NODES G` kall_tac
    \\ first_assum (strip_assume_tac o MATCH_MP IN_NODES)
    \\ Cases_on `y = x`
    THEN1 ( (* y = x *)
      rw[] \\ fs[INE_IN]
      \\ `G = (x,x) INSERT G DELETE (x,x)` by metis_tac[INSERT_DELETE]
      \\ pop_assum SUBST1_TAC
      \\ match_mp_tac CIRCUIT_OF_INSERT
      \\ conj_tac
      THEN1 metis_tac[IN_DELETE,INE_IN]
      THEN1 (
        first_x_assum irule \\ rw[]
        THEN1 cheat (* x IN NODES (G DELETE (x,x)) *)
        THEN1 cheat (* idem *)
        THEN1 rw[DELETE_PSUBSET]
        THEN1 cheat (* EVEN (DEG v (G DELETE (x,x))) *)
      )
    )
    THEN1 ( (* x <> y *)
      cheat
    )
  )
  THEN1 ( (* non-cycle *)
    cheat
  )
QED
*)

val _ = export_theory ()





(*
For most cases you want to use Define or the pretty syntax
for Define, new_definition and so one are more low-level things.
As for pretty vs non-pretty syntax: Use the one you think is
prettiest?

Is anything added to srw_ss by defining new functions? Maybe you
are thinking of compsets? It’s mostly defining new datatypes that
add things to srw_ss I think — see the documentation for
bossLib.Datatype (the things mentioned about TypeBase there).

There’s a zDefine that is like Define but does not add anything
to any compset.

Not sure if you can define a function without exporting it, maybe.
*)

(* STASH 

val HOP_def = Define`
  (HOP E x [] z <=> (x,z) IN E) /\
  (HOP E x (y :: l) z <=> (x,y) IN E /\ HOP E y l z)`
val HOP_PAIRS_SUBSET = Q.prove(
  `HOP E x l z <=> PAIRS x l z SUBSET E`,
    Q.SPEC_TAC (`x`,`x`) >>
    Induct_on `l` >>
    SRW_TAC[][HOP_def, PAIRS_def])

val LIST_COMPLETE_INDUCT = Q.prove(
  `!P. (!l. (!t. LENGTH t < LENGTH l ==> P t) ==> P l) ==> !l. P l`,
    CONV_TAC (DEPTH_CONV RIGHT_IMP_FORALL_CONV)
    \\ completeInduct_on `LENGTH l`
    \\ rw[])

val DEG_INE_EQUIV = Q.prove(
  `!E G. (!a b. (a,b) INE E <=> (a,b) INE G) ==> !x. DEG x E = DEG x G`,
    rw[DEG_def] >>
    `(x,x) IN E <=> (x,x) IN G` by metis_tac[INE_def] >>
    rw[])
*)


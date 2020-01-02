open HolKernel boolLib bossLib listTheory pred_setTheory arithmeticTheory

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
val (_, CIRCUIT_ind, _) = Hol_reln`
  (CIRCUIT x [] z) /\
  (~((x,y) INE PAIRS y l z) /\ CIRCUIT y l z ==> CIRCUIT x (y::l) z)`

Definition NEIGHB_def: NEIGHB x G = {y | (x,y) INE G}
End

Theorem FINITE_NEIGHB:
  !x G. FINITE G ==> FINITE (NEIGHB x G)
Proof
  `!x G. NEIGHB x G = IMAGE SND (G INTER ({x} CROSS UNIV)) UNION
                      IMAGE FST (G INTER (UNIV CROSS {x}))` by
    let open pairTheory in
      rw[NEIGHB_def,INE_def,EXTENSION]
      \\ metis_tac[PAIR,FST,SND]
    end
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


open HolKernel boolLib bossLib listTheory pred_setTheory arithmeticTheory
     pairTheory;

new_theory "euler";

(* An undirected graph. This definition of graphs does not permit nodes
   that do not appear in any edge; these seem somewhat pathological so
   I just kept it simple. *)
Definition GRAPH_def:
  GRAPH G <=> (!x y. (x,y) IN G <=> (y,x) IN G) /\ FINITE G
End

(* A graph with a single edge between x and y *)
Definition GRAPH1_def:
  GRAPH1 (x,y) = {(x,y); (y,x)}
End

Theorem GRAPH_COMPLETE_INDUCTION:
  !P. (!G. GRAPH G /\ (!E. GRAPH E /\ E PSUBSET G ==> P E) ==> P G) ==>
      !G. GRAPH G ==> P G
Proof
  gen_tac
  \\ qspec_then `\G. GRAPH G ==> P G`
                (mp_tac o BETA_RULE) FINITE_COMPLETE_INDUCTION
  \\ metis_tac[GRAPH_def]
QED

Definition ADDE_def:
  ADDE (x,y) G = (x,y) INSERT (y,x) INSERT G
End

Definition DELE_def:
  DELE (x,y) G = G DELETE (x,y) DELETE (y,x)
End

Theorem GRAPH_RWT[simp]:
  GRAPH {} /\
  (!x y. GRAPH (GRAPH1 (x,y))) /\
  (!G. GRAPH G ==> FINITE G) /\
  (!G e. GRAPH G ==> GRAPH (ADDE e G)) /\
  (!G e. GRAPH G ==> GRAPH (DELE e G))
Proof
  rw[GRAPH_def,GRAPH1_def]
  THEN1 metis_tac[]
  THEN Cases_on `e` \\ rw[ADDE_def,DELE_def] \\ metis_tac[]
QED

Theorem ADDE_DELE:
  !G x y. GRAPH G /\ (x,y) IN G ==> ADDE (x,y) (DELE (x,y) G) = G
Proof
  rw[ADDE_def,DELE_def]
  \\ Cases_on `(x,y) = (y,x)`
  THEN1 (rw[] \\ rw[INSERT_DELETE])
  THEN1 (
    `(y,x) IN G` by fs[GRAPH_def]
    \\ qmatch_abbrev_tac `_ INSERT (_ INSERT INNER DELETE _) = _`
    \\ `(y,x) IN INNER` by rw[Abbr`INNER`,IN_DELETE]
    \\ rw[Abbr`INNER`,INSERT_DELETE]
  )
QED

Theorem DELETE_PSUBSET:
  !s x. x IN s ==> (s DELETE x) PSUBSET s
Proof
  rw[PSUBSET_DEF,DELETE_SUBSET,EXTENSION] \\ metis_tac[]
QED

Theorem GRAPH_INDUCT:
  !P. P {} /\ (!G x y. GRAPH G /\ P G /\ (x,y) NOTIN G ==> P (ADDE (x,y) G)) ==>
      !G. GRAPH G ==> P G
Proof
  ntac 2 strip_tac
  \\ ho_match_mp_tac GRAPH_COMPLETE_INDUCTION
  \\ rw[] \\ Cases_on `G = {}`
  THEN1 rw[]
  THEN1 (
    pop_assum (assume_tac o MATCH_MP CHOICE_DEF)
    \\ Cases_on `CHOICE G`
    \\ rename [`(x,y)`]
    \\ `(y,x) IN G` by fs[GRAPH_def]
    \\ `G = ADDE (x,y) (DELE (x,y) G)` by rw[ADDE_DELE]
    \\ pop_assum SUBST1_TAC
    \\ last_x_assum match_mp_tac \\ reverse (rw[])
    THEN1 rw[DELE_def]
    THEN1 (
      first_x_assum match_mp_tac \\ rw[]
      \\ metis_tac[DELE_def,DELETE_PSUBSET,DELETE_SUBSET,SUBSET_PSUBSET_TRANS]
    )
  )
QED

(* The graph formed by all the edges used in a path from x to z going
   by the vertices of l in sequence *)
Definition PAIRS_def[simp]:
  (PAIRS x [] z = GRAPH1 (x,z)) /\
  (PAIRS x (y::l) z = ADDE (x,y) (PAIRS y l z))
End

Theorem GRAPH_PAIRS:
  !l x z. GRAPH (PAIRS x l z)
Proof Induct \\ rw[]
QED

(* A circuit is a path that does not go twice by the same
   undirected edge *)
Inductive CIRCUIT:
  (CIRCUIT x [] z) /\
  (~((x,y) IN PAIRS y l z) /\ CIRCUIT y l z ==> CIRCUIT x (y::l) z)
End

Definition NEIGHB_def:
  NEIGHB x G = {y | (x,y) IN G}
End

Theorem FINITE_NEIGHB[simp]:
  !x G. FINITE G ==> FINITE (NEIGHB x G)
Proof
  `!x G. NEIGHB x G = IMAGE SND (G INTER ({x} CROSS UNIV))` by
    (rw[NEIGHB_def,EXTENSION] \\ metis_tac[FST,SND,PAIR])
  \\ rw[]
QED

Definition DEG_def:
  DEG x G = CARD (NEIGHB x G) + if (x,x) IN G then 1 else 0
End

(* TODO: Maybe inline this inside DEG_ADDE below and drop GRAPH1 *)
Theorem DEG_GRAPH1:
  !x y z. DEG x (GRAPH1 (y,z)) =
          if x <> y /\ x <> z then 0 else
          if y = z then 2 else 1
Proof rw[DEG_def,NEIGHB_def,GRAPH1_def] \\ rpt (fs[])
QED

Theorem IN_ADDE:
  !x y u v E. (x,y) IN (ADDE (u,v) E) <=>
              (x,y) = (u,v) \/ (x,y) = (v,u) \/ (x,y) IN E
Proof rw[ADDE_def] \\ eq_tac \\ rw[]
QED

Theorem DEG_ADDE:
  !x y z G. GRAPH G /\ ~((y,z) IN G) ==>
            DEG x (ADDE (y,z) G) = DEG x (GRAPH1 (y,z)) + DEG x G
Proof
  simp[DEG_def]
  \\ rpt strip_tac
  \\ qmatch_abbrev_tac `CARD S0 + _ = CARD S1 + (CARD S2 + _)`
  \\ let val neighb_goal_tac =
       unabbrev_all_tac
       \\ rw[NEIGHB_def,IN_ADDE,GRAPH1_def,EXTENSION]
       \\ metis_tac[GRAPH_def]
     in 
     `S0 = S2 UNION S1` by neighb_goal_tac
  \\ pop_assum (fn eq => rewrite_tac [eq])
  \\ `FINITE S1` by rw[Abbr`S1`]
  \\ `FINITE S2` by rw[Abbr`S2`]
  \\ `CARD (S2 INTER S1) = 0` by neighb_goal_tac
  \\ rw[CARD_UNION_EQN]
  \\ rpt (fs[GRAPH1_def,IN_ADDE]) (* Hmm, lots seems to be done here... *)
  end
QED

Theorem EULER0:
  !x l z.
    CIRCUIT x l z ==>
    let G = PAIRS x l z in
    (!y. y <> x /\ y <> z ==> EVEN (DEG y G)) /\
    if x = z then EVEN (DEG x G) else ODD (DEG x G) /\ ODD (DEG z G)
Proof
  ho_match_mp_tac CIRCUIT_ind
  \\ conj_tac
  (* empty list *)
  THEN1 rw[DEG_GRAPH1]
  THEN1 (
    (* non-empty list *)
    qx_genl_tac [`l`,`x`,`y`,`z`]
    \\ strip_tac \\ pop_assum mp_tac
    \\ qspecl_then [`l`,`y`,`z`] assume_tac GRAPH_PAIRS 
    \\ simp[ODD_EVEN,DEG_ADDE,EVEN_ADD]
    \\ rw[] \\ rw[DEG_ADDE,DEG_GRAPH1,EVEN_ADD] \\ rw[]
  )
QED

Definition NODES_def:
  NODES G = IMAGE FST G
End

Theorem NODES_ADDE:
  !G x y. NODES (ADDE (x,y) G) = x INSERT y INSERT NODES G
Proof rw[NODES_def,ADDE_def]
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
  !G x. FINITE G /\ x NOTIN NODES G ==> DEG x G = 0
Proof
  rw[DEG_def]
  THEN1 (
    `G = ADDE (x,x) G` by (simp[ADDE_def] \\ metis_tac[ABSORPTION])
    \\ pop_assum SUBST1_TAC
    \\ rw[NODES_ADDE]
  )
  THEN1 (
    rw[NEIGHB_def,EXTENSION]
    \\ `NODES ((x,x') INSERT G) = x INSERT NODES G` by rw[NODES_def]
    \\ metis_tac[ABSORPTION]
  )
QED

Theorem HANDSHAKE:
  !G. GRAPH G ==> EVEN (SIGMA (\x. DEG x G) (NODES G))
Proof
  ho_match_mp_tac GRAPH_INDUCT
  \\ conj_tac
  THEN1 rw[NODES_def,SUM_IMAGE_THM]
  THEN1 (
    rw[]
    \\ `FINITE (NODES (ADDE (x,y) G))` by rw[NODES_def]
    \\ simp[DEG_ADDE,EVEN_ADD,SUM_IMAGE_ADD]
    \\ `EVEN (SIGMA (\x. DEG x G) (NODES (ADDE (x,y) G)))` by
         (fs[NODES_ADDE,ADDE_def,SUM_IMAGE_INSERT]
          \\ rw[] \\ fs[] \\ rw[DEG_NON_NODE])
    \\ `FINITE (NODES G)` by rw[NODES_def]
    \\ rw[NODES_ADDE,SUM_IMAGE_THM,DELETE_INSERT]
    THEN (
      rw[DEG_GRAPH1,EVEN_ADD]
      \\ `!n. n = 0 ==> EVEN n` by rw[]
      \\ pop_assum match_mp_tac
      \\ rw[SUM_IMAGE_ZERO]
    )
  )
QED

Theorem IN_NODES:
  !G x. x IN NODES G ==> ?y. (x,y) IN G (* really <=> *)
Proof
  rw[NODES_def] (* \\ eq_tac \\ rw[] *) \\ metis_tac[PAIR,SND,FST]
QED

Definition CIRCUIT_OF_def:
  CIRCUIT_OF G x l z = (CIRCUIT x l z /\ G = PAIRS x l z)
End

Theorem CIRCUIT_OF_ADDE:
  !G x y z. (x,y) NOTIN G /\ (?l. CIRCUIT_OF G y l z) ==>
            ?l. CIRCUIT_OF (ADDE (x,y) G) x l z
Proof
  rw[CIRCUIT_OF_def]
  \\ qexists_tac `y::l`
  \\ conj_tac
  THEN1 (match_mp_tac (CONJUNCT2 CIRCUIT_rules) \\ rw[])
  THEN1 rw[]
QED

(*
Theorem EULER1:
  !G. GRAPH G ==>
  !x z. x IN NODES G /\ z IN NODES G /\
        (if x = z
         then (!v. EVEN (DEG v G))
         else (ODD (DEG x G) /\ ODD (DEG z G) /\
               (!v. v <> x /\ v <> z ==> EVEN (DEG v G)))) ==>
        ?l. CIRCUIT_OF G x l z
Proof
  ho_match_mp_tac GRAPH_COMPLETE_INDUCTION
  \\ rw[]
  \\ Cases_on `x = z`
  THEN1 ( (* cycle *)
    rw[] \\ qpat_x_assum `x IN NODES G` kall_tac
    \\ first_assum (strip_assume_tac o MATCH_MP IN_NODES)
    \\ Cases_on `y = x`
    THEN1 ( (* y = x *)
      rw[]
      \\ `G = ADDE (x,x) (DELE (x,x) G)` by rw[ADDE_DELE]
      \\ pop_assum SUBST1_TAC
      (* Case analysis on DELE (x,x) G = {}; could be pushed even
         before the first case analysis on x = z *)
      \\ match_mp_tac CIRCUIT_OF_INSERT
      \\ conj_tac
      THEN1 rw[DELE_def]
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

export_theory ();


(* Attic 

Theorem IN_NODES_ADDE:
  !G e. GRAPH G /\ e IN G ==> NODES (ADDE e G) = NODES G
Proof
  Cases_on `e`
  \\ rw[NODES_ADDE]
  \\ `q IN NODES G /\ r IN NODES G` by
       (rw[NODES_def] \\ metis_tac[GRAPH_def,FST,SND])
  \\ metis_tac[ABSORPTION]
QED

Theorem IN_DEG_ADDE:
  !G e. GRAPH G /\ e IN G ==> !x. DEG x (ADDE e G) = DEG x G
Proof
  rpt strip_tac
  \\ `!x y. (x,y) IN (ADDE e G) <=> (x,y) IN G` by
       (Cases_on `e` \\ rw[IN_ADDE] \\ metis_tac[GRAPH_def])
  \\ rw[DEG_def,NEIGHB_def]
QED
*)

(* Notes

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

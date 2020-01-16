open HolKernel boolLib bossLib listTheory pred_setTheory arithmeticTheory
     pairTheory set_relationTheory;

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
  !P. (!G. (!E. GRAPH E /\ E PSUBSET G ==> P E) /\ GRAPH G ==> P G) ==>
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

Theorem GRAPH_CONV_THMS[simp]:
  GRAPH {} /\
  GRAPH (GRAPH1 (x,y)) /\
  (GRAPH G ==> FINITE G) /\
  (GRAPH G ==> GRAPH (ADDE e G)) /\
  (GRAPH G ==> GRAPH (DELE e G))
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

Theorem DEG_NOTIN_NODES:
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
          \\ rw[] \\ fs[] \\ rw[DEG_NOTIN_NODES])
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
  !G x. x IN NODES G ==> ?y. (x,y) IN G
Proof rw[NODES_def] \\ metis_tac[PAIR,SND,FST]
QED

Definition CIRCUIT_OF_def:
  CIRCUIT_OF G x l z = (CIRCUIT x l z /\ G = PAIRS x l z)
End

Theorem CIRCUIT_OF_ADDE:
  !G x y l z. (x,y) NOTIN G /\ CIRCUIT_OF G y l z ==>
              CIRCUIT_OF (ADDE (x,y) G) x (y::l) z
Proof rw[CIRCUIT_OF_def] \\ rw[CIRCUIT_rules]
QED

Definition CONNECTED_def:
  CONNECTED G = !x y. x IN NODES G /\ y IN NODES G /\ x <> y ==> (x,y) IN tc G
End

Theorem GRAPH_TC:
  !G. GRAPH G ==> GRAPH (tc G)
Proof
  rw[GRAPH_def]
  THEN1 (
    `!x y. (x,y) IN tc G ==> (y,x) IN tc G` by
      (ho_match_mp_tac tc_ind \\ metis_tac[tc_rules])
    \\ eq_tac \\ rw[]
  )
  THEN1 (
    (* TODO: extract FINITE s ==> FINITE (tc s) as a lemma *)
    `!x y. (x,y) IN G ==> x IN NODES G /\ y IN NODES G` by
      (rw[NODES_def] \\ metis_tac[FST,SND])
    \\ `!x y. (x,y) IN tc G ==> (x,y) IN (NODES G CROSS NODES G)` by
         (ho_match_mp_tac tc_ind \\ rw[] \\ metis_tac[])
    \\ `tc G SUBSET NODES G CROSS NODES G` by
         (rewrite_tac[SUBSET_DEF] \\ gen_tac \\ Cases_on `x` \\ rw[])
    \\ `FINITE (NODES G)` by rw[NODES_def] (* TODO: extract as lemma in simp *)
    \\ qspec_then `NODES G CROSS NODES G` mp_tac SUBSET_FINITE
    \\ rw[]
  )
QED

Theorem CONNECTED_DELE:
  !G x y. GRAPH G /\ CONNECTED G /\ (x,y) IN tc (DELE (x,y) G) ==>
          CONNECTED (DELE (x,y) G)
Proof
  rpt strip_tac \\ rw[CONNECTED_def]
  \\ `!n. n IN NODES (DELE (x,y) G) ==> n IN NODES G`
       by (rw[DELE_def,NODES_def] \\ metis_tac[])
  \\ `(x',y') IN tc G` by fs[CONNECTED_def]
  \\ pop_assum mp_tac
  \\ ntac 4 (pop_assum kall_tac)
  \\ map_every qid_spec_tac [`y'`,`x'`]
  \\ ho_match_mp_tac tc_ind \\ rw[tc_rules]
  \\ `(y,x) IN tc (DELE (x,y) G)` by
       metis_tac[GRAPH_TC,GRAPH_CONV_THMS,GRAPH_def]
  \\ Cases_on `(x',y') <> (x,y) /\ (x',y') <> (y,x)`
  THEN1 (
    simp[DELE_def]
    \\ rename[`_ <> xy /\ _ <> yx`]
    \\ rw[tc_rules]
  )
  THEN1 (rw[] \\ rw[])
QED

Theorem DELE_EMPTY_CASES:
  !G x y. GRAPH G /\ DELE (x,y) G = {} ==> (G = {} \/ G = GRAPH1 (x,y))
Proof
  rw[DELE_def,GRAPH1_def,EXTENSION]
  \\ metis_tac[GRAPH_def,PAIR,FST,SND] (* that's a bit of work! *)
QED

Definition REACH_def:
  REACH x G = { e | e IN G /\ (x,SND e) IN tc G }
End

Theorem REACH_SUBSET:
  !G n. REACH n G SUBSET G
Proof
  rw[REACH_def,SUBSET_DEF]
QED

Theorem GRAPH_REACH:
  !G n. GRAPH G ==> GRAPH (REACH n G)
Proof
  rw[GRAPH_def]
  THEN1 (
    rw[REACH_def]
    \\ eq_tac \\ rw[]
    \\ match_mp_tac ((CONJUNCT2 o Q.SPEC `G`) tc_rules)
    THEN1 (qexists_tac `y` \\ rw[tc_rules])
    THEN1 (qexists_tac `x` \\ rw[tc_rules])
  )
  THEN1 (
    pop_assum (match_mp_tac o MATCH_MP SUBSET_FINITE)
    \\ rw[REACH_SUBSET]
  )
QED

(* Combined with tc_mono and REACH_SUBSET, we can obtain the
   weaker conclusion (x,y) IN tc G *)
Theorem IN_NODES_REACH:
  !G x y. GRAPH G /\ y IN NODES (REACH x G) ==> (x,y) IN tc (REACH x G)
Proof
  rpt strip_tac
  \\ pop_assum mp_tac
  \\ `!G. GRAPH G ==> NODES G = IMAGE SND G` by
       (simp[GRAPH_def,EXTENSION,NODES_def]
        \\ metis_tac[PAIR,FST,SND])
  \\ pop_assum (fn thm => rw[GRAPH_REACH,thm])
  \\ Cases_on `x'` \\ rename [`(y,z) IN REACH x G`]
  \\ simp[]
  \\ `(x,z) IN tc G /\ (y,z) IN G` by fs[REACH_def]
  \\ `(x,y) IN tc G` by metis_tac[GRAPH_def,tc_rules]
  \\ match_mp_tac ((CONJUNCT2 o SPEC_ALL) tc_rules)
  \\ qexists_tac `y` \\ rw[tc_rules]
  \\ pop_assum mp_tac
  \\ ntac 3 (pop_assum kall_tac)
  \\ map_every qid_spec_tac [`y`,`x`]
  (* At this point we prove
    (x,y) IN tc G ==> (x,y) IN tc (REACH x G) *)
  \\ ho_match_mp_tac tc_ind_right \\ rw[]
  THEN1 rw[tc_rules,REACH_def]
  THEN1 (
    rename [`(y,z) IN G`,`(x,y) IN tc _`]
    \\ match_mp_tac ((CONJUNCT2 o SPEC_ALL) tc_rules)
    \\ qexists_tac `y` \\ rw[tc_rules]
    \\ match_mp_tac ((CONJUNCT1 o SPEC_ALL) tc_rules)
    \\ rw[REACH_def]
    \\ match_mp_tac ((CONJUNCT2 o SPEC_ALL) tc_rules)
    \\ qexists_tac `y` \\ rw[tc_rules]
    \\ irule (CONV_RULE (RAND_CONV (REWR_CONV SUBSET_DEF)) tc_mono)
    \\ qexists_tac `REACH x G`
    \\ rw[REACH_SUBSET]
  )
QED

Theorem CONNECTED_REACH:
  !G n. GRAPH G ==> CONNECTED (REACH n G)
Proof
  rw[CONNECTED_def]
  \\ imp_res_tac IN_NODES_REACH
  \\ `(x,n) IN tc (REACH n G)` by metis_tac[GRAPH_def,GRAPH_TC,GRAPH_REACH]
  \\ match_mp_tac ((CONJUNCT2 o SPEC_ALL) tc_rules)
  \\ qexists_tac `n` \\ rw[tc_rules]
QED

(*
Theorem CONNECTED_SPLIT:
  !G x y. GRAPH G /\ CONNECTED G /\ (x,y) IN G ==>
          DELE (x,y) G = REACH x (DELE (x,y) G) UNION REACH y (DELE (x,y) G)
Proof
  rpt strip_tac
  \\ match_mp_tac SUBSET_ANTISYM \\ reverse conj_tac
  THEN1 rw[REACH_SUBSET]
  THEN1 (
    rw[SUBSET_DEF]
    \\ Cases_on `x'`
    \\ rename [`(a,b) IN DELE _ _`]
    \\ simp[REACH_def]
    \\ pop_assum mp_tac

    (* On what should the induction be done... *)

    \\ `(x,b) IN tc G` by (
         `(a,b) IN G` by fs[DELE_def]
         \\ fs[CONNECTED_def]
         \\ first_assum irule
         \\ rw[NODES_def]
         THEN1 (qexists_tac `(x,y)` \\ rw[])
         THEN1 (qexists_tac `(b,a)` \\ rw[] \\ fs[GRAPH_def])
       )




    (* TODO: extract a lemma *)
    \\ simp[REACH_def]
    \\ qpat_x_assum `(x,y) IN G` mp_tac
    \\ qpat_x_assum `b <> y` mp_tac
    \\ qid_spec_tac `y`
    \\ qpat_x_assum `(x,b) IN tc G` mp_tac
    \\ ntac 2 (pop_assum kall_tac)
    \\ map_every qid_spec_tac [`b`,`x`]
    \\ ho_match_mp_tac tc_ind_right \\ rw[]
    THEN1 (
      disj1_tac
      \\ match_mp_tac ((CONJUNCT1 o SPEC_ALL) tc_rules)
      \\ rw[DELE_def]
      \\ cheat (* x <> y *)
    )
    THEN1 (
      Cases_on `b' = y`
      THEN1 (
        rw[]
        \\ disj1_tac
        \\ match_mp_tac ((CONJUNCT1 o SPEC_ALL) tc_rules)
        \\ rw[DELE_def]
        \\ cheat (* x <> y *)
      )
      THEN1 (
        first_x_assum (assume_tac o Q.SPEC `x`)
      )
    )
QED
*)

(*
Theorem EULER1:
  !G. GRAPH G /\ CONNECTED G ==>
  !x z. x IN NODES G /\ z IN NODES G /\
        (if x = z
         then (!v. EVEN (DEG v G))
         else (ODD (DEG x G) /\ ODD (DEG z G) /\
               (!v. v <> x /\ v <> z ==> EVEN (DEG v G)))) ==>
        ?l. CIRCUIT_OF G x l z
Proof
  CONV_TAC (BINDER_CONV (REWR_CONV (GSYM AND_IMP_INTRO)))
  \\ ho_match_mp_tac GRAPH_COMPLETE_INDUCTION
  \\ rw[]
  \\ qpat_assum `x IN NODES G` (strip_assume_tac o MATCH_MP IN_NODES)
  \\ Cases_on `DELE (x,y) G = {}`
  THEN1 (
    (* base case: graph is a single edge (x,y) *)
    last_x_assum kall_tac
    \\ `G = {} \/ G = GRAPH1 (x,y)` by rw[DELE_EMPTY_CASES] (* TODO: is it possible to not state this? *)
    THEN1 fs[NODES_def]
    THEN1 (
      qexists_tac `[]`
      \\ `z = y` by (
           fs[GRAPH1_def,NODES_def]
           \\ qpat_x_assum `z = x` (mp_tac o GSYM) \\ rw[]
           \\ CCONTR_TAC
           \\ first_x_assum (qspec_then `y` mp_tac)
           \\ simp[DEG_def,NEIGHB_def]
         )
      \\ `(x,y) IN GRAPH1 (x,y)` by rw[GRAPH1_def]
      \\ rw[CIRCUIT_OF_def,CIRCUIT_rules]
    )
  )
  THEN1 (
    (* Split the graph in two, X = REACH x G' and Y = REACH y G'
       where G' = DELE (x,y) G; then G = ADDE (x,y) (X UNION Y);
       and apply the induction hypotheses on X and Y *)

    (* Need a case analysis to know which of x,y,z are equal *)
    (* If x = y we should be able to apply the induction hypothesis
       on G' directly and connect x -- x to x --* z *)
    (* If x <> y we split G' = REACH x G' UNION REACH y G';
       each component is connected and satisfies the hypotheses
       so we can build x --* x and connect it to y --* z *)

    (* Might not be useful
     --
    `G = ADDE (x,y) (DELE (x,y) G)` by rw[ADDE_DELE]
    \\ pop_assum SUBST1_TAC
    \\ qmatch_abbrev_tac `?l. CIRCUIT_OF (ADDE _ G') x l z`
    \\ `(?l. CIRCUIT_OF G' y l z) ==> ?l. CIRCUIT_OF (ADDE (x,y) G') x l z`
         by (strip_tac \\ qexists_tac `y::l`
             \\ rw[Abbr`G'`,CIRCUIT_OF_ADDE,DELE_def])
    \\ pop_assum match_mp_tac
    *)

    \\ cheat
  )
QED
*)

export_theory ();


(* Attic 

(* Those cannot be used by the simplifier unfortunately because a variable
   of the hypotheses does not appear in the conclusion. *)
Theorem FST_EDGE_IN_NODES[simp]:
  !G x y. GRAPH G /\ (x,y) IN G ==> x IN NODES G
Proof
  rw[NODES_def] \\ qexists_tac `(x,y)` \\ rw[]
QED

Theorem SND_EDGE_IN_NODES[simp]:
  !G x y. GRAPH G /\ (x,y) IN G ==> y IN NODES G
Proof
  rw[NODES_def] \\ qexists_tac `(y,x)` \\ rw[] \\ fs[GRAPH_def]
QED

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

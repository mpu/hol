open HolKernel boolLib bossLib listTheory pred_setTheory arithmeticTheory
     pairTheory set_relationTheory;

new_theory "euler";

(* An undirected graph. Note: This definition of graphs does not permit
   nodes that do not appear in any edge; the advantage is that it's just
   a set. *)
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

Theorem ADDE_UNION:
  !G x y. ADDE (x,y) G = GRAPH1 (x,y) UNION G
Proof
  simp[ADDE_def,GRAPH1_def,INSERT_UNION_EQ]
QED

Theorem ADDE_DELE:
  !G x y. GRAPH G /\ (x,y) IN G ==> ADDE (x,y) (DELE (x,y) G) = G
Proof
  rw[GRAPH_def,ADDE_def,DELE_def,EXTENSION] \\ metis_tac[]
QED

Theorem DELE_ADDE:
  !G x y. GRAPH G /\ (x,y) NOTIN G ==> DELE (x,y) (ADDE (x,y) G) = G
Proof
  rw[GRAPH_def,ADDE_def,DELE_def,EXTENSION] \\ metis_tac[]
QED

Theorem DELE_DELE:
  !G a b c d. DELE (a,b) (DELE (c,d) G) = DELE (c,d) (DELE (a,b) G)
Proof
  rw[DELE_def,EXTENSION] \\ metis_tac[]
QED

Theorem ADDE_ADDE:
  !G a b c d. ADDE (a,b) (ADDE (c,d) G) = ADDE (c,d) (ADDE (a,b) G)
Proof
  rw[ADDE_def,EXTENSION] \\ metis_tac[]
QED

Theorem DELETE_PSUBSET:
  !s x. x IN s ==> (s DELETE x) PSUBSET s
Proof
  rw[PSUBSET_DEF,DELETE_SUBSET,EXTENSION] \\ metis_tac[]
QED

Theorem DELE_PSUBSET:
  !G e. e IN G ==> DELE e G PSUBSET G
Proof
  Cases_on `e` \\ rw[DELE_def]
  \\ match_mp_tac SUBSET_PSUBSET_TRANS
  \\ qexists_tac `G DELETE (q,r)`
  \\ rw[DELETE_PSUBSET]
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
    THEN1 (first_x_assum match_mp_tac \\ rw[DELE_PSUBSET])
  )
QED

(* The graph formed by all the edges used in a path from x to z going
   by the vertices of l in sequence *)
Definition PAIRS_def[simp]:
  (PAIRS x [] z = GRAPH1 (x,z)) /\
  (PAIRS x (y::l) z = ADDE (x,y) (PAIRS y l z))
End

Theorem GRAPH_PAIRS[simp]:
  !l x z. GRAPH (PAIRS x l z)
Proof Induct \\ rw[]
QED

(* A circuit is a path that does not go twice by the same
   undirected edge *)
Inductive CIRCUIT:
  (CIRCUIT x [] z) /\
  ((x,y) NOTIN PAIRS y l z /\ CIRCUIT y l z ==> CIRCUIT x (y::l) z)
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
  !x y z G. GRAPH G /\ (y,z) NOTIN G ==>
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
    \\ simp[ODD_EVEN,DEG_ADDE,EVEN_ADD]
    \\ rw[] \\ rw[DEG_ADDE,DEG_GRAPH1,EVEN_ADD] \\ rw[]
  )
QED

Definition NODES_def:
  NODES G = IMAGE FST G
End

Theorem IN_NODES_DELE:
  !G u v x. x IN NODES (DELE (u,v) G) ==> x IN NODES G
Proof
  rw[NODES_def,DELE_def]
  \\ qexists_tac `x'` \\ rw[]
QED

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
  !G x. x NOTIN NODES G ==> DEG x G = 0
Proof
  rw[DEG_def]
  THEN1 (simp[NODES_def] \\ qexists_tac `(x,x)` \\ rw[])
  THEN1 (
    `NEIGHB x G = {}` suffices_by rw[]
    \\ rw[NEIGHB_def,EXTENSION]
    \\ fs[NODES_def]
    \\ pop_assum (qspec_then `(x,x')` mp_tac)
    \\ simp[]
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
Proof
  rw[NODES_def] \\ qexists_tac `SND x'` \\ rw[PAIR]
QED

Definition CONNECTED_def:
  CONNECTED G = !x y. x IN NODES G /\ y IN NODES G /\ x <> y ==> (x,y) IN tc G
End

Theorem GRAPH_TC[simp]:
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

Theorem GRAPH_REACH[simp]:
  !G n. GRAPH G ==> GRAPH (REACH n G)
Proof
  rw[GRAPH_def]
  THEN1 (
    rw[REACH_def]
    \\ eq_tac \\ rw[]
    \\ match_mp_tac (CONJUNCT2 (SPEC_ALL tc_rules))
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
  \\ pop_assum (fn thm => rw[thm])
  \\ Cases_on `x'` \\ rename [`(y,z) IN REACH x G`]
  \\ simp[]
  \\ `(x,z) IN tc G /\ (y,z) IN G` by fs[REACH_def]
  \\ `(x,y) IN tc G` by metis_tac[GRAPH_def,tc_rules]
  \\ match_mp_tac (CONJUNCT2 (SPEC_ALL tc_rules))
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
    \\ match_mp_tac (CONJUNCT2 (SPEC_ALL tc_rules))
    \\ qexists_tac `y` \\ rw[tc_rules]
    \\ match_mp_tac (CONJUNCT1 (SPEC_ALL tc_rules))
    \\ rw[REACH_def]
    \\ match_mp_tac (CONJUNCT2 (SPEC_ALL tc_rules))
    \\ qexists_tac `y` \\ rw[tc_rules]
    \\ irule (CONV_RULE (RAND_CONV (REWR_CONV SUBSET_DEF)) tc_mono)
    \\ qexists_tac `REACH x G`
    \\ rw[REACH_SUBSET]
  )
QED

Theorem CONNECTED_REACH[simp]:
  !G n. GRAPH G ==> CONNECTED (REACH n G)
Proof
  rw[CONNECTED_def]
  \\ imp_res_tac IN_NODES_REACH
  \\ `GRAPH (tc (REACH n G))` by rw[]
  \\ metis_tac[tc_rules,GRAPH_def]
QED

Theorem REACH_CONNECTED_EQ:
  !G x. GRAPH G /\ CONNECTED G /\ x IN NODES G ==> REACH x G = G
Proof
  rw[REACH_def,EXTENSION]
  \\ rename [`e IN G /\ _`]
  \\ eq_tac \\ rw[]
  \\ `?y. (x,y) IN G` by rw[IN_NODES]
  \\ reverse (Cases_on `SND e = x`)
  THEN1 (
    fs[CONNECTED_def]
    \\ first_x_assum irule
    \\ simp[]
    \\ `(SND e, FST e) IN G` by fs[GRAPH_def]
    \\ simp[NODES_def]
    \\ qexists_tac `(SND e,FST e)` \\ simp[]
  )
  THEN1 (
    irule (CONJUNCT2 (SPEC_ALL tc_rules))
    \\ qexists_tac `y`
    \\ fs[tc_rules,GRAPH_def]
  )
QED

Theorem REACH_NON_EMPTY:
  !G x. REACH x G <> {} <=> x IN NODES G
Proof
  rw[] \\ eq_tac \\ strip_tac
  THEN1 (
    first_assum (mp_tac o MATCH_MP CHOICE_DEF)
    \\ rename [`e IN REACH _ _`]
    \\ simp[REACH_def,Once tc_cases_left]
    \\ strip_tac \\ simp[NODES_def]
    THEN1 (qexists_tac `(x,SND e)` \\ rw[])
    THEN1 (qexists_tac `(x,z)` \\ rw[])
  )
  THEN1 (
    fs[NODES_def]
    \\ simp[EXTENSION]
    \\ qexists_tac `x'`
    \\ rw[REACH_def,tc_rules]
  )
QED

Theorem REACH_INVOLUTIVE:
  !G x. GRAPH G ==> REACH x (REACH x G) = REACH x G
Proof
  rw[]
  \\ Cases_on `x IN NODES G`
  THEN1 (
    `?y. (x,y) IN G` by rw[IN_NODES]
    \\ `x IN NODES (REACH x G)`
         by (simp[NODES_def] \\ qexists_tac `(x,y)`
             \\ rw[REACH_def,tc_rules])
    \\ simp[REACH_CONNECTED_EQ]
  )
  THEN1 (
    `REACH x G = {}` by (CCONTR_TAC \\ fs[REACH_NON_EMPTY])
    \\ simp[REACH_def]
  )
QED

Theorem PATH_SPLIT0[local]:
  !G z w. (z,w) IN tc G ==>
          !x y. (x,y) IN G /\ w <> y /\ w <> x ==>
                (z,w) IN tc (DELE (x,y) G) \/
                (x,w) IN tc (DELE (x,y) G) \/
                (y,w) IN tc (DELE (x,y) G)
Proof
  strip_tac
  \\ ho_match_mp_tac tc_ind_left \\ rw[]
  THEN1 (
    disj1_tac
    \\ `(z,w) IN DELE (x,y) G` suffices_by rw[tc_rules]
    \\ rw[DELE_def]
  )
  THEN1 (
    first_x_assum (mp_tac o Q.SPECL [`x`,`y`])
    \\ disch_then (mp_tac o REWRITE_RULE[GSYM AND_IMP_INTRO])
    \\ rpt (disch_then (fn th => first_assum (mp_tac o MATCH_MP th)))
    \\ reverse strip_tac
    THEN1 (disj2_tac \\ disj2_tac \\ rw[])
    THEN1 (disj2_tac \\ disj1_tac \\ rw[])
    THEN1 (
      Cases_on `z' = x \/ z' = y` \\ rw[]
      THEN1 (disj2_tac \\ disj1_tac \\ rw[])
      THEN1 (disj2_tac \\ disj2_tac \\ rw[])
      THEN1 (
        fs[]
        \\ disj1_tac
        \\ match_mp_tac (CONJUNCT2 (SPEC_ALL tc_rules))
        \\ qexists_tac `z'` \\ rw[]
        \\ rw[DELE_def,tc_rules]
      )
    )
  )
QED

Theorem PATH_SPLIT[local] = PROVE[PATH_SPLIT0]
  ``!G x y z. (x,z) IN tc G /\ (x,y) IN G /\ x <> z /\ y <> z ==>
              (x,z) IN tc (DELE (x,y) G) \/
              (y,z) IN tc (DELE (x,y) G)``

Theorem CONNECTED_SPLIT:
  !G x y. GRAPH G /\ CONNECTED G /\ (x,y) IN G /\ x <> y ==>
          DELE (x,y) G = REACH x (DELE (x,y) G) UNION REACH y (DELE (x,y) G)
Proof
  rpt strip_tac
  \\ match_mp_tac SUBSET_ANTISYM \\ reverse conj_tac
  THEN1 rw[REACH_SUBSET]
  THEN1 (
    rw[SUBSET_DEF]
    \\ Cases_on `x'`
    \\ rename [`(u,v) IN DELE _ _`]
    THEN1 (
      `(v <> x /\ v <> y) \/ (u <> x /\ u <> y) \/
       (u = x /\ v = x) \/ (u = y /\ v = y)` by
         (fs[DELE_def] \\ metis_tac[]) \\ rw[]
      THEN1 (
        simp[REACH_def]
        \\ match_mp_tac PATH_SPLIT \\ rw[]
        \\ `(v,u) IN G` by fs[GRAPH_def,DELE_def]
        \\ full_simp_tac std_ss [CONNECTED_def]
        \\ first_assum irule
        \\ rw[NODES_def]
        THEN1 (qexists_tac `(x,y)` \\ rw[])
        THEN1 (qexists_tac `(v,u)` \\ rw[] \\ fs[GRAPH_def])
      )
      THEN1 (
        `(v,u) IN REACH x (DELE (x,y) G) \/ (v,u) IN REACH y (DELE (x,y) G)`
          suffices_by metis_tac[GRAPH_REACH,GRAPH_CONV_THMS,GRAPH_def]
        \\ `(v,u) IN DELE (x,y) G` by metis_tac[GRAPH_CONV_THMS,GRAPH_def]
        \\ simp[REACH_def]
        \\ match_mp_tac PATH_SPLIT \\ rw[]
        \\ `(u,v) IN G` by fs[DELE_def]
        \\ full_simp_tac std_ss [CONNECTED_def]
        \\ first_assum irule
        \\ rw[NODES_def]
        THEN1 (qexists_tac `(x,y)` \\ rw[])
        THEN1 (qexists_tac `(u,v)` \\ rw[] \\ fs[GRAPH_def])
      )
      THEN1 (simp[REACH_def] \\ disj1_tac \\ rw[tc_rules])
      THEN1 (simp[REACH_def] \\ disj2_tac \\ rw[tc_rules])
    )
  )
QED

Theorem IN_REACH_LEMMA[local]:
  !G x u v. GRAPH G /\ u IN NODES (REACH x G) ==>
            ((u,v) IN REACH x G <=> (u,v) IN G)
Proof
  simp[NODES_def] \\ rpt strip_tac \\ eq_tac \\ rw[REACH_def]
  \\ Cases_on `x'` \\ rename [`(u,w) IN REACH x G`] \\ fs[]
  \\ match_mp_tac (CONJUNCT2 (SPEC_ALL tc_rules))
  \\ qexists_tac `w` \\ conj_tac
  THEN1 (fs[REACH_def])
  THEN1 (
    match_mp_tac (CONJUNCT2 (SPEC_ALL tc_rules))
    \\ qexists_tac `u` \\ conj_tac
    THEN1 (fs[tc_rules,REACH_def,GRAPH_def])
    THEN1 (fs[tc_rules])
  )
QED

Theorem DEG_REACH:
  !G u x. GRAPH G /\ u IN NODES (REACH x G) ==> DEG u (REACH x G) = DEG u G
Proof
  simp[DEG_def,NEIGHB_def,IN_REACH_LEMMA]
QED

Theorem PATH_NO_LOOP[local]:
  !G u x y. (x,y) IN tc G /\ y <> u ==> (x,y) IN tc (G DELETE (u,u))
Proof
  ntac 2 gen_tac
  \\ simp[GSYM AND_IMP_INTRO]
  \\ ho_match_mp_tac tc_ind_left \\ conj_tac
  THEN1 rw[tc_rules]
  THEN1 (
    rw[] \\ Cases_on `(x,x') = (u,u)`
    THEN1 (rw[] \\ rw[])
    THEN1 (
      match_mp_tac (CONJUNCT2 (SPEC_ALL tc_rules))
      \\ qexists_tac `x'` \\ rw[tc_rules]
    )
  )
QED

Theorem CONNECTED_DELE_LOOP:
  !G. GRAPH G /\ CONNECTED G ==> CONNECTED (DELE (u,u) G)
Proof
  rw[] \\ rw[CONNECTED_def]
  \\ `(x,y) IN tc G` by (
       rpt (first_x_assum (assume_tac o MATCH_MP IN_NODES_DELE))
       \\ full_simp_tac std_ss [CONNECTED_def]
     )
  \\ `x <> u \/ y <> u` 
       by (full_simp_tac bool_ss [NODES_def,DELE_def] \\ metis_tac[])
  THEN1 (
    `(y,x) IN tc G ==> (y,x) IN tc (DELE (u,u) G)` suffices_by 
      metis_tac[GRAPH_def,GRAPH_TC,GRAPH_CONV_THMS]
    \\ rw[PATH_NO_LOOP,DELE_def]
  )
  THEN1 rw[PATH_NO_LOOP,DELE_def]
QED

Theorem REACH_EQ:
  !G x y. GRAPH G /\ REACH x G INTER REACH y G <> {} ==>
          REACH x G = REACH y G
Proof
  rpt strip_tac
  \\ `?e. e IN REACH x G /\ e IN REACH y G`
     by (qexists_tac`CHOICE (REACH x G INTER REACH y G)`
         \\ simp[GSYM IN_INTER,CHOICE_DEF])
  \\ qpat_x_assum `_ INTER _ <> {}` kall_tac
  \\ fs[REACH_def,EXTENSION]
  \\ metis_tac[tc_rules,GRAPH_def,GRAPH_TC,FST,SND,PAIR]
QED

Theorem LOOP_EULER_LEMMA[local]:
  !G. GRAPH G /\ CONNECTED G /\ (x,x) IN G /\ DELE (x,x) G <> {} ==>
      (!y. y IN NODES G ==> y IN NODES (DELE (x,x) G)) /\
      (!y. EVEN (DEG y (DELE (x,x) G)) <=> EVEN (DEG y G))
Proof
  rw[] \\ Cases_on `y = x` \\ rw[]
  THEN1 (
    `?u v. (u,v) IN DELE (x,x) G /\ u <> x` by (
      `?u v. (u,v) IN DELE (x,x) G` by metis_tac[CHOICE_DEF,FST,SND,PAIR]
      \\ `(v,u) IN DELE (x,x) G` by metis_tac[GRAPH_CONV_THMS,GRAPH_def]
      \\ `u <> x \/ v <> x` by fs[DELE_def]
      \\ metis_tac[]
    )
    \\ `(x,u) IN tc G` by (
         fs[CONNECTED_def]
         \\ first_assum match_mp_tac
         \\ rw[NODES_def]
         \\ qexists_tac `(u,v)` \\ fs[DELE_def]
       )
    \\ `(x,u) IN tc (G DELETE (x,x))` by rw[PATH_NO_LOOP]
    \\ pop_assum (fn th =>
         `?w. (x,w) IN G DELETE (x,x)` by metis_tac[tc_cases_left,th])
    \\ rw[NODES_def]
    \\ qexists_tac `(x,w)` \\ rw[DELE_def]
  )
  THEN1 (
    fs[NODES_def]
    \\ qexists_tac `x'` \\ rw[]
    \\ Cases_on `x'` \\ fs[DELE_def]
  )
  THEN1 (
    rw[DEG_def] THEN1 fs[DELE_def]
    \\ pop_assum kall_tac
    \\ `CARD (NEIGHB x G) = CARD (NEIGHB x (DELE (x,x) G)) + 1`
         suffices_by rw[EVEN_ADD]
    \\ `x NOTIN NEIGHB x (DELE (x,x) G)`
         by rw[NEIGHB_def,DELE_def]
    \\ `NEIGHB x G = x INSERT NEIGHB x (DELE (x,x) G)`
         suffices_by rw[]
    \\ rw[NEIGHB_def,DELE_def,EXTENSION]
    \\ metis_tac[]
  )
  THEN1 (
    `(y,y) IN DELE (x,x) G <=> (y,y) IN G` by rw[DELE_def]
    \\ simp[DEG_def]
    \\ `EVEN (CARD (NEIGHB y (DELE (x,x) G))) <=> EVEN (CARD (NEIGHB y G))`
         suffices_by (simp[EVEN_ADD] \\ metis_tac[])
    \\ `NEIGHB y (DELE (x,x) G) = NEIGHB y G`
         suffices_by rw[]
    \\ rw[NEIGHB_def,DELE_def,EXTENSION]
  )
QED

Theorem DEG_PARITY_DELE:
  !G x y u. GRAPH G /\ (x,y) IN G ==>
            (EVEN (DEG u (DELE (x,y) G)) <=>
             if (x = u \/ y = u) /\ x <> y
             then ~EVEN (DEG u G) else EVEN (DEG u G))
Proof
  rpt strip_tac
  \\ Cases_on `x = y`
  THEN1 (
    rw[]
    \\ Cases_on `x = u`
    THEN1 (
      rw[]
      \\ `DEG u G = DEG u (DELE (u,u) G) + 2` suffices_by rw[EVEN_ADD]
      \\ rw[DEG_def] \\ TRY (fs[DELE_def] \\ NO_TAC)
      \\ `NEIGHB u G = u INSERT NEIGHB u (DELE (u,u) G) /\
          u NOTIN NEIGHB u (DELE (u,u) G)`
           suffices_by rw[]
      \\ rw[] 
      THEN1 (rw[NEIGHB_def,DELE_def,EXTENSION] \\ metis_tac[])
      THEN1 (rw[NEIGHB_def,DELE_def])
    )
    THEN1 (
      `(u,u) IN DELE (x,x) G <=> (u,u) IN G`
        by (simp[DELE_def] \\ metis_tac[])
      \\ rw[DEG_def,NEIGHB_def,DELE_def,EXTENSION]
    )
  )
  THEN1 (
    `!v. (v,v) IN DELE (x,y) G <=> (v,v) IN G`
       by (simp[DELE_def] \\ metis_tac[])
    \\ Cases_on `(x = u \/ y = u) /\ x <> y`
    \\ simp[DEG_def,EVEN_ADD]
    THEN1 (
      `CARD (NEIGHB u G) = CARD (NEIGHB u (DELE (x,y) G)) + 1`
        suffices_by (rw[EVEN_ADD] \\ metis_tac[])
      \\ `?v. v NOTIN (NEIGHB u (DELE (x,y) G)) /\
                NEIGHB u G = v INSERT NEIGHB u (DELE (x,y) G)`
           suffices_by (rw[] \\ rw[])
      \\ fs[] \\ rw[NEIGHB_def,DELE_def,EXTENSION]
      THEN1 (qexists_tac `y` \\ metis_tac[])
      THEN1 (qexists_tac `x` \\ metis_tac[GRAPH_def])
    )
    THEN1 (
      fs[]
      \\ `NEIGHB u G = NEIGHB u (DELE (x,y) G)`
           suffices_by (rw[EVEN_ADD] \\ metis_tac[])
      \\ rw[NEIGHB_def,DELE_def,EXTENSION]
    )
  )
QED

Definition CIRCUIT_OF_def:
  CIRCUIT_OF G x l z = (CIRCUIT x l z /\ G = PAIRS x l z)
End

Theorem PAIRS_APPEND:
  !l1 l2 x y z. PAIRS x (l1 ++ [y] ++ l2) z = PAIRS x l1 y UNION PAIRS y l2 z
Proof
  Induct \\ rw[GRAPH1_def,ADDE_def,INSERT_UNION_EQ]
QED

Theorem CIRCUIT_APPEND:
  !G1 G2 l1 l2 x y z.
    GRAPH G1 /\ GRAPH G2 /\ DISJOINT G1 G2 /\
    CIRCUIT_OF G1 x l1 y /\ CIRCUIT_OF G2 y l2 z ==>
    CIRCUIT_OF (G1 UNION G2) x (l1 ++ [y] ++ l2) z
Proof
  Induct_on `l1`
  THEN1 (
    rw[CIRCUIT_OF_def]
    THEN1 (
      irule (CONJUNCT2 CIRCUIT_rules) \\ simp[]
      \\ qspecl_then [`GRAPH1 (x,y)`,`PAIRS y l2 z`] mp_tac DISJOINT_ALT
      \\ simp[GRAPH1_def]
    )
    THEN1 simp[GRAPH1_def,ADDE_def,INSERT_UNION_EQ]
  )
  THEN1 (
    reverse (rw[CIRCUIT_OF_def])
    THEN1 simp[PAIRS_APPEND,ADDE_def,INSERT_UNION_EQ]
    THEN1 (
      `CIRCUIT_OF (PAIRS h l1 y UNION PAIRS y l2 z) h (l1 ++ [y] ++ l2) z` by (
        first_x_assum irule
        \\ simp[CIRCUIT_OF_def]
        \\ conj_tac
        THEN1 fs[ADDE_def,DISJOINT_INSERT]
        THEN1 fs[Once CIRCUIT_cases]
      )
      \\ ntac 3 (last_x_assum kall_tac)
      \\ irule (CONJUNCT2 CIRCUIT_rules)
      \\ reverse conj_tac
      THEN1 fs[CIRCUIT_OF_def]
      THEN1 (
        simp[PAIRS_APPEND]
        \\ fs[ADDE_def,DISJOINT_INSERT]
        \\ fs[Once CIRCUIT_cases]
      )
    )
  )
QED

Theorem CIRCUIT_ADD_BEG:
  !G x y l z. GRAPH G /\ (x,y) IN G /\ CIRCUIT_OF (DELE (x,y) G) y l z ==>
              CIRCUIT_OF G x (y::l) z
Proof
  rw[CIRCUIT_OF_def] \\ first_x_assum (strip_assume_tac o GSYM)
  THEN1 (rw[CIRCUIT_rules,DELE_def])
  THEN1 (rw[ADDE_DELE])
QED

Theorem CIRCUIT_ADD_END:
  !G x y l z. GRAPH G /\ (y,z) IN G /\ CIRCUIT_OF (DELE (y,z) G) x l y ==>
              CIRCUIT_OF G x (l ++ [y]) z
Proof
  rw[]
  \\ qspecl_then [`DELE (y,z) G`,`GRAPH1 (y,z)`,`l`,`[]`]
                 mp_tac CIRCUIT_APPEND
  \\ `DELE (y,z) G UNION GRAPH1 (y,z) = G`
       by (simp[Once UNION_COMM] \\ simp[GSYM ADDE_UNION,ADDE_DELE])
  \\ simp[]
  \\ disch_then match_mp_tac
  \\ rw[]
  THEN1 (
    simp[Once DISJOINT_SYM]
    \\ simp[GRAPH1_def,DISJOINT_INSERT,DELE_def]
  )
  THEN1 simp[CIRCUIT_OF_def,CIRCUIT_rules]
QED

(*
Theorem EULER1:
  !G. GRAPH G /\ CONNECTED G ==>
  !x z. x IN NODES G /\ z IN NODES G /\
        (if z = x
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
    last_assum kall_tac
    \\ `G = {} \/ G = GRAPH1 (x,y)` by rw[DELE_EMPTY_CASES]
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
    `DELE (x,y) G PSUBSET G` by rw[DELE_PSUBSET]
    \\ fs[ODD_EVEN]
    \\ Cases_on `x = y`
    THEN1 (
      rw[]
      \\ `?l. CIRCUIT_OF (DELE (x,x) G) x l z`
           suffices_by (metis_tac[CIRCUIT_ADD_BEG])
      \\ last_x_assum (mp_tac o Q.SPEC `DELE (x,x) G`)
      \\ `CONNECTED (DELE (x,x) G)` by rw[CONNECTED_DELE_LOOP]
      \\ simp[]
      \\ disch_then match_mp_tac
      \\ qspec_then `G` mp_tac LOOP_EULER_LEMMA
      \\ simp[]
    )
    THEN1 (
      `DELE (x,y) G = REACH x (DELE (x,y) G) UNION REACH y (DELE (x,y) G)`
        by rw[CONNECTED_SPLIT]
      \\ (Cases_on `REACH x (DELE (x,y) G) = {}`
          \\ Cases_on `REACH y (DELE (x,y) G) = {}`
          \\ fs[])
      (* ++ x is only connected to y; build a circuit x -- y --* z *)
      THEN1 (
        `?l. CIRCUIT_OF (DELE (x,y) G) y l z`
           suffices_by (metis_tac[CIRCUIT_ADD_BEG])
        \\ last_x_assum (qspec_then `DELE (x,y) G` mp_tac)
        \\ `CONNECTED (DELE (x,y) G)`
             by (qpat_assum `DELE _ _ = REACH _ _` SUBST1_TAC
                 \\ simp[])
        \\ simp[]
        \\ disch_then match_mp_tac
        \\ `y IN NODES (DELE (x,y) G)` by rw[GSYM REACH_NON_EMPTY]
        \\ simp[]
        \\ reverse conj_tac
        THEN1 metis_tac[DEG_PARITY_DELE]
        THEN1 (
          (* here we show that z IN NODES (REACH y (DELE (x,y) G)) *)
          Cases_on `z = x`
          THEN1 ( (* z cannot be x *)
            rw[GSYM REACH_NON_EMPTY]
            \\ `NEIGHB x (DELE (x,y) G) = {}` suffices_by (
                 `ODD (DEG x (DELE (x,y) G))` by rw[ODD_EVEN,DEG_PARITY_DELE]
                 \\ strip_tac \\ fs[DEG_def]
                 \\ Cases_on `(x,x) IN DELE (x,y) G`
                 THEN1 (fs[NEIGHB_def,EXTENSION] \\ metis_tac[])
                 THEN1 fs[]
               )
            \\ rw[NEIGHB_def,EXTENSION] \\ strip_tac
            \\ `(x,x') IN REACH x (DELE (x,y) G)`
                 by (qpat_x_assum `REACH x _ = {}` kall_tac
                     \\ rw[REACH_def,tc_rules])
            \\ fs[EXTENSION] \\ metis_tac[]
          )
          THEN1 (
            Cases_on `z = y`
            THEN1 rw[]
            THEN1 (
              `?z'. (z,z') IN G` by rw[IN_NODES]
              \\ simp[NODES_def,DELE_def]
              \\ qexists_tac `(z,z')` \\ rw[]
            )
          )
        )
      )
      (* ++ y is only connected to x; it must be that y = z *)
      THEN1 (
        reverse (Cases_on `y = z`)
        THEN1 ( (* y <> z; that is impossible *)
           `NEIGHB y (DELE (x,y) G) = {}` suffices_by (
              strip_tac
              \\ `EVEN (DEG y G)` by metis_tac[]
              \\ `ODD (DEG y (DELE (x,y) G))` by rw[ODD_EVEN,DEG_PARITY_DELE]
              \\ pop_assum mp_tac
              \\ simp[DEG_def]
              \\ Cases_on `(y,y) IN DELE (x,y) G`
              THEN1 (fs[NEIGHB_def,EXTENSION] \\ metis_tac[])
              THEN1 fs[]
           )
           \\ rw[NEIGHB_def,EXTENSION] \\ strip_tac
           \\ `(y,x') IN REACH y (DELE (x,y) G)`
                 by (qpat_x_assum `REACH y _ = {}` kall_tac
                     \\ rw[REACH_def,tc_rules])
            \\ fs[EXTENSION] \\ metis_tac[]
        )
        THEN1 (
          (* build a circuit x --* x -- y *)
          rw[] \\ full_simp_tac std_ss []
          \\ `?l. CIRCUIT_OF (DELE (x,y) G) x l x`
               suffices_by (strip_tac
                            \\ qexists_tac `l ++ [x]`
                            \\ rw[CIRCUIT_ADD_END])
          \\ last_x_assum (qspec_then `DELE (x,y) G` mp_tac)
          \\ `CONNECTED (DELE (x,y) G)`
               by (qpat_assum `DELE _ _ = REACH _ _` SUBST1_TAC
                   \\ simp[])
          \\ simp[]
          \\ disch_then match_mp_tac
          \\ `x IN NODES (DELE (x,y) G)` by rw[GSYM REACH_NON_EMPTY]
          \\ simp[DEG_PARITY_DELE]
          \\ rw[] \\ rw[]
        )
      )
      (* ++ y and x are both connected to non-empty subgraphs *)
      THEN1 (
        qmatch_assum_abbrev_tac `DELE (x,y) G = REACHx UNION REACHy`
        \\ reverse (Cases_on `DISJOINT REACHx REACHy`)
        THEN1 (
          `REACHx = REACHy` by (
            unabbrev_all_tac
            \\ irule REACH_EQ
            \\ fs[DISJOINT_DEF]
          )
          \\ unabbrev_all_tac
          \\ `?l. CIRCUIT_OF (DELE (x,y) G) y l z`
               suffices_by metis_tac[CIRCUIT_ADD_BEG]
          \\ last_x_assum (qspec_then `DELE (x,y) G` mp_tac)
          \\ `CONNECTED (DELE (x,y) G)`
               by (qpat_assum `DELE _ _ = _ UNION _` SUBST1_TAC
                   \\ pop_assum SUBST1_TAC
                   \\ simp[])
          \\ simp[DELE_PSUBSET]
          \\ disch_then match_mp_tac
          \\ `y IN NODES (DELE (x,y) G)` by rw[GSYM REACH_NON_EMPTY]
          \\ simp[]
          \\ reverse conj_tac
          THEN1 metis_tac[DEG_PARITY_DELE]
          THEN1 (
            Cases_on `z = x` THEN1 rw[GSYM REACH_NON_EMPTY]
            \\ Cases_on `z = y` THEN1 rw[GSYM REACH_NON_EMPTY]
            \\ qpat_assum `z IN _` (mp_tac o MATCH_MP IN_NODES)
            \\ disch_then (qx_choose_then `z'` assume_tac)
            \\ simp[NODES_def]
            \\ qexists_tac `(z,z')`
            \\ rw[DELE_def]
          )
        )
        THEN1 (
          (* the two reachable graphs are disjoint, we will show
             that z is in REACH y then build x --* x -- y --* z *)
          unabbrev_all_tac
          \\ `(?lx. CIRCUIT_OF (REACH x (DELE (x,y) G)) x lx x) /\
              (?ly. CIRCUIT_OF (REACH y (DELE (x,y) G)) y ly z)`
               suffices_by (
                 strip_tac
                 \\ `G = REACH x (DELE (x,y) G) UNION
                         ADDE (x,y) (REACH y (DELE (x,y) G)) ` by (
                      `ADDE (x,y) (DELE (x,y) G) = G` by rw[ADDE_DELE]
                      \\ metis_tac[ADDE_UNION,UNION_COMM,UNION_ASSOC]
                    )
                 \\ pop_assum SUBST1_TAC
                 \\ qexists_tac `lx ++ [x] ++ y::ly`
                 \\ match_mp_tac CIRCUIT_APPEND
                 \\ simp[]
                 \\ conj_tac
                 THEN1 (
                   simp[ADDE_def,DISJOINT_INSERT]
                   \\ mp_tac (PROVE[REACH_SUBSET,SUBSET_DEF]
                              ``!a G. a NOTIN G ==> a NOTIN REACH x G``)
                   \\ rw[DELE_def]
                 )
                 THEN1 (
                   irule CIRCUIT_ADD_BEG
                   \\ simp[]
                   \\ conj_tac
                   THEN1 simp[ADDE_def]
                   THEN1 (
                     `(x,y) NOTIN REACH y (DELE (x,y) G)` by (
                        mp_tac (PROVE[REACH_SUBSET,SUBSET_DEF]
                               ``!a G. a NOTIN G ==> a NOTIN REACH y G``)
                        \\ rw[DELE_def])
                     \\ simp[DELE_ADDE]
                   )
                 )
               )
          \\ conj_tac
          THEN1 (
            (* build x --* x *)
            `REACH x (DELE (x,y) G) PSUBSET G`
              by metis_tac[SUBSET_PSUBSET_TRANS,REACH_SUBSET]
            \\ last_x_assum (qspec_then `REACH x (DELE (x,y) G)` mp_tac)
            \\ simp[]
            \\ disch_then match_mp_tac
            \\ simp[GSYM REACH_NON_EMPTY]
            (* need to show x IN NODES (REACH x (DELE (x,y) G)) *)
          )
          THEN1 (
            (* build y --* z *)
          )
        )
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

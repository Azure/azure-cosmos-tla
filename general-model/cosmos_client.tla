--------------------------- MODULE cosmos_client ----------------------------
(***************************************************************************)
(* Microsoft Azure Cosmos DB TLA+ specification for the five consistency   *)
(* levels the service offers. The spec focuses on the consistency          *)
(* guarantees Cosmos DB provides to the clients, without the details of    *)
(* the protocol implementation.                                            *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, Functions, SequencesExt

Merge(s1, s2) ==
    SetToSortSeq(Range(s1) \cup Range(s2), <)

(***************************************************************************)
(* Number of regions                                                       *)
(***************************************************************************)
CONSTANT NumRegions
CONSTANT NumWriteRegions

ASSUME NumRegions \in Nat
ASSUME NumWriteRegions >= 1 /\ NumWriteRegions <= NumRegions

(***************************************************************************)
(* Number of clients per region for modeling                               *)
(***************************************************************************)
CONSTANT NumClientsPerRegion

ASSUME NumClientsPerRegion \in Nat

(***************************************************************************)
(* Consistency level                                                       *)
(* (1) strong (Linearizability)                                            *)
(* (2) bounded (Bounded Staleness)                                         *)
(* (3) session                                                             *)
(* (4) prefix (Consistent Prefix)                                          *)
(* (5) eventual                                                            *)
(***************************************************************************)
VARIABLE Consistency

\* ASSUME Consistency \in {"Strong", "Bounded_staleness", "Session", "Consistent_prefix", "Eventual"}

(* The bounded version differences in Bounded Staleness consistency *)
CONSTANT K

ASSUME K \in Nat

(* All regions in topology *)
Regions == 1..NumRegions
(* All writable regions in topology *)
WriteRegions == 1..NumWriteRegions
(* All clients with local region *)
Clients == Regions \X (1..NumClientsPerRegion)

(* Max staleness. Strong is a special case of bounded with K = 1 *)
Bound ==
    CASE Consistency = "Strong" -> {0}
        [] Consistency = "Bounded_staleness" -> -(K-1)..(K-1)
        [] Consistency = "Session" -> Int
        [] Consistency = "Consistent_prefix" -> Int
        [] Consistency = "Eventual" -> Int

(***************************************************************************)
(* All possible operations in history                                      *)
(***************************************************************************)
Operations == [type: {"write"}, data: Nat, region: WriteRegions, client: Clients]
       \union [type: {"read"}, data: Nat, region: Regions, client: Clients]

(* --algorithm cosmos_client
{

    variables (* Client operation history *)
              History = <<>>;
              
              (* Tentative log in each region *)
              Database = [r \in Regions |-> <<0>>];
              
              (* Value used by clients *)
              value = 0;  
              
    (* -------------------------------------------------------------- *)
    (* --------------------- CLIENT ACTIONS ------------------------- *)
    (* -------------------------------------------------------------- *)
    
    (* Regular write at local region *)
    macro write(v)
    {
        with (w \in WriteRegions)
        {
            when \A i, j \in Regions : Last(Database[i]) - Last(Database[j]) \in Bound;
            Database[w] := Append(@, v);
            History := Append(History, [type |-> "write",
                                        data |-> v,
                                      region |-> w,
                                      client |-> self]);
            session_token := v;
        }
    }
    
    (* Reads with consistency checks *)
    macro read()
    {
        (* We check session token for session consistency *)
        when Consistency /= "Session" \/ Last(Database[self[1]]) >= session_token;
        (* We check global value for strong consistency *)
        when Consistency /= "Strong" \/ \A i, j \in Regions : Last(Database[i]) = Last(Database[j]);
        History := Append(History, [type |-> "read",
                                    data |-> Last(Database[self[1]]),
                                  region |-> self[1],
                                  client |-> self]);
        session_token := Last(Database[self[1]]);
    }
    
    (* -------------------------------------------------------------- *)
    (* --------------------- REGION ACTIONS ------------------------- *)
    (* -------------------------------------------------------------- *)
    
    (* Asynchronously replicates from source region to destination region and merges data history *)
    macro replicate()
    {
        with (s \in WriteRegions; d \in Regions)
        {
            Database[d] := Merge(Database[d], Database[s]);
        }
    }
    
    (* -------------------------------------------------------------- *)
    (* -------------------- CLIENT PROCESSES ------------------------ *)
    (* -------------------------------------------------------------- *)
    fair process (client \in Clients)
    variable session_token = 0;
    {
        client_actions:
        while(TRUE)
        {
            either
            {
                value := value + 1;
                write(value);
            }
            or read();
        }
    }
    
    (* -------------------------------------------------------------- *)
    (* -------------------- SERVER PROCESSES ------------------------ *)
    (* -------------------------------------------------------------- *)
    fair process (CosmosDB = <<0, 0>>)
    {
        database_action:
        while(TRUE)
        {
            replicate();
        }
    }
    
}
*)
\* BEGIN TRANSLATION
VARIABLES History, Database, value, session_token

vars == << History, Database, value, session_token >>

ProcSet == (Clients) \cup {<<0, 0>>}

Init == (* Global variables *)
        /\ History = <<>>
        /\ Database = [r \in Regions |-> <<0>>]
        /\ value = 0
        (* Process client *)
        /\ session_token = [self \in Clients |-> 0]

client(self) == \/ /\ value' = value + 1
                   /\ \E w \in WriteRegions:
                        /\ \A i, j \in Regions : Last(Database[i]) - Last(Database[j]) \in Bound
                        /\ Database' = [Database EXCEPT ![w] = Append(@, value')]
                        /\ History' = Append(History, [type |-> "write",
                                                       data |-> value',
                                                     region |-> w,
                                                     client |-> self])
                        /\ session_token' = [session_token EXCEPT ![self] = value']
                \/ /\ Consistency /= "Session" \/ Last(Database[self[1]]) >= session_token[self]
                   /\ Consistency /= "Strong" \/ \A i, j \in Regions : Last(Database[i]) = Last(Database[j])
                   /\ History' = Append(History, [type |-> "read",
                                                  data |-> Last(Database[self[1]]),
                                                region |-> self[1],
                                                client |-> self])
                   /\ session_token' = [session_token EXCEPT ![self] = Last(Database[self[1]])]
                   /\ UNCHANGED <<Database, value>>

CosmosDB == /\ \E s \in WriteRegions:
                 \E d \in Regions:
                   Database' = [Database EXCEPT ![d] = Merge(Database[d], Database[s])]
            /\ UNCHANGED << History, value, session_token >>

Next == CosmosDB
           \/ (\E self \in Clients: client(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(client(self))
        /\ WF_vars(CosmosDB)

\* END TRANSLATION

-----------------------------------------------------------------------------

CombinedInit ==
    /\ Consistency \in {"Strong", "Bounded_staleness", "Session", "Consistent_prefix", "Eventual"}
    /\ Init

CombinedNext ==
    /\ Next
    /\ UNCHANGED Consistency

CombinedSpec ==
    /\ CombinedInit /\ [][CombinedNext]_<<vars, Consistency>>
    /\ \A self \in Clients : WF_vars(client(self))
        /\ WF_vars(CosmosDB)

-----------------------------------------------------------------------------

(* enable these invariants in model checker *)

(* Check elements in History are type of Opertion *)
TypeOK == {History[i] : i \in DOMAIN History} \subseteq Operations

(* Read value in any regional database history *)                       
AnyReadPerRegion(r) == \A i \in DOMAIN History : /\ History[i].type = "read"
                                                 /\ History[i].region = r
                                                 => History[i].data \in Range(Database[r]) \union {0}

(* Operation in history h is monitonic *)
Monotonic(h) == \A i, j \in DOMAIN h : i <= j => h[i].data <= h[j].data

(* Reads in region r are monotonic *)
MonotonicReadPerRegion(r) == LET reads == [i \in {j \in DOMAIN History : /\ History[j].type = "read" 
                                                                         /\ History[j].region = r}
                                          |-> History[i]]
                              IN Monotonic(reads)

(* Reads from client c are monotonic *)
MonotonicReadPerClient(c) == LET reads == [i \in {j \in DOMAIN History : /\ History[j].type = "read" 
                                                                         /\ History[j].client = c} 
                                          |-> History[i]]
                              IN Monotonic(reads)
                             
MonotonicWritePerRegion(r) == LET writes == [i \in {j \in DOMAIN History : /\ History[j].type = "write" 
                                                                           /\ History[j].region = r} 
                                            |-> History[i]]
                               IN Monotonic(writes)

(* Clients read their own writes *)
ReadYourWrite == \A i, j \in DOMAIN History : /\ i < j
                                              /\ History[i].type = "write"
                                              /\ History[j].type = "read"
                                              /\ History[i].client = History[j].client
                                              => History[j].data >= History[i].data
                                              
(* Read the latest writes *)
ReadAfterWrite == \A i, j \in DOMAIN History : /\ i < j
                                               /\ History[i].type = "write"
                                               /\ History[j].type = "read"
                                               => History[j].data >= History[i].data
                                               
Linearizability == \A i, j \in DOMAIN History : /\ i < j
                                                => History[j].data >= History[i].data

BoundedStaleness == Consistency = "Bounded_staleness" =>
                    /\ \A i, j \in Regions : Last(Database[i]) - Last(Database[j]) \in -K..K
                    /\ \A r \in Regions : MonotonicReadPerRegion(r)
                    \* /\ ReadYourWrite

ConsistentPrefix == Consistency = "Consistent_prefix" =>
                    \A r \in Regions : /\ MonotonicWritePerRegion(r)
                                       /\ AnyReadPerRegion(r)

Strong == Consistency = "Strong" =>
          /\ Linearizability
          /\ Monotonic(History)
          /\ ReadAfterWrite

Session == Consistency = "Session" =>
           /\ \A c \in Clients : MonotonicReadPerClient(c)
           /\ ReadYourWrite

Eventual == Consistency = "Eventual" =>
            \A i \in DOMAIN History :
            LET r == History[i].region
            IN History[i].data \in {Database[r][j] : j \in DOMAIN Database[r]} \union {0}

Invariant == /\ TypeOK
             /\ CASE Consistency = "Strong" -> Strong
                  [] Consistency = "Bounded_staleness" -> BoundedStaleness
                  [] Consistency = "Session" -> Session
                  [] Consistency = "Consistent_prefix" -> ConsistentPrefix
                  [] Consistency = "Eventual" -> Eventual

Liveness == <>[] (\A i, j \in Regions : Database[i] = Database[j])

-----------------------------------------------------------------------------
(* Constraint the states-space to be finite for model-checking. *)
MaxNumOp ==
    Len(History) < 7

=============================================================================
\* Authored by Cosmos DB

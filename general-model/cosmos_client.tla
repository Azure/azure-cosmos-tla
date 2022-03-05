--------------------------- MODULE cosmos_client ----------------------------
(***************************************************************************)
(* Microsoft Azure Cosmos DB TLA+ specification for the five consistency   *)
(* levels the service offers. The spec focuses on the consistency          *)
(* guarantees Cosmos DB provides to the clients, without the details of    *)
(* the protocol implementation.                                            *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

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
CONSTANT Consistency

ASSUME Consistency \in {"Strong", "Bounded_staleness", "Session", "Consistent_prefix", "Eventual"}

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
    CASE Consistency = "Strong" -> 1
        [] Consistency = "Bounded_staleness" -> K
        [] Consistency = "Session" -> 100 \* effectively infinite.
        [] Consistency = "Consistent_prefix" -> 100
        [] Consistency = "Eventual" -> 100

(***************************************************************************)
(* All possible operations in history                                      *)
(***************************************************************************)
Operations == [type: {"write"}, data: Nat, region: WriteRegions, client: Clients]
       \union [type: {"read"}, data: Nat, region: Regions, client: Clients]

(* --algorithm cosmos_client
{

    variables (* Client operation history *)
              History = <<>>;
              
              (* Latest data value in each region *)
              Data = [r \in Regions |-> 0];
              
              (* Tentative log in each region *)
              Database = [r \in Regions |-> <<>>];
              
              (* Value used by clients *)
              value = 0;
              
    define {
        \* Removing duplicates from a sequence:
        RECURSIVE RemDupRec(_,_)
        RemDupRec(es, seen) == IF es = <<>> THEN <<>>
                               ELSE IF es[1] \in seen THEN RemDupRec(Tail(es), seen)
                               ELSE <<es[1]>> \o RemDupRec(Tail(es), seen \cup {es[1]})
                                         
        RemoveDuplicates(es) == RemDupRec(es, {})
                             
        Last(s) == s[Len(s)]
    }
    
    (* -------------------------------------------------------------- *)
    (* --------------------- CLIENT ACTIONS ------------------------- *)
    (* -------------------------------------------------------------- *)
    
    (* Regular write at local region *)
    macro write(v)
    {
        with (w \in WriteRegions)
        {
            when \A i, j \in Regions : Data[i] - Data[j] < Bound;
            Database[w] := Append(@, v);
            Data[w] := v;
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
        when Consistency /= "Session" \/ Data[self[1]] >= session_token;
        (* We check global value for strong consistency *)
        when Consistency /= "Strong" \/ \A i, j \in Regions : Data[i] = Data[j];
        History := Append(History, [type |-> "read",
                                    data |-> Data[self[1]],
                                  region |-> self[1],
                                  client |-> self]);
        session_token := Data[self[1]];
    }
    
    (* -------------------------------------------------------------- *)
    (* --------------------- REGION ACTIONS ------------------------- *)
    (* -------------------------------------------------------------- *)
    
    (* Asynchronously replicates from source region to destination region and merges data history *)
    macro replicate()
    {
        with (s \in WriteRegions; d \in Regions)
        {
            Database[d] := RemoveDuplicates(SortSeq(Database[d] \o Database[s], <));
            if (Len(Database[d]) > 0)
            {
                Data[d] := Last(Database[d]);
            }
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
                write:
                value := value + 1;
                write(value);
            }
            or read: read();
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
VARIABLES History, Data, Database, value, pc

(* define statement *)
RECURSIVE RemDupRec(_,_)
RemDupRec(es, seen) == IF es = <<>> THEN <<>>
                       ELSE IF es[1] \in seen THEN RemDupRec(Tail(es), seen)
                       ELSE <<es[1]>> \o RemDupRec(Tail(es), seen \cup {es[1]})

RemoveDuplicates(es) == RemDupRec(es, {})

Last(s) == s[Len(s)]

VARIABLE session_token

vars == << History, Data, Database, value, pc, session_token >>

ProcSet == (Clients) \cup {<<0, 0>>}

Init == (* Global variables *)
        /\ History = <<>>
        /\ Data = [r \in Regions |-> 0]
        /\ Database = [r \in Regions |-> <<>>]
        /\ value = 0
        (* Process client *)
        /\ session_token = [self \in Clients |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Clients -> "client_actions"
                                        [] self = <<0, 0>> -> "database_action"]

client_actions(self) == /\ pc[self] = "client_actions"
                        /\ \/ /\ pc' = [pc EXCEPT ![self] = "write"]
                           \/ /\ pc' = [pc EXCEPT ![self] = "read"]
                        /\ UNCHANGED << History, Data, Database, value, 
                                        session_token >>

write(self) == /\ pc[self] = "write"
               /\ value' = value + 1
               /\ \E w \in WriteRegions:
                    /\ \A i, j \in Regions : Data[i] - Data[j] < Bound
                    /\ Database' = [Database EXCEPT ![w] = Append(@, value')]
                    /\ Data' = [Data EXCEPT ![w] = value']
                    /\ History' = Append(History, [type |-> "write",
                                                   data |-> value',
                                                 region |-> w,
                                                 client |-> self])
                    /\ session_token' = [session_token EXCEPT ![self] = value']
               /\ pc' = [pc EXCEPT ![self] = "client_actions"]

read(self) == /\ pc[self] = "read"
              /\ Consistency /= "Session" \/ Data[self[1]] >= session_token[self]
              /\ Consistency /= "Strong" \/ \A i, j \in Regions : Data[i] = Data[j]
              /\ History' = Append(History, [type |-> "read",
                                             data |-> Data[self[1]],
                                           region |-> self[1],
                                           client |-> self])
              /\ session_token' = [session_token EXCEPT ![self] = Data[self[1]]]
              /\ pc' = [pc EXCEPT ![self] = "client_actions"]
              /\ UNCHANGED << Data, Database, value >>

client(self) == client_actions(self) \/ write(self) \/ read(self)

database_action == /\ pc[<<0, 0>>] = "database_action"
                   /\ \E s \in WriteRegions:
                        \E d \in Regions:
                          /\ Database' = [Database EXCEPT ![d] = RemoveDuplicates(SortSeq(Database[d] \o Database[s], <))]
                          /\ IF Len(Database'[d]) > 0
                                THEN /\ Data' = [Data EXCEPT ![d] = Last(Database'[d])]
                                ELSE /\ TRUE
                                     /\ Data' = Data
                   /\ pc' = [pc EXCEPT ![<<0, 0>>] = "database_action"]
                   /\ UNCHANGED << History, value, session_token >>

CosmosDB == database_action

Next == CosmosDB
           \/ (\E self \in Clients: client(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Clients : WF_vars(client(self))
        /\ WF_vars(CosmosDB)

\* END TRANSLATION

-----------------------------------------------------------------------------

(* enable these invariants in model checker *)

(* Check elements in History are type of Opertion *)
TypeOK == {History[i] : i \in DOMAIN History} \subseteq Operations

                     
Range(s) == {s[i] : i \in DOMAIN s}

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

BoundedStaleness == /\ \A i, j \in Regions : Data[i] - Data[j] <= K
                    /\ \A r \in Regions : MonotonicReadPerRegion(r)
                    /\ ReadYourWrite

ConsistentPrefix == \A r \in Regions : /\ MonotonicWritePerRegion(r)
                                       /\ AnyReadPerRegion(r)

Strong == /\ Linearizability
          /\ Monotonic(History)
          /\ ReadAfterWrite

Session == /\ \A c \in Clients : MonotonicReadPerClient(c)
           /\ ReadYourWrite

Eventual == \A i \in DOMAIN History : 
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

---- MODULE MCCosmosDBClient ----
EXTENDS CosmosDBClient

CONSTANTS c1, k1, v1
ASSUME c1 \in ClientIDs
ASSUME k1 \in Keys
ASSUME v1 \in Values

InitImpl ==
    /\ CosmosDB!Init
    /\ network \in (
        { net \in { [id \in ClientIDs |-> <<>>] @@ (SystemID :> msgs) :
            msgs \in SeqOf(ReqMessages, 2) } :
                \A i \in DOMAIN net[SystemID] :
                    /\ /\ net[SystemID][i].type = "read"
                       => CosmosDB!ReadConsistencyOK(net[SystemID][i].consistencyLevel)
                    /\ \/ /\ net[SystemID][i].type = "write"
                          /\ WriteConsistencyLevel # SessionConsistency
                       \/ /\ net[SystemID][i].type = "read"
                          /\ net[SystemID][i].consistencyLevel # SessionConsistency
                       => net[SystemID][i].token = NoSessionToken })
    /\ returnAddrMap = <<>>

LogIndicesImpl == 1..4

CheckpointsImpl == LogIndicesImpl \cup {0}

EpochsImpl == 1..3

SpecificStateSpace ==
    \* allow LogIndices to be 1 longer than max
    \* Len(log), so that NextSessionToken doesn't
    \* technically return invalid results at max
    \* log length
    /\ Len(log) < Max(LogIndicesImpl) - 1
    /\ epoch < Max(EpochsImpl)

StalenessBoundImpl == 2
VersionBoundImpl == 4

====
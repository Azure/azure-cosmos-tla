---- MODULE CosmosDBLinearizability ----
EXTENDS Naturals, Sequences

CONSTANTS Keys, Values, NoValue
CONSTANTS StrongConsistency, BoundedStaleness,
          SessionConsistency, ConsistentPrefix,
          EventualConsistency
CONSTANTS VersionBound, StalenessBound

VARIABLES log, commitIndex, readIndex, epoch, WriteConsistencyLevel

cosmosVarsExceptLog == <<commitIndex, readIndex, epoch, WriteConsistencyLevel>>
cosmosVars == <<cosmosVarsExceptLog, log>>

CosmosDB == INSTANCE CosmosDB

---------------------------------------------------------------------

\* This is a specification that performs arbitrary writes to Cosmos DB
\* forever, set to strong consistency. It is used to prove that
\* strong consistency reads + writes are linearizable.

\* This one extra state variable holds the set of pending write tokens.
\* They are added when a write begins, and removed whem a write completes
\* (successfully or not).
VARIABLE pending

vars == <<pending, cosmosVars>>

WriteBegin ==
    \E key \in Keys, value \in Values :
        /\ CosmosDB!WritesAccepted
        /\ CosmosDB!WriteInit(key, value)
        /\ pending' = pending \cup {CosmosDB!WriteInitToken}
        /\ UNCHANGED cosmosVarsExceptLog

WriteSucceed ==
    \E token \in pending :
        /\ CosmosDB!WriteCanSucceed(token)
        /\ pending' = pending \ {token}
        /\ UNCHANGED cosmosVars

WriteFail ==
    \E token \in pending :
        /\ pending' = pending \ {token}
        /\ UNCHANGED cosmosVars

DBNext ==
    /\ CosmosDB!Next
    /\ UNCHANGED <<pending>>

LinInit ==
    /\ pending = {}
    /\ WriteConsistencyLevel = StrongConsistency
    /\ CosmosDB!Init

LinNext ==
    \/ DBNext
    \/ WriteBegin
    \/ WriteSucceed
    \/ WriteFail

LinSpec ==
    /\ LinInit
    /\ [][LinNext]_vars

---------------------------------------------------------------------

\* This other section defines an atomic key-value store with two
\* state variables:
\* - commitIndex, which increases on every write
\* - dictView, a mapping from keys to pairs of value and commitIndex as of writing
\* The model performs a number of arbitrary writes to dictView on each step, or skips steps.
\* The point is, if the Cosmos DB arbitrary writes spec refines this one, then
\* the Cosmos DB spec at strong consistency offers linearizable operations.

\* dictView is expressed as a refinement mapping over Cosmos DB reads, choosing
\* the single strong consistency read value for each key per state.
dictView == [ key \in Keys |->
    CHOOSE read \in CosmosDB!StrongConsistencyRead(key) : TRUE
]

\* The dictionary starts empty, like Cosmos DB
DictInit ==
    /\ commitIndex = 0
    /\ dictView = [ key \in Keys |-> CosmosDB!NotFoundReadResult ]

\* Due to a quirk of Cosmos DB, that commitIndex may advance more than once per step,
\* DictWrite has this recursive structure that performs `n` writes per step.
\* Each write is tagged with a distinct value of commitIndex, and represents
\* the precise point in time at which a Cosmos DB strong consistency write becomes
\* both durable and readable.
RECURSIVE DictWriteNTimes(_, _, _)

DictWriteNTimes(n, dv, idx) ==
    IF   n = 0
    THEN /\ dictView' = dv
         /\ commitIndex' = idx
    ELSE \E key \in Keys, value \in Values :
            DictWriteNTimes(
                n - 1,
                [dv EXCEPT ![key] = [value |-> value, logIndex |-> idx + 1]],
                idx + 1)

DictWrite ==
    \E n \in 1..VersionBound :
        DictWriteNTimes(n, dictView, commitIndex)

DictNext ==
    \/ DictWrite
    \/ UNCHANGED <<dictView, commitIndex>>

DictSpec == DictInit /\ [][DictNext]_<<dictView, commitIndex>>

---------------------------------------------------------------------

SpecificStateSpace ==
    /\ epoch < 3
    /\ Len(log) < 4

Alias == [
    dictView |-> dictView,

    log |-> log,
    commitIndex |-> commitIndex,
    readIndex |-> readIndex,
    epoch |-> epoch,
    WriteConsistencyLevel |-> WriteConsistencyLevel
]

====
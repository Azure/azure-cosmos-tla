---- MODULE RefineGeneralModel ----
EXTENDS Naturals, FiniteSetsExt, Sequences, SequencesExt

StrongConsistency == "Strong"
BoundedStaleness == "Bounded_staleness"
SessionConsistency == "Session"
ConsistentPrefix == "Consistent_prefix"
EventualConsistency == "Eventual"

VARIABLES Consistency, History, Database, value, session_token
vars == <<Consistency, History, Database, value, session_token>>

K == 2
StalenessBound == K
VersionBound == 100

GeneralModel == INSTANCE cosmos_client WITH
    NumRegions <- 2,
    NumClientsPerRegion <- 2,
    NumWriteRegions <- 1

\* The set of log indices for the CosmosDB model.
\* It summarizes all writes in any region for
\* GeneralModel, where each "value" in GeneralModel
\* corresponds directly to a log index.
\* The remaining semantics, like what should be
\* readable when, are left to commitIndex.
LOCAL dbIdxs ==
    UNION {
            { Database[i][j]
                : j \in DOMAIN Database[i]}
            : i \in DOMAIN Database }

\* The commitIndex is the latest write that is
\* replicated across all regions.
commitIndex ==
    Max({idx \in dbIdxs :
        \A i \in DOMAIN Database :
            \E j \in DOMAIN Database[i] :
                Database[i][j] = idx})

\* GeneralModel doesn't really have a readIndex, so we just leave it
\* at 0
readIndex == 0

\* GeneralModel is for one hypothetical key and value, so we just use
\* dummy constants "key" and "value"
log ==
    [ i \in dbIdxs \ {0} |->
        [key |-> "key", value |-> "value"]]

\* The histories of the two models match by removing all the reads from
\* History, and adding dummy information for all the missing fields in
\* writeHistory. Writes are never considered to succeed or fail, because
\* there is no such concept in GeneralModel. Writes happen to become
\* durable at some point, but e.g there is no specific action for a
\* strongly consistent write succeeding (being globally replicated),
\* it just happens at some point.
\* This can also happen in simple-model if a write remains in state "init",
\* so writeHistory can be translated using just "init".
writeHistory ==
    LET onlyWrites == SelectSeq(History, LAMBDA elem : elem.type = "write")
    IN  [ i \in DOMAIN onlyWrites |->
            [
                token |-> [checkpoint |-> onlyWrites[i].data, epoch |-> 1],
                key |-> "key",
                value |-> "value",
                state |-> "init"
            ]
        ]

\* Because there is only one key (and one value), the value that was read
\* is generally irrelevant. The "value" in GeneralModel matches the
\* logIndex field, indicating which element of the log was read.
read ==
    LET onlyReads == SelectSeq(History, LAMBDA elem : elem.type = "read")
    IN  IF   onlyReads # <<>> /\ Last(onlyReads).data # 0
        THEN [ logIndex |-> Last(onlyReads).data, value |-> "value" ]
        ELSE [ logIndex |-> 0, value |-> "NoValue" ]

Values == {"value"}
Keys == {"key"}
NoValue == "NoValue"

CosmosDB == INSTANCE CosmosDBWithReads WITH
    readKey <- "key",
    WriteConsistencyLevel <- Consistency,
    ReadConsistency <- Consistency,
    epoch <- 1

GSpec == GeneralModel!CombinedSpec

CSpec == CosmosDB!RSpec

THEOREM GSpec => CSpec

-----------------------------------------------------------------------------

SpecificStateSpace ==
    /\ vars # vars'
    /\ Len(History) < 5

NatImpl == 1..10

Alias == [
    Consistency |-> Consistency,
    History |-> History,
    Database |-> Database,
    value |-> value,
    session_token |-> session_token,
    log |-> log,
    read |-> read,
    commitIndex |-> commitIndex,
    writeHistory |-> writeHistory
]

====
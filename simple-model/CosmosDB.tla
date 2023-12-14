---- MODULE CosmosDB ----
EXTENDS Sequences, Naturals, FiniteSets, FiniteSetsExt

CONSTANTS StrongConsistency, BoundedStaleness,
          SessionConsistency, ConsistentPrefix,
          EventualConsistency

ConsistencyLevels == {StrongConsistency, BoundedStaleness,
                      SessionConsistency, ConsistentPrefix,
                      EventualConsistency}


\* This comment represents how WriteConsistencyLevel should be understood;
\* as a constant you can choose from ConsistencyLevels.
\* It's a state variable so model checking can operate across all
\* consistency levels at once.
\* 
\* If your use of this spec needs a single consistency level, consider
\* that you can conjoin the following constraint to your Init operator:
\* /\ WriteConsistencyLevel = StrongConsistency
\* /\ CosmosDB!Init
\* 
\* CosmosDB!Init (referencing the Init in this file) will also state
\* WriteConsistencyLevel \in ConsistencyLevels, but if
\* WriteConsistencyLevel = ConsistencyLevels appears first, then only that
\* single value will be explored (the broader requirement is still true,
\* just restricted by the narrower condition added above).
\*
\* If you really need a constant value (e.g for some refinements),
\* then unfortunately you have to just uncomment the two lines below and
\* comment out all the references to WriteConsistencyLevel as a variable.
\*
\* CONSTANT WriteConsistencyLevel
\* ASSUME WriteConsistencyLevel \in ConsistencyLevels

LogIndices == Nat \ {0}

Checkpoints == Nat

Epochs == Nat \ {0}

\* StalenessBound and VersionBound together govern whether writes will be
\* accepted:
\* - StalenessBound, with consistency BoundedStaleness, indicates the maximum
\*   distance between Len(log) and commitIndex. Writes beyond that are
\*   rejected.
\* - VersionBound, at all consistency levels, indicates the maximum distance
\*   between Len(log) and readIndex. Writes beyond that are rejected.
\* A VersionBound or StalenessBound of 0 would mean no writes are accepted (as
\* per the definition of WritesAccepted below).
CONSTANT StalenessBound, VersionBound
ASSUME StalenessBound \in Nat \ {0}
ASSUME VersionBound \in Nat \ {0}

\* Session tokens represent a point in the log, as well as a particular "epoch".
\* Each session-consistent read and write will produce an updated token, and
\* a client that keeps using each updated token will see an effect similar to
\* strong consistency, but with the same effective durability as eventual consistency.
\* 
\* If the "epoch" has changed, all currently valid session tokens become invalid.
\* This is because session consistency operations have no actual durability guarantees beyond
\* eventual consistency: the right pattern of machine or replica failures can lose
\* your session data, so continuing to serve pre-failure session tokens could violate
\* session consistency guarantees.
\* Session consistency only gives the appearance of strong consistency
\* _as long as Cosmos DB doesn't drop your session token_, which it may do at any time.
\*
\* Note also that session tokens happen to uniquely identify any write operation.
\* The checkpoint indicates the position in the log, and the epoch distinguishes
\* multiple writes to the same log index when data loss erased the previous value
\* (thus increasing epoch).
\* This property can be used to track individual write operations even at
\* other consistency levels.
\* See property: SessionTokensUniquelyIdentifyWrites
SessionTokens == [
    checkpoint: Checkpoints,
    epoch: Epochs
]

\* The "not a session token" session token. It precedes all session tokens,
\* and should be used when no session token is known / available.
\* It is not a valid session token itself, but is compatible with them.
\*
\* It is not a member of SessionTokens because it has an epoch of 0,
\* which is special-cased such that it is valid at all epochs.
\* A read or write operation can be given this token, and that
\* operation should return a full session token.
\*
\* The NoSessionToken -> SessionTokens pipeline is not implemented
\* directly in this file. Look at CosmosDBClient to see how it's done.
\* The reads defined in this file will just always accept NoSessionToken
\* as some arbitrarily valid session token.
NoSessionToken == [
    checkpoint |-> 0,
    epoch |-> 0
]

MaybeSessionTokens ==
    SessionTokens \cup {NoSessionToken}

\* Session tokens are partially ordered.
\* For the same epoch, two session tokens form a valid succession
\* if the "previous" one has a lower or equal checkpoint in the
\* log than the "next" one.
SessionTokenLEQ(token1, token2) ==
    /\ token1.epoch = token2.epoch \/ token1.epoch = 0
    /\ token1.checkpoint <= token2.checkpoint

\* Keys is a set with arbitrary but distinguishable elements.
\* Values is a set with arbitrary but distinguishable elements.
\* NoValue is a special marker value, used to differentiate "key not found"
\* and "no results possible at your consistency level". If one possible
\* result of a read is NoValue, it means a corresponding request could
\* return "not found". If a result set is entirely empty, the system's
\* only valid behavior is to stall for time or return an error.
CONSTANTS Keys, Values, NoValue

MaybeValues == Values \cup {NoValue}

ValidReadResults == [
    logIndex: LogIndices,
    value: Values
]

\* The result a read will have if no value can be found.
NotFoundReadResult == [
    logIndex |-> 0,
    value |-> NoValue
]

ReadResults ==
    ValidReadResults \cup {NotFoundReadResult}

ReadsLEQ(r1, r2) == r1.logIndex <= r2.logIndex

ReadsLT(r1, r2) == r1.logIndex < r2.logIndex

ASSUME \A r \in ValidReadResults :
    /\ ReadsLT(NotFoundReadResult, r)
    /\ ReadsLEQ(NotFoundReadResult, r)

ASSUME \A r1 \in ReadResults :
    \E r2 \in ReadResults : ReadsLEQ(r1, r2)

\* The log keeps a record of all (give or take data loss) writes that have been performed.
\* Log entries contain one key-value pair each, modeled as a record
\* so the code handling records is easier to read than e.g with tuples.
LogEntries ==
    [
        key: Keys,
        value: Values
    ]

Logs == Seq(LogEntries)

---------------------------------------------------------------------

\* The system itself is modeled as a collection read operators and write actions.
\* Both reads and writes are implemented separately for each consistency level.
\* Read operators use the current state of system to generate the set of allowable
\* values reading a given key is allowed to return at any given point.
\* Write actions, when active, will mutate system state by leaving a record of the
\* write having occurred in the log.

\* Additionally, commitIndex, readIndex, and epoch express a high-level view of
\* underlying processes like replication and failure recovery:
\* - the commitIndex indicates a position in the log (or 0 for no position)
\*   before which data is durable. One can think of this as tracking global consensus,
\*   and in fact strongly consistent reads will always return the latest relevant
\*   information whose index is <= commitIndex.
\* - the readIndex arbitrarily lags behind the commitIndex, and models the point
\*   before which _every single replica in the entire system_ has already replicated
\*   the data in the log. No operation should ever return out of sync data staler
\*   than this point in the log, because by definition no replica can be staler than
\*   this point in the log.
\* - the epoch increments strictly monotonically whenever  log  is non-deterministically
\*   truncated in the range (commitIndex+1)..Len(log)), modeling loss of uncommitted data
\*   due to node failures when all session tokens of the current epoch become invalid.
\*   Thus, Epoch is only used by session consistency to detect data loss due to truncation
\*   and prevent invalid reads/writes when session consistency can no longer be guaranteed
\*   for a given token.
\*
\* WriteConsistencyLevel is conceptually a constant, i.e., [][UNCHANGED WriteConsistencyLevel]_vars.
\* Making it an unchanging state variable allows it to modelcheck multiple/all consistency levels
\* at once. In the real system, the WriteConsistencyLevel is a system-wide setting indicating
\* at what consistency level writes are performed.  It cannot be changed at runtime.

VARIABLES log, commitIndex, readIndex, epoch
VARIABLE WriteConsistencyLevel \* conceptually a constant, will never change!

vars == <<log, commitIndex, readIndex, epoch, WriteConsistencyLevel>>

TypesOK ==
    /\ log \in Logs
    /\ commitIndex \in Checkpoints
    /\ readIndex \in Checkpoints
    /\ epoch \in Epochs
    /\ WriteConsistencyLevel \in ConsistencyLevels

\* Assuming session-consistent reads and writes,
\* this operator describes the set of all session tokens that could be
\* acquired during the current state, independent of session-consistent
\* reads and writes.
\*
\* Note that the range of possible checkpoints is very broad: if the newest
\* write to a key is very old, the current spec will consider the returned
\* token's checkpoint to point to that oldest index, even if 
\* the checkpoint is older than readIndex.
AcquirableSessionTokens == [
    epoch: {epoch},
    checkpoint: 0..(Len(log) + 1) \* +1 to account for incomplete writes
]

\* Whether the database's current state accepts writes.
\* This is based on two conditions:
\* - whether the number of not-fully-propagated writes exceeds
\*   VersionBound
\* - whether, under bounded staleness, the staleness bound will
\*   be met by any incoming writes
WritesAccepted ==
    /\ Len(log) - readIndex < VersionBound
    /\ ((WriteConsistencyLevel = BoundedStaleness) =>
        \* this doesn't use <= because then it would
        \* allow writes that push Len(log) one unit too far
        Len(log) - commitIndex < StalenessBound)

\* This operator initiates a write, adding it to the log.
\* It is only useful alongside other constructs, such as:
\* - WritesAccepted
\* - WriteInitToken
WriteInit(key, value) ==
    /\ log' = Append(log, [
            key |-> key,
            value |-> value
       ])

\* Adjacent to WriteInit, this operator will return a token
\* representative of that write.
\* This token is suitable both as a fresh session token, and as an ephemeral
\* token tracking the progress of a write from init to success or failure.
WriteInitToken == [
    epoch |-> epoch,
    checkpoint |-> Len(log) + 1
]

SessionTokenIsValid(token) ==
    SessionTokenLEQ(token, WriteInitToken)

UpdateTokenFromRead(origToken, read) == [
    epoch |-> epoch,
    checkpoint |-> Max({origToken.checkpoint, read.logIndex})
]

\* This predicate indicates whether a write identified by the given
\* token can succeed. Writes can always happen to fail, but successful
\* writes must meet the conditions listed here.
WriteCanSucceed(token) ==
    /\ SessionTokenIsValid(token)
    /\ (WriteConsistencyLevel = StrongConsistency =>
        /\ token.epoch = epoch
        /\ token.checkpoint <= commitIndex)

\* This predicate indicates whether a read consistency is
\* valid, given a particular configured write consistency.
\* A read consistency is valid if it is not stronger than
\* the configured write consistency.  In other words, the
\* write consistency level defines the upper bound for the
\* strongest read consistency level that can be used.
ReadConsistencyOK(level) ==
    CASE WriteConsistencyLevel = StrongConsistency ->
            TRUE
      [] WriteConsistencyLevel = BoundedStaleness ->
            level # StrongConsistency
      [] WriteConsistencyLevel = SessionConsistency ->
            level \notin {StrongConsistency, BoundedStaleness}
      [] WriteConsistencyLevel = ConsistentPrefix ->
            level \in {ConsistentPrefix, EventualConsistency}
      [] WriteConsistencyLevel = EventualConsistency ->
            level = EventualConsistency

\* Attempting to read at a higher consistency level than the configured write consistency 
\* has undefined behavior. In this instance, we've chosen to map an invalid read consistency 
\* level to an empty read (we also considered mapping an invalid read consistency level to 
\* TLC!Assert(...). However, this specification should remain independent of the TLC module).
CheckReadConsistency(level, read) ==
    IF   ReadConsistencyOK(level)
    THEN read
    ELSE {} \* invalid read consistency level

\* This operator generalizes all possible read operations, since
\* they all follow a common pattern. It returns a set of possible
\* results, a subset of ReadResults.
\* For a given key, a read can be entirely defined by a value and a flag:
\* - point is a point in the log to which the read should be applied.
\*   for log entries at or "before" (index <=) point, the latest
\*   value associated with key will be included in the result.
\*   If the log at or before point does not mention the given key at all,
\*   then the result set will include NotFoundReadResult.
\*   An empty set as a result means the read is not possible; any valid read, even
\*   one that returns a "not found" result, will have at least one element in
\*   its set.
\* - allowDirty controls a secondary behavior: for elements of the log
\*   whose index > point, if allowDirty = TRUE then they will also
\*   be included in the result set. If allowDirty = FALSE, then only
\*   the single latest value whose index <= point will be in the result set.
GeneralRead(key, index, allowDirty) ==
    LET maxCandidateIndices == { i \in DOMAIN log :
            /\ log[i].key = key
            /\ i <= index }
        allIndices == { i \in DOMAIN log :
            /\ allowDirty
            /\ log[i].key = key
            /\ i > index }
    IN  { [logIndex |-> i, value |-> log[i].value]
          : i \in allIndices \cup (
            IF   maxCandidateIndices # {}
            THEN {Max(maxCandidateIndices)}
            ELSE {}) } \cup 
        (IF   maxCandidateIndices = {}
         THEN {NotFoundReadResult}
         ELSE {})

StrongConsistencyRead(key) ==
    CheckReadConsistency(
        StrongConsistency,
        GeneralRead(key, commitIndex, FALSE))

BoundedStalenessRead(key) ==
    CheckReadConsistency(
        BoundedStaleness,
        GeneralRead(key, commitIndex, TRUE))

SessionConsistencyRead(token, key) ==
    \* session token strictly becomes invalid on epoch change.
    \* being less strict about this, e.g by using an inequality,
    \* will sometimes allow a session consistent client to see
    \* non-monotonic behavior due to observing log truncations
    CheckReadConsistency(
        SessionConsistency,
        IF   \/ epoch = token.epoch
             \* if no session token is provided, token.checkpoint = 0.
             \* this means we are allowed to return any eventually
             \* consistent result, from which a session token and
             \* corresponding new session can be derived.
             \* see: SessionTokenFromRead
             \/ token = NoSessionToken
        THEN LET sessionIndex == Max({token.checkpoint, readIndex})
             IN  GeneralRead(key, sessionIndex, TRUE)
        ELSE {})

ConsistentPrefixRead(key) ==
    \* From a client perspective, consistent prefix and eventual
    \* consistency are the same.
    \* Consistent prefix as documented (https://docs.microsoft.com/en-us/azure/cosmos-db/consistency-levels#consistent-prefix-consistency)
    \* only applies to individual replicas, and queries are load-balanced
    \* between different replicas. Therefore, for a given read, a client
    \* can see any permutation of values beyond the readIndex.
    CheckReadConsistency(
        ConsistentPrefix,
        GeneralRead(key, readIndex, TRUE))

EventualConsistencyRead(key) ==
    CheckReadConsistency(
        EventualConsistency,
        GeneralRead(key, readIndex, TRUE))

---------------------------------------------------------------------
\* actions and main spec

\* Expand the prefix of the log that can no longer be lost.
\* In reality, this and IncreasereadIndex correspond to the
\* human-assisted process of ensuring propagation and
\* replication happens such that durability is guaranteed.
IncreaseReadIndexAndOrCommitIndex ==
    /\ commitIndex' \in commitIndex..Len(log)
    /\ readIndex' \in readIndex..commitIndex'
    /\ UNCHANGED <<log, epoch, WriteConsistencyLevel>>

\* Any data that is not part of the checkpointed log prefix
\* (see above) may be lost at any time. Operations that
\* require durability would wait until the commitIndex
\* "catches up" to ensure the data they add to the log is not
\* lost.
TruncateLog ==
    \E i \in (commitIndex+1)..Len(log) :
        /\ log' = SubSeq(log, 1, i - 1)
        /\ epoch' = epoch + 1
        /\ UNCHANGED <<readIndex, commitIndex, WriteConsistencyLevel>>

Init ==
    /\ log = <<>>
    /\ readIndex = 0
    /\ commitIndex = 0
    /\ epoch = 1
    /\ WriteConsistencyLevel \in ConsistencyLevels

\* This relation models all possible log actions, without performing any write.
\* To check general features of this specification, see CosmosDBProps.
\* To use this specification as part of your own, look at the show*simple.tla or
\* CosmosDBClient specs to see how specific writes should be modeled.
Next ==
    \/ IncreaseReadIndexAndOrCommitIndex
    \/ TruncateLog

====
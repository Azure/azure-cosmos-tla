---- MODULE CosmosDBProps ----
EXTENDS CosmosDB, Bags, SequencesExt

WriteInitState == "init"
WriteSucceededState == "succeeded"
WriteFailedState == "failed"

WriteStates == {
    WriteInitState,
    WriteSucceededState,
    WriteFailedState
}

WriteHistoryEntries == [
    token: SessionTokens,
    key: Keys,
    value: Values,
    state: WriteStates
]

WriteHistories == SubBag(SetToBag(WriteHistoryEntries))

AddToBag(bag, elem) ==
    bag (+) SetToBag({elem})

RemoveFromBag(bag, elem) ==
    bag (-) SetToBag({elem})

\* writeHistory tracks in-progress and completed writes in the system.
\* It is a bag of records containing key, value, success/failure/in-progress,
\* and write tokens which represent points in the log where the write should be,
\* and the epoch in which the write took place
VARIABLE writeHistory
varsWithHistory == <<vars, writeHistory>>

WTypesOK ==
    /\ TypesOK
    \* writeHistory will be a sequence of HistoryEntries, recording the sequence
    \* of writes that were performed in the system
    /\ writeHistory \in WriteHistories

\* write-related actions

\* Begin a write. this means the DB has received a write request and has begin
\* acting on it. Immediately adding the value to the log is intended.
WriteBegin ==
    \E key \in Keys, value \in Values :
        /\ WritesAccepted
        /\ WriteInit(key, value)
        /\ LET modHistory(initState) ==
                /\ writeHistory' = AddToBag(writeHistory, [
                    token |-> WriteInitToken,
                    key |-> key,
                    value |-> value,
                    state |-> initState
                   ])
           IN  \/ /\ WriteCanSucceed(WriteInitToken)
                  /\ modHistory(WriteSucceededState)
               \/ /\ modHistory(WriteInitState)
        /\ UNCHANGED <<readIndex, commitIndex, epoch, WriteConsistencyLevel>>

\* When a write succeeds, and the DB would report that success to the client.
\* Depending on WriteConsistencyLevel, this can either freely happen at any time,
\* or it has some restrictions.
WriteSuccess ==
    \E record \in DOMAIN writeHistory :
        /\ record.state = WriteInitState
        /\ WriteCanSucceed(record.token)
        /\ writeHistory' = AddToBag(
            RemoveFromBag(writeHistory, record),
            [record EXCEPT !.state = WriteSucceededState])
        /\ UNCHANGED <<log, readIndex, commitIndex, epoch, WriteConsistencyLevel>>

\* When a write fails, for whatever reason. The reason is left implicit, but in principle
\* this can always happen for any reason.
WriteFail ==
    \E record \in DOMAIN writeHistory :
        /\ record.state = WriteInitState
        /\ writeHistory' = AddToBag(
            RemoveFromBag(writeHistory, record),
            [record EXCEPT !.state = WriteFailedState])
        /\ UNCHANGED <<log, readIndex, commitIndex, epoch, WriteConsistencyLevel>>

StateOps ==
    /\ UNCHANGED writeHistory
    /\ Next

WriteOps ==
    \/ WriteBegin
    \/ WriteSuccess
    \/ WriteFail

WInit ==
    /\ Init
    /\ writeHistory = <<>>

WNext ==
    \/ StateOps
    \/ WriteOps

Spec ==
    /\ WInit /\ [][WNext]_varsWithHistory
    \* assuming a write will eventually succeed, or at least give up
    \* without waiting forever, WritesEventuallyComplete asserts that
    \* there is no case where neither of those things can happen
    /\ WF_varsWithHistory(WriteSuccess \/ WriteFail)

\* Below are all of the correctness properties, some of which are
\* written in terms of the writeHistory variable to capture possible writes.

---------------------------------------------------------------------

\* sanity rules for readIndex and commitIndex. they should
\* progress monotonically
PointsValid ==
    [][/\ readIndex <= commitIndex
       /\ readIndex <= readIndex'
       /\ commitIndex <= commitIndex']_vars

\* type-like invariants

ReadsOK(read(_)) ==
    \A key \in Keys :
        /\ read(key) \subseteq ReadResults
        /\ \A r \in read(key) :
            SessionTokenIsValid(
                UpdateTokenFromRead(NoSessionToken, r))

NewSessionTokensOK ==
    AcquirableSessionTokens \subseteq SessionTokens

StrongConsistencyReadsOK ==
    ReadConsistencyOK(StrongConsistency)
    => ReadsOK(StrongConsistencyRead)

BoundedStalenessReadsOK ==
    ReadConsistencyOK(BoundedStaleness)
    => ReadsOK(BoundedStalenessRead)

SessionConsistencyReadsOK ==
    ReadConsistencyOK(SessionConsistency)
    =>
    \A token \in MaybeSessionTokens :
        /\ ReadsOK(LAMBDA key : SessionConsistencyRead(token, key))
        /\ \A key \in Keys :
            \A read \in SessionConsistencyRead(token, key) :
                SessionTokenLEQ(token, UpdateTokenFromRead(token, read))

ConsistentPrefixReadsOK ==
    ReadConsistencyOK(ConsistentPrefix)
    => ReadsOK(ConsistentPrefixRead)

EventualConsistencyReadsOK ==
    ReadConsistencyOK(EventualConsistency)
    => ReadsOK(EventualConsistencyRead)

VersionBoundOK ==
    Len(log) - readIndex <= VersionBound

\* If two records are different, then their tokens are necessarily different.
\* Also, writeHistory should not contain the same record/write twice.
HistoryTokensUnique ==
    /\ \A record1, record2 \in DOMAIN writeHistory :
        record1 # record2 => record1.token # record2.token
    /\ \A record \in DOMAIN writeHistory :
        writeHistory[record] <= 1

---------------------------------------------------------------------

\* Any session token uniquely identifies a possible write.
\* This works because a session token is a log index and
\* an epoch. For the same epoch, the log can only grow, so
\* each log index unambiguously identifies a single append
\* to the log. For different epochs, the log may shrink,
\* so the epoch is included to distinguish re-appending the same
\* log element before and after an epoch increment.
SessionTokensUniquelyIdentifyWrites ==
    \A token \in SessionTokens, key \in Keys, value \in Values :
        [](/\ token.epoch = epoch
           /\ token.checkpoint \in DOMAIN log
           /\ log[token.checkpoint].key = key
           /\ log[token.checkpoint].value = value
           =>
           []\/ token.epoch # epoch
             \/ (token.checkpoint \in DOMAIN log =>
                    /\ log[token.checkpoint].key = key
                    /\ log[token.checkpoint].value = value))

\* commitIndex implies that all elements of log whose index
\* is <= commitIndex will always remain unchanged
CommitIndexImpliesDurability ==
    \A checkpoint \in Checkpoints :
        \A prefix \in SeqOf(LogEntries, checkpoint) :
            [](/\ checkpoint = commitIndex
               /\ \/ log = <<>> /\ prefix = <<>>
                  \/ SubSeq(log, 1, checkpoint) = prefix
               =>
               [](IF   log = <<>>
                  THEN /\ checkpoint = 0
                       /\ prefix = <<>>
                  ELSE /\ Len(log) >= checkpoint
                       /\ SubSeq(log, 1, checkpoint) = prefix))

\* all writes that begin will eventually complete or fail
\* by assumption of token uniqueness, these existentials
\* should be sufficient to find the same write in the writeHistory
\* each time
WritesEventuallyComplete ==
    \A token \in SessionTokens :
        /\ \E record \in DOMAIN writeHistory :
            /\ record.token = token
            /\ record.state = WriteInitState
        ~>
        /\ \E record \in DOMAIN writeHistory :
            /\ record.token = token
            /\ record.state \in {
                WriteSucceededState,
                WriteFailedState
               }

---------------------------------------------------------------------
\* invariants and properties grouped by consistency level

ObsoleteValues(key) ==
    { log[i].value : i \in { i \in DOMAIN log :
        /\ i <= readIndex
        /\ log[i].key = key
        /\ \E j \in (i+1)..readIndex : log[j].key = key } }

\* Asserts that a given read operation's results are "low monotonic".
\* This is a very weak condition, which just means that the earliest
\* value a given read operation can return increases monotonically
\* over time. This is true of all read types, because the readIndex,
\* which should govern the earliest allowable read, increases
\* monotonically itself.
IsLowMonotonic(read(_)) ==
    \A key \in Keys :
        LET low == CHOOSE r1 \in read(key) :
                \A r2 \in read(key) :
                    ReadsLEQ(r1, r2)
        IN  /\ read(key) # {}
            /\ read(key)' # {}
            => ReadsLEQ(low, low')

\* Asserts that a given read operation must always return
\* either a unique result or nothing. This is called
\* "consistent" because the alternative, that there might
\* be more than one valid read result for the same key,
\* means that, without any changes in system state, multiple
\* executions of the same read operation may "jump around"
\* between multiple possible results.
\* This property only holds for strong consistency.
IsConsistent(read(_)) ==
    \A key \in Keys :
        Cardinality(read(key)) \in {0, 1}

\* No read operations may return "obsolete values".
\* That is, no value that has a more recent version recorded in
\* a log entry whose index <= readIndex may be returned, because,
\* by definition, there should not exist a replica or region that
\* has stale enough data for that to be possible.
FollowsReadIndex(read(_)) ==
    \A key \in Keys :
        \A v1 \in ObsoleteValues(key) :
            v1 \notin read(key)

\* StrongConsistency
\* https://docs.microsoft.com/en-us/azure/cosmos-db/consistency-levels#strong-consistency

\* this is a log-based formulation of the "read after write"
\* property, requiring that a strongly consistent read may
\* not ignore any more recent durable log entry for a certain
\* key. This is weaker than the next property, however, because
\* the log may be truncated. The next property, using the complete
\* write writeHistory, would catch e.g rogue log truncations.
StrongConsistencyReadsGiveLatestDurableSCValue ==
    ReadConsistencyOK(StrongConsistency) =>
    \A key \in Keys :
        \A r1 \in StrongConsistencyRead(key) :
            \lnot \E i \in DOMAIN log :
                /\ i <= commitIndex
                /\ log[i].key = key
                /\ ReadsLT(r1, [logIndex |-> i, value |-> log[i].value])

\* this is a second "read after write" property, written
\* in terms of writeHistory: any strongly consistent
\* read must not return a value with a smaller log index
\* than some successful write in the write log.
StrongConsistencyReadsGiveLatestSuccessfulWrite ==
    WriteConsistencyLevel = StrongConsistency =>
    \A key \in Keys :
        \A r1 \in StrongConsistencyRead(key) :
            \lnot \E record \in DOMAIN writeHistory :
                /\ record.key = key
                /\ record.state = WriteSucceededState
                /\ record.token.checkpoint > r1.logIndex

StrongConsistencyReadsConsistent ==
    ReadConsistencyOK(StrongConsistency) =>
    IsConsistent(StrongConsistencyRead)

\* this is the read-your-writes property, guaranteeing that
\* a strong consistency write that succeeds will be witnessed by any
\* following reads
StrongConsistencyCommittedWritesDurable ==
    \A token \in SessionTokens :
        [](/\ WriteConsistencyLevel = StrongConsistency
           /\ \E record \in DOMAIN writeHistory :
                /\ record.token = token
                /\ record.state = WriteSucceededState
           =>
           [](/\ WriteConsistencyLevel = StrongConsistency
              /\ \E record \in DOMAIN writeHistory :
                /\ record.token = token
                /\ \A read \in StrongConsistencyRead(record.key) :
                        token.checkpoint <= read.logIndex))


StrongConsistencyReadsMonotonic ==
    [][ReadConsistencyOK(StrongConsistency)
       =>
       \A key \in Keys :
        \A r1 \in StrongConsistencyRead(key) :
            \A r2 \in StrongConsistencyRead(key)' :
                ReadsLEQ(r1, r2)]_vars

StrongConsistencyReadsFollowReadIndex ==
    ReadConsistencyOK(StrongConsistency) =>
    FollowsReadIndex(StrongConsistencyRead)

\* BoundedStaleness
\* https://docs.microsoft.com/en-us/azure/cosmos-db/consistency-levels#bounded-staleness-consistency

BoundedStalenessReadsLowMonotonic ==
    [][ReadConsistencyOK(BoundedStaleness) =>
       IsLowMonotonic(BoundedStalenessRead)]_vars

BoundedStalenessReadsFollowReadIndex ==
    ReadConsistencyOK(BoundedStaleness) =>
    FollowsReadIndex(BoundedStalenessRead)

\* this is the principal property guaranteed by bounded staleness:
\* there will never be more than StalenessBound non-durable writes
\* at once.
\* This way of writing the property is sufficient, because
\* CommitIndexImpliesDurability is independently true.
BoundedStalenessIsBounded ==
    WriteConsistencyLevel = BoundedStaleness
    =>
    Len(log) - commitIndex <= StalenessBound

\* SessionConsistency
\* https://docs.microsoft.com/en-us/azure/cosmos-db/consistency-levels#session-consistency

\* Within the same session, reads should be monotonic.
\* Sequential reads within the same session are identified
\* as session tokens for which SessionTokenLEQ is true.
\* Therefore, we can select sequential same-session reads
\* by choosing pairs of tokens that satisfy this condition.
\* Beyond this restriction, this is a monotonicity requirement,
\* that the "earlier" read must only contain values for which
\* a successor value exists in the "later" read, and vice versa
\* for the "later" read, which is the monotonic property adapted
\* to read with multiple possible results.
SessionConsistencyReadsMonotonicPerTokenSequence ==
    \A token1, token2 \in SessionTokens, key \in Keys :
        /\ ReadConsistencyOK(SessionConsistency)
        /\ SessionTokenLEQ(token1, token2)
        =>
        LET read1 == SessionConsistencyRead(token1, key)
            read2 == SessionConsistencyRead(token2, key)
        IN  /\ \A v2 \in read2 :
                \E v1 \in read1 :
                    ReadsLEQ(v1, v2)
            /\ \A v1 \in read1 :
                \E v2 \in read2 :
                    ReadsLEQ(v1, v2)

\* This is "read my writes", adapted to account for token sequences.
\* For any successful write with token1, all reads with token2,
\* which forms a sequence with token1, must return at least the
\* value written, or some later value.
SessionConsistencyReadMyWritesPerTokenSequence ==
    \A token1, token2 \in MaybeSessionTokens, key \in Keys, value \in Values :
        /\ ReadConsistencyOK(SessionConsistency)
        /\ SessionTokenLEQ(token1, token2)
        =>
        []((\E record \in DOMAIN writeHistory :
                /\ record.token = token1
                /\ record.state = WriteSucceededState
                /\ record.key = key
                /\ record.value = value)
           => [](LET lowRead == [
                        value |-> value,
                        logIndex |-> token1.checkpoint
                     ]
                 IN  /\ ReadConsistencyOK(SessionConsistency)
                     /\ \A read \in SessionConsistencyRead(token2, key) :
                            ReadsLEQ(lowRead, read)))

SessionConsistencyReadsLowMonotonic ==
    [][ReadConsistencyOK(SessionConsistency) =>
       \A token \in MaybeSessionTokens :
            IsLowMonotonic(LAMBDA key : SessionConsistencyRead(token, key))]_vars

SessionConsistencyReadsFollowReadIndex ==
    \A token \in MaybeSessionTokens :
        ReadConsistencyOK(SessionConsistency) =>
        FollowsReadIndex(LAMBDA key : SessionConsistencyRead(token, key))

\* Important property of session tokens: their validity is one-time.
\* A proxy for validity is the ability produce a read result (even NoValue).
\* Once a session token is valid, if at any point it is seen to not be valid,
\* then it must never become valid again.
SessionTokenDoesNotBecomeValidTwice ==
    \A token \in MaybeSessionTokens, key \in Keys :
        [](/\ ReadConsistencyOK(SessionConsistency)
           /\ SessionConsistencyRead(token, key) # {}
           =>
           [](/\ ReadConsistencyOK(SessionConsistency)
              /\ SessionConsistencyRead(token, key) = {}
              =>
              []/\ ReadConsistencyOK(SessionConsistency)
                /\ SessionConsistencyRead(token, key) = {}))

\* Additionally, the specific conditions for session token validity
\* are either being from the current epoch, or being the null
\* session token, which is always valid.
SessionTokenWhenValid ==
    \A token \in MaybeSessionTokens :
        \A key \in Keys :
            /\ ReadConsistencyOK(SessionConsistency)
            /\ token.epoch = epoch \/ token = NoSessionToken
            => SessionConsistencyRead(token, key) # {}

\* ConsistentPrefix
\* https://docs.microsoft.com/en-us/azure/cosmos-db/consistency-levels#consistent-prefix-consistency
\* Note: consistent prefix does not seem to be observable
\* for clients, so only the bare minimum of properties is covered here,
\* essentially the sanity properties for eventual consistency.

ConsistentPrefixReadsLowMonotonic ==
    [][ReadConsistencyOK(ConsistentPrefix) =>
       IsLowMonotonic(ConsistentPrefixRead)]_vars

ConsistentPrefixReadsFollowReadIndex ==
    ReadConsistencyOK(ConsistentPrefix) =>
    FollowsReadIndex(ConsistentPrefixRead)

\* EventualConsistency
\* https://docs.microsoft.com/en-us/azure/cosmos-db/consistency-levels#eventual-consistency
\* Since eventual consistency and consistent prefix are functionally
\* equivalent, the only meaningful property is to show that both
\* consistency levels behave equivalently in all cases, as an invariant.

EventuallyConsistentReadsEquivalentToConsistentPrefix ==
    /\ ReadConsistencyOK(ConsistentPrefix)
    /\ ReadConsistencyOK(EventualConsistency)
    => \A key \in Keys :
        ConsistentPrefixRead(key) = EventualConsistencyRead(key)

====
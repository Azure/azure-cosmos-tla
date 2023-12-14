------------------------ MODULE ConsistentPrefixRefinesEventualConsistency ------------------------
EXTENDS Naturals, Sequences, FiniteSetsExt

CONSTANTS Keys, Values, NoValue
CONSTANTS StrongConsistency, BoundedStaleness,
          SessionConsistency, ConsistentPrefix,
          EventualConsistency
CONSTANTS VersionBound, StalenessBound

VARIABLES read, readKey
VARIABLES ReadConsistencyImpl, ReadConsistencyHL
VARIABLES log, commitIndex, readIndex, epoch, WriteConsistencyLevel, writeHistory
vars == <<read, readKey, ReadConsistencyImpl, ReadConsistencyHL, log, commitIndex, readIndex, epoch, WriteConsistencyLevel, writeHistory>>

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

Impl == INSTANCE CosmosDBWithReads WITH
    ReadConsistency <- ReadConsistencyImpl
ImplSpec ==
   /\ ReadConsistencyImpl = ConsistentPrefix
   /\ ReadConsistencyHL = EventualConsistency
   /\ Impl!RInit
   /\ [][Impl!RNext /\ UNCHANGED ReadConsistencyHL]_vars

HL == INSTANCE CosmosDBWithReads WITH
    ReadConsistency <- ReadConsistencyHL
HLSpec ==
   /\ ReadConsistencyImpl = ConsistentPrefix
   /\ ReadConsistencyHL = EventualConsistency
   /\ HL!RInit
   /\ [][HL!RNext /\ UNCHANGED ReadConsistencyImpl]_vars

THEOREM ImplSpec => HLSpec

Aliases == <<>>

====

---------------------------- MODULE CosmosDBWithReads --------------------------
EXTENDS CosmosDBProps

VARIABLES read, readKey, ReadConsistency

RInit ==
    /\ ReadConsistency \in ConsistencyLevels
    /\ readKey \in Keys
    /\ read = NotFoundReadResult
    /\ WInit

DoStrongConsistencyRead(key) ==
    /\ ReadConsistency = StrongConsistency
    /\ ReadConsistencyOK(StrongConsistency)
    /\ read' \in StrongConsistencyRead(key)
    /\ readKey' = key

DoBoundedStalenessRead(key) ==
    /\ ReadConsistency = BoundedStaleness
    /\ ReadConsistencyOK(BoundedStaleness)
    /\ read' \in BoundedStalenessRead(key)
    /\ readKey' = key

DoSessionConsistencyRead(key) ==
    /\ ReadConsistency = SessionConsistency
    /\ ReadConsistencyOK(SessionConsistency)
    /\ \E token \in MaybeSessionTokens :
        /\ read' \in SessionConsistencyRead(token, key)
        /\ readKey' = key

DoConsistentPrefixRead(key) ==
    /\ ReadConsistency = ConsistentPrefix
    /\ ReadConsistencyOK(ConsistentPrefix)
    /\ read' \in ConsistentPrefixRead(key)
    /\ readKey' = key

DoEventualConsistencyRead(key) ==
    /\ ReadConsistency = EventualConsistency
    /\ ReadConsistencyOK(EventualConsistency)
    /\ read' \in EventualConsistencyRead(key)
    /\ readKey' = key

RNext ==
    \/ /\ UNCHANGED varsWithHistory
       /\ UNCHANGED ReadConsistency
       /\ \E key \in Keys:
            \/ DoStrongConsistencyRead(key)
            \/ DoBoundedStalenessRead(key)
            \/ DoSessionConsistencyRead(key)
            \/ DoConsistentPrefixRead(key)
            \/ DoEventualConsistencyRead(key)
    \/ /\ UNCHANGED <<read, readKey, ReadConsistency>>
       /\ WNext

RSpec ==
    RInit /\ [][RNext]_<<varsWithHistory, read, readKey, ReadConsistency>>

================================================================================
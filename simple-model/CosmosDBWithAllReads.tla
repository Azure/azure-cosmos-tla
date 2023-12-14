---------------------------- MODULE CosmosDBWithAllReads --------------------------
EXTENDS CosmosDBProps

VARIABLE read, readKey, readConsistency

RInit ==
    /\ read = {NotFoundReadResult}
    /\ readKey \in Keys
    /\ readConsistency \in ConsistencyLevels
    /\ WInit

DoStrongConsistencyRead(key) ==
    /\ ReadConsistencyOK(StrongConsistency)
    /\ readKey' = key
    /\ read' = StrongConsistencyRead(key)
    /\ readConsistency' = StrongConsistency

DoBoundedStalenessRead(key) ==
    /\ ReadConsistencyOK(BoundedStaleness)
    /\ readKey' = key
    /\ read' = BoundedStalenessRead(key)
    /\ readConsistency' = BoundedStaleness

DoSessionConsistencyRead(key) ==
    /\ ReadConsistencyOK(SessionConsistency)
    /\ \E token \in SessionTokens :
        /\ readKey' = key
        /\ read' = SessionConsistencyRead(token, key)
        /\ readConsistency' = SessionConsistency

DoConsistentPrefixRead(key) ==
    /\ ReadConsistencyOK(ConsistentPrefix)
    /\ readKey' = key
    /\ read' = ConsistentPrefixRead(key)
    /\ readConsistency' = ConsistentPrefix

DoEventualConsistencyRead(key) ==
    /\ ReadConsistencyOK(EventualConsistency)
    /\ readKey' = key
    /\ read' = EventualConsistencyRead(key)
    /\ readConsistency' = EventualConsistency

RNext ==
    \/ /\ UNCHANGED varsWithHistory
       /\ \E key \in Keys:
            \/ DoStrongConsistencyRead(key)
            \/ DoBoundedStalenessRead(key)
            \/ DoSessionConsistencyRead(key)
            \/ DoConsistentPrefixRead(key)
            \/ DoEventualConsistencyRead(key)
    \/ /\ UNCHANGED <<read, readKey, readConsistency>>
       /\ WNext

RSpec ==
    RInit /\ [][RNext]_<<varsWithHistory, read, readKey, readConsistency>>

================================================================================
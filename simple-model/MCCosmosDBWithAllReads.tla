---- MODULE MCCosmosDBWithAllReads ----
EXTENDS CosmosDBWithAllReads

LogIndicesImpl == 1..3

CheckpointsImpl == LogIndicesImpl \cup {0}

EpochsImpl == 1..3

SpecificStateSpace ==
    /\ Len(log) < Max(LogIndicesImpl)
    /\ epoch < Max(EpochsImpl)

StalenessBoundImpl == 2
VersionBoundImpl == 4

====
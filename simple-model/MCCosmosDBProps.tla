---- MODULE MCCosmosDBProps ----
EXTENDS CosmosDBProps

LogIndicesImpl == 1..4

CheckpointsImpl == LogIndicesImpl \cup {0}

EpochsImpl == 1..3

SpecificStateSpace ==
    /\ Len(log) < (Max(LogIndicesImpl) - 1)
    /\ epoch < Max(EpochsImpl)

StalenessBoundImpl == 2
VersionBoundImpl == 3

====
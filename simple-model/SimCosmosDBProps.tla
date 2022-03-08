---- MODULE SimCosmosDBProps ----
EXTENDS CosmosDBProps, TLC

SimInit == WInit

SimSpec == SimInit /\ [][WNext]_varsWithHistory

NatImpl == 0..100

StalenessBoundImpl == 2
VersionBoundImpl == 3

TraceLength ==
    TLCGet("level") < 5

====
------------------------- MODULE MCswscrw -------------------------
EXTENDS swscrw, IOUtils

MaxNumOp ==
    \A i \in Clients: op[i] < 5

mcNumClients ==
    1

mcK ==
    2

-------------------------------------------------------------------

mcConsistency ==
    IOEnv.mcConsistency

mcProperty ==
    IOEnv.mcProperty

mcEventual ==
    []\/ mcProperty # "Eventual"
      \/ Eventual

mcConsistent_Prefix ==
    []\/ mcProperty # "Consistent_Prefix"
      \/ Consistent_Prefix

mcSession ==
    []\/ mcProperty # "Session"
      \/ Session

mcBounded_Staleness ==
    []\/ mcProperty # "Bounded_Staleness"
      \/ Bounded_Staleness

mcStrong ==
    []\/ mcProperty # "Strong"
      \/ Strong

=============================================================================

---------------------------- CONFIG MCswscrw --------------------------------
SPECIFICATION Spec
\* Add statements after this line.
CHECK_DEADLOCK 
    FALSE
CONSTRAINT
    MaxNumOp
CONSTANT
    NumClients <- mcNumClients
    Consistency <- mcConsistency
    K <- mcK
PROPERTIES
    mcEventual
    mcConsistent_Prefix
    mcSession
    mcBounded_Staleness
    mcStrong
=============================================================================

--------------------------- MODULE MCcosmos_client --------------------------
EXTENDS cosmos_client, IOUtils

mcNumRegions ==
    atoi(IOEnv.mcNumRegions)

mcNumWriteRegions ==
    atoi(IOEnv.mcNumWriteRegions)

mcNumClientsPerRegion ==
    atoi(IOEnv.mcNumClientsPerRegion)

mcConsistency ==
    IOEnv.mcConsistency

mcProperty ==
    IOEnv.mcProperty

mcEventual ==
    []\/ mcProperty # "Eventual"
      \/ Eventual

mcSession ==
    []\/ mcProperty # "Session"
      \/ Session

mcStrong ==
    []\/ mcProperty # "Strong"
      \/ Strong

=============================================================================
--------------------------- CONFIG MCcosmos_client --------------------------
SPECIFICATION Spec
\* Add statements after this line.
CONSTRAINT 
    MaxNumOp
CONSTANT
    K = 1
CONSTANT
    NumRegions <- mcNumRegions
    NumWriteRegions <- mcNumWriteRegions
    NumClientsPerRegion <- mcNumClientsPerRegion
    Consistency <- mcConsistency
PROPERTIES
    mcEventual
    mcSession
    mcStrong
=============================================================================
    
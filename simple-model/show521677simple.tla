---- MODULE show521677simple ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS StrongConsistency, BoundedStaleness,
          SessionConsistency, ConsistentPrefix,
          EventualConsistency
CONSTANTS VersionBound, StalenessBound

VARIABLES log, commitIndex, readIndex, epoch, WriteConsistencyLevel

Keys == {"taskKey"}
Values == {"taskValue"}
NoValue == "NoValue"

cosmosVarsExceptLog == <<commitIndex, readIndex, epoch, WriteConsistencyLevel>>
cosmosVars == <<cosmosVarsExceptLog, log>>

CosmosDB == INSTANCE CosmosDB

---------------------------------------------------------------------

NoSessionToken == CosmosDB!NoSessionToken

TypesOK == CosmosDB!TypesOK

VARIABLE serviceBus, frontdoorPC, frontdoorToken, workerPC, workerToken, workerValue

specVars == <<serviceBus, frontdoorPC, frontdoorToken, workerPC, workerToken, workerValue>>
vars == <<cosmosVars, specVars>>

frontdoorWriteTaskDataInit ==
    /\ frontdoorPC = "frontdoorWriteTaskDataInit"
    /\ Assert(CosmosDB!WritesAccepted, "assume writes are accepted")
    /\ CosmosDB!WriteInit("taskKey", "taskValue")
    /\ frontdoorToken' = CosmosDB!WriteInitToken
    /\ frontdoorPC' = "frontdoorWriteTaskDataCommit"
    /\ UNCHANGED <<cosmosVarsExceptLog, serviceBus, workerPC, workerToken, workerValue>>

frontdoorWriteTaskDataCommit ==
    /\ frontdoorPC = "frontdoorWriteTaskDataCommit"
    /\ CosmosDB!WriteCanSucceed(frontdoorToken)
    /\ serviceBus' = <<"taskKey">>
    /\ frontdoorPC' = "Done"
    /\ UNCHANGED <<cosmosVars, frontdoorToken, workerPC, workerToken, workerValue>>

frontdoorDone ==
    /\ frontdoorPC = "Done"
    /\ UNCHANGED vars

workerBeginTask ==
    /\ workerPC = "workerBeginTask"
    /\ serviceBus # <<>>
    /\ LET taskKey == Head(serviceBus)
       IN  /\ serviceBus' = Tail(serviceBus)
           /\ \E read \in CosmosDB!SessionConsistencyRead(workerToken, taskKey) :
                /\ workerToken' = CosmosDB!UpdateTokenFromRead(workerToken, read)
                /\ workerValue' = read.value
                /\ workerPC' = "Done"
                /\ UNCHANGED <<cosmosVars, frontdoorToken, frontdoorPC>>

workerDone ==
    /\ workerPC = "Done"
    /\ UNCHANGED vars

---------------------------------------------------------------------

Init ==
    /\ WriteConsistencyLevel = SessionConsistency
    /\ serviceBus = <<>>
    /\ frontdoorPC = "frontdoorWriteTaskDataInit"
    /\ frontdoorToken = NoSessionToken
    /\ workerPC = "workerBeginTask"
    /\ workerToken = NoSessionToken
    /\ workerValue = NoValue
    /\ CosmosDB!Init

frontdoor ==
    \/ frontdoorWriteTaskDataInit
    \/ frontdoorWriteTaskDataCommit
    \/ frontdoorDone

worker ==
    \/ workerBeginTask
    \/ workerDone

cosmos ==
    /\ CosmosDB!Next
    /\ UNCHANGED specVars

Next ==
    \/ frontdoor
    \/ worker
    \/ cosmos

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(frontdoor)
        /\ WF_vars(worker)
        /\ WF_vars(cosmos)

---------------------------------------------------------------------

SpecificStateSpace ==
    \* Don't model data loss. It is not needed, and it allows a session
    \* token to expire after being acquired. Handling that would
    \* complicate this spec.
    /\ epoch = 1

---------------------------------------------------------------------

Termination ==
    <>(/\ frontdoorPC = "Done"
       /\ workerPC = "Done")

ValueEventuallyCorrect ==
    <>(workerValue = "taskValue")

WorkerReceivesCorrectValue ==
    workerPC = "Done" => workerValue = "taskValue"

====

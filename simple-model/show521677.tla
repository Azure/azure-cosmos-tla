---- MODULE show521677 ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS StrongConsistency, BoundedStaleness,
          SessionConsistency, ConsistentPrefix,
          EventualConsistency
CONSTANTS VersionBound, StalenessBound

VARIABLES log, commitIndex, readIndex, epoch, WriteConsistencyLevel

Keys == {"taskKey"}
Values == {"taskValue"}
NoValue == "NoValue"

VARIABLES network, returnAddrMap

ClientIDs == {"frontdoor", "worker"}
SystemID == "SystemID"

clientVarsExceptNetwork == <<log, commitIndex, readIndex, epoch, WriteConsistencyLevel, returnAddrMap>>
clientVars == <<clientVarsExceptNetwork, network>>

Client == INSTANCE CosmosDBClient WITH
    NetworkIsLossy <- FALSE,
    ModelFailure <- FALSE

---------------------------------------------------------------------

TypesOK == Client!TypesOK

VARIABLE serviceBus, frontdoorPC, frontdoorToken, workerPC, workerToken, workerValue

specVars == <<serviceBus, frontdoorPC, frontdoorToken, workerPC, workerToken, workerValue>>
vars == <<clientVars, specVars>>

frontdoorWriteTaskDataSend ==
    /\ frontdoorPC = "frontdoorWriteTaskDataSend"
    /\ Client!RequestWrite("frontdoor", "taskKey", "taskValue", frontdoorToken)
    /\ frontdoorPC' = "frontdoorWriteTaskDataReceive"
    /\ UNCHANGED <<clientVarsExceptNetwork, serviceBus, frontdoorToken, workerPC, workerToken, workerValue>>

frontdoorWriteTaskDataReceive ==
    /\ frontdoorPC = "frontdoorWriteTaskDataReceive"
    /\ Client!ReceiveWriteResult("frontdoor")
    /\ frontdoorToken' = Client!ReceivedWriteToken("frontdoor")
    /\ serviceBus' = <<"taskKey">>
    /\ frontdoorPC' = "Done"
    /\ UNCHANGED <<clientVarsExceptNetwork, workerPC, workerToken, workerValue>>

frontdoorDone ==
    /\ frontdoorPC = "Done"
    /\ UNCHANGED vars

workerBeginTaskSend ==
    /\ workerPC = "workerBeginTaskSend"
    /\ serviceBus # <<>>
    /\ LET taskKey == Head(serviceBus)
       IN  /\ serviceBus' = Tail(serviceBus)
           /\ Client!RequestRead("worker", taskKey, SessionConsistency, workerToken)
           /\ workerPC' = "workerBeginTaskReceive"
           /\ UNCHANGED <<clientVarsExceptNetwork, frontdoorToken, frontdoorPC, workerToken, workerValue>>

workerBeginTaskReceive ==
    /\ workerPC = "workerBeginTaskReceive"
    /\ Client!ReceiveReadResult("worker")
    /\ workerToken' = Client!ReceivedReadToken("worker")
    /\ workerValue' = Client!ReceivedRead("worker")
    /\ workerPC' = "Done"
    /\ UNCHANGED <<clientVarsExceptNetwork, serviceBus, frontdoorToken, frontdoorPC>>

workerDone ==
    /\ workerPC = "Done"
    /\ UNCHANGED vars

---------------------------------------------------------------------

Init ==
    /\ WriteConsistencyLevel = SessionConsistency
    /\ serviceBus = <<>>
    /\ frontdoorPC = "frontdoorWriteTaskDataSend"
    /\ frontdoorToken = Client!NoSessionToken
    /\ workerPC = "workerBeginTaskSend"
    /\ workerToken = Client!NoSessionToken
    /\ workerValue = NoValue
    /\ Client!Init

frontdoor ==
    \/ frontdoorWriteTaskDataSend
    \/ frontdoorWriteTaskDataReceive
    \/ frontdoorDone

worker ==
    \/ workerBeginTaskSend
    \/ workerBeginTaskReceive
    \/ workerDone

client ==
    /\ Client!Next
    /\ UNCHANGED specVars

Next ==
    \/ frontdoor
    \/ worker
    \/ client

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(frontdoor)
        /\ WF_vars(worker)
        /\ WF_vars(client)

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

WorkerReceivesCorrectValue ==
    workerPC = "Done" => workerValue = "taskValue"

====

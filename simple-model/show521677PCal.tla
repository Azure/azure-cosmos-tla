---- MODULE show521677PCal ----
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

(* --fair algorithm show521677PCal {

variables serviceBus = <<>>;

process (frontdoor = "frontdoor")
    variables frontdoorToken = Client!NoSessionToken;
{
frontdoorWriteTaskDataSend:
    await Client!RequestWrite("frontdoor", "taskKey", "taskValue", frontdoorToken);
    await UNCHANGED clientVarsExceptNetwork;
frontdoorWriteTaskDataReceive:
    await Client!ReceiveWriteResult("frontdoor");
    frontdoorToken := Client!ReceivedWriteToken("frontdoor");
    serviceBus := <<"taskKey">>;
    await UNCHANGED clientVarsExceptNetwork;
}

process (worker = "worker")
    variables workerToken = Client!NoSessionToken, workerValue;
{
workerBeginTaskSend:
    await serviceBus # <<>>;
    with(taskKey = Head(serviceBus)) {
        await Client!RequestRead("worker", taskKey, SessionConsistency, workerToken);
    };
    serviceBus := <<>>;
    await UNCHANGED clientVarsExceptNetwork;
workerBeginTaskReceive:
    await Client!ReceiveReadResult("worker");
    workerToken := Client!ReceivedReadToken("worker");
    workerValue := Client!ReceivedRead("worker");
    await UNCHANGED clientVarsExceptNetwork;
}

} *)

\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "ea1bcd8")
CONSTANT defaultInitValue
VARIABLES serviceBus, pc, frontdoorToken, workerToken, workerValue

vars == << serviceBus, pc, frontdoorToken, workerToken, workerValue >>

ProcSet == {"frontdoor"} \cup {"worker"}

Init == (* Global variables *)
        /\ serviceBus = <<>>
        (* Process frontdoor *)
        /\ frontdoorToken = Client!NoSessionToken
        (* Process worker *)
        /\ workerToken = Client!NoSessionToken
        /\ workerValue = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "frontdoor" -> "frontdoorWriteTaskDataSend"
                                        [] self = "worker" -> "workerBeginTaskSend"]

frontdoorWriteTaskDataSend == /\ pc["frontdoor"] = "frontdoorWriteTaskDataSend"
                              /\ Client!RequestWrite("frontdoor", "taskKey", "taskValue", frontdoorToken)
                              /\ UNCHANGED clientVarsExceptNetwork
                              /\ pc' = [pc EXCEPT !["frontdoor"] = "frontdoorWriteTaskDataReceive"]
                              /\ UNCHANGED << serviceBus, frontdoorToken, 
                                              workerToken, workerValue >>

frontdoorWriteTaskDataReceive == /\ pc["frontdoor"] = "frontdoorWriteTaskDataReceive"
                                 /\ Client!ReceiveWriteResult("frontdoor")
                                 /\ frontdoorToken' = Client!ReceivedWriteToken("frontdoor")
                                 /\ serviceBus' = <<"taskKey">>
                                 /\ UNCHANGED clientVarsExceptNetwork
                                 /\ pc' = [pc EXCEPT !["frontdoor"] = "Done"]
                                 /\ UNCHANGED << workerToken, workerValue >>

frontdoor == frontdoorWriteTaskDataSend \/ frontdoorWriteTaskDataReceive

workerBeginTaskSend == /\ pc["worker"] = "workerBeginTaskSend"
                       /\ serviceBus # <<>>
                       /\ LET taskKey == Head(serviceBus) IN
                            Client!RequestRead("worker", taskKey, SessionConsistency, workerToken)
                       /\ serviceBus' = <<>>
                       /\ UNCHANGED clientVarsExceptNetwork
                       /\ pc' = [pc EXCEPT !["worker"] = "workerBeginTaskReceive"]
                       /\ UNCHANGED << frontdoorToken, workerToken, 
                                       workerValue >>

workerBeginTaskReceive == /\ pc["worker"] = "workerBeginTaskReceive"
                          /\ Client!ReceiveReadResult("worker")
                          /\ workerToken' = Client!ReceivedReadToken("worker")
                          /\ workerValue' = Client!ReceivedRead("worker")
                          /\ UNCHANGED clientVarsExceptNetwork
                          /\ pc' = [pc EXCEPT !["worker"] = "Done"]
                          /\ UNCHANGED << serviceBus, frontdoorToken >>

worker == workerBeginTaskSend \/ workerBeginTaskReceive

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == frontdoor \/ worker
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

TerminatingImpl == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars
               /\ UNCHANGED clientVars

CombinedInit ==
    /\ WriteConsistencyLevel = SessionConsistency
    /\ Client!Init
    /\ Init

CombinedNext ==
    \/ Next
    \/ Client!Next /\ UNCHANGED vars

CombinedSpec ==
    /\ CombinedInit
    /\ [][CombinedNext]_<<vars, clientVars>>
    /\ WF_vars(Next)
    /\ WF_vars(Client!Next /\ UNCHANGED vars)

---------------------------------------------------------------------

SpecificStateSpace ==
    \* Don't model data loss. It is not needed, and it allows a session
    \* token to expire after being acquired. Handling that would
    \* complicate this spec.
    /\ epoch = 1

---------------------------------------------------------------------

WorkerReceivesCorrectValue ==
    pc["worker"] = "Done" => workerValue = "taskValue"

====

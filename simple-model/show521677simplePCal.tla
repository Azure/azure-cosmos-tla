---- MODULE show521677simplePCal ----
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

(* --fair algorithm show521677simplePCal {
variables serviceBus = <<>>;

process (frontdoor = "frontdoor")
variables frontdoorToken;
{
frontdoorWriteTaskDataInit:
    assert CosmosDB!WritesAccepted;
    await CosmosDB!WriteInit("taskKey", "taskValue");
    frontdoorToken := CosmosDB!WriteInitToken;
    await UNCHANGED cosmosVarsExceptLog;
frontdoorWriteTaskDataCommit:
    await CosmosDB!WriteCanSucceed(frontdoorToken);
    serviceBus := <<"taskKey">>;
    await UNCHANGED cosmosVars;
}

process (worker = "worker")
variables workerToken, workerValue;
{
workerBeginTask:
    await serviceBus # <<>>;
    with(taskKey = Head(serviceBus),
         read \in CosmosDB!SessionConsistencyRead(
             CosmosDB!NoSessionToken, taskKey)) {
        serviceBus := Tail(serviceBus);
        workerToken := CosmosDB!UpdateTokenFromRead(CosmosDB!NoSessionToken, read);
        workerValue := read.value;
        await UNCHANGED cosmosVars;
    }
}

}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "bfb6276d")
CONSTANT defaultInitValue
VARIABLES serviceBus, pc, frontdoorToken, workerToken, workerValue

vars == << serviceBus, pc, frontdoorToken, workerToken, workerValue >>

ProcSet == {"frontdoor"} \cup {"worker"}

Init == (* Global variables *)
        /\ serviceBus = <<>>
        (* Process frontdoor *)
        /\ frontdoorToken = defaultInitValue
        (* Process worker *)
        /\ workerToken = defaultInitValue
        /\ workerValue = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = "frontdoor" -> "frontdoorWriteTaskDataInit"
                                        [] self = "worker" -> "workerBeginTask"]

frontdoorWriteTaskDataInit == /\ pc["frontdoor"] = "frontdoorWriteTaskDataInit"
                              /\ Assert(CosmosDB!WritesAccepted, 
                                        "Failure of assertion at line 33, column 5.")
                              /\ CosmosDB!WriteInit("taskKey", "taskValue")
                              /\ frontdoorToken' = CosmosDB!WriteInitToken
                              /\ UNCHANGED cosmosVarsExceptLog
                              /\ pc' = [pc EXCEPT !["frontdoor"] = "frontdoorWriteTaskDataCommit"]
                              /\ UNCHANGED << serviceBus, workerToken, 
                                              workerValue >>

frontdoorWriteTaskDataCommit == /\ pc["frontdoor"] = "frontdoorWriteTaskDataCommit"
                                /\ CosmosDB!WriteCanSucceed(frontdoorToken)
                                /\ serviceBus' = <<"taskKey">>
                                /\ UNCHANGED cosmosVars
                                /\ pc' = [pc EXCEPT !["frontdoor"] = "Done"]
                                /\ UNCHANGED << frontdoorToken, workerToken, 
                                                workerValue >>

frontdoor == frontdoorWriteTaskDataInit \/ frontdoorWriteTaskDataCommit

workerBeginTask == /\ pc["worker"] = "workerBeginTask"
                   /\ serviceBus # <<>>
                   /\ LET taskKey == Head(serviceBus) IN
                        \E read \in      CosmosDB!SessionConsistencyRead(
                                    CosmosDB!NoSessionToken, taskKey):
                          /\ serviceBus' = Tail(serviceBus)
                          /\ workerToken' = CosmosDB!UpdateTokenFromRead(CosmosDB!NoSessionToken, read)
                          /\ workerValue' = read.value
                          /\ UNCHANGED cosmosVars
                   /\ pc' = [pc EXCEPT !["worker"] = "Done"]
                   /\ UNCHANGED frontdoorToken

worker == workerBeginTask

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
               /\ UNCHANGED cosmosVars

---------------------------------------------------------------------

combinedVars == <<vars, cosmosVars>>

CombinedInit ==
    /\ WriteConsistencyLevel = SessionConsistency
    /\ Init
    /\ CosmosDB!Init

cosmos ==
    /\ CosmosDB!Next
    /\ UNCHANGED vars

CombinedNext ==
    \/ Next
    \/ cosmos

CombinedSpec ==
    /\ CombinedInit
    /\ [][CombinedNext]_combinedVars
    /\ WF_vars(cosmos)
    /\ WF_vars(Next)

---------------------------------------------------------------------

SpecificStateSpace ==
    \* Don't model data loss. It is not needed, and it allows a session
    \* token to expire after being acquired. Handling that would
    \* complicate this spec.
    /\ epoch = 1

---------------------------------------------------------------------

ValueEventuallyCorrect ==
    <>(workerValue = "taskValue")

WorkerReceivesCorrectValue ==
    pc["worker"] = "Done" => workerValue = "taskValue"

====

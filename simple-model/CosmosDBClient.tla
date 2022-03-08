---- MODULE CosmosDBClient ----
EXTENDS Naturals, TLC, FiniteSets, FiniteSetsExt, Sequences, SequencesExt

\* This part just repeats and summarizes the necessary mechanisms to instantiate
\* the CosmosDB spec. For the semantics, see CosmosDB.tla.

CONSTANTS Keys, Values, NoValue
CONSTANTS StrongConsistency, BoundedStaleness,
          SessionConsistency, ConsistentPrefix,
          EventualConsistency
CONSTANTS VersionBound, StalenessBound

VARIABLES log, commitIndex, readIndex, epoch, WriteConsistencyLevel

cosmosVarsExceptLog == <<commitIndex, readIndex, epoch, WriteConsistencyLevel>>
cosmosVars == <<cosmosVarsExceptLog, log>>

CosmosDB == INSTANCE CosmosDB

---------------------------------------------------------------------

\* Two behavioral constants to enable / disable message loss in the
\* simulated network, or spontaneous request failure.

CONSTANT NetworkIsLossy
ASSUME NetworkIsLossy \in BOOLEAN

CONSTANT ModelFailure
ASSUME ModelFailure \in BOOLEAN

\* The set of client IDs who will be sending messages to Cosmos DB
\* alongside the ID of the Cosmos DB system itself, which will
\* respond to those requests.
CONSTANTS ClientIDs, SystemID

NoSessionToken == CosmosDB!NoSessionToken

IDs == ClientIDs \cup {SystemID}

ReadMessages == [
    type: {"read"},
    from: ClientIDs,
    consistencyLevel: CosmosDB!ConsistencyLevels,
    key: Keys,
    token: CosmosDB!MaybeSessionTokens
]

WriteMessages == [
    type: {"write"},
    from: ClientIDs,
    key: Keys,
    value: Values,
    token: CosmosDB!MaybeSessionTokens
]

ReadOKMessages == [
    type: {"read_ok"},
    from: {SystemID},
    value: CosmosDB!MaybeValues,
    token: CosmosDB!MaybeSessionTokens
]

WriteOKMessages == [
    type: {"write_ok"},
    from: {SystemID},
    token: CosmosDB!MaybeSessionTokens
]

FailMessages == [
    type: {"fail"},
    from: {SystemID}
]

ReqMessages ==
    ReadMessages \cup
    WriteMessages

Messages ==
    ReqMessages \cup
    ReadOKMessages \cup
    WriteOKMessages \cup
    FailMessages

Mailboxes == Seq(Messages)

Networks == [ IDs -> Mailboxes ]

VARIABLES network, returnAddrMap
vars == <<cosmosVars, network, returnAddrMap>>

TypesOK ==
    /\ network \in Networks
    /\ \A token \in DOMAIN returnAddrMap :
        /\ token \in CosmosDB!SessionTokens
        /\ returnAddrMap[token] \in ClientIDs
    /\ CosmosDB!TypesOK

---------------------------------------------------------------------

varsExceptNetwork == <<cosmosVars, returnAddrMap>>

LOCAL SendToSystem(msg) ==
    network' = [network EXCEPT ![SystemID] = Append(@, msg)]

LOCAL ReceiveFromSystem(self) ==
    /\ network[self] # <<>>
    /\ network' = [network EXCEPT ![self] = Tail(@)]

LOCAL TheMessage(self) == Head(network[self])

RequestRead(self, key, consistencyLevel, token) ==
    SendToSystem([
        type |-> "read",
        from |-> self,
        consistencyLevel |-> consistencyLevel,
        key |-> key,
        token |-> token
    ])

ReceiveReadResult(self) ==
    /\ ReceiveFromSystem(self)
    /\ TheMessage(self).type = "read_ok"

ReceivedRead(self) == TheMessage(self).value
ReceivedReadToken(self) == TheMessage(self).token

RequestWrite(self, key, value, token) ==
    SendToSystem([
        type |-> "write",
        from |-> self,
        key |-> key,
        value |-> value,
        token |-> token
    ])

ReceiveWriteResult(self) ==
    /\ ReceiveFromSystem(self)
    /\ TheMessage(self).type = "write_ok"

ReceivedWriteToken(self) == TheMessage(self).token

ReceiveFail(self) ==
    /\ ReceiveFromSystem(self)
    /\ TheMessage(self).type = "fail"

---------------------------------------------------------------------

HandleReadMessage ==
    /\ network[SystemID] # <<>>
    /\ LET msg == Head(network[SystemID])
           readResults ==
              CASE msg.consistencyLevel = StrongConsistency ->
                    CosmosDB!StrongConsistencyRead(msg.key)
                [] msg.consistencyLevel = BoundedStaleness ->
                    CosmosDB!BoundedStalenessRead(msg.key)
                [] msg.consistencyLevel = SessionConsistency ->
                    CosmosDB!SessionConsistencyRead(msg.token, msg.key)
                [] msg.consistencyLevel = ConsistentPrefix ->
                    CosmosDB!ConsistentPrefixRead(msg.key)
                [] msg.consistencyLevel = EventualConsistency ->
                    CosmosDB!EventualConsistencyRead(msg.key)
       IN  /\ msg.type = "read"
           /\ (msg.consistencyLevel # SessionConsistency =>
                Assert(msg.token = NoSessionToken, "session tokens are only meaningful for session consistent reads"))
           /\ \E read \in readResults :
                /\ network' = [network EXCEPT
                    ![SystemID] = Tail(@),
                    ![msg.from] = Append(@, [
                        type |-> "read_ok",
                        from |-> SystemID,
                        value |-> read.value,
                        token |-> CosmosDB!UpdateTokenFromRead(msg.token, read)
                    ])]
                /\ UNCHANGED <<returnAddrMap, cosmosVars>>

HandleWriteMessageInit ==
    /\ network[SystemID] # <<>>
    /\ LET msg == Head(network[SystemID])
       IN  /\ msg.type = "write"
           /\ CosmosDB!WritesAccepted
           /\ IF   WriteConsistencyLevel = SessionConsistency
              THEN CosmosDB!SessionTokenIsValid(msg.token)
              ELSE Assert(msg.token = NoSessionToken, "session tokens are only meaningful at session consistency")                  
           /\ CosmosDB!WriteInit(msg.key, msg.value)
           /\ returnAddrMap' = returnAddrMap @@ (CosmosDB!WriteInitToken :> msg.from)
           /\ network' = [network EXCEPT ![SystemID] = Tail(@)]
           /\ UNCHANGED cosmosVarsExceptLog

HandleWriteMessageSuccess ==
    \E token \in DOMAIN returnAddrMap :
        /\ CosmosDB!WriteCanSucceed(token)
        /\ returnAddrMap' = [t \in (DOMAIN returnAddrMap) \ {token} |-> returnAddrMap[t]]
        /\ network' = [network EXCEPT
                ![returnAddrMap[token]] = Append(@, [
                    type |-> "write_ok",
                    from |-> SystemID,
                    token |-> token
                ])]
        /\ UNCHANGED cosmosVars

HandleWriteMessageFail ==
    /\ ModelFailure
    /\ \E token \in DOMAIN returnAddrMap :
        /\ returnAddrMap' = [t \in (DOMAIN returnAddrMap) \ {token} |-> returnAddrMap[t]]
        /\ network' = [network EXCEPT
                ![returnAddrMap[token]] = Append(@, [
                    type |-> "fail",
                    from |-> SystemID
                ])]
        /\ UNCHANGED cosmosVars

HandleMessageFail ==
    /\ ModelFailure
    /\ network[SystemID] # <<>>
    /\ LET msg == Head(network[SystemID])
       IN  /\ network' = [network EXCEPT
                ![SystemID] = Tail(@),
                ![msg.from] = Append(@, [
                    type |-> "fail",
                    from |-> SystemID
                ])]
           /\ UNCHANGED <<returnAddrMap, cosmosVars>>

MessageLoss ==
    /\ NetworkIsLossy
    /\ \E id \in DOMAIN network :
        /\ network[id] # <<>>
        /\ network' = [network EXCEPT ![id] = Tail(@)]
        /\ UNCHANGED <<returnAddrMap, cosmosVars>>

Init ==
    /\ network = [id \in IDs |-> <<>>]
    /\ returnAddrMap = <<>>
    /\ CosmosDB!Init

Next ==
    \/ HandleReadMessage
    \/ HandleWriteMessageInit
    \/ HandleWriteMessageSuccess
    \/ HandleWriteMessageFail
    \/ HandleMessageFail
    \/ MessageLoss
    \/ /\ UNCHANGED <<network, returnAddrMap>>
       /\ CosmosDB!Next
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------------------------------------------------------------------

ReadResponsesWithoutFailure ==
    (\lnot NetworkIsLossy) =>
    \A id \in ClientIDs :
        (\E i \in DOMAIN network[SystemID] :
            /\ network[SystemID][i].type = "read"
            /\ network[SystemID][i].from = id)
        ~>
        (\E i \in DOMAIN network[id] :
            \/ network[id][i].type = "read_ok"
            \/ network[id][i].type = "fail")

WriteResponsesWithoutFailure ==
    (\lnot NetworkIsLossy) =>
    \A id \in ClientIDs :
        (\E i \in DOMAIN network[SystemID] :
            /\ network[SystemID][i].type = "write"
            /\ network[SystemID][i].from = id)
        ~>
        (\E i \in DOMAIN network[id] :
            \/ network[id][i].type = "write_ok"
            \/ network[id][i].type = "fail")

====
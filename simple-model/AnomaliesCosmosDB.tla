---- MODULE AnomaliesCosmosDB ----
EXTENDS Naturals, Sequences, TLC, Bags

CONSTANTS Keys, Values, NoValue
CONSTANTS StrongConsistency, BoundedStaleness,
          SessionConsistency, ConsistentPrefix,
          EventualConsistency
CONSTANTS VersionBound, StalenessBound

VARIABLES log, commitIndex, readIndex, epoch, read, readKey, readConsistency, writeHistory, WriteConsistencyLevel
vars == <<log, commitIndex, readIndex, epoch, read, readKey, readConsistency, writeHistory, WriteConsistencyLevel>>

CONSTANTS k1, k2, v1, v2, v3
ASSUME k1 \in Keys
ASSUME k2 \in Keys
ASSUME v1 \in Values
ASSUME v2 \in Values
ASSUME v3 \in Values

CosmosDB == INSTANCE CosmosDBWithAllReads
CosmosSpec == CosmosDB!RSpec

NotFoundReadResult == CosmosDB!NotFoundReadResult

---------------------------------------------------------------------

\* To add traces here, define an operator with a meaningful name,
\* and, as its value, include a sequence of records describing
\* state variable values along the sequence of states.
\* To have the trace checked against the CosmosDB spec, add it
\* to AllTraces.
\*
\* At its simplest, you can paste the result of TLCExt!Trace when
\* checking CosmosDBWithAllReads (or equivalent).
\* PastedFromTrace is an example of doing this, with a little formatting
\* to make the result easier to read.
\* 
\* If you want more control or have a specific example in mind,
\* you can hand-write traces more easily by only including variables
\* that are supposed to change.
\* You can also write starting states more simply using either
\* DefaultInitAllConsistencies (a constant which will check your
\* trace under all write consistencies, if write consistency level
\* doesn't matter), or DefaultInitWithConsistency(level), which
\* will give you a standard starting state, but restricting the
\* consistency level to only the level you specify, if your trace
\* would only make sense under a given write consistency.
\*
\* To asserts reads are / are not possible, require states where
\* read, readKey, and readConsistency have certain values.
\* read will be the set of possible reads, given readKey and
\* readConsistency.

LOCAL DefaultInitAllConsistencies == [
    readIndex |-> 0,
    commitIndex |-> 0,
    log |-> <<>>,
    epoch |-> 1,
    writeHistory |-> EmptyBag,
    read |-> {NotFoundReadResult},
    readKey |-> k1,
    readConsistency |-> EventualConsistency
]

LOCAL DefaultInitWithConsistency(level) ==
    DefaultInitAllConsistencies @@ ("ConsistencyLevel" :> level)

StrongConsistencyDirtyReads ==
    <<
        \* Action: Init
        DefaultInitWithConsistency(StrongConsistency),

        \* Action: Strong Write
        ([
            readIndex |-> 0,
            log |-> <<[value |-> v1, key |-> k1]>>,
            epoch |-> 1,
            commitIndex |-> 0,
            writeHistory |-> SetToBag({
                [
                    token |-> [epoch |-> 1, checkpoint |-> 1],
                    key |-> k1, value |-> v1, state |-> "init"
                ]
            })
        ]),

        \* Action: EventuallyConsistentRead (dirty read)
        ([
            readKey |-> k1,
            read |-> {
                NotFoundReadResult,
                [
                    value |-> v1,
                    logIndex |-> 1]
            },
            readConsistency |-> EventualConsistency
        ]),

        \* Action: StrongConsistency
        ([
            readKey |-> k1,
            read |-> {NotFoundReadResult},
            readConsistency |-> StrongConsistency
        ]),

        \* Action: TruncateLog
        ([
            readIndex |-> 0,
            log |-> <<>>,
            epoch |-> 2,
            commitIndex |-> 0
        ]),

        \* Action: EventuallyConsistentRead (v1 "disappeared").
        ([
            readKey |-> k1,
            read |-> {NotFoundReadResult},
            readConsistency |-> EventualConsistency
        ])
    >>

BoundedStalenessAllowsDirtyReads ==
    <<
        \* Action: Init
        DefaultInitWithConsistency(BoundedStaleness),

        \* Action: Bounded staleness write
        ([
            log |-> <<[key |-> k1, value |-> v1]>>,
            writeHistory |-> SetToBag({
                [
                    token |-> [epoch |-> 1, checkpoint |-> 1],
                    key |-> k1, value |-> v1, state |-> "init"
                ]
            }),
            commitIndex |-> 0
        ]),
        
        \* Action: Bounded staleness read
        ([
            commitIndex |-> 0,
            readKey |-> k1,
            read |-> {
                NotFoundReadResult,
                [value |-> v1, logIndex |-> 1]
            },
            readConsistency |-> BoundedStaleness
        ])
        \* The value read is not durable, even though
        \* commitIndex was at the head of the log.
        \* Strong consistency does not allow this, so, even
        \* under perfect circumstances (enforceable with StalenessBound = 0),
        \* bounded staleness will not refine strong consistency.

        \* More practically, even with StalenessBound=0, strong consistency
        \* and bounded staleness are not equivalent due to the possibility
        \* of a write region failover after the LM write.
    >>

ReadNonEquivalencies ==
    <<
        \* Action: Init
        DefaultInitWithConsistency(StrongConsistency),

        \* begin write k1: v1
        ([
            log |-> <<[key |-> k1, value |-> v1]>>,
            writeHistory |-> SetToBag({
                [
                    token |-> [epoch |-> 1, checkpoint |-> 1],
                    key |-> k1, value |-> v1, state |-> "init"
                ]
            })
        ]),

        \* begin write k1: v2
        ([
            log |-> <<[key |-> k1, value |-> v1], [key |-> k1, value |-> v2]>>,
            writeHistory |-> SetToBag({
                [
                    token |-> [epoch |-> 1, checkpoint |-> 1],
                    key |-> k1, value |-> v1, state |-> "init"
                ],
                [
                    token |-> [epoch |-> 1, checkpoint |-> 2],
                    key |-> k1, value |-> v2, state |-> "init"
                ]
            })
        ]),

        \* advance commitIndex
        ([
            commitIndex |-> 1
        ]),
        
        \* finish write k1: v1
        ([
            writeHistory |-> SetToBag({
                [
                    token |-> [epoch |-> 1, checkpoint |-> 1],
                    key |-> k1, value |-> v1, state |-> "succeeded"
                ],
                [
                    token |-> [epoch |-> 1, checkpoint |-> 2],
                    key |-> k1, value |-> v2, state |-> "init"
                ]
            })
        ]),

        \* strongly consistent read
        ([
            readConsistency |-> StrongConsistency,
            readKey |-> k1,
            read |-> {[value |-> v1, logIndex |-> 1]}
        ]),

        \* bounded staleness read (dirty reads possible)
        \* (confirmed w/ dev)
        ([
            readConsistency |-> BoundedStaleness,
            readKey |-> k1,
            read |-> {
                [value |-> v1, logIndex |-> 1],
                [value |-> v2, logIndex |-> 2]
            }
        ]),

        \* session consistency read
        \* (assuming a token with checkpoint = 2)
        ([
            readConsistency |-> SessionConsistency,
            readKey |-> k1,
            read |-> {[value |-> v2, logIndex |-> 2]}
        ]),

        \* consistent prefix read
        \* (because readIndex = 0)
        ([
            readConsistency |-> ConsistentPrefix,
            readKey |-> k1,
            read |-> {
                NotFoundReadResult,
                [value |-> v1, logIndex |-> 1],
                [value |-> v2, logIndex |-> 2]
            }
        ]),

        \* eventual consistency behaves exactly like 
        \* consistent prefix in all cases
        ([
            readConsistency |-> EventualConsistency,
            readKey |-> k1,
            read |-> {
                NotFoundReadResult,
                [value |-> v1, logIndex |-> 1],
                [value |-> v2, logIndex |-> 2]
            }
        ])
    >>

\* It is possible for a write to become durable / fully replicated
\* even though the client was informed that it failed.
\* If you make a strongly consistent write, see it fail, and wait a bit,
\* you might see the value in your strongly consistent read anyway.
\* note: specifically verified by DB dev
DurableDirtyRead ==
    <<
        \* Action: Init
        DefaultInitWithConsistency(StrongConsistency),

        \* begin write k1: v1
        ([
            log |-> <<[key |-> k1, value |-> v1]>>,
            writeHistory |-> SetToBag({
                [
                    token |-> [epoch |-> 1, checkpoint |-> 1],
                    key |-> k1, value |-> v1, state |-> "init"
                ]
            })
        ]),

        \* fail write k1: v1
        [
            writeHistory |-> SetToBag({
                [
                    token |-> [epoch |-> 1, checkpoint |-> 1],
                    key |-> k1, value |-> v1, state |-> "failed"
                ]
            })
        ],

        \* increase consistent point, make failed write k1: v1 durable anyway
        [
            commitIndex |-> 1
        ],

        \* strong consistency reads will actually see the "failed" write in
        \* this case.
        [
            readConsistency |-> StrongConsistency,
            readKey |-> k1,
            read |-> {[
                value |-> v1,
                logIndex |-> 1
            ]}
        ]
    >>

\* At strong consistency, bounded staleness cannot enforce bounds.
\* Bounded staleness just becomes a read that non-deterministically
\* returns incomplete writes as well as the strongly consistent value.
\* !Note: this only checks what it says it does if StalenessBound <= 2!
BoundedStalenessAtStrongConsistencyDoesNotEnforceBounds ==
    <<
        DefaultInitWithConsistency(StrongConsistency),

        [
            log |-> <<
                [key |-> k1, value |-> v1]
            >>,
            writeHistory |-> SetToBag({
                [
                    token |-> [epoch |-> 1, checkpoint |-> 1],
                    key |-> k1, value |-> v1, state |-> "init"
                ]
            })
        ],

        [
            log |-> <<
                [key |-> k1, value |-> v1],
                [key |-> k1, value |-> v2]
            >>,
            writeHistory |-> SetToBag({
                [
                    token |-> [epoch |-> 1, checkpoint |-> 1],
                    key |-> k1, value |-> v1, state |-> "init"
                ],
                [
                    token |-> [epoch |-> 1, checkpoint |-> 2],
                    key |-> k1, value |-> v2, state |-> "init"
                ]
            })
        ],

        [
            log |-> <<
                [key |-> k1, value |-> v1],
                [key |-> k1, value |-> v2],
                [key |-> k1, value |-> v3]
            >>,
            writeHistory |-> SetToBag({
                [
                    token |-> [epoch |-> 1, checkpoint |-> 1],
                    key |-> k1, value |-> v1, state |-> "init"
                ],
                [
                    token |-> [epoch |-> 1, checkpoint |-> 2],
                    key |-> k1, value |-> v2, state |-> "init"
                ],
                [
                    token |-> [epoch |-> 1, checkpoint |-> 3],
                    key |-> k1, value |-> v3, state |-> "init"
                ]
            })
        ],

        [
            readConsistency |-> BoundedStaleness,
            readKey |-> k1,
            read |-> {
                [value |-> NoValue, logIndex |-> 0],
                [value |-> v1, logIndex |-> 1],
                [value |-> v2, logIndex |-> 2],
                [value |-> v3, logIndex |-> 3]
            }
        ]
    >>

PastedFromTrace ==
    <<
        [ log |-> <<>>,
            epoch |-> 1,
            read |-> {[logIndex |-> 0, value |-> NoValue]},
            readKey |-> k1,
            readConsistency |-> StrongConsistency,
            commitIndex |-> 0,
            readIndex |-> 0,
            writeHistory |-> EmptyBag,
            ConsistencyLevel |-> BoundedStaleness ],
        [ log |-> <<[key |-> k2, value |-> v1]>>,
            epoch |-> 1,
            read |-> {[logIndex |-> 0, value |-> NoValue]},
            readKey |-> k1,
            readConsistency |-> StrongConsistency,
            commitIndex |-> 0,
            readIndex |-> 0,
            writeHistory |-> SetToBag({
                [
                    token |-> [epoch |-> 1, checkpoint |-> 1],
                    key |-> k2, value |-> v1, state |-> "init"
                ]
            }),
            ConsistencyLevel |-> BoundedStaleness ],
        [ log |-> <<[key |-> k2, value |-> v1]>>,
            epoch |-> 1,
            read |->
            {[logIndex |-> 0, value |-> NoValue], [logIndex |-> 1, value |-> v1]},
            readKey |-> k2,
            readConsistency |-> BoundedStaleness,
            commitIndex |-> 0,
            readIndex |-> 0,
            writeHistory |-> SetToBag({
                [
                    token |-> [epoch |-> 1, checkpoint |-> 1],
                    key |-> k2, value |-> v1, state |-> "init"
                ]
            }),
            ConsistencyLevel |-> BoundedStaleness ]
    >>

AllTraces == [
    StrongConsistencyDirtyReads |-> StrongConsistencyDirtyReads,
    BoundedStalenessAllowsDirtyReads |-> BoundedStalenessAllowsDirtyReads,
    ReadNonEquivalencies |-> ReadNonEquivalencies,
    DurableDirtyRead |-> DurableDirtyRead,
    BoundedStalenessAtStrongConsistencyDoesNotEnforceBounds |-> BoundedStalenessAtStrongConsistencyDoesNotEnforceBounds,
    PastedFromTrace |-> PastedFromTrace
]

VARIABLE AnomalyTrace, traceIdx

InterpretTraceInit(trace) ==
    /\ IF   "ConsistencyLevel" \in DOMAIN trace
       THEN WriteConsistencyLevel = trace.ConsistencyLevel
       ELSE WriteConsistencyLevel \in CosmosDB!ConsistencyLevels
    /\ readIndex = trace.readIndex
    /\ log = trace.log
    /\ epoch = trace.epoch
    /\ commitIndex = trace.commitIndex
    /\ read = trace.read
    /\ readKey = trace.readKey
    /\ readConsistency = trace.readConsistency
    /\ writeHistory = trace.writeHistory

Init ==
    /\ AnomalyTrace \in DOMAIN AllTraces
    /\ traceIdx = 1
    /\ InterpretTraceInit(AllTraces[AnomalyTrace][traceIdx])

InterpretTrace(trace) ==
    LET ApplyTraceElement(var, name) ==
        /\ (name \in DOMAIN trace[traceIdx]) =>
            var = trace[traceIdx][name]
        /\ IF   name \in DOMAIN trace[traceIdx']
           THEN var' = trace[traceIdx'][name]
           ELSE UNCHANGED var
    IN  
        /\ traceIdx \in DOMAIN trace
        /\ traceIdx' = traceIdx + 1
        /\ traceIdx' \in DOMAIN trace
        /\ UNCHANGED WriteConsistencyLevel
        /\ ApplyTraceElement(readIndex, "readIndex")
        /\ ApplyTraceElement(log, "log")
        /\ ApplyTraceElement(epoch, "epoch")
        /\ ApplyTraceElement(commitIndex, "commitIndex")
        /\ ApplyTraceElement(read, "read")
        /\ ApplyTraceElement(readKey, "readKey")
        /\ ApplyTraceElement(readConsistency, "readConsistency")
        /\ ApplyTraceElement(writeHistory, "writeHistory")

anomalyVars == <<vars, AnomalyTrace, traceIdx>>

Next ==
    \/ /\ UNCHANGED AnomalyTrace
       /\ InterpretTrace(AllTraces[AnomalyTrace])
    \/ /\ traceIdx = Len(AllTraces[AnomalyTrace])
       /\ UNCHANGED anomalyVars

Spec ==
    Init /\ [][Next]_anomalyVars /\ WF_anomalyVars(Next)

THEOREM Spec => CosmosSpec

Live ==
    <>[](traceIdx = Len(AllTraces[AnomalyTrace]))

THEOREM Spec => Live

====
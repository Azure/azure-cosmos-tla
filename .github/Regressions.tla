----------------------------- MODULE Regressions -----------------------------
EXTENDS TLC, Integers, Sequences, IOUtils

AbsolutePathOfTLC == 
    TLCGet("config").install

Cmd ==
    <<"bash",
    "-c",
    "java " \o
    "-XX:+UseParallelGC " \o
    "-Dtlc2.TLC.stopAfter=60 " \o \* Terminate each test after one minute (time-bound model-checking).
    "-DTLA-Library=../%2$s " \o
    "-cp %1$s tlc2.TLC " \o
    "-gzip -cleanup -checkpoint 0 -noTE -workers auto -config %3$s %3$s">>

-----------------------------------------------------------------------------

Consistency ==
    \* Eventual is equivalent to Consistent_Prefix.
    <<"Eventual"(*, "Consistent_Prefix"*), "Session"(*, "Bounded_Staleness"*), "Strong">>

Check(conf, isWeaker, folder, model) ==
    LET ret == IOEnvExecTemplate(conf, Cmd, <<AbsolutePathOfTLC, folder, model>>).exitValue
    IN CASE ret =  0 ->
                IF isWeaker THEN TRUE ELSE
                \* Consistency-level is weaker than the property.
                Print(<<folder, conf, "Missing violation">>, TRUE)
         [] ret = 10 -> 
                Print(<<folder, conf, "Assumption violation">>, FALSE)
         [] ret = 12 -> 
                IF ~isWeaker THEN TRUE ELSE
                \* Consistency-level is equal to or stronger than the property.
                Print(<<folder, conf, "Safety violation">>, TRUE)
         [] ret = 13 -> 
                Print(<<folder, conf, "Liveness violation">>, FALSE)
         [] OTHER    -> 
                Print(<<folder, conf, IOEnvExecTemplate(conf, Cmd, <<AbsolutePathOfTLC, folder, model>>), "Error">>, FALSE)

ASSUME 
    \A comb \in ((DOMAIN Consistency) \X (DOMAIN Consistency)) :
        LET conf == [
                        mcConsistency |-> Consistency[comb[1]],
                        mcProperty |-> Consistency[comb[2]]
                    ]
        IN Check(conf, \/ comb[1] >= comb[2] 
                       \/ /\ conf.mcConsistency = "Session" \* With one writer, Session => Strong
                          /\ conf.mcProperty = "Strong", "scenario1", "MCswscop.tla")

ASSUME
    \A comb \in ((DOMAIN Consistency) \X (DOMAIN Consistency)) :
        LET conf == [
                        mcConsistency |-> Consistency[comb[1]],
                        mcProperty |-> Consistency[comb[2]]
                    ]
        IN Check(conf, \/ comb[1] >= comb[2] 
                       \/ /\ conf.mcConsistency = "Session" \* With one writer, Session => Strong
                          /\ conf.mcProperty = "Strong", "scenario2", "MCswscrw.tla")

ASSUME
    \A comb \in ((DOMAIN Consistency) \X (DOMAIN Consistency) \X {2} \X {1,2} \X {1,2}) : \* Due to the way the spec is modeled, a single region provides strong consistency. Thus, do not chec a single region.
        LET conf == [ 
                        mcConsistency |-> Consistency[comb[1]], 
                        mcProperty |-> Consistency[comb[2]],
                        mcNumRegions |-> comb[3],
                        mcNumWriteRegions |-> comb[4],
                        mcNumClientsPerRegion |-> comb[5]
                    ]
        IN conf.mcNumRegions >= conf.mcNumWriteRegions =>
                Check(conf, comb[1] >= comb[2], "general-model", "MCcosmos_client.tla")

=============================================================================
-------- CONFIG Regressions --------
\* TLC always expects a config file
===================================
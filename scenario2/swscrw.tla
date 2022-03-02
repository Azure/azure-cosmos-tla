-------------------------- MODULE swscrw --------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets
CONSTANT NumClients, MaxNumOp, Consistency, K
ASSUME Consistency \in {"Eventual", "Consistent_Prefix", "Session", "Bounded_Staleness", "Strong"}
ASSUME MaxNumOp<10 /\ NumClients=1
Cloud == 0
Clients == 1..NumClients
(* --algorithm swscrw {
variables
   chan = [n \in 0..NumClients |-> <<>>];  \* FIFO channels 

    \* network functions 
    macro send(des, msg) {
        chan[des] := Append(chan[des], msg);
    }

    macro receive(msg) {
        await Len(chan[self]) > 0;
        msg := Head(chan[self]);
        chan[self] := Tail(chan[self]);
    }

    process (cosmosdb \in {Cloud})
    variables
        Database = <<0>>; msg = <<>>;    
    {D: while(TRUE) { 
           receive(msg);
           if (msg.type="Write"){
              Database:=Append(Database,msg.dat);
    DW:       send(msg.orig, [type|-> "Ack", dat|->Database[Len(Database)], ses|->Len(Database)]);}             
           else if (msg.type="Eventual")
    DE:       with (k \in 1..Len(Database))
                 send(msg.orig, [type|-> "Reply", dat|->Database[k], ses|->k]);          
           else if (msg.type="Consistent_Prefix")
    DP:       with (k \in 1..Len(Database))
                 send(msg.orig, [type|-> "Reply", dat|->Database[k], ses|->k]);
           else if (msg.type="Session")
    DS:       with (k \in msg.ses..Len(Database))
                 send(msg.orig, [type|-> "Reply", dat|->Database[k], ses|->k]);
           else if (msg.type="Bounded_Staleness")                  
    DB:       with (k \in (IF Len(Database)>K THEN Len(Database)-K ELSE 1)..Len(Database))
                 send(msg.orig, [type|-> "Reply", dat|->Database[k], ses|->k]);
           else if (msg.type="Strong")                  
    DG:       with (k= Len(Database))
                 send(msg.orig, [type|-> "Reply", dat|->Database[k], ses|->k]);          
       }
    }
    
    process (client \in Clients)
    variables
        m = <<>>; op=0; v=0; chistory = <<0>>; ses=1; 
    {
     CR: while(op<MaxNumOp) {
           send(Cloud, [type |-> Consistency, ses|->ses, orig |-> self]); \* read
     CRA:  receive(m);  \* Reply      
           chistory:= Append(chistory,m.dat);
           v:=m.dat;
           ses:=m.ses;            
           \* write v+1     
     CW:   send(Cloud, [type |-> "Write", dat |-> v+1, ses|->ses, orig |-> self]);
     CWA:  receive(m); \* Ack
           ses:=m.ses;
           op:=op+1;            
        }
    }

} \* end algorithm
*)
\* BEGIN TRANSLATION
VARIABLES chan, pc, Database, msg, m, op, v, chistory, ses

vars == << chan, pc, Database, msg, m, op, v, chistory, ses >>

ProcSet == ({Cloud}) \cup (Clients)

Init == (* Global variables *)
        /\ chan = [n \in 0..NumClients |-> <<>>]
        (* Process cosmosdb *)
        /\ Database = [self \in {Cloud} |-> <<0>>]
        /\ msg = [self \in {Cloud} |-> <<>>]
        (* Process client *)
        /\ m = [self \in Clients |-> <<>>]
        /\ op = [self \in Clients |-> 0]
        /\ v = [self \in Clients |-> 0]
        /\ chistory = [self \in Clients |-> <<0>>]
        /\ ses = [self \in Clients |-> 1]
        /\ pc = [self \in ProcSet |-> CASE self \in {Cloud} -> "D"
                                        [] self \in Clients -> "CR"]

D(self) == /\ pc[self] = "D"
           /\ Len(chan[self]) > 0
           /\ msg' = [msg EXCEPT ![self] = Head(chan[self])]
           /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
           /\ IF msg'[self].type="Write"
                 THEN /\ Database' = [Database EXCEPT ![self] = Append(Database[self],msg'[self].dat)]
                      /\ pc' = [pc EXCEPT ![self] = "DW"]
                 ELSE /\ IF msg'[self].type="Eventual"
                            THEN /\ pc' = [pc EXCEPT ![self] = "DE"]
                            ELSE /\ IF msg'[self].type="Consistent_Prefix"
                                       THEN /\ pc' = [pc EXCEPT ![self] = "DP"]
                                       ELSE /\ IF msg'[self].type="Session"
                                                  THEN /\ pc' = [pc EXCEPT ![self] = "DS"]
                                                  ELSE /\ IF msg'[self].type="Bounded_Staleness"
                                                             THEN /\ pc' = [pc EXCEPT ![self] = "DB"]
                                                             ELSE /\ IF msg'[self].type="Strong"
                                                                        THEN /\ pc' = [pc EXCEPT ![self] = "DG"]
                                                                        ELSE /\ pc' = [pc EXCEPT ![self] = "D"]
                      /\ UNCHANGED Database
           /\ UNCHANGED << m, op, v, chistory, ses >>

DW(self) == /\ pc[self] = "DW"
            /\ chan' = [chan EXCEPT ![(msg[self].orig)] = Append(chan[(msg[self].orig)], ([type|-> "Ack", dat|->Database[self][Len(Database[self])], ses|->Len(Database[self])]))]
            /\ pc' = [pc EXCEPT ![self] = "D"]
            /\ UNCHANGED << Database, msg, m, op, v, chistory, ses >>

DE(self) == /\ pc[self] = "DE"
            /\ \E k \in 1..Len(Database[self]):
                 chan' = [chan EXCEPT ![(msg[self].orig)] = Append(chan[(msg[self].orig)], ([type|-> "Reply", dat|->Database[self][k], ses|->k]))]
            /\ pc' = [pc EXCEPT ![self] = "D"]
            /\ UNCHANGED << Database, msg, m, op, v, chistory, ses >>

DP(self) == /\ pc[self] = "DP"
            /\ \E k \in 1..Len(Database[self]):
                 chan' = [chan EXCEPT ![(msg[self].orig)] = Append(chan[(msg[self].orig)], ([type|-> "Reply", dat|->Database[self][k], ses|->k]))]
            /\ pc' = [pc EXCEPT ![self] = "D"]
            /\ UNCHANGED << Database, msg, m, op, v, chistory, ses >>

DS(self) == /\ pc[self] = "DS"
            /\ \E k \in msg[self].ses..Len(Database[self]):
                 chan' = [chan EXCEPT ![(msg[self].orig)] = Append(chan[(msg[self].orig)], ([type|-> "Reply", dat|->Database[self][k], ses|->k]))]
            /\ pc' = [pc EXCEPT ![self] = "D"]
            /\ UNCHANGED << Database, msg, m, op, v, chistory, ses >>

DB(self) == /\ pc[self] = "DB"
            /\ \E k \in (IF Len(Database[self])>K THEN Len(Database[self])-K ELSE 1)..Len(Database[self]):
                 chan' = [chan EXCEPT ![(msg[self].orig)] = Append(chan[(msg[self].orig)], ([type|-> "Reply", dat|->Database[self][k], ses|->k]))]
            /\ pc' = [pc EXCEPT ![self] = "D"]
            /\ UNCHANGED << Database, msg, m, op, v, chistory, ses >>

DG(self) == /\ pc[self] = "DG"
            /\ LET k == Len(Database[self]) IN
                 chan' = [chan EXCEPT ![(msg[self].orig)] = Append(chan[(msg[self].orig)], ([type|-> "Reply", dat|->Database[self][k], ses|->k]))]
            /\ pc' = [pc EXCEPT ![self] = "D"]
            /\ UNCHANGED << Database, msg, m, op, v, chistory, ses >>

cosmosdb(self) == D(self) \/ DW(self) \/ DE(self) \/ DP(self) \/ DS(self)
                     \/ DB(self) \/ DG(self)

CR(self) == /\ pc[self] = "CR"
            /\ IF op[self]<MaxNumOp
                  THEN /\ chan' = [chan EXCEPT ![Cloud] = Append(chan[Cloud], ([type |-> Consistency, ses|->ses[self], orig |-> self]))]
                       /\ pc' = [pc EXCEPT ![self] = "CRA"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ chan' = chan
            /\ UNCHANGED << Database, msg, m, op, v, chistory, ses >>

CRA(self) == /\ pc[self] = "CRA"
             /\ Len(chan[self]) > 0
             /\ m' = [m EXCEPT ![self] = Head(chan[self])]
             /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
             /\ chistory' = [chistory EXCEPT ![self] = Append(chistory[self],m'[self].dat)]
             /\ v' = [v EXCEPT ![self] = m'[self].dat]
             /\ ses' = [ses EXCEPT ![self] = m'[self].ses]
             /\ pc' = [pc EXCEPT ![self] = "CW"]
             /\ UNCHANGED << Database, msg, op >>

CW(self) == /\ pc[self] = "CW"
            /\ chan' = [chan EXCEPT ![Cloud] = Append(chan[Cloud], ([type |-> "Write", dat |-> v[self]+1, ses|->ses[self], orig |-> self]))]
            /\ pc' = [pc EXCEPT ![self] = "CWA"]
            /\ UNCHANGED << Database, msg, m, op, v, chistory, ses >>

CWA(self) == /\ pc[self] = "CWA"
             /\ Len(chan[self]) > 0
             /\ m' = [m EXCEPT ![self] = Head(chan[self])]
             /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
             /\ ses' = [ses EXCEPT ![self] = m'[self].ses]
             /\ op' = [op EXCEPT ![self] = op[self]+1]
             /\ pc' = [pc EXCEPT ![self] = "CR"]
             /\ UNCHANGED << Database, msg, v, chistory >>

client(self) == CR(self) \/ CRA(self) \/ CW(self) \/ CWA(self)

Next == (\E self \in {Cloud}: cosmosdb(self))
           \/ (\E self \in Clients: client(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

Messages == 
      [type : {"Eventual","Consistent_Prefix","Bounded_Staleness","Strong"}, dat: {0..Nat}, ses: {0..Nat}, orig: Clients]
\cup  [type : {"Reply", "Ack"}, dat: {0..Nat}, ses: {0..Nat}] 

\* Invariants for single client(ID=1) writing with op++
Eventual == 
    chistory[1][Len(chistory[1])] \in {Database[Cloud][i]: i \in 1..Len(Database[Cloud])}

Monotonic(history) ==
    \* Assert monotonic reads.
    \A i, j \in DOMAIN history : i <= j => history[i] <= history[j]

Consistent_Prefix == 
    /\ chistory[1][Len(chistory[1])] \in 
        {Database[Cloud][i]: i \in 1..Len(Database[Cloud])}
    /\ Monotonic(chistory[1])

Session == pc[1]="CW" =>
    /\ chistory[1][Len(chistory[1])] \in
        {Database[Cloud][i]: i \in ses[1]..Len(Database[Cloud])}
    /\ Monotonic(chistory[1])

Bounded_Staleness == pc[1]="CW" => 
    /\ chistory[1][Len(chistory[1])] \in
        {Database[Cloud][i]: i \in (IF Len(Database[Cloud])>K THEN Len(Database[Cloud])-K ELSE 1)..Len(Database[Cloud])}
    /\ Monotonic(chistory[1])

Strong == pc[1]="CW" =>
    /\ chistory[1][Len(chistory[1])] = Database[Cloud][Len(Database[Cloud])]
    /\ Monotonic(chistory[1])

=============================================================================

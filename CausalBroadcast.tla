----------------------------- MODULE CausalBroadcast -----------------------------
EXTENDS Naturals, FiniteSets, TLC
CONSTANT Replica
CONSTANT Messages



(*
--algorithm causal_broadcast
variables
  pending = [r \in Replica |-> {}];
  delivered = [r \in Replica |-> {}];
  broadcast = [r \in Replica |-> {}];
  availableMessages = Messages;
  vc = [r \in Replica |-> [s \in Replica |-> 0]];

fair process Sender \in Replica
variables
    mMsg = [val |-> 0, origin |-> 0, vclock |-> [r \in Replica |-> 0]];
begin
Loop: while TRUE do
    with sender \in Replica do
        if availableMessages # {} then
            with m \in availableMessages do
                vc[sender][sender] := vc[sender][sender] + 1;
                mMsg := [val |-> m, origin |-> sender, vclock |-> vc[sender]];
                pending := [x \in Replica |-> pending[x] \union {mMsg}];
                broadcast[sender] := broadcast[sender] \union {m};
                availableMessages := availableMessages \ {m}
            end with;
        end if;
     end with;
    end while;
end process;


fair process Receiver \in Replica
variables
    mMsg = [val |-> 0, origin |-> 0, vclock |-> [r \in Replica |-> 0]];
begin
Loop: while TRUE do
        with receiver \in Replica do
            if pending[receiver] # {} then
                with m \in pending[receiver] do
                    \* Deliver (remove from channel)
                    if \A q \in Replica : m.vclock[q] <= vc[receiver][q] then
                        delivered[receiver] := delivered[receiver] \union {m.val};
                        broadcast[receiver] := broadcast[receiver] \{m.val};
                        pending[receiver] := pending[receiver] \{m};
                        vc[receiver][m.origin] := vc[receiver][m.origin] + 1;
                    end if;
                end with;
            end if;
       end with;
     end while;
end process;


end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "8420f4b" /\ chksum(tla) = "5bda3e72")
\* Label Loop of process Sender at line 21 col 7 changed to Loop_
\* Process variable mMsg of process Sender at line 19 col 5 changed to mMsg_
VARIABLES pending, delivered, broadcast, availableMessages, vc, mMsg_, mMsg

vars == << pending, delivered, broadcast, availableMessages, vc, mMsg_, mMsg
        >>

ProcSet == (Replica) \cup (Replica)

Init == (* Global variables *)
        /\ pending = [r \in Replica |-> {}]
        /\ delivered = [r \in Replica |-> {}]
        /\ broadcast = [r \in Replica |-> {}]
        /\ availableMessages = Messages
        /\ vc = [r \in Replica |-> [s \in Replica |-> 0]]
        (* Process Sender *)
        /\ mMsg_ = [self \in Replica |-> [val |-> 0, origin |-> 0, vclock |-> [r \in Replica |-> 0]]]
        (* Process Receiver *)
        /\ mMsg = [self \in Replica |-> [val |-> 0, origin |-> 0, vclock |-> [r \in Replica |-> 0]]]

Sender(self) == /\ \E sender \in Replica:
                     IF availableMessages # {}
                        THEN /\ \E m \in availableMessages:
                                  /\ vc' = [vc EXCEPT ![sender][sender] = vc[sender][sender] + 1]
                                  /\ mMsg_' = [mMsg_ EXCEPT ![self] = [val |-> m, origin |-> sender, vclock |-> vc'[sender]]]
                                  /\ pending' = [x \in Replica |-> pending[x] \union {mMsg_'[self]}]
                                  /\ broadcast' = [broadcast EXCEPT ![sender] = broadcast[sender] \union {m}]
                                  /\ availableMessages' = availableMessages \ {m}
                        ELSE /\ TRUE
                             /\ UNCHANGED << pending, broadcast, 
                                             availableMessages, vc, mMsg_ >>
                /\ UNCHANGED << delivered, mMsg >>

Receiver(self) == /\ \E receiver \in Replica:
                       IF pending[receiver] # {}
                          THEN /\ \E m \in pending[receiver]:
                                    IF \A q \in Replica : m.vclock[q] <= vc[receiver][q]
                                       THEN /\ delivered' = [delivered EXCEPT ![receiver] = delivered[receiver] \union {m.val}]
                                            /\ broadcast' = [broadcast EXCEPT ![receiver] = broadcast[receiver] \{m.val}]
                                            /\ pending' = [pending EXCEPT ![receiver] = pending[receiver] \{m}]
                                            /\ vc' = [vc EXCEPT ![receiver][m.origin] = vc[receiver][m.origin] + 1]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED << pending, delivered, 
                                                            broadcast, vc >>
                          ELSE /\ TRUE
                               /\ UNCHANGED << pending, delivered, broadcast, 
                                               vc >>
                  /\ UNCHANGED << availableMessages, mMsg_, mMsg >>

Next == (\E self \in Replica: Sender(self))
           \/ (\E self \in Replica: Receiver(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Replica : WF_vars(Sender(self))
        /\ \A self \in Replica : WF_vars(Receiver(self))

\* END TRANSLATION 

(* For any two correct replicas i and j,
   every message broadcast by i is eventually delivered by j. *)
Validity ==
    [](\A i \in Replica: \A j \in Replica: \A msg \in Messages:
        msg \in broadcast[i] => <>(msg \in delivered[j]))



Agreement ==
  \A r1, r2 \in Replica, v \in Messages :
    (<>(v \in delivered[r1])) => (<>(v \in delivered[r2]))


      
\* Messages are delivered respecting the causal order (vector clocks)
CausalDelivery ==
  \A r \in Replica :
    \A m \in delivered[r] :
      \A q \in Replica :
        m.vclock[q] <= vc[r][q]

\*SpecProperties == []Validity /\ []Agreement
\*
\*THEOREM Spec => SpecProperties

=============================================================================
\* Modification History
\* Last modified Thu Aug 21 20:59:33 CEST 2025 by tanvimoharir
\* Created Thu Aug 21 16:07:05 CEST 2025 by tanvimoharir

---------------------------- MODULE ReliableBroadcast ----------------------------
EXTENDS Naturals, FiniteSets, TLC
CONSTANT Replica
CONSTANT Messages



(*
--algorithm reliable_broadcast
variables
  pending = [r \in Replica |-> {}];
  delivered = [r \in Replica |-> {}];
  availableMessages = Messages;

fair process Channel \in Replica
begin
Loop: while TRUE do
    either
    \* Broadcast a message
    if availableMessages # {} then
        with m \in availableMessages do
            pending := [x \in Replica |-> pending[x] \union {m}];
            availableMessages := availableMessages \ {m}
        end with;
    end if;
    or
        \*non deterministically deliver or drop a message
        with r \in Replica do
            if pending[r] # {} then
                with m \in pending[r] do
                    \* Deliver (remove from channel)
                    delivered[r] := delivered[r] \union {m};
                    pending[r] := pending[r] \{m};
                end with;
            end if;
       end with;
     end either;
     end while;
end process;
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "5b7da62c" /\ chksum(tla) = "b0d956b7")
VARIABLES pending, delivered, availableMessages

vars == << pending, delivered, availableMessages >>

ProcSet == (Replica)

Init == (* Global variables *)
        /\ pending = [r \in Replica |-> {}]
        /\ delivered = [r \in Replica |-> {}]
        /\ availableMessages = Messages

Channel(self) == \/ /\ IF availableMessages # {}
                          THEN /\ \E m \in availableMessages:
                                    /\ pending' = [x \in Replica |-> pending[x] \union {m}]
                                    /\ availableMessages' = availableMessages \ {m}
                          ELSE /\ TRUE
                               /\ UNCHANGED << pending, availableMessages >>
                    /\ UNCHANGED delivered
                 \/ /\ \E r \in Replica:
                         IF pending[r] # {}
                            THEN /\ \E m \in pending[r]:
                                      /\ delivered' = [delivered EXCEPT ![r] = delivered[r] \union {m}]
                                      /\ pending' = [pending EXCEPT ![r] = pending[r] \{m}]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << pending, delivered >>
                    /\ UNCHANGED availableMessages

Next == (\E self \in Replica: Channel(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Replica : WF_vars(Channel(self))

\* END TRANSLATION 



(* For any two correct replicas i and j,
   every message broadcast by i is eventually delivered by j. *)
Validity ==
    [](\A i \in Replica: \A j \in Replica: \A msg \in Messages:
        msg \in pending[i] => <>(msg \in delivered[j]))
       
(* if a correct replica delivers a message then all correct replicas will eventually deliver it *)       
Agreement ==
    [](\A i \in Replica: \A j \in Replica: \A msg \in Messages:
        msg \in delivered[i] => <>(msg \in delivered[j]))
        
Integrity ==
    [](\A i \in Replica: \A msg \in delivered[i]: msg \in Messages)

=============================================================================
\* Modification History
\* Last modified Thu Aug 21 09:49:47 CEST 2025 by tanvimoharir
\* Created Thu Aug 21 09:15:59 CEST 2025 by tanvimoharir

--------------------------- MODULE OpCounter ---------------------------
EXTENDS Naturals, FiniteSets, TLC
CONSTANT Replica
CONSTANT Messages

(*
--algorithm op_counter
variables
  pending = [r \in Replica |-> {}];
  delivered = [r \in Replica |-> {}];
  availableMessages = Messages;
  count = [r \in Replica |-> 0];

fair process Counter \in Replica
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
                    count[r] := count[r] + 1;
                end with;
            end if;
       end with;
     end either;
     end while;
end process;
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "d4644b93" /\ chksum(tla) = "745b4047")
VARIABLES pending, delivered, availableMessages, count

vars == << pending, delivered, availableMessages, count >>

ProcSet == (Replica)

Init == (* Global variables *)
        /\ pending = [r \in Replica |-> {}]
        /\ delivered = [r \in Replica |-> {}]
        /\ availableMessages = Messages
        /\ count = [r \in Replica |-> 0]

Counter(self) == \/ /\ IF availableMessages # {}
                          THEN /\ \E m \in availableMessages:
                                    /\ pending' = [x \in Replica |-> pending[x] \union {m}]
                                    /\ availableMessages' = availableMessages \ {m}
                          ELSE /\ TRUE
                               /\ UNCHANGED << pending, availableMessages >>
                    /\ UNCHANGED <<delivered, count>>
                 \/ /\ \E r \in Replica:
                         IF pending[r] # {}
                            THEN /\ \E m \in pending[r]:
                                      /\ delivered' = [delivered EXCEPT ![r] = delivered[r] \union {m}]
                                      /\ pending' = [pending EXCEPT ![r] = pending[r] \{m}]
                                      /\ count' = [count EXCEPT ![r] = count[r] + 1]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << pending, delivered, count >>
                    /\ UNCHANGED availableMessages

Next == (\E self \in Replica: Counter(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Replica : WF_vars(Counter(self))

\* END TRANSLATION 

Convergence ==
    []( \A r1 \in Replica, r2 \in Replica :
          delivered[r1] = delivered[r2] => count[r1] = count[r2])
          
EventualDelivery ==
  \A m \in Messages:
    ( \E i \in Replica: m \in delivered[i] )
      ~> ( \A j \in Replica: m \in delivered[j] )

SEC ==
  []Convergence /\ []EventualDelivery
    


=============================================================================
\* Modification History
\* Last modified Thu Aug 21 16:06:46 CEST 2025 by tanvimoharir
\* Created Sat Aug 16 12:02:53 CEST 2025 by tanvimoharir

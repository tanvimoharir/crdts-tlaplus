---------------------------- MODULE OpPNCounter ----------------------------
EXTENDS Naturals, FiniteSets, TLC
CONSTANT Replica
CONSTANT Messages

(*
--algorithm op_pncounter
variables
  pending = [r \in Replica |-> {}];
  delivered = [r \in Replica |-> {}];
  availableMessages = Messages;
  count = [r \in Replica |-> 0];
  positive = [r \in Replica |-> 0];
  negative = [r \in Replica |-> 0];

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
                    if m = "I" then
                        positive[r] := positive[r] + 1;
                    elsif m = "D" then
                        negative[r] := negative[r] + 1;
                    end if;
                    count[r] := positive[r] - negative[r];
                end with;
            end if;
       end with;
     end either;
     end while;
end process;
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "f581f4d0" /\ chksum(tla) = "85eb8d99")
VARIABLES pending, delivered, availableMessages, count, positive, negative

vars == << pending, delivered, availableMessages, count, positive, negative
        >>

ProcSet == (Replica)

Init == (* Global variables *)
        /\ pending = [r \in Replica |-> {}]
        /\ delivered = [r \in Replica |-> {}]
        /\ availableMessages = Messages
        /\ count = [r \in Replica |-> 0]
        /\ positive = [r \in Replica |-> 0]
        /\ negative = [r \in Replica |-> 0]

Counter(self) == \/ /\ IF availableMessages # {}
                          THEN /\ \E m \in availableMessages:
                                    /\ pending' = [x \in Replica |-> pending[x] \union {m}]
                                    /\ availableMessages' = availableMessages \ {m}
                          ELSE /\ TRUE
                               /\ UNCHANGED << pending, availableMessages >>
                    /\ UNCHANGED <<delivered, count, positive, negative>>
                 \/ /\ \E r \in Replica:
                         IF pending[r] # {}
                            THEN /\ \E m \in pending[r]:
                                      /\ delivered' = [delivered EXCEPT ![r] = delivered[r] \union {m}]
                                      /\ pending' = [pending EXCEPT ![r] = pending[r] \{m}]
                                      /\ IF m = "I"
                                            THEN /\ positive' = [positive EXCEPT ![r] = positive[r] + 1]
                                                 /\ UNCHANGED negative
                                            ELSE /\ IF m = "D"
                                                       THEN /\ negative' = [negative EXCEPT ![r] = negative[r] + 1]
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED negative
                                                 /\ UNCHANGED positive
                                      /\ count' = [count EXCEPT ![r] = positive'[r] - negative'[r]]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << pending, delivered, count, 
                                                 positive, negative >>
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
\* Last modified Thu Aug 21 16:38:58 CEST 2025 by tanvimoharir
\* Created Thu Aug 21 16:17:29 CEST 2025 by tanvimoharir

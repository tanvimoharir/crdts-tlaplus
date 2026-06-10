------------------------------ MODULE OpGOSet ------------------------------
EXTENDS Naturals, FiniteSets, TLC
CONSTANT Replica
CONSTANT Messages

(*
--algorithm op_goset
variables
  pending = [r \in Replica |-> {}];
  delivered = [r \in Replica |-> {}];
  availableMessages = Messages;
  gset = [r \in Replica |-> {}];

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
        \*non deterministically deliver a message
        with r \in Replica do
            if pending[r] # {} then
                with m \in pending[r] do
                    \* Deliver (remove from channel)
                    delivered[r] := delivered[r] \union {m};
                    pending[r] := pending[r] \{m};
                    gset[r] := gset[r] \union {m};
                end with;
            end if;
       end with;
     end either;
     end while;
end process;
end algorithm;
*)
\* BEGIN TRANSLATION (chksum(pcal) = "e63bbcba" /\ chksum(tla) = "8515ca67")
VARIABLES pending, delivered, availableMessages, gset

vars == << pending, delivered, availableMessages, gset >>

ProcSet == (Replica)

Init == (* Global variables *)
        /\ pending = [r \in Replica |-> {}]
        /\ delivered = [r \in Replica |-> {}]
        /\ availableMessages = Messages
        /\ gset = [r \in Replica |-> {}]

Counter(self) == \/ /\ IF availableMessages # {}
                          THEN /\ \E m \in availableMessages:
                                    /\ pending' = [x \in Replica |-> pending[x] \union {m}]
                                    /\ availableMessages' = availableMessages \ {m}
                          ELSE /\ TRUE
                               /\ UNCHANGED << pending, availableMessages >>
                    /\ UNCHANGED <<delivered, gset>>
                 \/ /\ \E r \in Replica:
                         IF pending[r] # {}
                            THEN /\ \E m \in pending[r]:
                                      /\ delivered' = [delivered EXCEPT ![r] = delivered[r] \union {m}]
                                      /\ pending' = [pending EXCEPT ![r] = pending[r] \{m}]
                                      /\ gset' = [gset EXCEPT ![r] = gset[r] \union {m}]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << pending, delivered, gset >>
                    /\ UNCHANGED availableMessages

Next == (\E self \in Replica: Counter(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Replica : WF_vars(Counter(self))

\* END TRANSLATION 

Convergence ==
    []( \A r1 \in Replica, r2 \in Replica :
          delivered[r1] = delivered[r2] => gset[r1] = gset[r2])
          
EventualDelivery ==
  \A m \in Messages:
    ( \E i \in Replica: m \in delivered[i] )
      ~> ( \A j \in Replica: m \in delivered[j] )

SEC ==
  []Convergence /\ []EventualDelivery

=============================================================================
\* Modification History
\* Last modified Thu Aug 21 16:46:22 CEST 2025 by tanvimoharir
\* Created Thu Aug 21 16:39:30 CEST 2025 by tanvimoharir

----------------------------- MODULE mv_reg_rco -----------------------------
EXTENDS 
    Naturals, FiniteSets, TLC, Bags
    
    
CONSTANT Replica
CONSTANT Message

(* vector clock library *)
vc_initial == [p \in Replica |-> 0]
vc_leq(vc1, vc2) == \A p \in Replica: vc1[p] <= vc2[p]

(* --algorithm multi_value_register
variables 
    broadcast = [p \in Replica |-> {}];
    delivered = [p \in Replica |-> {}];
    happensBefore = [p \in Message |-> {}];
    available_messages = Message;
    rb_broadcast = [p \in Replica |-> EmptyBag];
    rb_delivered = [p \in Replica |-> EmptyBag];
    correctProcess \in SUBSET Replica;
    
    (* Multi value Register state *)
    mv_value = [p \in Replica |-> {}]; \* current value of register
    mv_vc = [p \in Replica |-> [v \in Message |-> vc_initial]]; \* vc per msg value
    

process client \in {[name |-> "client", proc |-> "p1"]}
    begin
        client_loop:
        while TRUE do
            with msg \in available_messages; p \in Replica do
                available_messages := available_messages \ {msg};
                broadcast[p] := broadcast[p] \union {msg};
                happensBefore[msg] := delivered[p];
            end with
        end while
end process

fair process causal_broadcast \in {[name |-> "do_causal_broadcast", proc |-> p] : p \in Replica}
    variables pending = {}, VC = [p \in Replica |-> 0]; 
    begin
        causal_broadcast:
        while TRUE do 
            either (* upon rco-broadcast *)
                with msg \in broadcast[self.proc] do
                    broadcast[self.proc] := broadcast[self.proc] \ {msg};
                    (* trigger rco-deliver(self, m) *)
                    delivered[self.proc] := delivered[self.proc] \union {msg};
                    (* trigger rb-broadcast(VC, m) *)
                    rb_broadcast[self.proc] := rb_broadcast[self.proc]
                                  (+) SetToBag({[sdr |-> self.proc, vc |-> VC, msg |-> msg]});
                    VC[self.proc] := VC[self.proc] + 1;
                end with
            or (* upon rb-deliver *)
                with msg \in BagToSet(rb_delivered[self.proc]) do
                    when msg.sdr # self.proc;
                    rb_delivered[self.proc] := rb_delivered[self.proc] (-) SetToBag({msg});
                    pending := pending \union {msg};
                end with
            or
                (* deliver loop *)
                with msg \in pending do
                    when vc_leq(msg.vc, VC);
                    pending := pending \ {msg};
                    
                    (* --- Multi value Register update --*)
                    \* we add to set only when msg.vc is concurrent, what if one happens before other?
                    mv_value[self.proc] := ({u \in mv_value[self.proc] : ~vc_leq(msg.vc, mv_vc[self.proc][u]) } \cup {msg.msg});
                    mv_vc[self.proc][msg.msg] := msg.vc;
                    
                    
                    (* trigger rco-deliver *)
                    delivered[self.proc] := delivered[self.proc] \union {msg.msg};
                    VC[msg.sdr] := VC[msg.sdr] + 1;
                end with
            end either
        end while
end process

fair process do_rb_deliver \in {[name |-> "do_rb_deliver", proc |-> "p1"]}
    begin
        upon_receive:
        while TRUE do
            with proc \in Replica; msg \in BagToSet(rb_broadcast[proc]); receivers \in SUBSET Replica do
                (* when sender is correct, must deliver to self *)
                when proc \in correctProcess => proc \in receivers;
                (* when delivered to one correct process, must deliver to all *)
                when (\E p \in receivers: p \in correctProcess) =>
                        \A p \in correctProcess: p \in receivers;  
                rb_broadcast[proc] := rb_broadcast[proc] (-) SetToBag({msg});
                rb_delivered := [ p \in Replica |-> IF p \in receivers THEN rb_delivered[p] (+) SetToBag({msg}) ELSE rb_delivered[p]]
            end with
        end while
end process


end algorithm *)
\* BEGIN TRANSLATION (chksum(pcal) = "e51b6711" /\ chksum(tla) = "cf4ec105")
\* Label causal_broadcast of process causal_broadcast at line 44 col 9 changed to causal_broadcast_
VARIABLES broadcast, delivered, happensBefore, available_messages, 
          rb_broadcast, rb_delivered, correctProcess, mv_value, mv_vc, 
          pending, VC

vars == << broadcast, delivered, happensBefore, available_messages, 
           rb_broadcast, rb_delivered, correctProcess, mv_value, mv_vc, 
           pending, VC >>

ProcSet == ({[name |-> "client", proc |-> "p1"]}) \cup ({[name |-> "do_causal_broadcast", proc |-> p] : p \in Replica}) \cup ({[name |-> "do_rb_deliver", proc |-> "p1"]})

Init == (* Global variables *)
        /\ broadcast = [p \in Replica |-> {}]
        /\ delivered = [p \in Replica |-> {}]
        /\ happensBefore = [p \in Message |-> {}]
        /\ available_messages = Message
        /\ rb_broadcast = [p \in Replica |-> EmptyBag]
        /\ rb_delivered = [p \in Replica |-> EmptyBag]
        /\ correctProcess \in SUBSET Replica
        /\ mv_value = [p \in Replica |-> {}]
        /\ mv_vc = [p \in Replica |-> [v \in Message |-> vc_initial]]
        (* Process causal_broadcast *)
        /\ pending = [self \in {[name |-> "do_causal_broadcast", proc |-> p] : p \in Replica} |-> {}]
        /\ VC = [self \in {[name |-> "do_causal_broadcast", proc |-> p] : p \in Replica} |-> [p \in Replica |-> 0]]

client(self) == /\ \E msg \in available_messages:
                     \E p \in Replica:
                       /\ available_messages' = available_messages \ {msg}
                       /\ broadcast' = [broadcast EXCEPT ![p] = broadcast[p] \union {msg}]
                       /\ happensBefore' = [happensBefore EXCEPT ![msg] = delivered[p]]
                /\ UNCHANGED << delivered, rb_broadcast, rb_delivered, 
                                correctProcess, mv_value, mv_vc, pending, VC >>

causal_broadcast(self) == /\ \/ /\ \E msg \in broadcast[self.proc]:
                                     /\ broadcast' = [broadcast EXCEPT ![self.proc] = broadcast[self.proc] \ {msg}]
                                     /\ delivered' = [delivered EXCEPT ![self.proc] = delivered[self.proc] \union {msg}]
                                     /\ rb_broadcast' = [rb_broadcast EXCEPT ![self.proc] =              rb_broadcast[self.proc]
                                                                                            (+) SetToBag({[sdr |-> self.proc, vc |-> VC[self], msg |-> msg]})]
                                     /\ VC' = [VC EXCEPT ![self][self.proc] = VC[self][self.proc] + 1]
                                /\ UNCHANGED <<rb_delivered, mv_value, mv_vc, pending>>
                             \/ /\ \E msg \in BagToSet(rb_delivered[self.proc]):
                                     /\ msg.sdr # self.proc
                                     /\ rb_delivered' = [rb_delivered EXCEPT ![self.proc] = rb_delivered[self.proc] (-) SetToBag({msg})]
                                     /\ pending' = [pending EXCEPT ![self] = pending[self] \union {msg}]
                                /\ UNCHANGED <<broadcast, delivered, rb_broadcast, mv_value, mv_vc, VC>>
                             \/ /\ \E msg \in pending[self]:
                                     /\ vc_leq(msg.vc, VC[self])
                                     /\ pending' = [pending EXCEPT ![self] = pending[self] \ {msg}]
                                     /\ mv_value' = [mv_value EXCEPT ![self.proc] = ({u \in mv_value[self.proc] : ~vc_leq(msg.vc, mv_vc[self.proc][u]) } \cup {msg.msg})]
                                     /\ mv_vc' = [mv_vc EXCEPT ![self.proc][msg.msg] = msg.vc]
                                     /\ delivered' = [delivered EXCEPT ![self.proc] = delivered[self.proc] \union {msg.msg}]
                                     /\ VC' = [VC EXCEPT ![self][msg.sdr] = VC[self][msg.sdr] + 1]
                                /\ UNCHANGED <<broadcast, rb_broadcast, rb_delivered>>
                          /\ UNCHANGED << happensBefore, available_messages, 
                                          correctProcess >>

do_rb_deliver(self) == /\ \E proc \in Replica:
                            \E msg \in BagToSet(rb_broadcast[proc]):
                              \E receivers \in SUBSET Replica:
                                /\ proc \in correctProcess => proc \in receivers
                                /\ (\E p \in receivers: p \in correctProcess) =>
                                      \A p \in correctProcess: p \in receivers
                                /\ rb_broadcast' = [rb_broadcast EXCEPT ![proc] = rb_broadcast[proc] (-) SetToBag({msg})]
                                /\ rb_delivered' = [ p \in Replica |-> IF p \in receivers THEN rb_delivered[p] (+) SetToBag({msg}) ELSE rb_delivered[p]]
                       /\ UNCHANGED << broadcast, delivered, happensBefore, 
                                       available_messages, correctProcess, 
                                       mv_value, mv_vc, pending, VC >>

Next == (\E self \in {[name |-> "client", proc |-> "p1"]}: client(self))
           \/ (\E self \in {[name |-> "do_causal_broadcast", proc |-> p] : p \in Replica}: causal_broadcast(self))
           \/ (\E self \in {[name |-> "do_rb_deliver", proc |-> "p1"]}: do_rb_deliver(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {[name |-> "do_causal_broadcast", proc |-> p] : p \in Replica} : WF_vars(causal_broadcast(self))
        /\ \A self \in {[name |-> "do_rb_deliver", proc |-> "p1"]} : WF_vars(do_rb_deliver(self))

\* END TRANSLATION 
        
\* MVReg keeps sets of values → convergence requires all replicas to have seen all messages.
EventualConvergence ==
  \A r1, r2 \in Replica :
      <> (mv_value[r1] = mv_value[r2])

EventualDelivery ==
  \A m \in Message:
    (\E i \in correctProcess: m \in delivered[i])
      ~> (\A j \in correctProcess: m \in delivered[j])
      
SEC ==
  [](EventualConvergence /\ EventualDelivery)

=============================================================================
\* Modification History
\* Last modified Tue Oct 14 10:33:34 CEST 2025 by tanvimoharir
\* Created Thu Sep 18 21:26:51 CEST 2025 by tanvimoharir

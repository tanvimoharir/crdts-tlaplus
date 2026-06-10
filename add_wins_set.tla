---------------------------- MODULE add_wins_set ----------------------------
EXTENDS 
    Naturals, FiniteSets, TLC, Bags
    
    
CONSTANT Replica
CONSTANT Message

(* vector clock library *)
vc_initial == [p \in Replica |-> 0]
vc_leq(vc1, vc2) == \A p \in Replica: vc1[p] <= vc2[p]
vc_lt(vc1, vc2) == \A p \in Replica: vc1[p] < vc2[p]
vc_gt(vc1, vc2) == \A p \in Replica: vc1[p] > vc2[p]

(* --algorithm add_wins_set
variables 
    broadcast = [p \in Replica |-> {}];
    delivered = [p \in Replica |-> {}];
    happensBefore = [p \in Message |-> {}];
    available_messages = Message;
    rb_broadcast = [p \in Replica |-> EmptyBag];
    rb_delivered = [p \in Replica |-> EmptyBag];
    correctProcess \in SUBSET Replica;
    
    
    (* add and remove buffers *)
    abuf = [p \in Replica |-> {}];
    rbuf = [p \in Replica |-> {}];
    (* add win set and vc? *)
    aw_set = [p \in Replica |-> {}];
    
    

process client \in {[name |-> "client", proc |-> "p1"]}
    begin
        client_loop:
        while TRUE do
            with msg \in available_messages; p \in Replica do
                if msg.op = "add" then
                    abuf[p] := abuf[p] \union {msg.elem};
                elsif msg.op = "remove"  then
                    rbuf[p] := rbuf[p] \union {msg.elem};
                end if;
                available_messages := available_messages \ {msg};
                broadcast[p] := broadcast[p] \union {msg};
                happensBefore[msg] := delivered[p];
                
            end with;
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
                    
                    (* add-wins logic *)
\*                    The sender’s aw_set reflects its own adds right away, because there is sender's delivery below
                    if msg.op = "add" then
                        aw_set[self.proc] := aw_set[self.proc] \union {msg.elem};
                        abuf[self.proc] := abuf[self.proc] \ {msg.elem};
\*                    elsif msg.op = "remove" then
\*                        if msg.elem \in aw_set[self.proc]  then
\*                             aw_set[self.proc] := aw_set[self.proc] \ {msg.elem};
\*                        end if;
\*                        rbuf[self.proc] := rbuf[self.proc] \ {msg.elem};
                    end if;
                    
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
                    
                    (* add-wins logic *)
                    if msg.msg.op = "add" then
                        aw_set[self.proc] := aw_set[self.proc] \union {msg.msg.elem};
                        abuf[self.proc] := abuf[self.proc] \ {msg.msg.elem};
                    elsif msg.msg.op = "remove" then
                        if msg.msg.elem \in aw_set[self.proc]  then
                            if (vc_lt(msg.vc, VC) \/ vc_gt(msg.vc, VC)) then
                                aw_set[self.proc] := aw_set[self.proc] \ {msg.msg.elem};
                            end if;
                        end if;
                        rbuf[self.proc] := rbuf[self.proc] \ {msg.msg.elem};
                    end if;

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
\* BEGIN TRANSLATION (chksum(pcal) = "9f02d498" /\ chksum(tla) = "82f6129")
\* Label causal_broadcast of process causal_broadcast at line 56 col 9 changed to causal_broadcast_
VARIABLES broadcast, delivered, happensBefore, available_messages, 
          rb_broadcast, rb_delivered, correctProcess, abuf, rbuf, aw_set, 
          pending, VC

vars == << broadcast, delivered, happensBefore, available_messages, 
           rb_broadcast, rb_delivered, correctProcess, abuf, rbuf, aw_set, 
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
        /\ abuf = [p \in Replica |-> {}]
        /\ rbuf = [p \in Replica |-> {}]
        /\ aw_set = [p \in Replica |-> {}]
        (* Process causal_broadcast *)
        /\ pending = [self \in {[name |-> "do_causal_broadcast", proc |-> p] : p \in Replica} |-> {}]
        /\ VC = [self \in {[name |-> "do_causal_broadcast", proc |-> p] : p \in Replica} |-> [p \in Replica |-> 0]]

client(self) == /\ \E msg \in available_messages:
                     \E p \in Replica:
                       /\ IF msg.op = "add"
                             THEN /\ abuf' = [abuf EXCEPT ![p] = abuf[p] \union {msg.elem}]
                                  /\ rbuf' = rbuf
                             ELSE /\ IF msg.op = "remove"
                                        THEN /\ rbuf' = [rbuf EXCEPT ![p] = rbuf[p] \union {msg.elem}]
                                        ELSE /\ TRUE
                                             /\ rbuf' = rbuf
                                  /\ abuf' = abuf
                       /\ available_messages' = available_messages \ {msg}
                       /\ broadcast' = [broadcast EXCEPT ![p] = broadcast[p] \union {msg}]
                       /\ happensBefore' = [happensBefore EXCEPT ![msg] = delivered[p]]
                /\ UNCHANGED << delivered, rb_broadcast, rb_delivered, 
                                correctProcess, aw_set, pending, VC >>

causal_broadcast(self) == /\ \/ /\ \E msg \in broadcast[self.proc]:
                                     /\ broadcast' = [broadcast EXCEPT ![self.proc] = broadcast[self.proc] \ {msg}]
                                     /\ IF msg.op = "add"
                                           THEN /\ aw_set' = [aw_set EXCEPT ![self.proc] = aw_set[self.proc] \union {msg.elem}]
                                                /\ abuf' = [abuf EXCEPT ![self.proc] = abuf[self.proc] \ {msg.elem}]
                                           ELSE /\ TRUE
                                                /\ UNCHANGED << abuf, aw_set >>
                                     /\ delivered' = [delivered EXCEPT ![self.proc] = delivered[self.proc] \union {msg}]
                                     /\ rb_broadcast' = [rb_broadcast EXCEPT ![self.proc] =              rb_broadcast[self.proc]
                                                                                            (+) SetToBag({[sdr |-> self.proc, vc |-> VC[self], msg |-> msg]})]
                                     /\ VC' = [VC EXCEPT ![self][self.proc] = VC[self][self.proc] + 1]
                                /\ UNCHANGED <<rb_delivered, rbuf, pending>>
                             \/ /\ \E msg \in BagToSet(rb_delivered[self.proc]):
                                     /\ msg.sdr # self.proc
                                     /\ rb_delivered' = [rb_delivered EXCEPT ![self.proc] = rb_delivered[self.proc] (-) SetToBag({msg})]
                                     /\ pending' = [pending EXCEPT ![self] = pending[self] \union {msg}]
                                /\ UNCHANGED <<broadcast, delivered, rb_broadcast, abuf, rbuf, aw_set, VC>>
                             \/ /\ \E msg \in pending[self]:
                                     /\ vc_leq(msg.vc, VC[self])
                                     /\ pending' = [pending EXCEPT ![self] = pending[self] \ {msg}]
                                     /\ IF msg.msg.op = "add"
                                           THEN /\ aw_set' = [aw_set EXCEPT ![self.proc] = aw_set[self.proc] \union {msg.msg.elem}]
                                                /\ abuf' = [abuf EXCEPT ![self.proc] = abuf[self.proc] \ {msg.msg.elem}]
                                                /\ rbuf' = rbuf
                                           ELSE /\ IF msg.msg.op = "remove"
                                                      THEN /\ IF msg.msg.elem \in aw_set[self.proc]
                                                                 THEN /\ IF (vc_lt(msg.vc, VC[self]) \/ vc_gt(msg.vc, VC[self]))
                                                                            THEN /\ aw_set' = [aw_set EXCEPT ![self.proc] = aw_set[self.proc] \ {msg.msg.elem}]
                                                                            ELSE /\ TRUE
                                                                                 /\ UNCHANGED aw_set
                                                                 ELSE /\ TRUE
                                                                      /\ UNCHANGED aw_set
                                                           /\ rbuf' = [rbuf EXCEPT ![self.proc] = rbuf[self.proc] \ {msg.msg.elem}]
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED << rbuf, 
                                                                           aw_set >>
                                                /\ abuf' = abuf
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
                                       abuf, rbuf, aw_set, pending, VC >>

Next == (\E self \in {[name |-> "client", proc |-> "p1"]}: client(self))
           \/ (\E self \in {[name |-> "do_causal_broadcast", proc |-> p] : p \in Replica}: causal_broadcast(self))
           \/ (\E self \in {[name |-> "do_rb_deliver", proc |-> "p1"]}: do_rb_deliver(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {[name |-> "do_causal_broadcast", proc |-> p] : p \in Replica} : WF_vars(causal_broadcast(self))
        /\ \A self \in {[name |-> "do_rb_deliver", proc |-> "p1"]} : WF_vars(do_rb_deliver(self))

\* END TRANSLATION

Convergence ==
    []( \A r1 \in Replica, r2 \in Replica :
          delivered[r1] = delivered[r2] => aw_set[r1] = aw_set[r2])
          
EventualDelivery ==
  \A m \in Message:
    (\E i \in correctProcess: m \in delivered[i])
      ~> (\A j \in correctProcess: m \in delivered[j])


=============================================================================
\* Modification History
\* Last modified Wed Oct 01 13:17:19 CEST 2025 by tanvimoharir
\* Created Sun Sep 21 16:25:22 CEST 2025 by tanvimoharir

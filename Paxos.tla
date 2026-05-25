------------- MODULE Paxos --------------------
(*\* Paxos algorithm *)
(*\* Copr. (c) Murat Demirbas, Nov 10, 2016 *)
EXTENDS Integers, Sequences, FiniteSets
CONSTANT M, N, STOP, MAXB
ASSUME M \in Nat /\ N \in Nat /\ M<=N
Leader == 0..M-1
Acceptor == M..N
\* \* M leaders, and N-M+1 acceptors
Slots == 1..STOP
Ballots == 0..MAXB
\* \* In the model, use M=2, N=3, STOP=5 (number of slots), MAXB=10

(*
 --algorithm pax2
 { variable AccMsg={}, LMsg={};

   define{
   ExtractValSet(S) == {m.valSet : m \in S}
   SuitVal(S,s) == CHOOSE x \in S: x[1]=s /\ (\A z \in S:z[1]=s => x[2] >= z[2])

   SentAccMsgs(t,b) == {m \in AccMsg: (m.type=t) /\ (m.bal=b)}
   SentLMsgs(t,b) == {m \in LMsg: (m.type=t) /\ (m.bal=b)}
   SentLMsgs2(t,b,s) == {m \in LMsg: (m.type=t) /\ (m.bal=b) /\ (m.slot=s)}
   }

\* \* leader calls this to send p1a msg to acceptors
   macro SendP1 (b)
   {
     AccMsg:=AccMsg \union {[type |->"p1a", bal |-> b]};
   }

\* \* acceptor calls this to reply with a p1b msg to leader
   macro ReplyP1 (b)
   {
    await (b> maxBal) /\ (SentAccMsgs("p1a",b) #{});
    maxBal:=b;
    LMsg:=LMsg \union {[type |->"p1b", acc |-> self, bal |-> b, valSet |-> hVal]};
   }

\* \* leader calls this to collect p1b msgs from acceptors
   macro CollectP1 (b)
   {
    await Cardinality(SentLMsgs("p1b",b)) * 2 > Cardinality(Acceptor);
    elected:=TRUE;
    pVal:=UNION ExtractValSet(SentLMsgs("p1b",b));
   }


\* \* leader calls this to send p2a msg to acceptors
   macro SendP2 (b,s)
   {
    if (Cardinality({pv \in pVal: pv[1]=s})=0)
         AccMsg:=AccMsg \union {[type |-> "p2a", bal |-> b, slot |-> s, val |-> <<s,b,self>> ]};
    else AccMsg:=AccMsg \union {[type |-> "p2a", bal |-> b, slot |-> s, val |->SuitVal(pVal,s)]};
   }

\* \* acceptor calls this to reply with a p2b msg to leader
   macro ReplyP2 (b)
   {
    await (b>= maxBal);
    with (m \in SentAccMsgs("p2a",b)){
      maxBal:=b;
      hVal:= hVal \union {m.val}; \* update val heard with message of maxBal so far
      LMsg:=LMsg \union {[type |->"p2b", acc |-> self, bal |-> b, slot|-> m.slot, vv |->m.val[3] ]};
    }
   }

\* \* leader calls this to collect p1b msgs from acceptors
   macro CollectP2 (b,s)
   {
    await \/ (2*Cardinality(SentLMsgs2 ("p2b",b,s))> Cardinality(Acceptor))
           \/ (\E B \in Ballots: B>b /\ SentLMsgs("p1a",B)#{});
    if (\E B \in Ballots: B>b /\ SentLMsgs("p1a",B)#{})
       elected:=FALSE;
    else with (m \in SentLMsgs("p2b",b)) {lv:=m.vv;}
   }

\* \* leader calls this to finalize decision for slot s
   macro SendP3 (b,s)
   {
    AccMsg := AccMsg \union {[type |-> "p3a", bal |-> b, slot |-> s, dcd |->lv ]};
   }

\* \* acceptor calls this to finalize decision for slot
   macro RcvP3 (b)
   {
    await (b>= maxBal);
    with (m \in SentAccMsgs("p3a",b)){
      maxBal:=b;
      decided[m.slot]:= decided[m.slot] \union {m.dcd};
    }
   }

\* \* Acceptor process actions
   fair process (a \in Acceptor)
   variable maxBal=-1, hVal={<<-1,-1,-1>>}, \* \* <<s,b,v>>
            decided=[i \in Slots |-> {}];
   {
A:  while (TRUE) {
     with (ba \in Ballots) {
      either ReplyP1(ba)
      or ReplyP2(ba)
      or RcvP3(ba)
     }
     }
   }


\* \* Leader process
   fair process (l \in Leader)
   variable b=self, s=1, elected=FALSE, lv=-1, pVal={<<-1,-1,-1>>}; \* \* <<s,b,v>>
   {
L:  while (s \in Slots /\ b \in Ballots) {
\*\* Try to get elected as leader first
P1L:  while (elected # TRUE) {
          b:=b+M; \*\* guarantees unique ballot num
          SendP1(b);
CP1L:     CollectP1(b);
      };
\*\* Move to phase2
P2L:  SendP2(b,s);
CP2L: CollectP2(b,s);
\*\* Move to phase 3
P3L:  if (elected=TRUE){ \*\* leader may have been overthrown in P2
         SendP3 (b,s);
         s:=s+1;};
     }
   }

 }
*)

====

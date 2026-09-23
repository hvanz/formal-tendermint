------------------- MODULE TendermintByzantineRefinement --------------------
(***************************************************************************)
(* Refinement of TendermintByzantine by the leaderless                     *)
(* TendermintOperational, via a projection onto the honest validators      *)
(* (Lamport's "Byzantizing by refinement" pattern), admitting Byzantine    *)
(* leaders. Honest-scoped safety transfers by transitivity.                *)
(*                                                                         *)
(* THE MAPPING                                                             *)
(*   Validators <- Honest                                                  *)
(*   Quorum <- { Q \cap Honest : Q \in ByzQuorum } (honest quorums)        *)
(*   sent <- ProjByz: keep every PROPOSAL (sender-stripped, since the      *)
(*             leaderless upstream specs carry no proposal sender) and     *)
(*             every honest-sender VOTE; drop faulty votes.                *)
(*   locked, decision, Values, Valid <- by name                            *)
(*                                                                         *)
(* - Faulty VOTES are dropped, so faulty equivocation is invisible in the  *)
(*   image and the image honest validators never equivocate.               *)
(* - ALL proposals are kept (sender-stripped). The designated proposer     *)
(*   Proposer[r] may be FAULTY (Byzantine leaders); the proposal an honest *)
(*   validator acts on is then a FaultyStep-injected message, but because  *)
(*   every proposal is kept, its stripped image lands in the leaderless    *)
(*   operational proposal layer -- no honest sender, and no 2av relay, is  *)
(*   needed. An honest Propose and a faulty proposal-injecting FaultyStep  *)
(*   both map to P!Propose; a faulty vote maps to stuttering.              *)
(* - A 2f+1 ByzQuorum projects to its >= f+1 honest members, an honest     *)
(*   quorum; ByzQuorumIntersection (Q1 \cap Q2 \cap Honest # {}) makes     *)
(*   these honest quorums satisfy TendermintOperational's                  *)
(*   QuorumIntersection.                                                   *)
(*                                                                         *)
(* WHY SAFETY IS UNAFFECTED BY BYZANTINE LEADERS                           *)
(*   An equivocating proposer can split honest prevotes across values, but *)
(*   two values cannot both reach a polka in one round (each honest        *)
(*   validator prevotes once; two polkas need 2(f+1) > 2f+1 honest         *)
(*   prevoters). So Agreement/Validity (honest-scoped) still               *)
(*   hold; they transfer along the chain                                   *)
(*     TendermintVoting <- TendermintOperational <- TendermintByzantine,   *)
(*   reusing the safety theorems TendermintOperationalRefinement already   *)
(*   proves (which it in turn draws from TendermintVoting).                *)
(*                                                                         *)
(* MAIN RESULTS                                                            *)
(* - THEOREM Refinement == Spec => P!Spec (the linear-chain edge, onto the *)
(*   leaderless TendermintOperational).                                    *)
(* - THEOREM AgreementInv / ValidityInv: honest-scoped safety of           *)
(*   TendermintByzantine, each proved by transitivity Spec => P!Spec =>    *)
(*   []P!<prop>, reusing TendermintOperationalRefinement's already-proven  *)
(*   safety theorems.                                                      *)
(*                                                                         *)
(* The two honest-scoped bridge invariants on TendermintByzantine (TypeOK, *)
(*   VoteStepProgress) are proved here by induction: the honest-sender     *)
(*   cases are routine, and FaultyStep is excluded by the honest-scoped    *)
(*   guards (its message has a faulty sender) while leaving                *)
(*   round/step/locked untouched.                                          *)
(***************************************************************************)

EXTENDS TendermintByzantine

(***************************************************************************)
(* The refinement mapping.                                                 *)
(***************************************************************************)
\* Sender-strip a proposal (the leaderless upstream specs carry no proposal
\* sender); identity on votes.
Strip(m) == IF m.type = "Proposal"
            THEN [type |-> "Proposal", round |-> m.round,
                  value |-> m.value, validRound |-> m.validRound]
            ELSE m

\* Kept by the projection: every proposal (whatever its sender) and every
\* honest-sender vote. Faulty votes are dropped (erasing equivocation).
Kept(m) == m.type = "Proposal" \/ m.sender \in Honest

HonestQuorums == { Q \cap Honest : Q \in ByzQuorum }
ProjByz == { Strip(m) : m \in { x \in sent : Kept(x) } }

\* The linear-chain target: the operational, leaderless
\* TendermintOperational, projected onto the honest validators by the SAME
\* mapping. Honest validators run the TendermintOperational actions verbatim,
\* so each honest Byz action simulates its TendermintOperational namesake. We
\* instance TendermintOperationalRefinement (which EXTENDS
\* TendermintOperational and already proves its honest-independent safety by
\* refinement onto TendermintVoting), so P!Spec, every P!... operator, AND
\* its P!AgreementInv / P!ValidityInv safety theorems are
\* all in scope; the honest projection only needs the spec's CONSTANT
\* assumptions (discharged below). The per-honest-validator
\* round/step/locked/valid/decision map by identity (TendermintByzantine
\* already carries them only for Honest).
P == INSTANCE TendermintOperationalRefinement
     WITH Validators <- Honest, Quorum <- HonestQuorums, sent <- ProjByz

(***************************************************************************)
(* Bridge invariants on TendermintByzantine (honest-scoped).               *)
(* round[m.sender] is referenced only for honest senders (m.sender \in     *)
(* Honest), which are the domain of round. Honest validators run the       *)
(* TendermintOperational actions; FaultyStep adds a faulty-sender message, *)
(* which the honest-scoped guards exclude (m.sender \in Faulty so m.sender *)
(* \notin Honest), leaving round/step/locked untouched.                    *)
(***************************************************************************)
VoteStepProgress ==
  /\ \A m \in SentPrevotes : m.sender \in Honest =>
        \/ m.round < round[m.sender]
        \/ /\ (m.round = round[m.sender] 
           /\ step[m.sender] \in {"prevote", "precommit", "decided"})
  /\ \A m \in SentPrecommits : m.sender \in Honest =>
        \/ m.round < round[m.sender]
        \/ /\ (m.round = round[m.sender] 
           /\ step[m.sender] \in {"precommit", "decided"})

\* Every honest validator is a validator (so round/step/etc. are well-typed).
LEMMA HonestIsValidator == Honest \subseteq Validators
BY DEF Honest

THEOREM TypeOKInv == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK, LockState, ValuesOrNil, Rounds, Step
<1>2. ASSUME TypeOK, [Next]_vars PROVE TypeOK'
  <2> USE <1>2, HonestIsValidator DEFS TypeOK, ValuesOrNil, Message, ProposalMsg, PrevoteMsg, 
    PrecommitMsg, Rounds, Step, LockState, Proposal, getValue, Prevote, Precommit, ProposalsFromProposerAt, SentProposals
  <2>1. CASE Next
    <3>1. ASSUME NEW p \in Honest, Propose(p) PROVE TypeOK'
      BY <3>1 DEF Propose
    <3>2. ASSUME NEW p \in Honest, PrevoteNil(p) PROVE TypeOK'
      BY <3>2 DEF PrevoteNil
    <3>3. ASSUME NEW p \in Honest, OnProposalNoPOL(p) PROVE TypeOK'
      BY <3>3 DEF OnProposalNoPOL
    <3>4. ASSUME NEW p \in Honest, OnProposalWithPOL(p) PROVE TypeOK'
      BY <3>4 DEF OnProposalWithPOL
    <3>5. ASSUME NEW p \in Honest, OnPrevoteQuorumValueFirstTime(p) PROVE TypeOK'
      BY <3>5 DEF OnPrevoteQuorumValueFirstTime
    <3>6. ASSUME NEW p \in Honest, OnPrevoteQuorumValueLateUpdate(p) PROVE TypeOK'
      BY <3>6 DEF OnPrevoteQuorumValueLateUpdate
    <3>7. ASSUME NEW p \in Honest, OnPrevoteQuorumNil(p) PROVE TypeOK'
      BY <3>7 DEF OnPrevoteQuorumNil
    <3>8. ASSUME NEW p \in Honest, PrecommitNil(p) PROVE TypeOK'
      BY <3>8 DEF PrecommitNil 
    <3>9. ASSUME NEW p \in Honest, OnPrecommitQuorumValue(p) PROVE TypeOK'
      BY <3>9 DEF OnPrecommitQuorumValue
    <3>10. ASSUME NEW p \in Honest, AdvanceRound(p) PROVE TypeOK'
      BY <3>10 DEF AdvanceRound
    <3>11. ASSUME NEW p \in Honest, SkipRound(p) PROVE TypeOK'
      BY <3>11 DEF SkipRound
    <3>12. ASSUME NEW p \in Faulty, FaultyStep(p) PROVE TypeOK'
      BY <3>12 DEF FaultyStep
    <3>13. QED
      BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12 DEF Next
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEF vars
  <2>3. QED
    BY <2>1, <2>2
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM VoteStepProgressInv == Spec => []VoteStepProgress
<1>1. Init => VoteStepProgress
  BY DEF Init, VoteStepProgress, SentPrevotes, SentPrecommits
<1>2. ASSUME TypeOK, VoteStepProgress, [Next]_vars PROVE VoteStepProgress'
  <2> USE <1>2, HonestIsValidator DEFS VoteStepProgress, TypeOK, Message, ProposalMsg, PrevoteMsg, PrecommitMsg,
    ValuesOrNil, Rounds, Step, SentPrevotes, SentPrecommits, Proposal, Prevote, Precommit
  <2>1. CASE Next
    <3>1. ASSUME NEW p \in Honest, Propose(p) PROVE VoteStepProgress'
      BY <3>1 DEF Propose
    <3>2. ASSUME NEW p \in Honest, PrevoteNil(p) PROVE VoteStepProgress'
      BY <3>2 DEF PrevoteNil
    <3>3. ASSUME NEW p \in Honest, OnProposalNoPOL(p) PROVE VoteStepProgress'
      BY <3>3 DEF OnProposalNoPOL
    <3>4. ASSUME NEW p \in Honest, OnProposalWithPOL(p) PROVE VoteStepProgress'
      BY <3>4 DEF OnProposalWithPOL
    <3>5. ASSUME NEW p \in Honest, OnPrevoteQuorumValueFirstTime(p) PROVE VoteStepProgress'
      BY <3>5 DEF OnPrevoteQuorumValueFirstTime
    <3>6. ASSUME NEW p \in Honest, OnPrevoteQuorumValueLateUpdate(p) PROVE VoteStepProgress'
      BY <3>6 DEF OnPrevoteQuorumValueLateUpdate
    <3>7. ASSUME NEW p \in Honest, OnPrevoteQuorumNil(p) PROVE VoteStepProgress'
      BY <3>7 DEF OnPrevoteQuorumNil
    <3>8. ASSUME NEW p \in Honest, PrecommitNil(p) PROVE VoteStepProgress'
      BY <3>8 DEF PrecommitNil
    <3>9. ASSUME NEW p \in Honest, OnPrecommitQuorumValue(p) PROVE VoteStepProgress'
      BY <3>9 DEF OnPrecommitQuorumValue
    <3>10. ASSUME NEW p \in Honest, AdvanceRound(p) PROVE VoteStepProgress'
      BY <3>10 DEF AdvanceRound
    <3>11. ASSUME NEW p \in Honest, SkipRound(p) PROVE VoteStepProgress'
      BY <3>11 DEF SkipRound
    <3>12. ASSUME NEW p \in Faulty, FaultyStep(p) PROVE VoteStepProgress'
      BY <3>12, FaultyType DEF FaultyStep, Honest
    <3>15. QED
      BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12 DEF Next
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEF vars, VoteStepProgress, SentPrevotes, SentPrecommits
  <2>3. QED
    BY <2>1, <2>2
<1>3. QED
  BY <1>1, <1>2, TypeOKInv, PTL DEF Spec

-----------------------------------------------------------------------------

(***************************************************************************)
(* Refinement onto TendermintOperational: the LINEAR-CHAIN step            *)
(*   TendermintVoting <- TendermintOperational <- TendermintByzantine.     *)
(*                                                                         *)
(* Both specs are now leaderless. Honest validators run the                *)
(* TendermintOperational actions verbatim, so each honest Byz action       *)
(* simulates its TendermintOperational NAMESAKE under the same honest      *)
(* projection (sent <- ProjByz, Quorum <- HonestQuorums,                   *)
(* round/step/locked/valid/decision by identity). Unlike the abstract      *)
(* TendermintVoting (whose Prevote* carry vote-uniqueness guards), the     *)
(* operational target's guards are the SAME step/round guards Byz uses, so *)
(* the simulation needs no abstract one-vote bridge, only the              *)
(* quorum/proposal projection lemmas below, retargeted at P! operators.    *)
(*                                                                         *)
(* The decisive cases: a faulty PROPOSAL injected by FaultyStep maps to    *)
(* P!Propose (kept, stripped to a leaderless proposal); a faulty VOTE is a *)
(* stuttering step. SkipRound: Byz's WeakQuorum gate yields an honest      *)
(* sender at r (WeakQuorumHasHonest), whose message is kept and witnesses  *)
(* TendermintOperational's one-message guard P!ExistsMessageAt(r).         *)
(***************************************************************************)
LEMMA NilProjP == P!nil = nil
BY DEF P!nil, nil

\* Vote constructors coincide; a stripped proposal equals the leaderless
\* 3-arg P!Proposal.
LEMMA PrevoteProjP   == \A a, b, c : P!Prevote(a, b, c)   = Prevote(a, b, c)
BY DEF P!Prevote, Prevote
LEMMA PrecommitProjP == \A a, b, c : P!Precommit(a, b, c) = Precommit(a, b, c)
BY DEF P!Precommit, Precommit
LEMMA StrippedProposalIsP ==
  \A m : m.type = "Proposal" => Strip(m) = P!Proposal(m.round, m.value, m.validRound)
BY DEF Strip, P!Proposal

\* The projection keeps the honest part of each vote set (P side).
LEMMA SentPrevotesProjP   == P!SentPrevotes   = { m \in SentPrevotes   : m.sender \in Honest }
BY DEFS P!SentPrevotes, SentPrevotes, ProjByz, Kept, Strip
LEMMA SentPrecommitsProjP == P!SentPrecommits = { m \in SentPrecommits : m.sender \in Honest }
BY DEFS P!SentPrecommits, SentPrecommits, ProjByz, Kept, Strip
LEMMA SentProposalsProjP  == P!SentProposals  = { Strip(m) : m \in SentProposals }
BY DEFS P!SentProposals, SentProposals, ProjByz, Kept, Strip

LEMMA HonestPrevoteSenderKeptP ==
  ASSUME NEW v, NEW r, NEW s \in Honest, s \in PrevoteSendersFor(v, r)
  PROVE  s \in P!PrevoteSendersFor(v, r)
BY SentPrevotesProjP DEFS P!PrevotesAt, P!PrevoteSendersFor, PrevotesAt, PrevoteSendersFor

LEMMA HonestPrecommitSenderKeptP ==
  ASSUME NEW v, NEW r, NEW s \in Honest, s \in PrecommitSendersFor(v, r)
  PROVE  s \in P!PrecommitSendersFor(v, r)
BY SentPrecommitsProjP DEFS P!PrecommitsAt, P!PrecommitSendersFor, PrecommitsAt, PrecommitSendersFor

LEMMA ByzPrevoteQuorumProjP ==
  ASSUME NEW v, NEW r, ExistsPrevoteQuorum(v, r)
  PROVE  P!ExistsPrevoteQuorum(v, r)
BY HonestPrevoteSenderKeptP DEFS ExistsPrevoteQuorum, HonestQuorums, P!ExistsPrevoteQuorum

LEMMA ByzPrecommitQuorumProjP ==
  ASSUME NEW v, NEW r, ExistsPrecommitQuorum(v, r)
  PROVE  P!ExistsPrecommitQuorum(v, r)
BY HonestPrecommitSenderKeptP DEFS ExistsPrecommitQuorum, HonestQuorums, P!ExistsPrecommitQuorum

\* A proposal at round r (any sender) is kept and stripped, so it lands in the
\* leaderless P!ProposalsAt(r) -- the guard the operational actions read.
LEMMA ProposalKeptInOperationalAt ==
  ASSUME NEW r \in Rounds, NEW prop \in ProposalsFromProposerAt(r)
  PROVE  Strip(prop) \in P!ProposalsAt(r)
BY SentProposalsProjP DEFS P!ProposalsAt, ProposalsFromProposerAt, SentProposals, Strip

\* An honest sender of any message at r is kept (its message survives the
\* projection), witnessing P!ExistsMessageAt(r) = \E msg \in P!sent: msg.round=r.
LEMMA HonestMessageAtKeptP ==
  ASSUME NEW r, NEW s \in Honest, s \in SendersOfAnyMessageAt(r)
  PROVE  P!ExistsMessageAt(r)
BY DEFS Kept, P!ExistsMessageAt, ProjByz, SendersOfAnyMessageAt, SendersOfTypeAtRound, Strip

\* Growth of the projection when one kept message is added to sent: its
\* stripped image joins ProjByz. Generic over the base set S so it applies to
\* the primed ProjByz (S <- sent). Isolates the set-builder-over-union step
\* the backends do not discharge inline (needed by the nil-vote cases below).
LEMMA ProjAddKept ==
  ASSUME NEW S, NEW m, Kept(m)
  PROVE  { Strip(x) : x \in { y \in S \cup {m} : Kept(y) } }
       = { Strip(x) : x \in { y \in S : Kept(y) } } \cup { Strip(m) }
BY DEF Kept

(***************************************************************************)
(* Refinement proof to the higher-level spec.                              *)
(***************************************************************************)
THEOREM Refinement == Spec => P!Spec
<1>1. Init => P!Init
  BY NilProjP DEF Init, P!Init, ProjByz, Kept
<1>2. ASSUME TypeOK, VoteStepProgress, [Next]_vars PROVE [P!Next]_(P!vars)
  <2> USE DEF P!vars
  <2>1. CASE Next
    <3> USE <1>2, <2>1, NilProjP, PrevoteProjP, PrecommitProjP, HonestNonEmpty, HonestIsValidator,
          ByzPrevoteQuorumProjP, ByzPrecommitQuorumProjP, ProposalKeptInOperationalAt
        DEFS TypeOK, ProjByz, P!Next, P!Rounds, P!ProposalsAt, Rounds, Strip, Kept, 
          ProposalsFromProposerAt, SentProposals, Prevote, Precommit
    <3>1. ASSUME NEW p \in Honest, Propose(p)
          PROVE  [P!Next]_(P!vars)
      BY <3>1, StrippedProposalIsP DEFS getValue, LockState, P!Propose, Proposal, Propose, ValuesOrNil
    <3>2. ASSUME NEW p \in Honest, PrevoteNil(p)
          PROVE  [P!Next]_(P!vars)
      BY <3>2, ProjAddKept DEFS P!PrevoteNil, PrevoteNil
    <3>3. ASSUME NEW p \in Honest, OnProposalNoPOL(p)
          PROVE  [P!Next]_(P!vars)
      BY <3>3 DEFS OnProposalNoPOL, P!OnProposalNoPOL
    <3>4. ASSUME NEW p \in Honest, OnProposalWithPOL(p)
          PROVE  [P!Next]_(P!vars)
      BY <3>4 DEFS OnProposalWithPOL, P!OnProposalWithPOL, P!Range, Range
    <3>5. ASSUME NEW p \in Honest, OnPrevoteQuorumValueFirstTime(p)
          PROVE  [P!Next]_(P!vars)
      BY <3>5 DEFS OnPrevoteQuorumValueFirstTime, P!OnPrevoteQuorumValueFirstTime
    <3>6. ASSUME NEW p \in Honest, OnPrevoteQuorumValueLateUpdate(p)
          PROVE  [P!Next]_(P!vars)
      BY <3>6 DEFS OnPrevoteQuorumValueLateUpdate, P!OnPrevoteQuorumValueLateUpdate
    <3>7. ASSUME NEW p \in Honest, OnPrevoteQuorumNil(p)
          PROVE  [P!Next]_(P!vars)
      BY <3>7, ProjAddKept DEFS OnPrevoteQuorumNil, P!OnPrevoteQuorumNil
    <3>8. ASSUME NEW p \in Honest, PrecommitNil(p)
          PROVE  [P!Next]_(P!vars)
      BY <3>8, ProjAddKept DEFS PrecommitNil, P!PrecommitNil
    <3>9. ASSUME NEW p \in Honest, OnPrecommitQuorumValue(p)
          PROVE  [P!Next]_(P!vars)
      BY <3>9 DEFS OnPrecommitQuorumValue, P!OnPrecommitQuorumValue
    <3>10. ASSUME NEW p \in Honest, AdvanceRound(p)
           PROVE  [P!Next]_(P!vars)
      BY <3>10 DEFS AdvanceRound, P!AdvanceRound, P!Next
    <3>11. ASSUME NEW p \in Honest, SkipRound(p)
           PROVE  [P!Next]_(P!vars)
      BY <3>11, HonestMessageAtKeptP, WeakQuorumHasHonest DEFS P!SkipRound, SkipRound
    <3>12. ASSUME NEW p \in Faulty, FaultyStep(p)
           PROVE  [P!Next]_(P!vars)
      BY <3>12, FaultyType, StrippedProposalIsP 
      DEFS FaultyStep, Honest, Message, P!Propose, PrecommitMsg, PrevoteMsg, ProposalMsg
    <3>15. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12 DEF Next
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEF vars, ProjByz
  <2>3. QED
    BY <1>2, <2>2, <2>1
<1>3. QED
  BY <1>1, <1>2, TypeOKInv, VoteStepProgressInv, PTL DEF Spec, P!Spec

-----------------------------------------------------------------------------
LEMMA ConstantAssumptions ==
  /\ Honest # {}
  /\ \A v \in Values : Valid(v) \in BOOLEAN
  /\ \E v \in Values : Valid(v)
  /\ HonestQuorums \in SUBSET (SUBSET Honest)
  /\ \A Q1, Q2 \in HonestQuorums : Q1 \cap Q2 # {}
<1>1. HonestQuorums \in SUBSET (SUBSET Honest)
  BY DEF HonestQuorums
<1>2. \A Q1, Q2 \in HonestQuorums : Q1 \cap Q2 # {}
  BY ByzQuorumIntersection DEF HonestQuorums
<1>. QED
  BY HonestNonEmpty, ValidIsBoolean, ValidNonEmpty, <1>1, <1>2

(***************************************************************************)
(* End-to-end transfer: honest-scoped Agreement / Validity follow by       *)
(* TRANSITIVITY along the linear chain -- Spec => P!Spec                   *)
(* (Refinement), then P!Spec => []P!<prop> reusing                         *)
(* TendermintOperationalRefinement's already-proven safety theorems        *)
(* (P!AgreementInv etc., which in turn refine onto TendermintVoting). The  *)
(* discharge of TendermintOperational's CONSTANT assumptions under the     *)
(* mapping (see ConstantAssumptions) is                                    *)
(* supplied as the HonestQuorum* / ValidIs* facts. Each property mentions  *)
(* only decision (mapped by identity) over P!Validators = Honest, and      *)
(* Valid / nil (mapped by name / by the same CHOOSE), so the operational   *)
(* property IS the honest-scoped TendermintByzantine property.             *)
(***************************************************************************)
THEOREM AgreementInv == Spec => []Agreement
<1>1. P!Spec => []P!Agreement
  BY P!AgreementInv, ConstantAssumptions, PTL
<1>2. QED
  BY <1>1, Refinement, PTL DEF P!Agreement, Agreement, P!nil, nil

THEOREM ValidityInv == Spec => []Validity
<1>1. P!Spec => []P!Validity
  BY P!ValidityInv, ConstantAssumptions, PTL
<1>2. QED
  BY <1>1, Refinement, PTL DEF P!Validity, Validity, P!nil, nil

THEOREM IntegrityInv == Spec => []IntegrityStep
<1>1. P!Spec => []P!IntegrityStep
  BY P!IntegrityInv, ConstantAssumptions, PTL
<1>2. QED
  BY <1>1, Refinement, PTL DEF P!IntegrityStep, IntegrityStep, P!nil, nil

=============================================================================
\* Modification History
\* Created Jun 10 2026 by hvanz (Hernán Vanzetto)

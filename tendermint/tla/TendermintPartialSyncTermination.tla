----------------------- MODULE TendermintPartialSyncTermination ----------------
(***************************************************************************)
(* TLAPS proof of the conditional liveness property Termination for        *)
(* TendermintPartialSync.tla. That module is the DLS real-time-clock       *)
(* specification at the bottom of the refinement chain. The strategy       *)
(* follows Section IV of the paper, Lemmas 5 to 7.                         *)
(*                                                                         *)
(* This is the COMPOSITION module of the termination lattice. The lattice  *)
(* is split into modules, so that tlapm can check them in parallel and     *)
(* incrementally. See the `termination` targets of the Makefile, and       *)
(* ARCHITECTURE.md. This module EXTENDS the independent middle modules,    *)
(* and it assembles TerminationThm.                                        *)
(* - TendermintPartialSyncTerminationBase holds Layers 0 to 2. Those are   *)
(*   safety, the facts about the clock and the latches, the invariants     *)
(*   about the messages, the decision and the delivery, and HonestFinite.  *)
(*   It EXTENDS TendermintPartialSyncRefinement, so the discharged safety  *)
(*   results are in scope by name throughout. Those results are InvProof,  *)
(*   IntegrityInv, []IntegrityStep, and the Mono* and SentExtend lemmas.   *)
(* - TendermintPartialSyncTerminationWithinRound holds the within-round    *)
(*   safety support for the repaired case split of paper Lemma 5.          *)
(* - TendermintPartialSyncTerminationCascade holds the quantitative        *)
(*   cascade of Lemma 5, which is Lemma5OrBlockingLock. Lemma5OrPriorLock  *)
(*   is a proved corollary of it. The cascade is reached through           *)
(*   ...LockRetry.                                                         *)
(* - TendermintPartialSyncTerminationCrossRound holds paper Lemma 6, which *)
(*   ValidCatchUp and its corollary HighLockCatchUp represent.             *)
(* - TendermintPartialSyncTerminationRoundProgress holds                   *)
(*   PostGSTRoundProgress, derived from RoundGrowth, which that module     *)
(*   proves. It EXTENDS ...NonZeno, so the burst core is in scope through  *)
(*   it.                                                                   *)
(* - TendermintPartialSyncTerminationSelection holds the selection of the  *)
(*   entry into a good round.                                              *)
(* - TendermintPartialSyncTerminationDominator holds the stable entry      *)
(*   dominance.                                                            *)
(* - TendermintPartialSyncTerminationLockRetry holds the termination of    *)
(*   the retry, which is LockRetryDecides, by a finite count of disruptive *)
(*   pairs.                                                                *)
(*                                                                         *)
(*  This module owns paper Lemma 7. Lemma7Selection, GoodRoundRecurrence   *)
(*  and TerminationThm are all a checked temporal composition. The         *)
(*  ingredients of the selection are discharged here. They are three: a    *)
(*  dominating correct process always exists, the timeout condition 4      *)
(*  holds beyond a round threshold, and the dominating process proposes    *)
(*  again. Checked glue consumes paper Lemma 5. NO admission carries open  *)
(*  content here. ...LockRetry owns the retry frontier, and ...Cascade     *)
(*  proves Lemma5OrBlockingLock. TerminationThm is therefore proved        *)
(*  outright.                                                              *)
(***************************************************************************)

EXTENDS TendermintPartialSyncTerminationDominator,
        TendermintPartialSyncTerminationLockRetry
\* ===========================================================================
\* Phase 2: a single correct decision propagates to ALL correct.
\*
\* A decided correct validator holds two things in its own rcvd. It holds the
\* proposal that it decided on, which is DecidedBackedByProposal. It also
\* holds a precommit quorum for that value, which is DecidedBackedByQuorum.
\* Also rcvd \subseteq sent, so the whole certificate sits in the global pool
\* `sent`, which is CertInSent. The certificate is message-latched, so it
\* stays there. `Deliver` is BATCHED, so one Deliver(c) hands the entire
\* certificate to any correct c, which is CertToOne. Each correct validator
\* that is still undecided then has OnPrecommitQuorumValue enabled, which is
\* EnabledDecide, and it decides by WF, which is CertDecideOne. A lift over
\* the finite set Honest turns the two steps for each correct validator into
\* "every correct validator decides", which is CertPropagatesAll. No
\* reachability of the clock or of GST is necessary. Neither Deliver nor the
\* decide action is gated on the clock, and eventual delivery is enough.
\* Bounded delivery is not necessary, because a sent message always has
\* sentTime <= now, which is SentTimeLeNow. Deliver(c) therefore stays enabled
\* until it fires.
\* ===========================================================================
\*
\* The precommit certificate for (v, r) present in the global pool `sent`:
\* the proposer's v-proposal and a 2f+1 precommit quorum for v at r.
CertInSent(v, r) ==
  /\ \E vr \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr) \in sent
  /\ \E Q \in ByzQuorum : \A s \in Q : Precommit(s, r, v) \in sent

\* The same certificate present in correct c's own received set. This is
\* exactly the OnPrecommitQuorumValue(c) decide precondition, modulo
\* Valid(v).
CertAt(c, v, r) ==
  /\ \E vr \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr) \in rcvd[c]
  /\ RExistsPrecommitQuorum(c, v, r)

\* ---- The decided-proposal invariant (sibling of DecidedBackedByQuorum) -----
\* A correct validator that has latched a deciding round holds the proposal of
\* the proposer for its decision at that round, in its OWN rcvd. The guard of
\* the deciding action installs it, because OnPrecommitQuorumValue reads the
\* proposal from rcvd. It is preserved because decision and decidedRound
\* latch, and because rcvd only grows.
DecidedBackedByProposal ==
  \A c \in Honest : decidedRound[c] # OFF =>
    \E vr \in Rounds \cup {-1} :
      Proposal(Proposer[decidedRound[c]], decidedRound[c], decision[c], vr) \in rcvd[c]

LEMMA DecBackedByProposalStepL ==
  ASSUME TypeOK, RcvdSubsetSent, [Next]_vars, DecidedBackedByProposal
  PROVE  DecidedBackedByProposal'
<1> SUFFICES ASSUME NEW c \in Honest, decidedRound'[c] # OFF
             PROVE  \E vr \in Rounds \cup {-1} :
                      Proposal(Proposer[decidedRound'[c]], decidedRound'[c], decision'[c], vr)
                        \in rcvd'[c]
  BY DEF DecidedBackedByProposal
<1>mono. rcvd[c] \subseteq rcvd'[c]
  BY RcvdMonotoneStep
<1>1. CASE \E p \in Honest : OnPrecommitQuorumValue(p)
  BY <1>1, <1>mono
  DEFS DecidedBackedByProposal, Message, OnPrecommitQuorumValue, PrecommitMsg,
    PrevoteMsg, Proposal, ProposalMsg, RcvdSubsetSent, RProposals, RProposalsFromProposerAt, sent, TypeOK
<1>2. CASE ~(\E p \in Honest : OnPrecommitQuorumValue(p))
  BY <1>2, <1>mono
  DEFS DecidedBackedByProposal, Deliver, FaultyStep, HonestNext, HonestStep,
    Next, OnPrevoteQuorumNil, OnPrevoteQuorumValueFirstTime, OnPrevoteQuorumValueLateUpdate,
    OnProposalNoPOL, OnProposalWithPOL, OnTimeoutPrecommit, OnTimeoutPrevote, OnTimeoutPropose, Propose,
    ScheduleTimeoutPrecommit, ScheduleTimeoutPrevote, SkipRound, Tick, vars
<1> QED
  BY <1>1, <1>2

THEOREM DecidedBackedByProposalInv == Spec => []DecidedBackedByProposal
<1> SUFFICES ASSUME Spec PROVE []DecidedBackedByProposal
  OBVIOUS
<1>1. DecidedBackedByProposal
  BY DEF Spec, Init, DecidedBackedByProposal, OFF
<1>2. [](TypeOK /\ RcvdSubsetSent /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>3. [](DecidedBackedByProposal => DecidedBackedByProposal')
  BY <1>2, DecBackedByProposalStepL, PTL
<1> QED
  BY <1>1, <1>3, PTL

\* ---- Certificate monotonicity (sent / rcvd only grow)
\* ---------------------
LEMMA CertInSentStepL ==
  ASSUME TypeOK, [Next]_vars, NEW v \in Values, NEW r \in Rounds, CertInSent(v, r)
  PROVE  CertInSent(v, r)'
<1>mono. sent \subseteq sent'
  BY SentMonotoneStep
<1>1. \E vr \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr) \in sent'
  <2> PICK vr \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr) \in sent
    BY DEF CertInSent
  <2> QED
    BY <1>mono
<1>2. \E Q \in ByzQuorum : \A s \in Q : Precommit(s, r, v) \in sent'
  <2> PICK Q \in ByzQuorum : \A s \in Q : Precommit(s, r, v) \in sent
    BY DEF CertInSent
  <2> QED
    BY <1>mono
<1> QED
  BY <1>1, <1>2 DEF CertInSent

LEMMA CertAtStepL ==
  ASSUME TypeOK, [Next]_vars, NEW c \in Honest, NEW v \in Values, NEW r \in Rounds,
         CertAt(c, v, r)
  PROVE  CertAt(c, v, r)'
<1>mono. rcvd[c] \subseteq rcvd'[c]
  BY RcvdMonotoneStep
<1>1. \E vr \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr) \in rcvd'[c]
  <2> PICK vr \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr) \in rcvd[c]
    BY DEF CertAt
  <2> QED
    BY <1>mono
<1>2. RExistsPrecommitQuorum(c, v, r)'
  <2>1. PICK Q \in ByzQuorum : Q \subseteq RPrecommitSendersFor(c, v, r)
    BY DEF CertAt, RExistsPrecommitQuorum
  <2>2. RPrecommitSendersFor(c, v, r) \subseteq RPrecommitSendersFor(c, v, r)'
    BY <1>mono DEF RPrecommitSendersFor, RPrecommits
  <2> QED
    BY <2>1, <2>2 DEF RExistsPrecommitQuorum
<1> QED
  BY <1>1, <1>2 DEF CertAt

\* ---- Delivery WF1: one batched Deliver(c) hands c the whole certificate ----
\* This mirrors Lemma6MissingEvidenceMessage and Lemma6DeliverEvidenceSome. It
\* is for a precommit certificate instead, and it carries no bound on now or
\* on GST, because delivery only needs to be eventual.
LEMMA CertMissingMsg ==
  ASSUME TypeOK, NEW c \in Honest, NEW v \in Values, NEW r \in Rounds,
         CertInSent(v, r), ~CertAt(c, v, r)
  PROVE  \E m \in Message : m \in sent /\ m \notin rcvd[c]
<1>p. PICK vr \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr) \in sent
  BY DEF CertInSent
<1>q. PICK Q \in ByzQuorum : \A s \in Q : Precommit(s, r, v) \in sent
  BY DEF CertInSent
<1>1. CASE Proposal(Proposer[r], r, v, vr) \notin rcvd[c]
  BY <1>1, <1>p DEF sent
<1>2. CASE Proposal(Proposer[r], r, v, vr) \in rcvd[c]
  BY <1>2, <1>q DEFS CertAt, Precommit, RExistsPrecommitQuorum, RPrecommits, RPrecommitSendersFor, sent
<1> QED
  BY <1>1, <1>2

LEMMA CertDeliverAch ==
  ASSUME TypeOK, SentTimeLeNow, NEW c \in Honest, NEW v \in Values, NEW r \in Rounds,
         CertInSent(v, r), Deliver(c)
  PROVE  CertAt(c, v, r)'
<1>del. rcvd' = [rcvd EXCEPT ![c] = rcvd[c] \cup Available(c)] /\ now' = now
  BY DEF Deliver
<1>p. PICK vr \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr) \in sent
  BY DEF CertInSent
<1>q. PICK Q \in ByzQuorum : \A s \in Q : Precommit(s, r, v) \in sent
  BY DEF CertInSent
\* Any sent message is Available (sentTime <= now) or already received, so it
\* is in rcvd'[c] after the batched delivery.
<1>avail. \A m \in Message : m \in sent /\ m \notin rcvd[c] => m \in rcvd'[c]
  BY <1>del DEFS Available, sent, SentTimeLeNow, TypeOK
<1>1. \E vr2 \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr2) \in rcvd'[c]
  BY <1>avail, <1>del, <1>p DEFS sent, TypeOK
<1>2. RExistsPrecommitQuorum(c, v, r)'
  BY <1>avail, <1>del, <1>q DEFS Precommit, RExistsPrecommitQuorum, RPrecommits, RPrecommitSendersFor, sent, TypeOK
<1> QED
  BY <1>1, <1>2 DEF CertAt

\* Pending / done region and next-action bundle for the delivery WF1.
\* Module-level operators (not local DEFINEs) so the WF1 PTL rule does not
\* trip the anonymizer.
CPend(c, v, r) == CertInSent(v, r) /\ ~CertAt(c, v, r)
CStep == DInv /\ Next /\ DInv'

LEMMA CertBoxActLeg ==
  ASSUME NEW c \in Honest, NEW v \in Values, NEW r \in Rounds
  PROVE  [](DInv /\ CPend(c, v, r) /\ <<Deliver(c)>>_vars => CertAt(c, v, r)')
<1>1. DInv /\ CPend(c, v, r) /\ <<Deliver(c)>>_vars => CertAt(c, v, r)'
  BY CertDeliverAch DEFS CPend, DInv, vars
<1> QED
  BY <1>1, PTL

LEMMA CertBoxEnabledLeg ==
  ASSUME NEW c \in Honest, NEW v \in Values, NEW r \in Rounds
  PROVE  [](DInv /\ CPend(c, v, r) => ENABLED <<Deliver(c)>>_vars)
<1>1. DInv /\ CPend(c, v, r) => ENABLED <<Deliver(c)>>_vars
  BY CertMissingMsg, EnabledDeliver DEFS CPend, DInv
<1> QED
  BY <1>1, PTL

LEMMA CertBoxStabLeg ==
  ASSUME NEW c \in Honest, NEW v \in Values, NEW r \in Rounds
  PROVE  [](  DInv /\ CPend(c, v, r) /\ [CStep]_vars
                => ( (DInv /\ CPend(c, v, r))' \/ CertAt(c, v, r)' )  )
<1>1. DInv /\ CPend(c, v, r) /\ [CStep]_vars
        => ( (DInv /\ CPend(c, v, r))' \/ CertAt(c, v, r)' )
  BY CertInSentStepL DEFS CertAt, CertInSent, CPend, CStep, DInv, RExistsPrecommitQuorum,
    RPrecommits, RPrecommitSendersFor, sent, SentTimeLeNow, TypeOK, vars
<1> QED
  BY <1>1, PTL

LEMMA CertStartBox ==
  ASSUME NEW c \in Honest, NEW v \in Values, NEW r \in Rounds
  PROVE  [](DInv /\ CertInSent(v, r) => (CPend(c, v, r) \/ CertAt(c, v, r)))
<1>1. DInv /\ CertInSent(v, r) => (CPend(c, v, r) \/ CertAt(c, v, r))
  BY DEF CPend
<1> QED
  BY <1>1, PTL

\* ---- Decide WF1: a correct with the certificate and no decision decides
\* -----
LEMMA CertDecEnabled ==
  ASSUME Inv, NEW c \in Honest, NEW v \in Values, NEW r \in Rounds,
         Valid(v), CertAt(c, v, r), decision[c] = nil
  PROVE  ENABLED <<OnPrecommitQuorumValue(c)>>_vars
<1>1. PICK vr \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr) \in rcvd[c]
  BY DEF CertAt
<1> DEFINE prop == Proposal(Proposer[r], r, v, vr)
<1>2. prop \in RProposalsFromProposerAt(c, r)
  BY <1>1 DEFS Proposal, RProposals, RProposalsFromProposerAt
<1>3. prop.value = v
  BY DEF Proposal
<1>4. RExistsPrecommitQuorum(c, prop.value, r)
  BY <1>3 DEF CertAt
<1>5. Valid(prop.value)
  BY <1>3
<1> QED
  BY <1>2, <1>4, <1>5, EnabledDecide DEF Inv

LEMMA CertDecAct ==
  ASSUME Inv, NEW c \in Honest, OnPrecommitQuorumValue(c)
  PROVE  (decision[c] # nil)'
<1>1. PICK r2 \in Rounds : \E prop \in RProposalsFromProposerAt(c, r2) :
        decision' = [decision EXCEPT ![c] = prop.value]
  BY DEF OnPrecommitQuorumValue
<1>2. PICK prop \in RProposalsFromProposerAt(c, r2) :
        decision' = [decision EXCEPT ![c] = prop.value]
  BY <1>1
<1>3. prop.value \in Values
  <2>1. prop \in rcvd[c] /\ prop.type = "Proposal"
    BY <1>2 DEF RProposalsFromProposerAt, RProposals
  <2>2. prop \in sent
    BY <2>1 DEF Inv, RcvdSubsetSent
  <2>3. prop \in ProposalMsg
    BY <2>1, <2>2 DEF sent, Message, ProposalMsg, PrevoteMsg, PrecommitMsg
  <2> QED
    BY <2>3 DEF ProposalMsg
<1>4. decision'[c] = prop.value
  BY <1>2 DEF Inv, TypeOK
<1> QED
  BY <1>3, <1>4, NilNotInValues

\* Decide milestone / step. CDPend carries Inv so EnabledDecide / CertDecAct
\* have TypeOK / RcvdSubsetSent inside the WF1.
CDPend(c, v, r) == Inv /\ CertAt(c, v, r) /\ decision[c] = nil
CDStep == Inv /\ Next /\ Inv'

LEMMA CertDecBoxActLeg ==
  ASSUME NEW c \in Honest, NEW v \in Values, NEW r \in Rounds
  PROVE  [](CDPend(c, v, r) /\ <<OnPrecommitQuorumValue(c)>>_vars => (decision[c] # nil)')
BY CertDecAct, PTL DEFS CDPend, vars

LEMMA CertDecBoxEnabledLeg ==
  ASSUME NEW c \in Honest, NEW v \in Values, NEW r \in Rounds, Valid(v)
  PROVE  [](CDPend(c, v, r) => ENABLED <<OnPrecommitQuorumValue(c)>>_vars)
BY CertDecEnabled, PTL DEF CDPend

LEMMA CertDecBoxStabLeg ==
  ASSUME NEW c \in Honest, NEW v \in Values, NEW r \in Rounds
  PROVE  [](  CDPend(c, v, r) /\ [CDStep]_vars
                => ( CDPend(c, v, r)' \/ (decision[c] # nil)' )  )
<1>1. CDPend(c, v, r) /\ [CDStep]_vars => ( CDPend(c, v, r)' \/ (decision[c] # nil)' )
  <2> SUFFICES ASSUME CDPend(c, v, r), [CDStep]_vars
               PROVE  CDPend(c, v, r)' \/ (decision[c] # nil)'
    OBVIOUS
  <2>1. CASE vars' = vars
    <3>a. Inv'
      BY <2>1 DEF CDPend, Inv, TypeOK, RcvdSubsetSent, vars, sent
    <3>b. CertAt(c, v, r)'
      BY <2>1 DEF CDPend, CertAt, RExistsPrecommitQuorum,
                  RPrecommitSendersFor, RPrecommits, vars
    <3>c. CASE (decision[c] = nil)'
      BY <3>a, <3>b, <3>c DEF CDPend
    <3>d. CASE (decision[c] # nil)'
      BY <3>d
    <3> QED
      BY <3>c, <3>d
  <2>2. CASE CDStep
    <3>0. TypeOK /\ [Next]_vars
      BY <2>2 DEF CDStep, Inv
    <3>1. CertAt(c, v, r)'
      BY <3>0, CertAtStepL DEF CDPend
    <3>2. Inv'
      BY <2>2 DEF CDStep
    <3>3. CASE (decision[c] = nil)'
      BY <3>1, <3>2, <3>3 DEF CDPend
    <3>4. CASE (decision[c] # nil)'
      BY <3>4
    <3> QED
      BY <3>3, <3>4
  <2> QED
    BY <2>1, <2>2 DEF CDStep
<1> QED
  BY <1>1, PTL

\* A clean start box, free of Spec, for the glue of the precondition of the
\* decide WF1. PTL cannot necessitate this inline once Spec is in scope.
LEMMA CertDecStartBox ==
  ASSUME NEW c \in Honest, NEW v \in Values, NEW r \in Rounds
  PROVE  [](Inv /\ CertAt(c, v, r) => (CDPend(c, v, r) \/ (decision[c] # nil)))
<1>1. Inv /\ CertAt(c, v, r) => (CDPend(c, v, r) \/ (decision[c] # nil))
  BY DEF CDPend
<1> QED
  BY <1>1, PTL

\* A boxed single decision step, which is the step of DecLatch at a fixed c.
\* It is necessitated in a clean context that is free of Spec, because an
\* ambient Spec defeats an inline necessitation of DecStepL. The latch of the
\* decision of each correct validator uses it, in the CertPropagatesAll lift.
LEMMA DecStepBoxC ==
  ASSUME NEW c \in Honest
  PROVE  [](IntegrityStep => (HasDecided(c) => HasDecided(c)'))
<1>1. IntegrityStep => (HasDecided(c) => HasDecided(c)')
  BY DecStepL
<1> QED
  BY <1>1, PTL

\* Boxed set identities for the eventually-always lift of the finite
\* conjunction. They are in clean top-level lemmas that are free of Spec, so
\* that PTL can necessitate them. NEW T and c are named to match the use site
\* of the FS-induction, and the predicate decision[d] # nil is free of the
\* value.
LEMMA CertBoxUnfoldEmpty ==
  ASSUME NEW T, NEW c, T = {}
  PROVE  []((\A d \in T \cup {c} : decision[d] # nil) <=> decision[c] # nil)
<1>1. (\A d \in T \cup {c} : decision[d] # nil) <=> decision[c] # nil
  OBVIOUS
<1> QED BY <1>1, PTL

LEMMA CertBoxSplit ==
  ASSUME NEW T, NEW c
  PROVE  [](((\A d \in T : decision[d] # nil) /\ decision[c] # nil)
              <=> (\A d \in T \cup {c} : decision[d] # nil))
<1>1. ((\A d \in T : decision[d] # nil) /\ decision[c] # nil)
        <=> (\A d \in T \cup {c} : decision[d] # nil)
  OBVIOUS
<1> QED BY <1>1, PTL

LEMMA CertAllDecidedFold ==
  [](  (\A d \in Honest : decision[d] # nil)
       <=> (\A c \in Honest : HasDecided(c))  )
<1>1. (\A d \in Honest : decision[d] # nil)
       <=> (\A c \in Honest : HasDecided(c))
  BY DEF HasDecided
<1> QED
  BY <1>1, PTL

\* Drop the aggregate decision latch in a clean context. Keeping this exact
\* concrete formula out of CertPropagatesAll avoids temporal instantiation and
\* the ambient Spec assumption blocking PTL.
LEMMA CertDropAllLatch ==
  ASSUME NEW v \in Values, NEW r \in Rounds,
         CertInSent(v, r) ~> [](\A d \in Honest : decision[d] # nil)
  PROVE  CertInSent(v, r) ~> (\A d \in Honest : decision[d] # nil)
BY PTL

THEOREM CertPropagatesAll ==
  ASSUME NEW v \in Values, NEW r \in Rounds, Valid(v), Spec
  PROVE  CertInSent(v, r) ~> (\A c \in Honest : HasDecided(c))
<1>lift. CertInSent(v, r) ~> [](\A d \in Honest : decision[d] # nil)
  <2> DEFINE Q(T) ==
        (T \in SUBSET Honest /\ T # {}) =>
          (CertInSent(v, r) ~> [](\A d \in T : decision[d] # nil))
  <2>1. Q({})
    OBVIOUS
  <2>2. ASSUME NEW T, IsFiniteSet(T), Q(T), NEW c, c \notin T
        PROVE  Q(T \cup {c})
    <3> SUFFICES ASSUME T \cup {c} \in SUBSET Honest, T \cup {c} # {}
                 PROVE  CertInSent(v, r) ~> [](\A d \in T \cup {c} : decision[d] # nil)
      BY DEF Q
    <3>t. T \in SUBSET Honest
      OBVIOUS
    <3>c. c \in Honest
      OBVIOUS
    \* Per-correct step, INLINED at the induction element c (a rule-shaped
    \* ~>-conclusion theorem cannot be cited at an FS element: identity is
    \* required, but the element / lemma NEW-c clash forces a rename under [];
    \* the single-[] boxed legs, by contrast, cite fine at the clashing c).
    <3>1. CertInSent(v, r) ~> [](decision[c] # nil)
      \* deliver the whole certificate to c (batched Deliver(c) WF1)
      <4>del. CertInSent(v, r) ~> CertAt(c, v, r)
        <5>g. []DInv
          BY InvProof, SentTimeLeNowInv, PTL DEF DInv, Inv
        <5>1. [](DInv /\ CPend(c, v, r) /\ <<Deliver(c)>>_vars => CertAt(c, v, r)')
          BY CertBoxActLeg
        <5>2. [](DInv /\ CPend(c, v, r) => ENABLED <<Deliver(c)>>_vars)
          BY CertBoxEnabledLeg
        <5>3. WF_vars(Deliver(c))
          BY DEF Spec, Fairness
        <5>4. [](DInv /\ CPend(c, v, r) /\ [CStep]_vars
                   => ((DInv /\ CPend(c, v, r))' \/ CertAt(c, v, r)'))
          BY CertBoxStabLeg
        <5>5. [][CStep]_vars
          BY <5>g, PTL DEFS CStep, Spec
        <5>6. (DInv /\ CPend(c, v, r)) ~> CertAt(c, v, r)
          BY <5>1, <5>2, <5>3, <5>4, <5>5, PTL
        <5>7a. [](DInv /\ CertInSent(v, r) => (CPend(c, v, r) \/ CertAt(c, v, r)))
          BY CertStartBox
        <5>7. [](CertInSent(v, r) => ((DInv /\ CPend(c, v, r)) \/ CertAt(c, v, r)))
          BY <5>g, <5>7a, PTL DEF DInv
        <5> QED
          BY <5>6, <5>7, PTL
      \* c decides from the certificate (OnPrecommitQuorumValue(c) WF1)
      <4>dec. CertAt(c, v, r) ~> (decision[c] # nil)
        <5>1. [](CDPend(c, v, r) /\ <<OnPrecommitQuorumValue(c)>>_vars => (decision[c] # nil)')
          BY CertDecBoxActLeg
        <5>2. [](CDPend(c, v, r) => ENABLED <<OnPrecommitQuorumValue(c)>>_vars)
          BY CertDecBoxEnabledLeg
        <5>3. WF_vars(OnPrecommitQuorumValue(c))
          BY DEF Spec, Fairness
        <5>4. [](CDPend(c, v, r) /\ [CDStep]_vars => (CDPend(c, v, r)' \/ (decision[c] # nil)'))
          BY CertDecBoxStabLeg
        <5>5. [][CDStep]_vars
          BY InvProof, PTL DEFS CDStep, Spec
        <5>6. CDPend(c, v, r) ~> (decision[c] # nil)
          BY <5>1, <5>2, <5>3, <5>4, <5>5, PTL
        <5>7a. [](Inv /\ CertAt(c, v, r) => (CDPend(c, v, r) \/ (decision[c] # nil)))
          BY CertDecStartBox
        <5>7. [](CertAt(c, v, r) => (CDPend(c, v, r) \/ (decision[c] # nil)))
          BY InvProof, <5>7a, PTL
        <5> QED
          BY <5>6, <5>7, PTL
      \* the decision latches
      <4>lat. (decision[c] # nil) ~> [](decision[c] # nil)
        <5>1. []IntegrityStep
          BY IntegrityInv
        <5>2a. [](IntegrityStep => (HasDecided(c) => HasDecided(c)'))
          BY DecStepBoxC
        <5>2. [](HasDecided(c) => HasDecided(c)')
          BY <5>1, <5>2a, PTL
        <5> QED
          BY <5>2, PTL DEF HasDecided
      <4> QED
        BY <4>del, <4>dec, <4>lat, PTL
    <3>2. CASE T = {}
      <4>1. []((\A d \in T \cup {c} : decision[d] # nil) <=> decision[c] # nil)
        BY <3>2, CertBoxUnfoldEmpty
      <4> QED
        BY <3>1, <4>1, PTL
    <3>3. CASE T # {}
      <4>1. CertInSent(v, r) ~> [](\A d \in T : decision[d] # nil)
        BY <2>2, <3>3
      <4>2. CertInSent(v, r) ~> []((\A d \in T : decision[d] # nil) /\ decision[c] # nil)
        BY <3>1, <4>1, PTL
      <4>3. [](((\A d \in T : decision[d] # nil) /\ decision[c] # nil)
                 <=> (\A d \in T \cup {c} : decision[d] # nil))
        BY CertBoxSplit
      <4> QED
        BY <4>2, <4>3, PTL
    <3> QED
      BY <3>2, <3>3
  <2>3. Q(Honest)
    <3> HIDE DEF Q
    <3> QED
      BY <2>1, <2>2, HonestFinite, FS_Induction, IsaM("blast")
  <2>ne. (Honest # {}) => (CertInSent(v, r) ~> [](\A d \in Honest : decision[d] # nil))
    BY <2>3 DEF Q
  <2> QED
    BY <2>ne, HonestNonEmptyL, PTL
<1>unlatched. CertInSent(v, r) ~> (\A d \in Honest : decision[d] # nil)
  BY <1>lift, CertDropAllLatch
<1> QED
  BY <1>unlatched, CertAllDecidedFold, PTL

\* ---- Source: a correct decision installs a certificate in `sent`
\* -----------
LEMMA CertFromDecision ==
  ASSUME TypeOK, RcvdSubsetSent, Validity, DecidedRoundConsistent,
         DecidedBackedByQuorum, DecidedBackedByProposal,
         NEW c0 \in Honest, HasDecided(c0)
  PROVE  \E v \in Values : \E r \in Rounds : Valid(v) /\ CertInSent(v, r)
<1>d. decidedRound[c0] # OFF
  BY DEF DecidedRoundConsistent, HasDecided
<1>v. decision[c0] \in Values
  BY <1>d DEF TypeOK, HasDecided, ValuesOrNil, OFF
<1>r. decidedRound[c0] \in Rounds
  BY <1>d DEF TypeOK, OFF
<1> DEFINE v == decision[c0]
<1> DEFINE r == decidedRound[c0]
<1>sub. rcvd[c0] \subseteq sent
  BY DEF RcvdSubsetSent
<1>valid. Valid(v)
  BY DEF Validity, HasDecided
<1>prop. \E vr \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr) \in sent
  <2>1. \E vr \in Rounds \cup {-1} : Proposal(Proposer[r], r, v, vr) \in rcvd[c0]
    BY <1>d DEF DecidedBackedByProposal
  <2> QED
    BY <2>1, <1>sub
<1>quorum. \E Q \in ByzQuorum : \A s \in Q : Precommit(s, r, v) \in sent
  <2>1. RExistsPrecommitQuorum(c0, v, r)
    BY <1>d DEF DecidedBackedByQuorum
  <2>2. PICK Q \in ByzQuorum : Q \subseteq RPrecommitSendersFor(c0, v, r)
    BY <2>1 DEF RExistsPrecommitQuorum
  <2>3. \A s \in Q : Precommit(s, r, v) \in sent
    <3> TAKE s \in Q
    <3>1. s \in RPrecommitSendersFor(c0, v, r)
      BY <2>2
    <3> QED
      BY <3>1, <1>sub, <1>v, <1>r, PrecommitSenderVoted DEF ValuesOrNil
  <2> QED
    BY <2>2, <2>3
<1>cert. CertInSent(v, r)
  BY <1>prop, <1>quorum DEF CertInSent
<1> QED
  BY <1>v, <1>r, <1>valid, <1>cert

LEMMA CertFromDecisionBox ==
  [](  Inv /\ Validity /\ DecidedRoundConsistent /\ DecidedBackedByQuorum
         /\ DecidedBackedByProposal
       => ( (\E c \in Honest : HasDecided(c))
              => (\E v \in Values : \E r \in Rounds : Valid(v) /\ CertInSent(v, r)) )  )
<1>1. Inv /\ Validity /\ DecidedRoundConsistent /\ DecidedBackedByQuorum
        /\ DecidedBackedByProposal
        => ( (\E c \in Honest : HasDecided(c))
               => (\E v \in Values : \E r \in Rounds : Valid(v) /\ CertInSent(v, r)) )
  <2> SUFFICES ASSUME Inv, Validity, DecidedRoundConsistent, DecidedBackedByQuorum,
                      DecidedBackedByProposal, NEW c0 \in Honest, HasDecided(c0)
               PROVE  \E v \in Values : \E r \in Rounds : Valid(v) /\ CertInSent(v, r)
    OBVIOUS
  <2> QED
    BY CertFromDecision DEF Inv
<1> QED
  BY <1>1, PTL

\* ---- Existential collapse over (Values, Rounds) (skill: existential
\* leads-to)
LEMMA ELTCertCommute ==
  ASSUME NEW TEMPORAL D,
         \A v \in Values : \A r \in Rounds : [](Valid(v) /\ CertInSent(v, r) => D)
  PROVE  [](\A v \in Values : \A r \in Rounds : (Valid(v) /\ CertInSent(v, r) => D))
OBVIOUS

LEMMA ELTCertBoxFO ==
  ASSUME TRUE
  PROVE  [](  (\A v \in Values : \A r \in Rounds :
                 (Valid(v) /\ CertInSent(v, r) => <>(\A c \in Honest : HasDecided(c))))
              => ( (\E v \in Values : \E r \in Rounds : Valid(v) /\ CertInSent(v, r))
                     => <>(\A c \in Honest : HasDecided(c)) )  )
<1>1. (\A v \in Values : \A r \in Rounds :
          (Valid(v) /\ CertInSent(v, r) => <>(\A c \in Honest : HasDecided(c))))
       => ( (\E v \in Values : \E r \in Rounds : Valid(v) /\ CertInSent(v, r))
              => <>(\A c \in Honest : HasDecided(c)) )
  OBVIOUS
<1> QED
  BY <1>1, PTL

THEOREM ExistsCertLeadsTo ==
  ASSUME \A v \in Values : \A r \in Rounds :
           (Valid(v) /\ CertInSent(v, r) ~> (\A c \in Honest : HasDecided(c)))
  PROVE  (\E v \in Values : \E r \in Rounds : Valid(v) /\ CertInSent(v, r))
           ~> (\A c \in Honest : HasDecided(c))
<1>0. \A v \in Values : \A r \in Rounds :
        [](Valid(v) /\ CertInSent(v, r) => <>(\A c \in Honest : HasDecided(c)))
  BY PTL
<1>1. [](\A v \in Values : \A r \in Rounds :
           (Valid(v) /\ CertInSent(v, r) => <>(\A c \in Honest : HasDecided(c))))
  BY <1>0, ELTCertCommute
<1>2. [](  (\A v \in Values : \A r \in Rounds :
              (Valid(v) /\ CertInSent(v, r) => <>(\A c \in Honest : HasDecided(c))))
           => ( (\E v \in Values : \E r \in Rounds : Valid(v) /\ CertInSent(v, r))
                  => <>(\A c \in Honest : HasDecided(c)) )  )
  BY ELTCertBoxFO
<1> QED
  BY <1>1, <1>2, PTL

\* Clean (Spec-free) vacuous box: when v is not valid the certificate
\* antecedent is unsatisfiable, so the per-(v, r) leads-to holds trivially.
LEMMA CertVacuousBox ==
  ASSUME NEW v \in Values, NEW r \in Rounds, ~Valid(v)
  PROVE  [](  (Valid(v) /\ CertInSent(v, r)) => (\A c \in Honest : HasDecided(c))  )
<1>1. (Valid(v) /\ CertInSent(v, r)) => (\A c \in Honest : HasDecided(c))
  OBVIOUS
<1> QED
  BY <1>1, PTL

\* ---- DecisionPropagates: assemble source + core --------------------------
LEMMA DecisionPropagates ==
  ASSUME Spec PROVE SomeCorrectDecided ~> AllCorrectDecided
\* A decision installs a full certificate for some (v, r) in `sent`.
<1>src. (\E c \in Honest : HasDecided(c))
          ~> (\E v \in Values : \E r \in Rounds : Valid(v) /\ CertInSent(v, r))
  BY CertFromDecisionBox, DecidedBackedByProposalInv, DecidedBackedByQuorumInv, DecidedRoundConsistentInv, InvProof, PTL, ValidityInv
\* A certificate for a rigid (v, r) makes every correct decide.
<1>core. \A v \in Values : \A r \in Rounds :
           (Valid(v) /\ CertInSent(v, r) ~> (\A c \in Honest : HasDecided(c)))
  <2> SUFFICES ASSUME NEW v \in Values, NEW r \in Rounds
               PROVE  Valid(v) /\ CertInSent(v, r) ~> (\A c \in Honest : HasDecided(c))
    OBVIOUS
  <2>1. CASE Valid(v)
    <3>1. Spec => (CertInSent(v, r) ~> (\A c \in Honest : HasDecided(c)))
      BY <2>1, CertPropagatesAll
    <3>2. QED
      BY <3>1, PTL
  <2>2. CASE ~Valid(v)
    <3>1. [](  (Valid(v) /\ CertInSent(v, r)) => (\A c \in Honest : HasDecided(c))  )
      BY <2>2, CertVacuousBox
    <3>2. QED
      BY <3>1, PTL
  <2>3. QED
    BY <2>1, <2>2
\* Collapse the (v, r) existential and chain with the source.
<1>elt. (\E v \in Values : \E r \in Rounds : Valid(v) /\ CertInSent(v, r))
          ~> (\A c \in Honest : HasDecided(c))
  BY <1>core, ExistsCertLeadsTo
<1> QED
  BY <1>src, <1>elt, PTL DEF SomeCorrectDecided, AllCorrectDecided

-----------------------------------------------------------------------------
(***************************************************************************)
(* Paper Lemma 7: selection (Section IV).                                  *)
(*                                                                         *)
(* The paper fixes a correct process whose valid round dominates every     *)
(* correct lock, then selects a later round where it proposes.             *)
(* ...Dominator now proves that such a process stabilizes at every fresh   *)
(* entry. This module supplies recurring selected entries and composes     *)
(* them with the within-round and retry results.                           *)
(***************************************************************************)

\* ---- Lemma 5 condition 4 beyond a round ----------------------------------
\* Only the precommit inequality grows with the round, so TDelta > 0 carries
\* that one past any Delta. The propose inequality and the prevote inequality
\* do NOT grow. Each r*TDelta term cancels against TimeoutPrecommit(r - 1).
\* That leaves the two constant premises ProposeTimeoutMargin and
\* PrevoteTimeoutMargin, and TendermintPartialSync assumes both. Without them NO
\* round satisfies condition 4, and Lemma5OrPriorLock could never be applied.
LEMMA MulGeSelf ==
  ASSUME NEW a \in Nat, NEW b \in Nat, b >= 1
  PROVE  a * b >= a
BY SMT

LEMMA MulPred ==
  ASSUME NEW a \in Nat, NEW b \in Nat, a >= 1
  PROVE  (a - 1) * b = a * b - b
BY SMT

LEMMA Lemma5TimeoutsBeyond ==
  ASSUME NEW r \in Rounds, r >= 2 * Delta
  PROVE  Lemma5Timeouts(r)
<1>d. Delta \in Nat /\ Delta > 0 /\ TDelta \in Nat /\ TDelta >= 1
  BY DeltaType, TDeltaType
<1>r. r \in Nat /\ r >= 1
  BY <1>d DEF Rounds
<1>m. r * TDelta \in Nat /\ r * TDelta >= r
  BY <1>d, <1>r, MulGeSelf
<1>1. TimeoutPrevote(r) > 2 * Delta + TimeoutPrecommit(r - 1)
  <2>1. (r - 1) * TDelta = r * TDelta - TDelta
    BY <1>d, <1>r, MulPred
  <2>2. TimeoutPrecommit(r - 1) = T0Precommit + r * TDelta - TDelta
    BY <2>1 DEF TimeoutPrecommit
  <2> QED
    BY <2>2, <1>d, <1>r, <1>m, PrevoteTimeoutMargin, T0PrevoteType,
       T0PrecommitType, SMT DEF TimeoutPrevote
<1>2. TimeoutPrecommit(r) > 2 * Delta
  BY <1>d, <1>r, <1>m, T0PrecommitType, SMT DEF TimeoutPrecommit
<1>3. TimeoutPropose(r) > 2 * Delta + TimeoutPrecommit(r - 1)
  <2>1. (r - 1) * TDelta = r * TDelta - TDelta
    BY <1>d, <1>r, MulPred
  <2>2. TimeoutPrecommit(r - 1) = T0Precommit + r * TDelta - TDelta
    BY <2>1 DEF TimeoutPrecommit
  <2> QED
    BY <2>2, <1>d, <1>r, <1>m, ProposeTimeoutMargin, T0ProposeType, T0PrecommitType,
       SMT DEF TimeoutPropose
<1> QED
  BY <1>1, <1>2, <1>3 DEF Lemma5Timeouts

LEMMA TimeoutsSufficientBeyondL == TimeoutsSufficientBeyond
BY Lemma5TimeoutsBeyond DEF TimeoutsSufficientBeyond

\* ---- Selection ingredient 4: the dominating process proposes again --------
ProposerRecurrence ==
  \A d \in Honest : \A b \in Rounds : \E r \in Rounds : r > b /\ Proposer[r] = d

LEMMA ProposerRecurrenceL ==
  ASSUME TerminationConditions
  PROVE  ProposerRecurrence
BY DEF TerminationConditions, EveryHonestProposesAgain, ProposerRecurrence

\* ---- Lemma 5 consumption, checked ----------------------------------------
\* Recurring good rounds resolve into a decision, or into a correct lock after
\* GST below the good round. Lemma5OrPriorLock gives this, through the checked
\* existential glue Lemma5ResolutionExists. GoodRoundResolution is a
\* definition, and no backend unfolds a definition under []. The disjunction
\* is therefore exposed to PTL through a clean boxed identity.
SomeLockAfterGST == \E r \in Rounds : PostGSTPriorRoundLock(r)

LEMMA GoodRoundResolutionBox ==
  [](GoodRoundResolution <=> (SomeCorrectDecided \/ SomeLockAfterGST))
<1>1. GoodRoundResolution <=> (SomeCorrectDecided \/ SomeLockAfterGST)
  BY DEF GoodRoundResolution, SomeLockAfterGST
<1> QED
  BY <1>1, PTL

LEMMA RecurringResolution ==
  ASSUME Spec, []<>GoodRoundExists
  PROVE  <>SomeCorrectDecided \/ <>SomeLockAfterGST
<1>1. GoodRoundExists ~> GoodRoundResolution
  BY Lemma5ResolutionExists
<1>2. []<>GoodRoundResolution
  BY <1>1, PTL
<1> QED
  BY <1>2, GoodRoundResolutionBox, PTL

\* ---- Selection assembly ---------------------------------------------------
\*
\* Frontier A covers the growth of the clock and of the round, with no
\* reasoning about locks. It is in TendermintPartialSyncTerminationRoundProgress.
\* That module defines RoundAbove and ProgressBeyond, and it DERIVES
\* PostGSTRoundProgress from the proved theorem RoundGrowth. The clock
\* conjunct of ProgressBeyond costs nothing there. RoundBelowNowInv gives
\* round[c] <= now, so one instant above b + GST carries both conjuncts.
\*
\* Selection constructs recurring fresh entries. ...Dominator proves that a
\* fixed correct process eventually dominates at every such entry.
\*
LEMMA RoundAboveBridgeBox ==
  ASSUME NEW b \in Rounds
  PROVE  [](now > GST /\ RoundAbove(b) => SelRoundAbove(b))
<1>1. now > GST /\ RoundAbove(b) => SelRoundAbove(b)
  BY DEF RoundAbove, SelRoundAbove
<1> QED
  BY <1>1, PTL

\* ---- Frontier B, assembled -----------------------------------------------
\* ProgressBeyond reaches each round bound ONCE. Rounds never go down, which
\* is RoundMonotoneStep, so the reach latches into a recurrence. That is what
\* the selection needs at unboundedly many rounds. Selected entries then recur
\* at the dominating process d. From some instant on, d dominates at every
\* entry instant, which is StableEntryDominator. The two coincide infinitely
\* often, because <>[]A together with []<>B gives []<>(A /\ B).
\*
\* The recurrence is a NEW-parameterized THEOREM rather than a
\* \A b : []<>... hypothesis on purpose. TLAPS applies a theorem as a RULE,
\* which instantiates fine at a PICKed round; instantiating a \A whose body
\* is temporal does NOT work, because the coalesced []<> body is an opaque
\* atom. That is why the bound-by-bound loop runs HERE and not inside
\* ...Selection: SelectedEntryRecurs only commutes the collapsed family.
THEOREM SelRoundRecurs ==
  ASSUME Spec, ProgressBeyond, []~SomeCorrectDecided, NEW b \in Rounds
  PROVE  []<>SelRoundAbove(b)
<1>ty. [](TypeOK /\ [Next]_vars)
  BY InvProof, PTL DEF Spec, Inv
<1>1. <>SomeCorrectDecided \/ <>(now > GST /\ RoundAbove(b))
  BY DEF ProgressBeyond
<1>2. <>(now > GST /\ RoundAbove(b))
  BY <1>1, PTL
<1>3. [](now > GST /\ RoundAbove(b) => SelRoundAbove(b))
  BY RoundAboveBridgeBox
<1>4. <>SelRoundAbove(b)
  BY <1>2, <1>3, PTL
<1>5. [](TypeOK /\ [Next]_vars /\ SelRoundAbove(b) => SelRoundAbove(b)')
  BY SelRoundAboveLatchBox
<1>6. [](SelRoundAbove(b) => SelRoundAbove(b)')
  BY <1>ty, <1>5, PTL
<1> QED
  BY <1>4, <1>6, PTL

THEOREM SelectedEntryFamily ==
  ASSUME Spec, ProgressBeyond, []~SomeCorrectDecided, NEW d \in Honest
  PROVE  \A bnd \in Rounds : \A b \in Rounds :
           (b > bnd /\ b > 0 /\ b > GST /\ Proposer[b] = d /\ Lemma5Timeouts(b))
             => [](RoundAtMost(bnd) => <>SelectedEntry(d))
<1> TAKE bnd \in Rounds
<1> TAKE b \in Rounds
<1> SUFFICES ASSUME b > bnd, b > 0, b > GST, Proposer[b] = d, Lemma5Timeouts(b)
             PROVE  [](RoundAtMost(bnd) => <>SelectedEntry(d))
  OBVIOUS
<1>1. []<>SelRoundAbove(b)
  BY SelRoundRecurs
<1> QED
  BY <1>1, SelectedEntryFromBound

THEOREM DominatorExists ==
  ASSUME Spec, []~SomeCorrectDecided, TimeoutsSufficientBeyond
  PROVE  SomeStableDominator
<1>1. <>SomeCorrectDecided \/ SomeStableDominator
  BY StableEntryDominator
<1> QED
  BY <1>1, PTL

\* Everything downstream of the dominator, with d a NEW constant so the
\* family and the collapse can be cited at it by identity. The conclusion is
\* d-free, which is what lets GoodRoundRecurrence PICK d.
THEOREM GoodRoundFromDominator ==
  ASSUME Spec, ProgressBeyond, []~SomeCorrectDecided, ProposerRecurrence,
         TimeoutsSufficientBeyond, NEW d \in Honest, <>[]EntryDominator(d)
  PROVE  []<>GoodRoundExists
<1>c. Delta \in Nat /\ Delta > 1 /\ GST \in Nat
  BY DeltaType, GSTType
<1>to. \A rr \in Rounds : rr >= 2 * Delta => Lemma5Timeouts(rr)
  BY DEF TimeoutsSufficientBeyond
<1>fam. \A bnd \in Rounds : \A b \in Rounds :
          (b > bnd /\ b > 0 /\ b > GST /\ Proposer[b] = d /\ Lemma5Timeouts(b))
            => [](RoundAtMost(bnd) => <>SelectedEntry(d))
  BY SelectedEntryFamily
\* The collapse. Each bound gets the proposer round above bnd + 2*Delta + GST,
\* which makes the three inequalities one arithmetic leaf.
<1>bd. \A bnd \in Rounds : [](RoundAtMost(bnd) => <>SelectedEntry(d))
  <2> TAKE bnd \in Rounds
  <2>n. bnd \in Nat /\ bnd + 2 * Delta + GST \in Rounds
    BY <1>c DEF Rounds
  <2>1. PICK b \in Rounds : b > bnd + 2 * Delta + GST /\ Proposer[b] = d
    BY <2>n DEF ProposerRecurrence
  <2>2. b \in Nat
    BY DEF Rounds
  <2>3. b > bnd /\ b > 0 /\ b > GST /\ b >= 2 * Delta
    BY <2>1, <2>2, <2>n, <1>c
  <2>4. Lemma5Timeouts(b)
    BY <1>to, <2>3
  <2> QED
    BY <2>1, <2>3, <2>4, <1>fam
<1>e. []<>SelectedEntry(d)
  BY <1>bd, SelectedEntryRecurs
<1>cc. []<>(SelectedEntry(d) /\ EntryDominator(d))
  BY <1>e, PTL
<1>g. [](SelectedEntry(d) /\ EntryDominator(d) => GoodRoundExists)
  BY SelectedGoodRoundBox
<1> QED
  BY <1>cc, <1>g, PTL

THEOREM GoodRoundRecurrence ==
  ASSUME Spec, ProposerRecurrence, TimeoutsSufficientBeyond,
         ProgressBeyond
  PROVE  <>SomeCorrectDecided \/ []<>GoodRoundExists
<1> SUFFICES ASSUME []~SomeCorrectDecided
             PROVE  []<>GoodRoundExists
  BY PTL
\* The existential travels as the atom SomeStableDominator. Written out it
\* fails HERE, in this large context of assumptions, even though
\* DominatorExists proves it in a small one. The witness is not PICKed either.
\* The goal is free of d, so the tail is proved for an arbitrary d, and
\* StableDominatorElim discharges the existential at an abstract conclusion.
<1>ex. SomeStableDominator
  BY DominatorExists
<1>all. \A d \in Honest : (<>[]EntryDominator(d) => []<>GoodRoundExists)
  <2> TAKE d \in Honest
  <2> SUFFICES ASSUME <>[]EntryDominator(d)
               PROVE  []<>GoodRoundExists
    OBVIOUS
  <2> QED
    BY GoodRoundFromDominator
<1> QED
  BY <1>ex, <1>all, StableDominatorElim

\*   Frontier C covers paper Lemma 7, case 2, and the retry. It is in
\*   TendermintPartialSyncTerminationLockRetry, which derives LockRetryDecides.
\*   That theorem says that recurring good rounds alone give a decision.
\*   Without a decision, the Byzantine disruption of a good round does not
\*   recur forever. The interface change in WithinRound made the split
\*   possible. That change gives a lock branch relativized to the instant of
\*   the round ENTRY, which is BlockingLockDuring. The GST-relative
\*   PostGSTPriorRoundLock can only latch. After one correct lock exists after
\*   GST, the lock branch of Lemma 5 is true at the hypothesis state of every
\*   later round. The retry then learns nothing. An entry-relative branch is
\*   instead re-armed by every later round.
\*
\* LockRetryDecides needs only Spec and the good-round recurrence.
THEOREM LockRetryTerminates ==
  ASSUME Spec
  PROVE  ([]<>GoodRoundExists /\ <>SomeLockAfterGST) => <>SomeCorrectDecided
<1> SUFFICES ASSUME []<>GoodRoundExists, <>SomeLockAfterGST
             PROVE  <>SomeCorrectDecided
  BY PTL
<1> QED
  BY LockRetryDecides

THEOREM Lemma7Selection ==
  ASSUME Spec, TerminationConditions
  PROVE  <>SomeCorrectDecided
<1>pr. ProposerRecurrence
  BY ProposerRecurrenceL
<1>to. TimeoutsSufficientBeyond
  BY TimeoutsSufficientBeyondL
<1>prog. ProgressBeyond
  BY PostGSTRoundProgress
<1>1. <>SomeCorrectDecided \/ []<>GoodRoundExists
  BY <1>pr, <1>to, <1>prog, GoodRoundRecurrence
<1>2. ([]<>GoodRoundExists /\ <>SomeLockAfterGST) => <>SomeCorrectDecided
  BY LockRetryTerminates
<1>3. []<>GoodRoundExists => (<>SomeCorrectDecided \/ <>SomeLockAfterGST)
  BY RecurringResolution
<1> QED
  BY <1>1, <1>2, <1>3, PTL

\* ---- Final composition: Spec => Termination, paper Lemma 7 ---------------
\* This theorem contains temporal composition only. Every ingredient it cites
\* is proved, so Termination holds under the three environment premises alone.
THEOREM TerminationThm == Spec => Termination
<1> SUFFICES ASSUME Spec, TerminationConditions
             PROVE  \A p \in Honest : <>HasDecided(p)
  BY DEF Termination, HasDecided
<1>1. <>SomeCorrectDecided
  BY Lemma7Selection, PTL
<1>2. SomeCorrectDecided ~> AllCorrectDecided
  BY DecisionPropagates, PTL
<1>3. <>AllCorrectDecided
  BY <1>1, <1>2, PTL
<1>4. QED
  BY <1>3, AllDecidedLeadsToEach
=============================================================================
\* Modification History
\* Created Aug 4 2026 by hvanz (Hernán Vanzetto)
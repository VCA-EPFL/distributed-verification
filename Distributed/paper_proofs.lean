-- Properties that check that the network is a valid network
import Distributed.paper_implementation
import Mathlib.Tactic.ByContra

namespace Steps
open Model

-- Init properties: Check that the program has a valid init state
def coordinatorInits (c: Coordinator n) : Prop :=
    c.decision = none ∧ c.yesVotes = emptySet ∧ c.noVotes = emptySet

def participantInits (p: Participant n) (idx: Fin n): Prop :=
    p.decision = none ∧ (p.hostid = idx)

def networkInits (n: Network n): Prop :=
    n.network = []

def systemInits (s: System n) : Prop :=
    networkInits s.network ∧ coordinatorInits s.coordinator ∧ ∀ i, participantInits (s.participants i) i

-- Steps: list all possible steps

def ParticipantSendsPreference (p1: Participant n) (p2: Participant n) (snd: Message n) : Prop :=
snd = Message.Vote p1.preference p1.hostid ∧ p2 = p1

def CoordinatorReceivesPreference(c1: Coordinator n) (c2: Coordinator n) (rcv: Message n): Prop:= 
    ∃ (pref: Model.Preference) (id: Fin n), rcv = Message.Vote pref id
    ∧ if pref = Preference.Yes then
      c2 = {c1 with yesVotes := insertElem c1.yesVotes id}
    else
      c2 = {c1 with noVotes := insertElem c1.noVotes id}    


def CoordinatorMakesDecisionStep (c1: Coordinator n) (c2: Coordinator n) : Prop:=
c1.decision = none ∧
if count c1.yesVotes = n  then
   c2 = {c1 with decision := some Decision.Commit}
else if count c1.noVotes >= 1 then
   c2 = {c1 with decision := some Decision.Abort}
else
   c2 = c1

def CoordinatorSendDecideStep (c1: Coordinator n) (c2: Coordinator n) (m: Message n) : Prop:=
∃ a, c1.decision = some a ∧ m = Message.Decide a

def ParticipantReceiveDecisionStep (p1: Participant n) (p2: Participant n) (m: Message n) : Prop:=
∃ a, m = Message.Decide a ∧ p1.decision = none ∧ p2 = {p1 with decision := some a}



inductive step : System n -> System n -> Prop where
| partSendPref: ∀ (s: System n) (i: Fin n) (p2: Participant n) (snd: Message n), ParticipantSendsPreference (s.participants i) p2 snd -> step s {s with participants := updateMap s.participants i p2, network := {s.network with network := snd :: s.network.network}}
| coordRecvPref: ∀ (s: System n) (c2: Coordinator n) (rcv: Message n) , CoordinatorReceivesPreference s.coordinator c2 rcv -> rcv ∈ s.network.network-> step s {s with coordinator := c2, network := {s.network with network := s.network.network.erase rcv}}
| coordMksDec: ∀ (s: System n) (c2: Coordinator n), CoordinatorMakesDecisionStep s.coordinator c2 -> step s {s with coordinator := c2}
| coordSndDecStep: ∀ (s: System n) (snd: Message n), CoordinatorSendDecideStep s.coordinator s.coordinator snd -> step s {s with coordinator := s.coordinator, network := {s.network with network := snd :: s.network.network}}
| partRecvDec: ∀ (s: System n) (p2: Participant n) (i: Fin n) (rcv: Message n), ParticipantReceiveDecisionStep (s.participants i) p2 rcv -> rcv ∈ s.network.network -> step s {s with participants := updateMap s.participants i p2, network := s.network}

inductive steps : System n -> System n -> Prop where
| refl : ∀ s1, steps s1 s1
| trans: ∀ s1 s2 s3, steps s1 s2 -> step s2 s3 -> steps s1 s3 

def validSystem (s: System n) :=
∃ s0, systemInits s0  ∧ steps s0 s


theorem validSystemMapIds (s: System n) :
validSystem s
-> ∀ i, (s.participants i).hostid = i := by
   intros sIsValid; unfold validSystem at sIsValid; rcases sIsValid with ⟨ s0, s0Inits, sSteps ⟩
   induction sSteps
   unfold systemInits participantInits at s0Inits; grind
   rename_i s1 s2 sSteps sStep IH
   cases sStep <;> try grind
   rename_i i p m stepRule;simp [ParticipantSendsPreference] at stepRule; simp [updateMap]; grind
   rename_i p i  m stepRule mInN ;simp [ParticipantReceiveDecisionStep] at stepRule; simp [updateMap]; grind








theorem commitImpYesVotesIsNINV (s: System n) :
validSystem s
-> count s.coordinator.yesVotes ≠ n
-> (∀ i, (s.participants i).decision ≠  some Decision.Commit) ∧ Message.Decide Decision.Commit ∉ s.network.network ∧ s.coordinator.decision ≠ Decision.Commit := by
   intros validSys
   intro coordNeqN
   unfold validSystem at validSys; rcases  validSys with ⟨ s0, s0Inits, sSteps ⟩
   induction sSteps with
   | refl => simp [systemInits, networkInits, participantInits, coordinatorInits] at s0Inits; grind
   | trans s1 s2 sStep sSteps IH =>
     cases sSteps with
     | partRecvDec p i m stepRule mInN =>
       simp [ParticipantReceiveDecisionStep, updateMap] at *;
       grind
     | coordSndDecStep m stepRule =>
       simp [CoordinatorSendDecideStep] at *; 
       grind
     | coordMksDec c stepRule =>
       simp [CoordinatorMakesDecisionStep] at *;
       grind
     | partSendPref i p m stepRule =>
       simp [ParticipantSendsPreference, updateMap] at *; 
       grind
     | coordRecvPref c m stepRule mInN =>
       simp [CoordinatorReceivesPreference] at *; rcases stepRule with ⟨ p, i', mNat, splitFun ⟩; split at splitFun <;> try grind
       subst_vars; simp at *;
       have abs := fullSetCannotIncreaseContra s1.coordinator.yesVotes i' coordNeqN; grind
       
  
theorem commitImpYesVotesIsN (s: System n) :
validSystem s
-> (∃ i, (s.participants i).decision = some Decision.Commit)
-> count s.coordinator.yesVotes = n:= by
   intros validSys partIsCommit
   have contra := commitImpYesVotesIsNINV s validSys
   by_contra h; grind


theorem acceptImpliesMessageSent (s: System n) (i: Fin n):
    validSystem s
    -> s.coordinator.yesVotes i = true 
    -> (s.participants i).preference = Preference.Yes := by
       intro sIsValid sCoord
       sorry

theorem forAllIVotesImpMessageSent (s: System n):
    validSystem s
    -> count s.coordinator.yesVotes == n
    -> ∀ i, (s.participants i).preference = Preference.Yes := by
       intros validS coordTrue i
       apply acceptImpliesMessageSent
       grind; simp at *; apply fullSetImpN; grind;
       
-- Final property we want to prove
theorem commitImpliesPreference (s: System n) :
    validSystem s
    -> (∃ i, (s.participants i).decision = Decision.Commit)
    -> ∀ i, (s.participants i).preference = Preference.Yes := by
    intros validSystem existsI i
    apply forAllIVotesImpMessageSent s validSystem; simp
    apply commitImpYesVotesIsN s validSystem existsI
    
    
    
   

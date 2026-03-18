-- Properties that check that the network is a valid network
import Distributed.paper_implementation

namespace Steps
open Model

-- Init properties: Check that the program has a valid init state
def coordinatorInits (c: Coordinator n) : Prop :=
    c.decision = none ∧ c.yesVotes = Array.replicate n false ∧ c.noVotes = Array.replicate n false

def participantInits (p: Participant n): Prop :=
    p.decision = none

def networkInits (n: Network n): Prop :=
    n.network = []

def systemInits (s: System) : Prop :=
    networkInits s.network ∧ coordinatorInits s.coordinator ∧ ∀ i, participantInits (s.participants i)

-- Steps: list all possible steps

def ParticipantSendsPreference (p1: Participant n) (p2: Participant n) (snd: Message n) : Prop :=
snd = Message.Vote p1.preference p1.hostid ∧ p2 = p1

def CoordinatorReceivesPreference(c1: Coordinator n) (c2: Coordinator n) (rcv: Message n): Prop:= 
    ∃ (pref: Model.Preference) (id: Fin n), rcv = Message.Vote pref id
    ∧ if pref = Preference.Yes then
      c2 = {c1 with yesVotes := c1.yesVotes.insertIdx! id.toNat true}
    else
      c2 = {c1 with noVotes := c1.noVotes.insertIdx! id.toNat true}    


def CoordinatorMakesDecisionStep (c1: Coordinator n) (c2: Coordinator n) : Prop:=
c1.decision = none ∧
if c1.yesVotes.count true == n then
   c2 = {c1 with decision := some Decision.Commit}
else if c1.noVotes.count true  >= 1 then
   c2 = {c1 with decision := some Decision.Abort}
else
   c2 = c1

def CoordinatorSendDecideStep (c1: Coordinator n) (c2: Coordinator n) (m: Message n) : Prop:=
∃ a, c1.decision = some a ∧ m = Message.Decide a

def ParticipantReceiveDecisionStep (p1: Participant n) (p2: Participant n) (m: Message n) : Prop:=
∃ a, m = Message.Decide a ∧ p1.decision = none ∧ p2 = {p1 with decision := some a}


inductive step : System -> System -> Prop where
| partSendPref: ∀ (s: System) i p2 snd, ParticipantSendsPreference (s.participants i) p2 snd -> step s {s with participants := updateSet s.participants i p2, network := {s.network with network := snd :: s.network.network}}
| coordRecvPref: ∀ (s: System) c2 rcv , CoordinatorReceivesPreference s.coordinator c2 rcv -> step s {s with coordinator := c2, network := {s.network with network := s.network.network.erase rcv}}
| coordMksDec: ∀ s c2, CoordinatorMakesDecisionStep s.coordinator c2 -> step s {s with coordinator := c2}
| coordSndDecStep: ∀ (s: System) snd, CoordinatorSendDecideStep s.coordinator s.coordinator snd -> step s {s with coordinator := s.coordinator, network := {s.network with network := snd :: s.network.network}}
| partRecvDec: ∀ s p2 i rcv, ParticipantReceiveDecisionStep (s.participants i) p2 rcv -> rcv ∈ s.network.network -> step s {s with participants := updateSet s.participants i p2, network := {s.network with network := s.network.network.erase rcv}}

inductive steps : System -> System -> Prop where
| refl : ∀ s1, steps s1 s1
| trans: ∀ s1 s2 s3, steps s1 s2 -> step s2 s3 -> steps s1 s3 

def validSystem (s: System) :=
∃ s0, systemInits s0  ∧ steps s0 s




theorem commitImpliesMessageSent (s0 s: System) :
    validSystem s0
    -> step s0 s 
    -> (∃ i, (s.participants i).decision = Decision.Commit)
    -> ∃ i, (s0.participants i).decision = Decision.Commit ∨ Message.Decide Decision.Commit ∈ s0.network.network := by
    intros s0Valid sSteps sCommits
    cases sSteps with
    | partSendPref i p m stepRule =>
      simp [ParticipantSendsPreference] at stepRule; simp at sCommits; rcases sCommits with ⟨ i', oldCommit⟩; unfold updateSet at oldCommit 
      grind
    | partRecvDec  p i m stepRule net =>
      simp [ParticipantReceiveDecisionStep] at stepRule; simp at sCommits;rcases sCommits with ⟨ i', oldCommit⟩; unfold updateSet at oldCommit; exists i'
      split at oldCommit <;> try grind
    | coordSndDecStep m stepRule =>
      grind
    | coordMksDec c stepRule => grind
    | coordRecvPref => grind

theorem messageSentImplies (s: System) :
    validSystem s ->
    Message.Decide Decision.Commit ∈ s.network.network
    -> s.coordinator.decision = Decision.Commit := by
       intro sValid messInNetwwork; unfold validSystem at sValid; rcases sValid  with ⟨ s0, s0Inits, sSteps ⟩
       induction sSteps with
       | refl =>
         unfold systemInits networkInits at s0Inits
         grind
       | trans s1 s2 s1Steps s2Step IH =>
         cases s2Step <;> simp [CoordinatorSendDecideStep, CoordinatorSendDecideStep, CoordinatorMakesDecisionStep, CoordinatorReceivesPreference, ParticipantSendsPreference] at * <;> grind
         
         
theorem decisionImpliesVotes (s: System) :
    validSystem s 
    -> s.coordinator.decision = Decision.Commit
    -> s.coordinator.yesVotes.count true == s.n := by
       intro sValid messInNetwwork; unfold validSystem at sValid; rcases sValid  with ⟨ s0, s0Inits, sSteps ⟩
       induction sSteps with
       | refl =>
         unfold systemInits coordinatorInits at s0Inits
         grind
       | trans s1 s2 s1Steps s2Step IH =>
         cases s2Step with
         | partSendPref i p m stepRule =>
           simp [ParticipantSendsPreference] at stepRule; grind
         | partRecvDec  p i m stepRule net =>
           simp [ParticipantReceiveDecisionStep] at stepRule; grind
         | coordSndDecStep m stepRule => grind
         | coordMksDec c stepRule => simp [CoordinatorMakesDecisionStep] at stepRule; grind
         | coordRecvPref c m stepRule=>
           simp [CoordinatorReceivesPreference ] at *; rcases stepRule with ⟨pref, id, mNat, func⟩
           sorry


                       
         
         



-- Final property we want to prove
theorem commitImpliesPreference (s: System) :
    validSystem s
    -> (∃ i, (s.participants i).decision = Decision.Commit)
    -> ∀ i, (s.participants i).preference = Preference.Yes := by
    intros validSystem existsI i; simp [Steps.validSystem] at validSystem
    rcases validSystem with ⟨s0, s0Inits, s0StepsS⟩
    
    sorry
    
    

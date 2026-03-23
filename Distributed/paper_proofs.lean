-- Properties that check that the network is a valid network
import Distributed.paper_implementation

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
| partRecvDec: ∀ (s: System n) (p2: Participant n) (i: Fin n) (rcv: Message n), ParticipantReceiveDecisionStep (s.participants i) p2 rcv -> rcv ∈ s.network.network -> step s {s with participants := updateMap s.participants i p2, network := {s.network with network := s.network.network.erase rcv}}

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


theorem commitImpliesMessageSent (s0 s: System n) :
    validSystem s0
    -> step s0 s 
    -> (∃ i, (s.participants i).decision = Decision.Commit)
    -> ∃ i, (s0.participants i).decision = Decision.Commit ∨ Message.Decide Decision.Commit ∈ s0.network.network := by
    intros s0Valid sSteps sCommits
    cases sSteps with
    | partSendPref i p m stepRule =>
      simp [ParticipantSendsPreference] at stepRule; simp at sCommits; rcases sCommits with ⟨ i', oldCommit⟩; unfold updateMap at oldCommit 
      grind
    | partRecvDec p i m stepRule net =>
      simp [ParticipantReceiveDecisionStep] at stepRule; simp at sCommits;rcases sCommits with ⟨ i', oldCommit⟩; unfold updateMap at oldCommit; exists i'
      split at oldCommit <;> try grind
    | coordSndDecStep m stepRule =>
      grind
    | coordMksDec c stepRule => grind
    | coordRecvPref => grind



theorem messageSentImplies (s: System n) :
    validSystem s ->
    Message.Decide Decision.Commit ∈ s.network.network
    -> s.coordinator.decision = Decision.Commit := by
       intro sValid messInNetwwork; unfold validSystem at sValid; rcases sValid  with ⟨ s0, s0Inits, sSteps ⟩
       induction sSteps with
       | refl =>
         unfold systemInits networkInits at s0Inits
         grind
       | trans s1 s2 s1Steps s2Step IH =>
         cases s2Step <;> simp [CoordinatorSendDecideStep, CoordinatorSendDecideStep, CoordinatorMakesDecisionStep, CoordinatorReceivesPreference, ParticipantSendsPreference] at * <;> try grind
         
       
              
         
theorem decisionImpliesVotes (s: System n) :
    validSystem s 
    -> s.coordinator.decision = Decision.Commit
    -> count s.coordinator.yesVotes == n := by
       intro sValid messInNetwork; unfold validSystem at sValid; rcases sValid  with ⟨ s0, s0Inits, sSteps ⟩
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
           split at func <;> try grind
           subst_vars; simp at *
           apply fullSetCannotIncrease; apply IH; apply messInNetwork
           

theorem yesVotesImpMessage (s_ s: System n) (i: Fin n):
    validSystem s_
    -> step s_ s
    -> ∀ i, s.coordinator.yesVotes i = true 
    -> s_.coordinator.yesVotes i = true ∨ Message.Vote Preference.Yes i ∈ s_.network.network := by
       intros s0Valid stepS
       cases stepS with
       | partSendPref i p m stepRule =>
           simp [ParticipantSendsPreference] at stepRule; grind
       | partRecvDec  p i m stepRule net =>
           simp [ParticipantReceiveDecisionStep] at stepRule; grind
       | coordSndDecStep m stepRule => grind
       | coordRecvPref c m stepRule =>
         simp [CoordinatorReceivesPreference] at stepRule; simp; intro x
         intros yesVotesIsTrue; rcases stepRule with ⟨p, i', mIsVote, funcFlow ⟩; split at funcFlow; subst_vars; simp [insertElem, updateMap] at yesVotesIsTrue <;> try grind
         subst_vars; grind
       | coordMksDec c stepRule =>
         simp [CoordinatorMakesDecisionStep] at stepRule; rcases stepRule with ⟨ cIsNone, splitFun ⟩; split at splitFun
         intros i cTrue; subst_vars; grind
         intros i cTrue; subst_vars; simp at *; split at splitFun <;> try grind
         subst_vars; simp at *; left; apply cTrue
         
         
theorem messageSentImp (s: System n) (i: Fin n) :
    validSystem s
    -> Message.Vote Preference.Yes i ∈ s.network.network
    -> (s.participants i).preference = Preference.Yes := by
       intro sIsValid pInN; simp [validSystem] at sIsValid; rcases sIsValid with ⟨s0, s0Inits, sSteps⟩
       induction sSteps
       simp [systemInits, networkInits] at s0Inits; grind
       rename_i s1 s2 steps1 step1 IH
       cases step1 <;> simp [CoordinatorSendDecideStep, CoordinatorSendDecideStep, CoordinatorMakesDecisionStep, CoordinatorReceivesPreference, ParticipantSendsPreference, ParticipantReceiveDecisionStep] at * <;> try grind
       rename_i i' p m sysInfo; rcases sysInfo with ⟨ eq1, eq2 ⟩; subst eq1 eq2; simp [updateMap]; split <;> try cases pInN <;> try grind
       rename_i neq messEq; simp at messEq;
       rw [validSystemMapIds] at messEq; grind; simp [validSystem]; grind
       rename_i p n1  m rule messInN; rcases rule with ⟨ d, mDec ,decNone , pNat ⟩; subst_vars; simp [updateMap]; split <;> try grind
       
                   
           
theorem acceptImpliesMessageSent (s: System n) (i: Fin n):
    validSystem s
    -> s.coordinator.yesVotes i = true 
    -> (s.participants i).preference = Preference.Yes := by
       intro sIsValid sCoord
       apply messageSentImp; apply sIsValid
       simp [validSystem] at sIsValid; rcases sIsValid with ⟨ s0, s0Inits, sSteps ⟩
       induction sSteps
       simp [systemInits, networkInits] at s0Inits; 
       sorry
       sorry
       
       
       

           
theorem votesImpliesMessagesSent (s: System n):
    validSystem s
    -> n ≠ 0
    -> count s.coordinator.yesVotes == n
    -> ∀ i, (s.participants i).preference = Preference.Yes := by
       intros validS neqZero coordTrue i
       apply acceptImpliesMessageSent
       grind; simp at *; apply fullSetImpN; grind;



       
-- Final property we want to prove
theorem commitImpliesPreference (s: System n) :
    validSystem s
    -> n ≠ 0
    -> (∃ i, (s.participants i).decision = Decision.Commit)
    -> ∀ i, (s.participants i).preference = Preference.Yes := by
    intros validSystem existsI i; simp [Steps.validSystem] at validSystem
    rcases validSystem with ⟨s0, s0Inits, s0StepsS⟩
    apply votesImpliesMessagesSent; unfold validSystem; grind
    exact existsI
    sorry
    
    
   

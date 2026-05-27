-- Properties that check that the network is a valid network
import Distributed.paper_model
import Distributed.base_structures
import Mathlib.Tactic.ByContra

namespace Steps
open PaperModel
open Model

theorem validSystemMapIds (s: System n) :
validSystem s
-> ∀ i, (s.participants i).hostid = i := by
   intros sIsValid; unfold validSystem at sIsValid; rcases sIsValid with ⟨ s0, s0Inits, sSteps, nNeqZero ⟩
   induction sSteps
   unfold systemInits participantInits at s0Inits; grind
   rename_i s1 s2 sSteps sStep IH
   cases sStep <;> try grind
   rename_i i p m stepRule;simp [ParticipantSendsPreference] at stepRule; simp [updateMap]; grind
   rename_i p i  m stepRule mInN ;simp [ParticipantReceiveDecisionStep] at stepRule; simp [updateMap]; grind


theorem commitImpYesVotesIsNINV (s: System n) :
validSystem s
-> count s.coordinator.yesVotes ≠ n
-> (∀ i, (s.participants i).decision ≠ some Decision.Commit) ∧ Message.Decide Decision.Commit ∉ s.network.network ∧ s.coordinator.decision ≠ Decision.Commit := by
   intros validSys
   intro coordNeqN
   unfold validSystem at validSys; rcases  validSys with ⟨ s0, s0Inits, sSteps , nNeqZero⟩
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


theorem acceptImpliesMessageSentINV (s: System n) (i: Fin n):
    validSystem s
     -> (s.participants i).preference ≠ Preference.Yes
     -> s.coordinator.yesVotes i = false ∧ Message.Vote Preference.Yes i ∉ s.network.network := by
       intro validSys sPref
       unfold validSystem at validSys; rcases validSys with ⟨ s0, s0Inits, sSteps , nNeqZero⟩
       induction sSteps with
       | refl => simp [systemInits, coordinatorInits, participantInits, networkInits] at s0Inits; unfold emptySet at s0Inits; grind
       | trans s1 s2 sSteps sStep IH =>
         cases sStep with
         | partRecvDec p i m stepRule mInN =>
           simp [ParticipantReceiveDecisionStep, updateMap] at *;
           grind
         | coordSndDecStep m stepRule =>
           simp [CoordinatorSendDecideStep] at *; 
           grind
         | coordMksDec c stepRule =>
           simp [CoordinatorMakesDecisionStep] at *;
           rcases stepRule with ⟨ s1None, splitFun ⟩;  
           split at splitFun
           subst_vars; grind
           split at splitFun <;> try (subst_vars; grind)
         | partSendPref i' p m stepRule =>
           simp [ParticipantSendsPreference, updateMap] at *; 
           rcases stepRule with ⟨ _, _ ⟩ ;
           subst_vars;split at sPref <;> try grind
           rename_i i_neq; rw [validSystemMapIds] <;> try grind
           unfold validSystem; exists s0
         | coordRecvPref c m stepRule mInN =>
           simp [CoordinatorReceivesPreference] at *; rcases stepRule with ⟨ p, i', mNat, splitFun ⟩; split at splitFun; subst_vars; simp;
           have IHAPP := IH sPref; 
           unfold insertElem updateMap; split <;> try grind
           subst_vars; grind
           
           
     

theorem acceptImpliesMessageSent (s: System n) (i: Fin n):
    validSystem s
    -> s.coordinator.yesVotes i = true 
    -> (s.participants i).preference = Preference.Yes := by
       have contra := acceptImpliesMessageSentINV s i 
       by_contra h;
       grind
       

theorem forAllIVotesImpMessageSent (s: System n):
    validSystem s
    -> count s.coordinator.yesVotes == n
    -> ∀ i, (s.participants i).preference = Preference.Yes := by
       intros validS coordTrue i
       apply acceptImpliesMessageSent
       grind; simp [validSystem] at *; apply fullSetImpN; grind;
       grind
       
       
-- Final property we want to prove
theorem commitImpliesPreference (s: System n) :
    validSystem s
    -> (∃ i, (s.participants i).decision = Decision.Commit)
    -> ∀ i, (s.participants i).preference = Preference.Yes := by
    intros validSystem existsI i
    apply forAllIVotesImpMessageSent s validSystem; simp
    apply commitImpYesVotesIsN s validSystem existsI
    
    
    
   

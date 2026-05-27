import Distributed.base_structures
import Distributed.paxos_model
import Mathlib.Tactic.ByContra

open Model
open PaxosModel
namespace PaxosProof


theorem learner_choice_is_constant_inv_step (s s': System a l p):
 ∀ i v, (s.learners i).decide = some v -> step s s' -> (s'.learners i).decide = some v := by
   intros i v v_decides s_step_s' 
   cases s_step_s' with
   | workingStep =>
     rename_i curr_step
     cases curr_step <;> try grind
     simp at *
     rename_i i_ l2 m v_ netState
     rcases netState with ⟨mNat, sLearn, sDec, l2Val⟩
     rcases l2 with ⟨lLeq, vVal⟩
     sorry
     sorry
     sorry
     sorry
     sorry
     sorry
   | failureStep =>
     rename_i curr_step
     cases curr_step <;> try grind
     
     

theorem learner_choice_is_constant_inv (s s': System a l p):
 ∀ i v, (s.learners i).decide = some v -> steps s s' -> (s'.learners i).decide = some v := by
   intros i v sDecV sSteps
   induction sSteps
   . assumption
   . rename_i s1 s2 _ _ IH
     apply (learner_choice_is_constant_inv_step s1 s2 i v IH)
     assumption
     

theorem learner_choice_is_constant (s s': System a l p):
 ∀ i v, (s.learners i).decide = some v -> steps s s' -> (s'.learners i).decide = some v := by
   apply learner_choice_is_constant_inv

    
theorem acceptor_choice_is_constant_inv_step (s s': System a l p):
 ∀ i v, (s.acceptors i).accepted = some v -> step s s' -> (s'.acceptors i).accepted = some v := by
   intros i v v_decides s_step_s' 
   cases s_step_s' with
   | workingStep =>
     rename_i curr_step
     cases curr_step <;> try grind
     simp at *
     rename_i pid i_ l2 acc m currState
     rcases currState with ⟨mAcc, sAccPid, sAccNone, accVal ⟩ 
     by_cases (i = i_)
     . sorry
     . unfold updateMap
       grind
   | failureStep =>
     rename_i curr_step
     cases curr_step <;> try grind
     
     

theorem acceptor_choice_is_constant_inv (s s': System a l p):
 ∀ i v, (s.acceptors i).accepted = some v -> steps s s' -> (s'.acceptors i).accepted = some v := by
   intros i v sDecV sSteps
   induction sSteps
   . assumption
   . rename_i s1 s2 _ _ IH
     apply (acceptor_choice_is_constant_inv_step s1 s2 i v IH)
     assumption
     

theorem acceptor_choice_is_constant (s s': System a l p):
 ∀ i v, (s.acceptors i).accepted = some v -> steps s s' -> (s'.acceptors i).accepted = some v := by
   apply acceptor_choice_is_constant_inv


@[simp]
def learner_invariant (ls: Map l (Learner a l)) (v1 v2: Value):=
(∀ j v (s1: Set a), count s1 > a / 2 -> (∀ (i : Fin a), contains s1 i = true → (ls j).decMap i = v) )
∧ ∀ i j, ((ls j).decide ≠ some v2 ∨  (ls i).decide ≠ some v1)


theorem learners_choice_is_unique_inv (s: System a l p):
∀ v1 v2, systemIsValid s-> v1 ≠ v2 -> learner_invariant s.learners v1 v2
:= by
  intros v1 v2 sIsValid v1NeqV2
  unfold systemIsValid at sIsValid; rcases sIsValid with ⟨s0, sInits, sSteps ⟩
  induction sSteps with
  | refl =>
    simp [systemInits, learnerInits, acceptorInits, networkInits, proposerInits] at sInits
    simp [sInits] 
  | trans s1 s2 s0_steps_s1 s1_step_s2 IH =>
    cases s1_step_s2 with
    | failureStep stepRule =>
      cases stepRule <;> try grind
    | workingStep stepRule =>
      cases stepRule with
      | sendprepare =>
        grind
      | sendpromise => grind
      | receivepromise => grind
      | sendacceptor => grind
      | receiveacceptor => grind
      | sendlearner => grind
      | receivelearner  i k l2 m v id stepRule =>
        simp [updateMap]
        simp at stepRule; rcases stepRule with ⟨ mNat, decNat, l2Nat⟩
        subst_vars
        sorry
      | choosefinalvalue  l2 v k stepRule =>
        simp [updateMap] at *
        rcases stepRule with ⟨set1, s1Bound, s1Nat, l2Nat⟩
        rcases IH with ⟨ ⟨ v', leftRule⟩ , rightRule ⟩ 
        constructor
        . exists v'; subst l2Nat
          intros i st1 st1Bound j stNat 
          sorry
        . intros i j; split <;> split <;> try grind
          cases rightRule i j <;> try grind
          subst_vars; simp; left
          
          
        
        
        
theorem learners_choice_is_unique (s : System a l p):
 ∀ i j v1 v2,systemIsValid s -> (s.learners i).decide = some v1 -> (s.learners j).decide = some v2 -> v1 = v2 := by
   intros i j v1 v2
   have cc := learners_choice_is_unique_inv s v1 v2
   simp at cc
   by_contra contra
   grind
   
   

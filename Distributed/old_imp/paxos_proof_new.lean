import Distributed.base_structures
import Distributed.paxos_model
import Mathlib.Tactic.ByContra

open Model
open PaxosModel
namespace PaxosProof


@[simp]
def learner_invariant (learner: Learner a l) (v: Value) :=
(∃ (s: Set a), count s > a / 2 ∧ (∀ i, contains s i -> learner.decMap i = v ))



theorem unique_set (learners: Map l (Learner a l)) (v1 v2: Value) (j: Fin l):
(∃ s, a / 2 < count s ∧ ∀ (i : Fin a), contains s i = true → (learners j).decMap i = some v1)
-> (∃ s, a / 2 < count s ∧ ∀ (i : Fin a), contains s i = true → (learners j).decMap i = some v2)
-> v1 = v2 := by sorry

theorem valid_sys_imp_sing_val_contra (s: System a l p):
systemIsValid s
-> ∃ v, ∀ j, (s.learners j).decide ≠ none
→ (s.learners j).decide = some v ∧ learner_invariant (s.learners j) v  := by
  intros sIsValid; simp [systemIsValid] at sIsValid; rcases sIsValid with ⟨ s0, s0Inits, s0Steps⟩
  induction s0Steps with
  | refl =>
    exists 1;
    simp [systemInits, networkInits, proposerInits, acceptorInits, learnerInits] at s0Inits
    simp [s0Inits]
  | trans s1 s2 s0Steps s1Step IH =>
    cases s1Step with
    | failureStep stepRule => cases stepRule; simp; sorry
    | workingStep stepRule =>
      cases stepRule with
      | choosefinalvalue l1 v' i stepRule =>
        rcases IH with ⟨v, IHProp⟩
        exists v; intros j learnerUpd; simp [updateMap] at *
        split <;> try grind
        
          

          
          


theorem valid_sys_imp_sing_val (s : System a l p):
systemIsValid s
-> ∃ v, ∀ j, (s.learners j).decide = some v ∨ (s.learners j).decide = none:= by
   intros sIsValid
   have cc := valid_sys_imp_sing_val_contra s sIsValid
   rcases cc with ⟨v, exec ⟩; exists v
   grind
   

theorem learners_choice_is_unique (s : System a l p):
 ∀ i j v1 v2, systemIsValid s -> (s.learners i).decide = some v1 -> (s.learners j).decide = some v2 -> v1 = v2 := by
   intro i j v1 v2 sIsValid sDecV1 sDecV2
   have t1 := valid_sys_imp_sing_val s
   grind
     
   
   
   
   

import Distributed.base_structures
import Distributed.paxos_model
import Mathlib.Tactic.ByContra

open Model
open PaxosModel
namespace PaxosProof


@[simp]
def set_invariant (s1: System a l p) (v: Value) (learnerId: Fin l) :=
(∃  (s: Set a), count s > a / 2 ∧  (∀ i, contains s i -> (s1.learners learnerId).decide = some v ∨ (s1.learners learnerId).decMap i = v ∨ (@Message.Learn a (i, v) ∈ s1.network.messages) ∨ (∃ id, (s1.acceptors i).accepted = some (id, v)))) 


/--
def setCounts (s: System a l p) (v1 v2: Value) (j: Fin l):
set_invariant s v1 j
-> set_invariant s v2 j
-> v1 = v2 := by
   sorry




theorem inv2_prop (s1 s2: System a l p) (j: Fin l):
step s1 s2
-> ((s1.learners j).decide = none ∧ ∀ (v' : Value), ¬set_invariant s1 v' j)
-> (s2.learners j).decide = none ∧ ∀ (v' : Value), ¬set_invariant s2 v' j := by
   intros s1Step IH
   simp [set_invariant] at *
   cases s1Step with
   | failureStep stepRule =>
     cases stepRule with
     | lostmessage m n2 stepRule =>
       simp at *; simp [IH]
       intros v' set countSet
       rcases (IH.right v' set countSet) with ⟨ x, setContains, decInside, decMap, messIn, acceptedOk ⟩ ; clear IH
       grind
   | workingStep stepRule =>
     cases stepRule with
     | choosefinalvalue l2 v i stepRule =>
       simp at *;simp [updateMap]; split <;> try grind
       rename_i eq; subst eq
       rcases stepRule with ⟨set1, set1Count, set1Contains,set1None, l2Nat ⟩
       subst l2Nat; exfalso;
       rcases (IH.right v set1 set1Count) with ⟨ x, setContains, decInside, decMap, messIn, acceptedOk ⟩ ; clear IH
       grind
     | _ => sorry
       
--/


theorem inv_proof (s1 s2: System a l p) (v: Value):
step s1 s2
-> ∀ j, (s2.learners j).decide ≠ some v
-> (s1.learners j).decide ≠ some v  := by
   intros s1Step j IH
   by_contra contra
   cases s1Step <;> rename_i stepRule <;> cases stepRule <;> try grind
   . rename_i i learn m v' x stepRule; simp at *
     have ⟨ learnNat,mInNet, learnDec, iNat ⟩ := stepRule;clear stepRule; subst_vars
     unfold updateMap at IH; split at IH <;> try grind
   . rename_i l2 v' u stepRule; simp at *
     have ⟨set, setCount, setContains, l1None, l2Nat ⟩ := stepRule; clear stepRule
     subst l2Nat; simp [updateMap] at IH; split at IH <;> try grind

theorem valid_sys_imp_sing_val_contra (s: System a l p):
systemIsValid s
-> ∃ v, ∀ j, (s.learners j).decide ≠ some v
→ (s.learners j).decide = none ∧ (∀ v', ¬ set_invariant s v' j) := by
  intros sIsValid;
  simp [systemIsValid] at sIsValid
  have ⟨ s0, s0Inits, s0Steps ⟩ := sIsValid; clear sIsValid
  induction s0Steps with
  | refl =>
    simp [systemInits, learnerInits, networkInits, acceptorInits] at s0Inits
    exists 1; simp [s0Inits]
    intros j v' set1 setCount
    have cc := countSupImpContains (a / 2) set1; simp [s0Inits] at cc
    have cc_ := cc setCount; exact cc_
  | trans s1 s2 s0Steps s1Step IH=>
    rcases IH with ⟨ v, IHApp ⟩
    exists v; intros j s2DecidesNone
    have inv_app := inv_proof s1 s2 v s1Step j s2DecidesNone
    have IHProp := IHApp j inv_app
    have ind_proof := inv2_prop s1 s2 j s1Step IHProp
    grind
  
     
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
     
   

   
   
   

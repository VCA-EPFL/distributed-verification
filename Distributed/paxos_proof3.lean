import Distributed.base_structures
import Distributed.paxos_model
import Mathlib.Tactic.ByContra

open Model
open PaxosModel
namespace PaxosProof


@[simp]
def set_invariant (s1: System a l p) (v: Value) (learnerId: Fin l) :=
(∃  (s: Set a), count s > a / 2 ∧  (∀ i, contains s i -> ((s1.learners learnerId).decMap i = v ∧ (s1.learners learnerId).decide = some v ∧  (∃ id, (s1.acceptors i).accepted = some (id, v))))) 



   




theorem decide_imp_set_exists (s: System a l p) (j: Fin l) (v: Value):
systemIsValid s
-> (s.learners j).decide = some v
-> set_invariant s v j := by
   intros sIsValid learnIsSome
   simp [systemIsValid] at sIsValid
   --have absCase := absCase s j v
   rcases sIsValid with ⟨ s0, s0Inits, s0Steps⟩
   induction s0Steps with
   | refl =>
     simp [systemInits, learnerInits] at s0Inits
     simp [s0Inits] at learnIsSome
   | trans s1 s2 s0Steps s1Step IH=>
     cases s1Step with
     | failureStep stepRule=>
       cases stepRule; rename_i m n2 stepRule; 
       simp at stepRule ⊢ learnIsSome; have IHApp := IH learnIsSome; simp at IHApp; rcases IHApp with ⟨ set, setCount, setContains ⟩
       exists set;
     | workingStep stepRule =>
       cases stepRule with
       | choosefinalvalue learner v' i stepRule=>
         simp at *

theorem set_inv_is_unique (s: System a l p) (v1 v2: Value) (i j: Fin l):
a >=  2
-> set_invariant s v1 i
-> set_invariant s v2 j
-> v1 = v2 := by
   intros aBound inv1 inv2
   simp at inv1 inv2
   rcases inv1 with ⟨ set1, countSet1, containsSet1⟩
   rcases inv2 with ⟨ set2, countSet2, containsSet2⟩
   have f1 := setMaxContainsBoth set1 set2
   grind

theorem learners_choice_is_unique (s : System a l p):
 ∀ i j v1 v2, systemIsValid s -> (s.learners i).decide = some v1 -> (s.learners j).decide = some v2 -> v1 = v2 := by
   intro i j v1 v2 sIsValid sDecV1 sDecV2
   have t1 := decide_imp_set_exists s i v1 sIsValid
   have t2 := decide_imp_set_exists s j v2  sIsValid
   have f := set_inv_is_unique s v1 v2  i j
   simp [systemIsValid, systemInits] at sIsValid;
   have aBound: (a >= 2 ) := by (rcases sIsValid with ⟨ s0, rest⟩ ; simp [rest])
   have f_ := f aBound
   grind

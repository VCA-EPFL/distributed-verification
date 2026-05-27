import Distributed.base_structures
import Distributed.paxos_model
import Mathlib.Tactic.ByContra

open Model
open PaxosModel
namespace PaxosProof


def inv_1 (learners: Map l (Learner a l) ) (v: Value) (j: Fin l):=
(learners j).decide = some v
-> (∃  (s: Set a) (id: PropId), count s > a / 2 ∧  (∀ i, contains s i -> (learners j).decMap i = (v, id) )) 

theorem inv1_holds (s1 s2: System a l p):
∀ j v, step s1 s2 
-> inv_1 s1.learners v j
-> inv_1 s2.learners v j := by
   intros j v step inv1
   cases step <;> rename_i stepRule <;> cases stepRule <;> try grind
   . rename_i i learner mess v' stepRule
     simp [inv_1, updateMap] at *
     split <;> try grind
     intros decNone; have ⟨ x, rest ⟩ :=inv1 decNone
     exists x 
   . rename_i l1 v' i stepRule
     simp [inv_1, updateMap] at *
     split <;> try grind
     rcases stepRule with ⟨ set, setCounts, setContains, setIsNone, set ⟩
     intros l1Decs; exists set; simp [setCounts]; simp at l1Decs; subst l1Decs;
     sorry
     sorry
     



def inv_2 (learners: Map l (Learner a l)) (acceptors: Map a (Acceptor a) )  (j: Fin l) :=
  ∀ i v (id: PropId), (learners j).decMap i = some (id, v) →
    ∃ (id': PropId), id' ≥ id -> (acceptors i).accepted = some (id', v)

theorem inv2_holds (s1 s2: System a l p):
∀ j, step s1 s2 
-> inv_2 s1.learners s1.acceptors  j
-> inv_2 s2.learners s2.acceptors  j := by sorry


def inv_3 (acceptors: Map a (Acceptor a) ) (v1 v2: Value) :=
∀ (key1 key2: PropId),
key1 <= key2
-> (∃  (s: Set a), count s > a / 2 ∧  (∀ i, contains s i -> (acceptors i).accepted = some (key1, v1)))
-> (∃  (s: Set a), count s > a / 2 ∧  (∀ i, contains s i -> (acceptors i).accepted = some (key2, v2)))
-> v1 = v2

theorem inv3_holds (s1 s2: System a l p):
step s1 s2 
-> inv_3  s1.acceptors v1 v2
-> inv_3 s2.acceptors v1 v2 := by sorry



/--     
theorem inv2_holds (s1 s2: System a l p):
∀ j v, step s1 s2 
-> inv_2 s1.learners s1.acceptors v j
-> inv_2 s2.learners s2.acceptors v j := by
   intros j v s1Step IH
   cases s1Step <;> rename_i stepRule <;> cases stepRule <;> try grind
   . rename_i id i v' acc m stepRule
     simp [inv_2] at *; intros set1 set1Counts set1Contains
     rcases stepRule with ⟨ sAcc, sId, accNat ⟩ 
     rcases (IH set1 set1Counts set1Contains) with ⟨ set2, set2Counts, set2Contains ⟩; subst_vars
     have IHApp := IH set1 set1Counts set1Contains; 
     rcases IHApp with ⟨set3,  set3Counts, set3Contains ⟩
     simp [updateMap]; exists set3
     simp [set3Counts]; intros i2 i2IsContained;
     split <;> try grind
     simp; sorry
--/


theorem inv_app (s : System a l p):
 ∀ i v1 v2, systemIsValid s
 -> inv_1 s.learners v1 i ∧ inv_2 s.learners s.acceptors i ∧ inv_3 s.acceptors v1 v2 := by
   simp [systemIsValid]
   intros i v1 v2 s0 inits sSteps
   induction sSteps with
   | refl =>
     simp [systemInits, learnerInits, acceptorInits] at inits
     simp [inv_1, inv_2, inv_3, inits]
     sorry
   | trans =>
     rename_i s2 s3 Steps step IH
     have c1 := inv1_holds s2 s3 i v1 step IH.left
     have c2 := inv2_holds s2 s3 i  step IH.right.left
     have c3 := inv3_holds s2 s3 step IH.right.right
     grind





theorem learners_choice_is_unique (s : System a l p):
 ∀ i j v1 v2, systemIsValid s -> (s.learners i).decide = some v1 -> (s.learners j).decide = some v2 -> v1 = v2 := by
   intros i j v1 v2 sIsValid sSomeV1 sSomeV2
   have inv_true1 := inv_app s i v1 v2 sIsValid
   have inv_true2 := inv_app s j v2 v1 sIsValid 
   rcases inv_true1 with ⟨ i11, i12, i13 ⟩ 
   rcases inv_true2 with ⟨ i21, i22, i23 ⟩
   clear i23
   simp [inv_1] at i11; simp [inv_1] at i21
   have s1 := i11 sSomeV1; rcases s1 with ⟨set1, countsSet1, x1,containsSet1 ⟩; clear i11
   have s2:= i21 sSomeV2; rcases s2 with ⟨set2, countsSet2, x2,containsSet2 ⟩ ; clear i21
   simp [inv_2] at i12; simp [inv_2] at i22; simp [inv_3] at i13;
   sorry

import Distributed.base_structures
import Distributed.paxos_model
import Mathlib.Tactic.ByContra

open Model
open PaxosModel
namespace PaxosProof


def acc_invariant (s1 : System a l p) (v : Value):=
  ∃ (s : Set a), count s > a / 2 ∧
    ∀ i, contains s i →
      ∃ id', (s1.acceptors i).accepted = some (v, id')

def mess_invariant (s1 : System a l p) (v : Value) :=
  ∃ (s : Set a), count s > a / 2 ∧
    ∀ i, contains s i →
      ∃ (id: PropId), Message.Learn (i, v, id) ∈ s1.network.messages

def learn_invariant (s1 : System a l p) (v : Value) (j: Fin l):=
  ∃ (s : Set a), count s > a / 2 ∧
    ∀ i, contains s i →
      ∃ id,  (s1.learners j).decMap i = some (v, id)

theorem some_to_learn_holds (s1 s2: System a l p) (v : Value) (j: Fin l) :
step s1 s2
-> ((s1.learners j).decide = some v -> learn_invariant s1 v j)
-> ((s2.learners j).decide = some v -> learn_invariant s2 v j)
:= by
   intros step IH sLearnDec; simp [learn_invariant] at *
   cases step <;> rename_i stepRule <;> cases stepRule <;> try grind
   . rename_i i learn mess v' pid k stepRule; simp at stepRule
     simp [updateMap] at sLearnDec ⊢ ; split at sLearnDec <;> try grind
   . rename_i l2 v i pid stepRule; simp at stepRule
     simp [updateMap] at sLearnDec ⊢; split at sLearnDec <;> try grind


theorem learn_to_mess_holds_simp (s1 s2: System a l p) (v : Value) (j: Fin l) (i: Fin a) (id: PropId):
step s1 s2
-> ((s1.learners j).decMap i = some (v, id)
      -> Message.Learn (i, v, id) ∈ s1.network.messages)
-> ((s2.learners j).decMap i = some (v, id)
      -> Message.Learn (i, v, id) ∈ s1.network.messages) := by sorry



theorem learn_to_mess_holds (s1 s2: System a l p) (v : Value) :
step s1 s2
-> (learn_invariant s1 v j -> mess_invariant s1 v)
-> (learn_invariant s2 v j -> mess_invariant s2 v) := by
   intros step IH learn_inv; simp [learn_invariant, mess_invariant] at *
   rcases learn_inv with ⟨ set, setCount, setCont ⟩
   exists set; simp [setCount]
   intros i iContained
   have si :=  learn_to_mess_holds_simp s1 s2 v 
   /--
   intros step IH learn_inv; simp [learn_invariant, mess_invariant] at *
   cases step <;> rename_i stepRule <;> cases stepRule <;> try (rename_i stepRule; simp at stepRule; grind)
   . rename_i v' n2 j stepRule; simp at stepRule;
     rcases learn_inv with ⟨ set, setCount, setCont ⟩ 
     have ⟨ set2, countSet2, set2Contains⟩  := IH set setCount setCont;
     exists set2; simp [countSet2]
     rcases stepRule with ⟨ b, n2Nat ⟩;
     rw [n2Nat]; simp; exact set2Contains
   . rename_i i n2 v' pid stepRule; simp at stepRule;
     rcases learn_inv with ⟨ set, setCount, setCont ⟩ 
     have ⟨ set2, countSet2, set2Contains⟩  := IH set setCount setCont;
     exists set2; simp [countSet2]
     rcases stepRule with ⟨ b, n2Nat ⟩;
     rw [n2Nat]; simp; intros i iContains
     rcases set2Contains i iContains with ⟨ id, idProp ⟩
     exists id; simp [idProp]; 
   . rename_i i l2 m v' pid k stepRule
     rcases learn_inv with ⟨ set, countSet, setCont ⟩
     rcases stepRule with ⟨ mIsLearn, mInN, l1None, l2Nat ⟩ ; subst l2Nat
     
     
   . rename_i l2 v' k  pid stepRule; simp at stepRule;
     rcases learn_inv with ⟨ set, setCount, setCont ⟩ ; simp at *
     apply (IH set setCount)
     intros i iCont; rcases (setCont i iCont) with ⟨ id, idProp ⟩
     simp [updateMap] at idProp; split at idProp <;> try grind
     -/
     



/--
     clear IH IHApp; simp at contra
     exists set; simp [countSet]
     intros c cContained; rcases contra with ⟨ id, idTrue, idNotCont ⟩
     have ⟨ ex, exProp ⟩  := setCont id idTrue;
     simp [updateMap] at exProp; split at exProp<;> try grind
     simp [updateMap] at exProp; split at exProp<;> try grind
     simp at exProp; rcases exProp with ⟨ eq1, eq2 ⟩
     subst_vars
     -/
     
theorem mess_to_acc_holds (s1 s2: System a l p) (v : Value):
step s1 s2
-> (mess_invariant s1 v -> acc_invariant s1 v) 
-> (mess_invariant s2 v -> acc_invariant s2 v) := by sorry

theorem full_inv_proof (s: System a l p) (v : Value) (j: Fin l):
systemIsValid s
-> ((s.learners j).decide = some v -> learn_invariant s v j)
∧ (learn_invariant s v j -> mess_invariant s v)
∧ (mess_invariant s v -> acc_invariant s v) := by
   intros sIsValid; rcases sIsValid with ⟨ s0, s0Inits, s0Steps ⟩ 
   induction s0Steps with
   | refl =>
     simp [systemInits, learnerInits, acceptorInits, networkInits] at s0Inits; simp [s0Inits, mess_invariant, learn_invariant]
     intros s countS containsS
     have abound:(2 ≤ a) := by grind
     have contra := countSupImpContains (a/2) s; simp [abound] at contra
     rcases (contra countS) with ⟨ i, containsI ⟩
     grind
   | trans s1 s2 sSteps sStep IH =>
     have e1 := some_to_learn_holds s1 s2 v j sStep IH.left
     have e2 := learn_to_mess_holds s1 s2 v sStep IH.right.left
     have e3 := mess_to_acc_holds s1 s2 v sStep IH.right.right
     grind



theorem ind_proof (s: System a l p) (v: Value) (i: Fin l):
systemIsValid s
-> (s.learners i).decide = some v
-> acc_invariant s v := by
   intros svalid sDevSome
   have ⟨ inv1, inv2, inv3 ⟩  := full_inv_proof s v i svalid
   exact (inv3 (inv2 (inv1 sDevSome)))


theorem acc_eqs (s1: System a l p) (v1 v2: Value):
acc_invariant s1 v1
-> acc_invariant s1 v2
-> v1 = v2 := by 
   intros acc1 acc2; simp [acc_invariant] at acc1 acc2
   rcases acc1 with ⟨ set1, set1Counts, set1Contains ⟩
   rcases acc2 with ⟨ set2, set2Counts, set2Contains ⟩ 
   have ⟨ i, contain1, contain2 ⟩ := setMaxContainsBoth set1 set2 set1Counts set2Counts
   have ⟨ id1, accSome1 ⟩  := set1Contains i contain1
   have ⟨ id2, accSome2 ⟩  := set2Contains i contain2; simp [accSome2] at accSome1 ; simp [accSome1]

theorem learners_choice_is_unique (s : System a l p):
 ∀ i j v1 v2, systemIsValid s -> (s.learners i).decide = some v1 -> (s.learners j).decide = some v2 -> v1 = v2 := by
  intros i j v1 v2 sIsValid sDecSome1 sDecSome2
  have t1 := ind_proof s v1 i sIsValid sDecSome1
  have t2 := ind_proof s v2 j sIsValid sDecSome2
  exact (acc_eqs s v1 v2 t1 t2)

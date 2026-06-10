import Distributed.base_structures
import Distributed.Paxos.paxos_model
import Distributed.Paxos.p2a
import Distributed.Paxos.learner_helpers
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Cases 

open Model
open PaxosModel
namespace PaxosProof

def acc_invariant (s1 : System a l p) (v : Value) (id: PropId):=
  ∃ (s : Set a), count s > a / 2 ∧
    (∀ i, contains s i →
      ∃ id', id' >= id ∧ (s1.acceptors i).accepted = some (v, id'))



-- INV4: If there are enough learners then there are enough acceptors
def inv4 (s: System a l p) (v: Value) (id: PropId) :=
(∃ set, count set > a / 2 ∧ (∀ (i: Fin a), contains  set i -> Message.Learn (i, v, id) ∈ s.network.messages))
-> ∃ id', id' >= id ∧ acc_invariant s v id'




theorem inv4Proof (s: System a l p) (v: Value) (id: PropId) :
systemIsValid s
-> inv4 s v id := by
intros svalid IH
have ⟨ set, countSet, setContains ⟩ := IH
have p1 := inv41Proof s v
have p2 := inv4aProof s v id svalid  IH
have ⟨ set2, set2Count, set2Contains ⟩ : (∃ (set : Set a), count set > a / 2 ∧
    (∀ i, contains set i →
      ∃ id' v', id' >= id ∧ (s.acceptors i).accepted = some (v', id'))) := by {
      exists set; simp [countSet]; intro i containsI
      have ⟨ v, id1, id1Bound, sAcc ⟩ := p1 i id svalid (setContains i containsI); exists id1; simp [id1Bound]; exists v 
}
have set2Contains_ :(∀ (i : Fin a), contains set2 i = true → ∃ id', id' ≥ id ∧ (s.acceptors i).accepted = some (v, id')) := by {
intros i containsI; have ⟨ id', v', idBound ⟩ := set2Contains i containsI
exists id'; simp [idBound]; rw [p2 id' i v' idBound.right idBound.left]
}
simp [acc_invariant]
exists id; simp [PropId]
exists set2


-- INV2: A learner maps to Learner message
def inv2 (s1: System a l p) (j: Fin l) (i: Fin a) (v: Value) (id: PropId):=
(s1.learners j).decMap i = some (v, id)
->  Message.Learn (i, v, id) ∈ s1.network.messages


theorem inv2Proof_ind (s1 s2: System a l p) (j: Fin l) (i: Fin a) (v: Value) (id: PropId) :
step s1 s2
-> inv2 s1 j i v id
-> inv2 s2 j i v id := by
simp [inv2]; intros step IH sIsSome
cases step <;> rename_i stepRule <;> cases stepRule <;> try (rename_i stepRule; simp at stepRule; grind)
. rename_i k l2 m v' pid c stepRule
  rcases stepRule with ⟨ mIsLearn, mInN, decIsNone, l2Nat⟩; subst l2Nat 
  simp; simp [updateMap] at sIsSome; split at sIsSome <;> try grind
  simp [updateMap] at sIsSome <;> split at sIsSome <;> try grind
. rename_i l2 v k pid stepRule
  simp [updateMap] at sIsSome; split at sIsSome <;> try grind
  rcases stepRule with ⟨ set, countSet, setContains, decisNone, l2Nat⟩; subst l2Nat; simp at ⊢ sIsSome
  grind


theorem inv2Proof (s: System a l p) (j: Fin l) (i: Fin a) (v: Value) (id: PropId) :
systemIsValid s
-> inv2 s j i v id := by
intros sIsValid 
rcases sIsValid with ⟨ s0, s0Inits, s0Steps ⟩
induction s0Steps  with
| refl =>
  simp [systemInits, learnerInits] at s0Inits
  simp [inv2, s0Inits] at ⊢ 
| trans s2 s3 s0Steps s2Step IH=>
  exact (inv2Proof_ind s2 s3 j i v id s2Step IH)




def learn_invariant (s1 : System a l p) (v : Value) (j: Fin l) (id: PropId):=
   ∃ (s : Set a), count s > a / 2 ∧
    ∀ i, contains s i →
      (s1.learners j).decMap i = some (v, id)

theorem some_to_learn_ind (s1 s2: System a l p) (v : Value) (j: Fin l) :
step s1 s2
-> ((s1.learners j).decide = some v -> ∃ id, learn_invariant s1 v j id)
-> ((s2.learners j).decide = some v -> ∃ id, learn_invariant s2 v j id)
:= by
   intros step IH sLearnDec; simp [learn_invariant] at *
   cases step <;> rename_i stepRule <;> cases stepRule <;> try (simp at sLearnDec; have ⟨ id, s, rest ⟩ := IH sLearnDec; exists id; exists s; try grind)
   . rename_i i learn mess v' pid k stepRule; simp at stepRule;
     rcases stepRule with ⟨ messNat, messInN, l1None, l2Nat ⟩; subst l2Nat
     simp [updateMap] at sLearnDec ⊢ ; split at sLearnDec
     . exists pid; grind
     . have ⟨ pid2, s, rest ⟩  := IH sLearnDec; exists pid2; exists s; grind
   . rename_i l2 v i pid stepRule
     rcases stepRule with ⟨ s, sCount, sContains, l1Nat, l2Nat ⟩ ; subst l2Nat
     simp [updateMap] at sLearnDec ⊢; split at sLearnDec
     . exists pid; grind
     . have ⟨ pid2, s, rest ⟩  := IH sLearnDec; exists pid2; exists s; grind
     
theorem some_to_learn_holds (s: System a l p) (v : Value) (j: Fin l) :
systemIsValid s
 ->
 ((s.learners j).decide = some v -> ∃ id, learn_invariant s v j id) := by
    intros sIsValid sDec
    rcases sIsValid with ⟨ s0, s0Inits, s0Steps ⟩
    induction s0Steps with
    | refl =>
      simp [systemInits, learnerInits] at s0Inits
      simp [s0Inits] at sDec
    | trans s2 s3 s0Steps s2Step IH=>
      exact (some_to_learn_ind s2 s3 v j s2Step IH sDec)

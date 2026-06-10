import Distributed.base_structures
import Distributed.Paxos.paxos_model
import Distributed.Paxos.learners
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Cases 

open Model
open PaxosModel
namespace PaxosProof


theorem ind_proof (s: System a l p) (v: Value) (i: Fin l) :
systemIsValid s
-> (s.learners i).decide = some v
-> ∃ id, acc_invariant s v id := by
   intros svalid sDevSome
   have ⟨ id, p1 ⟩  := some_to_learn_holds s v i svalid sDevSome;
   rcases p1 with ⟨ set, setCount, setContains⟩ 
   simp [acc_invariant]; 
   have cc : (∃ set, count set > a / 2 ∧ (∀ (i: Fin a), contains  set i -> Message.Learn (i, v, id) ∈ s.network.messages)) := by exists set; simp [setCount]; intros j contj; have cc := setContains j contj; exact inv2Proof s i j v id svalid cc
   have  ⟨  id', id'Bound, rest ⟩  := inv4Proof s v id svalid cc; exists id'


theorem acc_eqs (s1: System a l p) (v1 v2: Value) (id: PropId) (id': PropId):
acc_invariant s1 v1 id 
-> acc_invariant s1 v2 id'
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
  have ⟨ id1, t1⟩  := ind_proof s v1 i sIsValid sDecSome1
  have ⟨ id2, t2 ⟩  := ind_proof s v2 j sIsValid sDecSome2
  exact (acc_eqs s v1 v2 id1 id2 t1 t2) 

import Distributed.base_structures
import Distributed.paxos_model
import Mathlib.Tactic.ByContra

open Model
open PaxosModel
namespace PaxosProof



def set_invariant (s1 : System a l p) (v : Value) (learnerId : Fin l):=
  ∃ (s : Set a), count s > a / 2 ∧
    ∀ i, contains s i →
      ∃ id, (s1.learners learnerId).decMap i = some (v, id)
      ∧ (s1.acceptors i).accepted = some (v, id)


theorem inv_proof_ (s1 s2: System a l p) (v: Value) (j: Fin l):
step s1 s2 
→ (s2.learners j).decide ≠ some v 
→ (s1.learners j).decide ≠ some v := by
   intros s1Step i IH
   by_contra contra
   cases s1Step <;> rename_i stepRule <;> cases stepRule <;> try grind
   . rename_i i learn m v' x stepRule; simp at *
     have ⟨ learnNat,mInNet, learnDec, iNat ⟩ := stepRule;clear stepRule; subst_vars
     unfold updateMap at i; split at i <;> try grind
   . rename_i l2 v' u pid stepRule; simp at *
     have ⟨set, setCount, setContains, l2None, l2Nat ⟩ := stepRule
     subst l2Nat; simp [updateMap] at i; split at i <;> try grind

theorem inv_proof (s1 s2: System a l p) (v: Value):
step s1 s2 
→ (s1.learners j).decide = some v 
→ (s2.learners j).decide = some v := by
  intros step s1Dec
  by_contra
  have cc := inv_proof_ s1 s2 v
  grind

theorem set_inv_is_unique (s: System a l p) (i j: Fin l) (v1 v2: Value) : 
set_invariant s v1 i 
→ set_invariant s v2 j 
→ v1 = v2 := by
  intros setInv1 setInv2
  simp [set_invariant] at *;
  rcases setInv1 with ⟨ set1, countSet1, set1Contains ⟩
  rcases setInv2 with ⟨ set2, countSet2, set2Contains ⟩ 
  have f := setMaxContainsBoth set1 set2 countSet1 countSet2
  rcases f with ⟨ k, icontainedSet1, icontainedSet2⟩
  have ⟨ id1, eqV1⟩  := set1Contains k icontainedSet1
  have ⟨ id2, eqV2⟩  := set2Contains k icontainedSet2
  simp [eqV1] at eqV2
  grind

theorem decide_imp_set_invariant (s: System a l p) (j: Fin l) (v: Value) :
systemIsValid s
→ (s.learners j).decide = some v 
→ set_invariant s v j  := by
  simp [systemIsValid]; intros s0 s0Inits s0Steps sDecSome
  induction s0Steps with
  | refl =>
    simp [systemInits, learnerInits] at s0Inits
    simp [s0Inits, set_invariant]; exists fullSet; simp [fullSetCountsN a]
    constructor <;> try grind
  | trans s1 s2 s1Steps s1Step IH =>
    cases s1Step <;> rename_i stepRule <;> cases stepRule <;> try (simp [set_invariant] at *<;>grind)
    . sorry
    . rename_i i learn m v' pid d stepRule; simp [updateMap, set_invariant] at *
      split at sDecSome <;> try grind
    . rename_i learn2 v' i pid stepRule
      simp [updateMap, set_invariant, IH] at *
      split at sDecSome <;> try grind
      rename_i eq; subst eq; simp
      grind
    
theorem learners_choice_is_unique (s : System a l p):
 ∀ i j v1 v2, systemIsValid s -> (s.learners i).decide = some v1 -> (s.learners j).decide = some v2 -> v1 = v2 := by
  intros i j v1 v2 sIsValid sDecSome1 sDecSome2
  have h1 := decide_imp_set_invariant s i v1 sIsValid sDecSome1
  have h2 := decide_imp_set_invariant s j v2 sIsValid sDecSome2
  exact set_inv_is_unique s i j v1 v2 h1 h2

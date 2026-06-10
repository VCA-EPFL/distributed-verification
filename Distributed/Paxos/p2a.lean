import Distributed.base_structures
import Distributed.Paxos.paxos_model
import Distributed.Paxos.p2b
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Cases 

open Model
open PaxosModel
namespace PaxosProof

def inv4a1 (s: System a l p) (i: Fin a) (v : Value) (id: PropId) :=
(s.acceptors i).accepted = some (v, id)
-> Message.Accept (id, v) ∈ s.network.messages



theorem inv4a1Proof_ind (s1 s2: System a l p) (i: Fin a) (v: Value) (id: PropId) :
step s1 s2
-> inv4a1 s1 i v id
-> inv4a1 s2 i v id := by
simp [inv4a1]; intros step IH sIsSome 
cases step <;> rename_i stepRule <;> cases stepRule <;> (try (rename_i stepRule; simp at stepRule; grind))
. rename_i j pid mess acc net stepRule
  rcases stepRule with ⟨mRules, accNat, netNat⟩; subst accNat
  simp; rw [netNat]; simp; clear netNat; simp [updateMap] at sIsSome; split at sIsSome <;> try grind  
. rename_i pid j v' acc mess stepRule
  simp [updateMap] at ⊢ sIsSome; split at sIsSome <;> try grind
  rcases stepRule with ⟨ mAcc, accBound, mInN, accNat⟩; subst accNat mAcc
  simp at sIsSome; rcases sIsSome with ⟨ eq1, eq2 ⟩; subst eq1 eq2
  exact mInN



theorem inv4a1Proof (s: System a l p) (i: Fin a) (v: Value) (id: PropId)  :
systemIsValid s
-> inv4a1 s i v id:= by 
intros sIsValid 
rcases sIsValid with ⟨ s0, s0Inits, s0Steps ⟩
induction s0Steps  with
| refl =>
  simp [systemInits, acceptorInits] at s0Inits
  simp [inv4a1, s0Inits] at ⊢ 
| trans s2 s3 s0Steps s2Step IH=>
  exact (inv4a1Proof_ind s2 s3 i v id s2Step IH)



-- INV4a: learners and an accepted element show that there is 
def inv4a (s: System a l p) (v : Value) (id: PropId) :=
(∃ set, count set > a / 2 ∧ (∀ (i: Fin a), contains  set i -> Message.Learn (i, v, id) ∈ s.network.messages))
-> ∀ id' i v', (s.acceptors i).accepted = some (v', id')
->  id' >= id
->  v = v'

theorem inv4aProof (s: System a l p) (v: Value) (id: PropId)  :
systemIsValid s
-> inv4a s v id:= by
intros sIsValid set id1 i v' accIn idBound
have p2 := inv4a1Proof s i v' id1 sIsValid accIn
exact (inv4bProof s v id sIsValid set id1 v' p2 idBound)

import Distributed.base_structures
import Distributed.Paxos.paxos_model
import Distributed.Paxos.p2c
import Distributed.Paxos.learner_helpers
import Distributed.Paxos.acceptors_helpers
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Cases 

open Model
open PaxosModel
namespace PaxosProof





-- INV4b1
def inv4b1 (s: System a l p) (i: Fin a) (v: Value) (id: PropId) :=
Message.Learn (i,  v, id)  ∈ s.network.messages
-> ∀  id' p, Message.Promise id' i p ∈ s.network.messages
-> id' > id
-> p ≠ none

theorem inv4b1Proof_ind (s1 s2: System a l p) (i: Fin a)  (v: Value) (id: PropId) :
step s1 s2
-> inv4b1 s1 i v id
-> inv41 s1 i v id
-> (∀ k, (s1.acceptors k).id = k)
-> inv4b1 s2 i v id := by
   simp [inv4b1]; intros step IH i41 idIsK mLearnInN id' opt mPromisInN idBound
   cases step <;> rename_i stepRule <;> cases stepRule <;> repeat (rename_i stepRule; rcases stepRule) <;> (try grind)
   . simp at *; rename_i j pid mess acc net accNat netNat mRules
     subst accNat; rw [netNat] at mLearnInN mPromisInN; simp at mLearnInN mPromisInN
     cases mPromisInN <;> try grind
     rename_i eqs; rcases eqs with ⟨ eq1, eq2, eq3 ⟩; subst_vars
     have ⟨ v', id' , idBound, sAccSome ⟩  := i41 mLearnInN
     rw [idIsK j] at sAccSome; rw [sAccSome]; simp
   . simp at *; rename_i mNat; rw [mNat] at mLearnInN mPromisInN; simp at mLearnInN mPromisInN; rename_i j net v2 pid accSome
     cases mLearnInN <;> try grind
     rename_i eqs; rcases eqs with ⟨ e1, e2, e3 ⟩; subst e1 e2 e3
     by_cases c:(opt = none) <;> try grind
     subst c; simp; clear mNat
     sorry

theorem inv4b1Proof (s: System a l p) (i: Fin a) (v: Value) (id: PropId)  :
systemIsValid s
-> inv4b1 s i v id:= by
intros sIsValid
have ⟨ s0, s0Inits, s0Steps ⟩ := sIsValid
induction s0Steps  with
| refl =>
  simp [systemInits, networkInits] at s0Inits
  simp [inv4b1, s0Inits] at ⊢
| trans s2 s3 s0Steps s2Step IH=>
  simp [systemIsValid, ] at (IH)
  have IHApp := IH s0; simp [s0Inits, s0Steps] at IHApp
  have s2Valid:(systemIsValid s2) := by (simp [systemIsValid]; grind)
  have p1 := inv41Proof s2 v i id s2Valid
  sorry








-- INV4b
def inv4b (s: System a l p) (v : Value) (id: PropId) :=
(∃ set, count set > a / 2 ∧ (∀ (i: Fin a), contains  set i -> Message.Learn (i, v, id) ∈ s.network.messages))
-> ∀ id' v', Message.Accept (id', v') ∈ s.network.messages
->  id' >= id
->  v = v'


theorem inv4bProof (s: System a l p) (v: Value) (id: PropId)  :
systemIsValid s
-> inv4b s v id:= by
intros sIsValid setRule id2 v2 mAccs idBound
rcases setRule with ⟨ set1, setCount1, setContains1 ⟩ 
have ⟨ set2, setCount2, setContains2R1, setContains2R2 ⟩  := inv4cProof s v2 id2 sIsValid mAccs
have ⟨ i, iContained1, iContained2 ⟩ := setMaxContainsBoth set1 set2 setCount1 setCount2
by_cases (id2 = id)
. rename_i eq; subst eq
  have l1 := setContains1 i iContained1
  have ⟨ p, l2 ⟩  := setContains2R1 i iContained2
  have i3 := inv3Proof s i v id2 sIsValid l1
  rw [inva1Proof s v2 v id2 sIsValid mAccs i3]
. sorry

import Distributed.base_structures
import Distributed.Paxos.paxos_model
import Distributed.Paxos.learner_helpers
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Cases

open Model
open PaxosModel
namespace PaxosProof



def inv4c4 (s: System a l p) (i: Fin p) (j: Fin a) :=
(s.proposers i).propRec j = true
-> (Message.Promise (s.proposers i).propId j none ∈ s.network.messages ∨ ∃ v, (s.proposers i).propVal = some v)


--INV4c1
def inv4c1 (s: System a l p) (i: Fin p) :=
(s.proposers i).propVal = none
-> ∀ j, contains (s.proposers i).propRec j = true
-> Message.Promise (s.proposers i).propId j none ∈ s.network.messages


theorem inv4c1Proof_ind (s1 s2: System a l p) (i: Fin p):
step s1 s2
-> inv4c1 s1 i
-> inv4c1 s2 i := by
simp [inv4c1]; intros step IH sPropNone j jContained
cases step <;> rename_i stepRule <;> cases stepRule <;> repeat (rename_i stepRule; rcases stepRule) <;> (try simp [updateMap] at * <;> split) <;> (try grind)
. unfold contains emptySet at jContained; grind
. simp at *; rename_i s; split at s <;> try grind
  subst_vars; simp at *;
  simp [insertElem, contains, updateMap] at jContained IH
  cases jContained <;> try grind


theorem inv4c1Proof (s: System a l p) (i: Fin p):
systemIsValid s
-> inv4c1 s i:= by
intros sIsValid 
rcases sIsValid with ⟨ s0, s0Inits, s0Steps ⟩
induction s0Steps  with
| refl =>
  simp [systemInits, proposerInits, networkInits] at s0Inits
  simp [inv4c1, s0Inits, ] at ⊢
  unfold emptySet contains;grind
| trans s2 s3 s0Steps s2Step IH=>
  exact (inv4c1Proof_ind s2 s3 i s2Step  IH)




--INV4c2
def inv4c2 (s: System a l p) (i: Fin p) (v: Value):=
(s.proposers i).propVal = v
-> (∃ j, contains (s.proposers i).propRec j = true
∧ Message.Promise (s.proposers i).propId j (some (v, (s.proposers i).accPropId )) ∈ s.network.messages)
∧ (∀ j, contains (s.proposers i).propRec j = true
-> (∃ v' id', (Message.Promise (s.proposers i).propId j (some (v', id')) ∈ s.network.messages ∧   id' <= (s.proposers i).accPropId)) ∨ Message.Promise (s.proposers i).propId j none ∈ s.network.messages)


theorem inv4c2Proof_ind (s1 s2: System a l p) (i: Fin p) (v: Value):
step s1 s2
-> inv4c2 s1 i v
-> (∀ j v id, inv43 s1 j v id)
-> (∀ j, inv4c4 s1 i j)
-> inv4c2 s2 i v := by
simp [inv4c2]; intros step IH i43 i4c4 sPropNone 
cases step <;> rename_i stepRule <;> cases stepRule <;> repeat (rename_i stepRule; rcases stepRule) <;> (try simp [updateMap] at * <;> split) <;> (try grind) <;> subst_vars
. rename_i j k prop opt v pid2 mInN  idBound splitX
  simp at *; split at splitX
  . subst splitX; simp [contains, insertElem, updateMap] at *
    constructor <;> try grind
  . rcases splitX with ⟨ eq1, eq2 ⟩; subst eq1 eq2; simp [contains, insertElem, updateMap] at *
    constructor <;> try grind
    subst sPropNone; intros h eq
    cases eq
    rename_i k; subst k; left; exists v, pid2; constructor <;> try grind
    simp [PropId]; rename_i acc
    sorry
. simp at *; subst_vars; rename_i v net k retBound
  split at retBound; try grind
  . clear IH; rw [retBound]; simp
. sorry


theorem inv4c2Proof (s: System a l p) (i: Fin p) (v: Value):
systemIsValid s
-> inv4c2 s i v:= by
intros sIsValid 
rcases sIsValid with ⟨ s0, s0Inits, s0Steps ⟩
induction s0Steps  with
| refl =>
  simp [systemInits, proposerInits, networkInits] at s0Inits
  simp [inv4c2, s0Inits, ] at ⊢
| trans s2 s3 s0Steps s2Step IH=>
  sorry

--INV4c3
def inv4c3 (s: System a l p) (j: Fin p) :=
(s.proposers j).accPropId ≤ (s.proposers j).propId


theorem inv4c3Proof_ind (s1 s2: System a l p) (i: Fin p):
step s1 s2
-> inv4c3 s1 i 
-> inv4c3 s2 i := by
simp [inv4c3]; intros step IH 
cases step <;> rename_i stepRule <;> cases stepRule <;> repeat (rename_i stepRule; rcases stepRule) <;> (try simp [updateMap] at * <;> split) <;> (try grind)
. simp [uniqueId]; exact Nat.zero_le _

  
theorem inv4c3Proof (s: System a l p) (i: Fin p):
systemIsValid s
-> inv4c3 s i:= by
intros sIsValid 
rcases sIsValid with ⟨ s0, s0Inits, s0Steps ⟩
induction s0Steps  with
| refl =>
  simp [systemInits, proposerInits, networkInits] at s0Inits
  simp [inv4c3, s0Inits, ] at ⊢;
  grind
| trans s2 s3 s0Steps s2Step IH=>
  exact (inv4c3Proof_ind s2 s3 i s2Step  IH)



-- INV4c: The message implies there is a set of elements in both places
def inv4c (s: System a l p) (v : Value) (id: PropId) :=
Message.Accept (id, v) ∈ s.network.messages
 -> ∃ (set: Set a), count set > a / 2
∧ (∀ i, contains set i -> ∃ p, Message.Promise id i p ∈ s.network.messages) 
∧ ((∀ i, contains set i -> Message.Promise id i none ∈ s.network.messages)
∨ (∃ idmax, idmax <= id  ∧ ((∃ i, contains set i ∧ Message.Promise  id i (some (v, idmax)) ∈ s.network.messages)
∧ (∀ i, contains set i  -> ∃ v' id', Message.Promise id i (some (v', id')) ∈ s.network.messages -> id' <= idmax))))

theorem inv4cProof_ind (s1 s2: System a l p) (v: Value) (id: PropId):
step s1 s2
-> inv4c s1 v id
-> (∀ i , inv4c1 s1 i )
-> (∀ i v, inv4c2 s1 i v)
-> (∀ i, inv4c3 s1 i)
-> (∀ i v id, inv43 s1 i v id)
-> inv4c s2 v id := by
simp [inv4c]; intros step IH i4c1 i4c2 i4c3 i43 accInN
cases step <;> rename_i stepRule <;> cases stepRule <;> repeat (rename_i stepRule; rcases stepRule) <;> (try (rename_i mNat; rw [mNat] at accInN ⊢)) <;> (try (simp at accInN ⊢; exact (IH accInN))) <;> try grind
. simp at accInN mNat; subst_vars; rename_i mNat
  rw [mNat] at accInN ⊢; simp at accInN ⊢ ; exact (IH accInN)
. simp at *; clear i4c1 i4c2 i4c3 i43
  have ⟨ set, setCount, setContains ⟩ := IH accInN
  exists set; simp [setCount]
  constructor; have c := setContains.left; grind
  cases setContains.right
  . left; grind
  . right; rename_i c; rcases c with ⟨ idMax, idMaxBound, rest ⟩   
    exists idMax; simp [idMaxBound];
    constructor <;> try grind
    sorry
. sorry
. rename_i prop v2 net j propRecCount pNat splitN; simp at accInN ⊢ 
  split at splitN <;> (try rw [splitN] at accInN ⊢) <;> (try rw [splitN.left] at accInN ⊢) <;> simp at accInN ⊢ <;> cases accInN <;> rename_i accInN <;> (try (exact IH accInN)) <;> exists (s1.proposers j).propRec <;> simp [propRecCount] <;> rename_i eq <;> simp at eq <;> rcases accInN with ⟨ eq1, eq2 ⟩ 
  . have dd := i4c1 j eq
    constructor
    . intros i iContained; exists none; rw [eq1]; exact (dd i iContained)
    . left; intros i iContained; rw [eq1]; exact (dd  i iContained)
  .sorry
    
    
    

theorem inv4cProof (s: System a l p) (v: Value) (id: PropId)  :
systemIsValid s
-> inv4c s v id:= by
intros sIsValid 
rcases sIsValid with ⟨ s0, s0Inits, s0Steps ⟩
induction s0Steps  with
| refl =>
  simp [systemInits, networkInits] at s0Inits
  simp [inv4c, s0Inits] at ⊢ 
| trans s2 s3 s0Steps s2Step IH=>
  sorry

import Distributed.base_structures
import Distributed.Paxos.paxos_model
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Cases 

open Model
open PaxosModel
namespace PaxosProof

def inv43 (s1: System a l p) (i: Fin a) (v: Value) (id: PropId):=
(s1.acceptors i).accepted = some (v, id)
-> (s1.acceptors i).maxPrepareId >= id


theorem inv43Proof_ind (s1 s2: System a l p) (i: Fin a)  (v: Value) (id: PropId) :
step s1 s2
-> inv43 s1 i v id
-> (∀ i, (s1.acceptors i).id = i)
-> inv43 s2 i v id := by
simp [inv43]; intros step IH kIsTrue learnInN
cases step <;> rename_i stepRule <;> cases stepRule <;> (try (rename_i stepRule; simp at stepRule; grind)) <;> (try (simp [updateMap] at *; split <;> try grind  ))
. rename_i j pid mess acc net stepRule eq; subst eq
  split at learnInN <;> try grind
  rcases stepRule with ⟨ messRules, accNat, netNat⟩; subst accNat 
  simp at ⊢ learnInN; have b1 := IH learnInN; have b2 := messRules.right.right
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt b1 b2)
. rename_i stepRule eq; split at learnInN <;> try grind
  rcases stepRule with ⟨ messAcc, b2, mInN, accNat⟩; subst eq; subst accNat
  simp at ⊢ learnInN; simp [learnInN, PropId]


theorem inv43Proof (s: System a l p) (v: Value) (i: Fin a) (id: PropId)  :
systemIsValid s
-> inv43 s i v id:= by
intros sIsValid
have ⟨ s0, s0Inits, s0Steps ⟩ := sIsValid
induction s0Steps  with
| refl =>
  simp [systemInits, acceptorInits] at s0Inits
  simp [inv43, s0Inits] at ⊢
| trans s2 s3 s0Steps s2Step IH=>
  simp [systemIsValid, ] at (IH)
  have IHApp := IH s0; simp [s0Inits, s0Steps] at IHApp
  have s2Valid:(systemIsValid s2) := by (simp [systemIsValid]; grind)
  --have IH2 := inv43Proof s2 v i id s2Valid
  exact (inv43Proof_ind s2 s3 i v id s2Step IHApp (idIsK s2 s2Valid))


def inv42 (s1: System a l p) (i: Fin a) (v: Value) (id: PropId):=
Message.Learn (i, v, id) ∈ s1.network.messages
-> (s1.acceptors i).maxPrepareId >= id



theorem inv42Proof_ind (s1 s2: System a l p) (i: Fin a)  (v: Value) (id: PropId) :
step s1 s2
-> inv42 s1 i v id
-> (∀ i, (s1.acceptors i).id = i)
-> inv43 s1 i v id
-> inv42 s2 i v id := by
simp [inv42]; intros step IH kIsTrue i43  learnInN
cases step <;> rename_i stepRule <;> cases stepRule <;> (try (rename_i stepRule; simp at stepRule; grind)) <;> (try (simp [updateMap] at *; split <;> try grind  ))
. rename_i j pid mess acc net  stepRule eq;
  rcases stepRule with ⟨ mRules, accNat, natRules ⟩ 
  subst_vars; simp; rw [natRules] at learnInN; simp at learnInN
  have IHApp := IH learnInN
  exact Nat.le_of_lt (Nat.lt_of_le_of_lt  IHApp mRules.right.right)
. have IHApp := IH learnInN; rename_i stepRule eq
  rcases stepRule with ⟨ mNat, idBound, mInN, a2Nat ⟩; subst a2Nat ; simp; subst eq
  exact (Nat.le_trans  IHApp idBound)
. rename_i j net v' pid stepRule
  rcases stepRule with ⟨ accIsSome , netNat ⟩ ; rw [netNat] at learnInN
  simp at learnInN; cases learnInN <;> try grind
  rename_i eq; rcases eq with ⟨ eq1, eq2, eq3 ⟩;
  subst_vars; rw [kIsTrue j] at *
  simp at *; have bound :=  i43 accIsSome
  simp [bound]

theorem inv42Proof (s: System a l p) (v: Value) (i: Fin a) (id: PropId)  :
systemIsValid s
-> inv42 s i v id:= by
intros sIsValid
have ⟨ s0, s0Inits, s0Steps ⟩ := sIsValid
induction s0Steps  with
| refl =>
  simp [systemInits, networkInits] at s0Inits
  simp [inv42, s0Inits] at ⊢
| trans s2 s3 s0Steps s2Step IH=>
  simp [systemIsValid, ] at (IH)
  have IHApp := IH s0; simp [s0Inits, s0Steps] at IHApp
  have s2Valid:(systemIsValid s2) := by (simp [systemIsValid]; grind)
  have IH2 := inv43Proof s2 v i id s2Valid
  exact (inv42Proof_ind s2 s3 i v id s2Step IHApp (idIsK s2 s2Valid) IH2)


-- INV41
def inv41 (s1: System a l p) (i: Fin a) (v: Value) (id: PropId):=
Message.Learn (i, v, id) ∈ s1.network.messages
-> ∃ v' id', id' >= id ∧ (s1.acceptors i).accepted = some (v', id')

theorem inv41Proof_ind (s1 s2: System a l p) (i: Fin a)  (v: Value) (id: PropId) :
step s1 s2
-> inv41 s1 i v id
-> (∀ i, (s1.acceptors i).id = i)
-> inv42 s1 i v id
-> inv41 s2 i v id := by
simp [inv41]; intros step IH iBound i42 learnInN
cases step <;> rename_i stepRule <;> cases stepRule <;> try (rename_i stepRule; simp at stepRule; grind)
. rename_i j pid mess acc net stepRule
  simp [updateMap] at *
  split <;> try grind  
. rename_i pid j v' acc mess stepRule
  simp [updateMap] at *
  split <;> try grind
  rcases stepRule with ⟨ mNat, mIdBound, mInN, accNat ⟩; subst accNat
  simp;
  have dd := i42 learnInN; rename_i eq; subst eq
  exact (Nat.le_trans dd mIdBound)
. rename_i j net v' pid stepRule
  rcases stepRule with ⟨ sAcc, nNat ⟩; simp at learnInN;rw [nNat] at learnInN; simp at ⊢ learnInN
  cases learnInN <;> try grind
  rename_i eqs; rcases eqs with ⟨ iId, vEq, idEq ⟩; subst_vars
  exists v'; exists pid; simp [PropId, iBound]; exact sAcc


theorem inv41Proof (s: System a l p) (v: Value) (i: Fin a) (id: PropId)  :
systemIsValid s
-> inv41 s i v id:= by
intros sIsValid
have ⟨ s0, s0Inits, s0Steps ⟩ := sIsValid
induction s0Steps  with
| refl =>
  simp [systemInits, networkInits] at s0Inits
  simp [inv41, s0Inits] at ⊢
| trans s2 s3 s0Steps s2Step IH=>
  simp [systemIsValid, ] at (IH)
  have IHApp := IH s0; simp [s0Inits, s0Steps] at IHApp
  have s2Valid:(systemIsValid s2) := by (simp [systemIsValid]; grind)
  have IH2 := inv42Proof s2 v i id s2Valid
  exact (inv41Proof_ind s2 s3 i v id s2Step IHApp (idIsK s2 s2Valid) IH2)

def inv31 (s1: System a l p) (i: Fin a) (v: Value) (id: PropId):=
(s1.acceptors i).accepted = some (v, id)
->  Message.Accept (id, v) ∈ s1.network.messages

theorem inv31Proof_ind (s1 s2: System a l p) (i: Fin a) (v: Value) (id: PropId) :
step s1 s2
-> inv31 s1 i v id
-> inv31 s2 i v id := by
simp [inv31]; intros step  IH accIsSome
cases step <;> rename_i stepRule <;> cases stepRule <;> try (rename_i stepRule; simp at stepRule; grind)
. rename_i j pid m acc n stepRule; simp [updateMap] at *
  split at accIsSome <;> try grind
. rename_i pid j v' acc m stepRule; simp [updateMap] at *
  split at accIsSome <;> try grind


theorem inv31Proof (s: System a l p) (i: Fin a) (v: Value) (id: PropId) :
systemIsValid s
-> inv31 s i v id := by
intros sIsValid 
rcases sIsValid with ⟨ s0, s0Inits, s0Steps ⟩
induction s0Steps  with
| refl =>
  simp [systemInits, acceptorInits] at s0Inits
  simp [inv31, s0Inits] at ⊢ 
| trans s2 s3 s0Steps s2Step IH=>
  exact (inv31Proof_ind s2 s3 i v id s2Step IH)



def inv3 (s1: System a l p) (i: Fin a) (v: Value) (id: PropId):=
Message.Learn (i, v, id) ∈ s1.network.messages
->  Message.Accept (id, v) ∈ s1.network.messages
theorem inv3Proof_ind (s1 s2: System a l p) (i: Fin a) (v: Value) (id:PropId) :
step s1 s2
-> inv3 s1 i v id
-> (∀ i, (s1.acceptors i).id = i)
-> inv31 s1 i v id
-> inv3 s2 i v id := by
simp [inv3, inv31]; intros step  IH accIsK IH2 sIsSome
cases step <;> rename_i stepRule <;> cases stepRule <;> try (rename_i stepRule; simp at stepRule; grind)




theorem inv3Proof (s: System a l p) (i: Fin a) (v: Value) (id: PropId) :
systemIsValid s
-> inv3 s i v id := by
intros sIsValid
have ⟨ s0, s0Inits, s0Steps ⟩ := sIsValid
induction s0Steps  with
| refl =>
  simp [systemInits, networkInits] at s0Inits
  simp [inv3, s0Inits] at ⊢ 
| trans s2 s3 s0Steps s2Step IH=>
  simp [systemIsValid, ] at (IH)
  have IHApp := IH s0; simp [s0Inits, s0Steps] at IHApp
  have s2Valid:(systemIsValid s2) := by (simp [systemIsValid]; grind)
  have IH2 := inv31Proof s2 i v id s2Valid
  exact (inv3Proof_ind s2 s3 i v id s2Step IHApp (idIsK s2 s2Valid) IH2)


def inv5 (s: System a l p) (i: Fin p)(id: PropId) (v: Value):=
Message.Accept (id, v) ∈ s.network.messages
-> (s.proposers i).propVal = some v
-> id <= (s.proposers i).propId

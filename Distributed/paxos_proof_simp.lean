import Distributed.base_structures
import Distributed.Paxos.paxos_model
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Cases 

open Model
open PaxosModel
namespace PaxosProof
/-
theorem idIsK (s1: System a l p):
systemIsValid s1
-> ∀ k, (s1.acceptors k).id = k := by
intros svalid; rcases  svalid with ⟨ s0, s0Inits, s0Steps ⟩
induction s0Steps
. simp [systemInits, acceptorInits] at s0Inits; simp [s0Inits]
. rename_i s2 s3 steps step IH;
  cases step <;> rename_i stepRule <;> cases stepRule <;> try (rename_i stepRule; simp at stepRule; grind)
  intros k; simp [updateMap] at *; split <;> try grind
  intros k; simp [updateMap] at *; split <;> try grind
  -/
def acc_invariant (s1 : System a l p) (v : Value) (id: PropId):=
  ∃ (s : Set a), count s > a / 2 ∧
    (∀ i, contains s i →
      ∃ id', id' >= id ∧ (s1.acceptors i).accepted = some (v, id'))

def mess_invariant (s1 : System a l p) (v : Value) (id: PropId) :=
  ∃ (s : Set a), count s > a / 2 ∧
    (∀ i, contains s i →
      Message.Learn (i, v, id) ∈ s1.network.messages)

def learn_invariant (s1 : System a l p) (v : Value) (j: Fin l) (id: PropId):=
   ∃ (s : Set a), count s > a / 2 ∧
    ∀ i, contains s i →
      (s1.learners j).decMap i = some (v, id)

def inv2 (s1: System a l p) (j: Fin l) (i: Fin a) (v: Value) (id: PropId):=
(s1.learners j).decMap i = some (v, id)
->  Message.Learn (i, v, id) ∈ s1.network.messages


def inv3 (s1: System a l p) (i: Fin a) (v: Value) (id: PropId):=
Message.Learn (i, v, id) ∈ s1.network.messages
->  Message.Accept (id, v) ∈ s1.network.messages


def inv31 (s1: System a l p) (i: Fin a) (v: Value) (id: PropId):=
(s1.acceptors i).accepted = some (v, id)
->  Message.Accept (id, v) ∈ s1.network.messages


def inv4b1 (s: System a l p) (i: Fin a) (v: Value) (id: PropId) :=
Message.Learn (i,  v, id)  ∈ s.network.messages
-> ∀  id' p, Message.Promise id' i p ∈ s.network.messages
-> id' >= id
-> p ≠ none



def inv4b3 (s: System a l p) (i: Fin a) (id: PropId) (p: Option (Value × PropId)):=
Message.Promise id i p ∈ s.network.messages
-> id <= (s.acceptors i).maxPrepareId


def inv4b2 (s: System a l p) (i: Fin a) (id: PropId) (p: Option (Value × PropId)):=
Message.Promise id i p ∈ s.network.messages
-> ∀ v' id', (s.acceptors i).accepted = some (v', id')
-> id' > id ∨ p = (s.acceptors i).accepted


def inv4b (s: System a l p) (v : Value) (id: PropId) :=
(∃ set, count set > a / 2 ∧ (∀ (i: Fin a), contains  set i -> Message.Learn (i, v, id) ∈ s.network.messages))
-> ∀ id' v', Message.Accept (id', v') ∈ s.network.messages
->  id' >= id
->  v = v'


def inv4c (s: System a l p) (v : Value) (id: PropId) :=
Message.Accept (id, v) ∈ s.network.messages
 -> ∃ (set: Set a), count set > a / 2
∧ (∀ i, contains set i -> ∃ p, Message.Promise id i p ∈ s.network.messages) 
∧ ((∀ i, contains set i -> Message.Promise id i none ∈ s.network.messages)
∨ ((∃ i, contains set i ∧ Message.Promise  id i (some (v, id)) ∈ s.network.messages)
∧ (∀ i, contains set i  -> ∀ v' id', Message.Promise id i (some (v', id')) ∈ s.network.messages -> id' <= id)))


def inv42 (s1: System a l p) (i: Fin a) (v: Value) (id: PropId):=
Message.Learn (i, v, id) ∈ s1.network.messages
-> (s1.acceptors i).maxPrepareId >= id


def inv43 (s1: System a l p) (i: Fin a) (v: Value) (id: PropId):=
(s1.acceptors i).accepted = some (v, id)
-> (s1.acceptors i).maxPrepareId >= id

def inv4a1 (s: System a l p) (i: Fin a) (v : Value) (id: PropId) :=
(s.acceptors i).accepted = some (v, id)
-> Message.Accept (id, v) ∈ s.network.messages

def inv4a (s: System a l p) (v : Value) (id: PropId) :=
(∃ set, count set > a / 2 ∧ (∀ (i: Fin a), contains  set i -> Message.Learn (i, v, id) ∈ s.network.messages))
-> ∀ id' i v', (s.acceptors i).accepted = some (v', id')
->  id' >= id
->  v = v'


def inv41 (s1: System a l p) (i: Fin a) (v: Value) (id: PropId):=
Message.Learn (i, v, id) ∈ s1.network.messages
-> ∃ v' id', id' >= id ∧ (s1.acceptors i).accepted = some (v', id')

def inv4 (s: System a l p) (v: Value) (id: PropId) :=
(∃ set, count set > a / 2 ∧ (∀ (i: Fin a), contains  set i -> Message.Learn (i, v, id) ∈ s.network.messages))
-> ∃ id', id' >= id ∧ acc_invariant s v id'







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


theorem inv4b1Proof_ind (s1 s2: System a l p) (i: Fin a)  (v: Value) (id: PropId) :
step s1 s2
-> inv4b1 s1 i v id
-> inv41  s1 i v id
-> (∀ i, (s1.acceptors i).id = i)
-> (∀ p id, inv4b2 s1 i id p )
-> inv4b1 s2 i v id := by
   simp [inv4b1]; intros step IH i41 iEq i4b2 mLearn id2 prop  mProp id2Bound
   cases step <;> rename_i stepRule <;> cases stepRule <;> repeat (rename_i stepRule; rcases stepRule) <;> subst_vars  <;> try grind 
   . rename_i i pid m net netRules mNat
     simp at *; rw[mNat] at mLearn mProp; simp at mLearn mProp
     cases mProp <;> try grind
     have ⟨ v2, id2 , rest⟩  := i41 mLearn
     rename_i contra; rcases contra with ⟨ eq1, eq2, eq3 ⟩; rcases rest with ⟨ eq4, eq5 ⟩; subst_vars; rw [iEq i] at *
     rw [eq5]; simp
   . simp at *; grind
   . simp at *; rename_i mNat; rw [mNat] at mLearn mProp; simp at mLearn mProp; clear mNat
     cases mLearn <;> try grind
     clear IH; rename_i dd; rcases dd with ⟨ eq1, eq2, eq3 ⟩ 
     subst eq1 eq2 eq3; clear i41
     have contra := i4b2 prop id2 mProp v id;
     rename_i j net prop
     rw [iEq j] at contra
     cases (contra prop) <;> try grind
     rename_i cc; exfalso
     exact absurd id2Bound (Nat.not_le.mpr cc)
     


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


theorem inv4b2Proof_ind (s1 s2: System a l p) (i: Fin a) (id: PropId)  (p: Option (Value × PropId)):
step s1 s2
-> inv4b2 s1 i id p
-> inv4b2 s2 i id p := by
simp [inv4b2]; intros step  IH promInM v2 id2 accIsSome
cases step <;> rename_i stepRule <;> cases stepRule <;> try (rename_i stepRule; simp at stepRule; grind)
. rename_i j pid mess acc net stepRule
  simp at *; simp [updateMap] at *
  by_cases (j = i) <;> try grind
  rename_i neq; simp [neq] at ⊢ accIsSome
  sorry
. rename_i id3 j v3 acc mess stepRule
  rcases stepRule with ⟨ mAccs, idBound, mInN, accNat ⟩; subst_vars
  simp [updateMap] at *; split at accIsSome
  . rename_i s; subst s; simp at ⊢ accIsSome
    rcases accIsSome with ⟨ eq1, eq2 ⟩; subst eq1 eq2
    sorry
  . rename_i neq; simp [neq] at accIsSome ⊢
    exact (IH promInM v2 id2 accIsSome)
  
  


theorem inv4b2Proof (s: System a l p) (i: Fin a) (id: PropId)  (p: Option (Value × PropId)):
systemIsValid s
-> inv4b2 s i id p:= by
intros sIsValid 
rcases sIsValid with ⟨ s0, s0Inits, s0Steps ⟩
induction s0Steps  with
| refl =>
  simp [systemInits, networkInits] at s0Inits
  simp [inv4b2, s0Inits] at ⊢ 
| trans s2 s3 s0Steps s2Step IH=>
  exact (inv4b2Proof_ind s2 s3 i id p s2Step IH)




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
  have p2 :(∀ (p_1 : Option (Value × PropId)) (id : PropId), inv4b2 s2 i id p_1) := by intros opt id; exact (inv4b2Proof s2 i id opt s2Valid)
  exact (inv4b1Proof_ind s2 s3 i v id s2Step (IH s0 s0Inits s0Steps ) p1 (idIsK s2 s2Valid) p2)





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

theorem inv4cProof_ind (s1 s2: System a l p) (v: Value) (id: PropId):
step s1 s2
-> inv4c s1 v id
-> inv4c s2 v id := by
simp [inv4c]; intros step IH accInN
cases step <;> rename_i stepRule <;> cases stepRule <;> repeat (rename_i stepRule; rcases stepRule) <;> (try (rename_i mNat; rw [mNat] at accInN ⊢)) <;> try grind
. simp at accInN mNat; subst_vars; rename_i mNat
  rw [mNat] at accInN ⊢; simp at accInN ⊢ ; exact (IH accInN)
. simp at *; 
. sorry
. sorry
. sorry
. sorry
. sorry


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
  exact (inv4cProof_ind s2 s3 v id s2Step IH)

  

  
  




theorem inv4bProof (s: System a l p) (v: Value) (id: PropId)  :
systemIsValid s
-> inv4b s v id:= by
intros sIsValid setRule id2 v2 mAccs
rcases setRule with ⟨ set1, setCount1, setContains1 ⟩ 
have ⟨ set2, setCount2, setContains2R1, setContains2R2 ⟩  := inv4cProof s v2 id2 sIsValid mAccs
have ⟨ i, iContained1, iContained2 ⟩ := setMaxContainsBoth set1 set2 setCount1 setCount2
rcases setContains2R2 with setContains2R2 | setContains2R3
. have p1 := setContains2R2 i iContained2
  have p2 := setContains1 i iContained1
  intros id2Bound; exfalso
  have dd := inv4b1Proof s i v id sIsValid p2 id2 none p1 id2Bound (by simp)
  exact dd
. rcases setContains2R3 with ⟨ existsOneId, forAllId ⟩ 
  have p2 := setContains1 i iContained1
  have ⟨ prop , p3 ⟩ := setContains2R1 i iContained2
  have p4 := forAllId i iContained2
  intros idBound; cases prop 
  . have dd := inv4b1Proof s i v id sIsValid p2 id2 none p3 idBound;simp at dd
  . rename_i prop2; rcases prop2 with ⟨ v3, id3 ⟩;  
    
  
  


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




theorem inv4aProof (s: System a l p) (v: Value) (id: PropId)  :
systemIsValid s
-> inv4a s v id:= by
intros sIsValid set id1 i v' accIn idBound
have p2 := inv4a1Proof s i v' id1 sIsValid accIn
exact (inv4bProof s v id sIsValid set id1 v' p2 idBound)


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
  

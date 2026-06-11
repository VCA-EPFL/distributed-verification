import Distributed.base_structures
import Distributed.Paxos.paxos_model
import Distributed.Paxos.learner_helpers
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Cases


open Model
open PaxosModel
namespace PaxosProof





--INV4c1
def inv4c1 (s: System a l p) (i: Fin p) :=
(s.proposers i).propVal = none
-> (∀ j, contains (s.proposers i).propRec j = true
-> Message.Promise (s.proposers i).propId j none ∈ s.network.messages)
∧ (s.proposers i).accPropId = 0


theorem inv4c1Proof_ind (s1 s2: System a l p) (i: Fin p):
step s1 s2
-> inv4c1 s1 i
-> inv4c1 s2 i := by
simp [inv4c1]; intros step IH sPropNone 
cases step <;> rename_i stepRule <;> cases stepRule <;> repeat (rename_i stepRule; rcases stepRule) <;> (try simp [updateMap] at * <;> split) <;> (try grind)
. unfold contains emptySet at ⊢ ; simp
. simp at *; rename_i s; split at s <;> try grind
  subst_vars; simp at *;
  simp [insertElem, contains, updateMap] at ⊢ IH
  constructor
  . rename_i cas prom; cases cas <;> try grind
    rw [(IH sPropNone).right] at *
    exfalso; grind
  . exact (IH sPropNone).right

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
-> ((∃ j, contains (s.proposers i).propRec j = true
∧ Message.Promise (s.proposers i).propId j (some (v, (s.proposers i).accPropId )) ∈ s.network.messages)
∧ (∀ j, contains (s.proposers i).propRec j = true
-> (∃ v' id', (Message.Promise (s.proposers i).propId j (some (v', id')) ∈ s.network.messages ∧   id' <= (s.proposers i).accPropId)) ∨ Message.Promise (s.proposers i).propId j none ∈ s.network.messages)) ∨ (∀ j, contains (s.proposers i).propRec j = true -> Message.Promise (s.proposers i).propId j none ∈ s.network.messages)



--INV4C21
def inv4c21 (s1 : System a l p) (i: Fin p) :=
0 < ((s1.proposers i).accPropId)
-> ∃ v j, (s1.proposers i).propVal = some v
∧ (s1.proposers i).propRec j = true
∧ Message.Promise (s1.proposers i).propId j (some (v, (s1.proposers i).accPropId)) ∈ s1.network.messages


theorem inv4c21Proof_ind (s1 s2: System a l p) (i: Fin p):
step s1 s2
-> inv4c21 s1 i 
-> inv4c21 s2 i := by
simp [inv4c21]; intros step IH sPropTrue
cases step <;> rename_i stepRule <;> cases stepRule <;> repeat (rename_i stepRule; rcases stepRule) <;> (try simp [updateMap, PropId] at * <;> split) <;> subst_vars <;> (try simp [PropId] at *) <;> (try grind)  <;> (try exact (IH sPropTrue))
. rename_i prop opt v pid mInN idBound optSome splitX
  split at splitX <;> try grind
  . subst splitX; simp [insertElem, updateMap] at *
    rcases (IH sPropTrue) with ⟨ v1, sPropSome, x, sIsTrue, messInN⟩
    exists v1; simp [sPropSome]; exists x; simp [sIsTrue, messInN]
  . clear IH; subst splitX; simp [insertElem, updateMap] at *
    rename_i bAndOptIsNone; simp [bAndOptIsNone] at optSome
    rename_i accId
    subst optSome; simp at *; exists accId; constructor <;> try grind
. rename_i prop v net k propBound c kNeq
  rcases c with ⟨ pNat, splitX⟩
  split at splitX <;> (try rw [splitX]) <;> (try (rw [splitX.left])) <;> (simp [kNeq] at sPropTrue ⊢ ; exact (IH sPropTrue))
  


theorem inv4c21Proof (s: System a l p) (i: Fin p):
systemIsValid s
-> inv4c21 s i := by
intros sIsValid
have ⟨ s0, s0Inits, s0Steps ⟩ := sIsValid
induction s0Steps  with
| refl =>
  simp [systemInits, proposerInits, networkInits] at s0Inits
  simp [inv4c21, s0Inits, PropId] at ⊢; 
| trans s2 s3 s0Steps s2Step IH=>
  simp [systemIsValid, ] at (IH)
  have IHApp := IH s0; simp [s0Inits, s0Steps] at IHApp
  have s2Valid:(systemIsValid s2) := by (simp [systemIsValid]; grind)
  --have p1:(inv4c1 s2 i):= by {exact (inv4c1Proof s2 i s2Valid)}
  --have p4:(∀ i v id, inv43 s2 i v id) := by {intros i v id; exact (inv43Proof s2 v i id  s2Valid)}
  exact (inv4c21Proof_ind s2 s3 i s2Step IHApp )





theorem inv4c2Proof_ind (s1 s2: System a l p) (i: Fin p) (v: Value):
step s1 s2
-> (∀ i v, inv4c2 s1 i v)
-> (∀ j v id, inv43 s1 j v id)
-> inv4c21 s1 i
-> inv4c1 s1 i
-> inv4c2 s2 i v := by
simp [inv4c2]; intros step IH i43 i4c21 i4c1 sPropNone 
cases step <;> rename_i stepRule <;> cases stepRule <;> repeat (rename_i stepRule; rcases stepRule) <;> (try simp [updateMap] at * <;> split) <;> (try grind) <;> subst_vars <;> by_cases ((s1.proposers i).propVal = some v) <;> (try grind)
. rename_i i accId p2 mess opt v2 pid stepRule;
  simp [updateMap] at *
  rcases stepRule with ⟨mIsProp, mInN, pidBound, optIsSome, splitX ⟩
  split at splitX <;> split at sPropNone <;> subst_vars <;> simp [updateMap, insertElem, contains] at * <;> by_cases (opt = none) <;> (try grind) 
  . left; constructor <;> try grind
    . have IccBound: (0 < ((s1.proposers i).accPropId)) := by {
      by_cases ((s1.proposers i).accPropId = 0) <;> try grind
      . rename_i dEq someNone zeroEq; simp [someNone] at optIsSome dEq
        rw [zeroEq] at dEq; exfalso; simp at dEq
      . rename_i a; exact Nat.pos_of_ne_zero a
      }
      have ⟨ v, j, r1, r2, r3 ⟩  := i4c21 IccBound
      grind
    . intros j jContained; cases jContained <;> try grind
      . rename_i eq1 eq2; have eq3 := optIsSome eq1
        subst eq3 eq2; left; exists v2, pid
        constructor <;> try grind
        . rename_i contra; simp at contra; exact Nat.le_of_lt contra
  . left; constructor <;> try grind
    . rename_i notNone; have someV := optIsSome notNone; subst someV
      intros j jContained; cases jContained <;> try grind
      . left; rename_i eq1; subst eq1; exists v2, pid; constructor <;> try grind
        . simp [PropId]
      . rename_i jContained;
        by_cases c: (∃ v, (s1.proposers i).propVal = some v) <;> try grind
        . have ⟨ v', someExists ⟩  := c
          rcases (IH i v' someExists) with h1 | h2 <;> try grind
          . cases (h1.right j jContained) <;> try grind
            . rename_i eq; rcases eq with ⟨ v2, id2, rest ⟩
              left; exists v2, id2; constructor <;> try grind
              rename_i d; exact Nat.le_trans rest.right d.right
        . have sIsNone:((s1.proposers i).propVal = none) := by cases h : (s1.proposers i).propVal <;> try grind
          clear c; right; exact (i4c1 sIsNone).left j jContained
. rename_i prop v2 net j stepRule; simp [updateMap, contains] at *
  rcases stepRule with ⟨ r1, r2, r3 ⟩ 
  by_cases (j = i) <;> rename_i eqs <;> simp [eqs] at ⊢ sPropNone r3
  . subst eqs r2; simp at sPropNone; subst sPropNone
    split at r3 
    . rw [r3]; simp at *; rename_i isNone
      have IHApp := i4c1 isNone; right; exact IHApp.left
    . rw [r3.left]; simp at *; grind
  . have IHApp := IH i v sPropNone; split at r3 
    . rw [r3]; simp; exact IHApp
    . rw [r3.left]; simp; exact IHApp

theorem inv4c2Proof (s: System a l p) (i: Fin p) (v: Value):
systemIsValid s
-> inv4c2 s i v:= by
intros sIsValid
have ⟨ s0, s0Inits, s0Steps ⟩ := sIsValid
revert i v
induction s0Steps  with
| refl =>
  simp [systemInits, proposerInits, networkInits] at s0Inits
  simp [inv4c2, s0Inits] at ⊢
| trans s2 s3 s0Steps s2Step IH=>
  intros i v
  simp [systemIsValid, ] at (IH)
  have IHApp := IH s0; simp [s0Inits, s0Steps] at IHApp
  have s2Valid:(systemIsValid s2) := by (simp [systemIsValid]; grind)
  have p1:(∀ j v id, inv43 s2 j v id):= by {intros v j id; exact (inv43Proof s2 j v id s2Valid)}
  have p2: inv4c21 s2 i:= by {exact (inv4c21Proof s2 i s2Valid)}
  have p3: (inv4c1 s2 i):= by {exact (inv4c1Proof s2 i s2Valid)}
  exact (inv4c2Proof_ind s2 s3 i v s2Step IHApp p1 p2 p3)


  

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
∧ (∀ i, contains set i  -> (∃ v' id', Message.Promise id i (some (v', id')) ∈ s.network.messages ∧ id' <= idmax) ∨  Message.Promise id i none ∈ s.network.messages))))

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
    clear IH mNat setContains
    intros j jContained
    cases (rest.right j jContained)
    . left; rename_i d; rcases d with ⟨ v2, id2, mProp ⟩; exists v2, id2; grind
    . right; grind   
. simp at *; clear i4c1 i4c2 i4c3 i43
  have ⟨ set, setCount, setContains ⟩ := IH accInN
  exists set; simp [setCount]
  constructor; have c := setContains.left; grind
  cases setContains.right
  . left; grind
  . right; rename_i c; rcases c with ⟨ idMax, idMaxBound, rest ⟩   
    exists idMax; simp [idMaxBound];
    constructor <;> try grind
    clear IH mNat setContains
    intros j jContained
    cases (rest.right j jContained)
    . left; rename_i d; rcases d with ⟨ v2, id2, mProp ⟩; exists v2, id2; grind
    . right; grind   
. rename_i prop v2 net j propRecCount pNat splitN; simp at accInN ⊢ 
  split at splitN <;> (try rw [splitN] at accInN ⊢) <;> (try rw [splitN.left] at accInN ⊢) <;> simp at accInN ⊢ <;> cases accInN <;> rename_i accInN <;> (try (exact IH accInN)) <;> exists (s1.proposers j).propRec <;> simp [propRecCount] <;> rename_i eq <;> simp at eq <;> rcases accInN with ⟨ eq1, eq2 ⟩ 
  . have dd := i4c1 j eq
    constructor
    . intros i iContained; exists none; rw [eq1]; exact (dd.left i iContained)
    . left; intros i iContained; rw [eq1]; exact (dd.left  i iContained)
  . clear IH; subst pNat
    have ⟨ v', rest ⟩:(∃ v , (s1.proposers j).propVal = some v) := by grind
    have ip4 := i4c2 j v' rest
    cases ip4 <;> try grind
    rename_i dd; constructor <;> try grind
    right; subst eq1 eq2; exists (s1.proposers j).accPropId
    constructor <;> try grind
    . exact ( i4c3 j)
      
                  
      
    
    
    
    
    

theorem inv4cProof (s: System a l p) (v: Value) (id: PropId)  :
systemIsValid s
-> inv4c s v id:= by
intros sIsValid
have ⟨ s0, s0Inits, s0Steps ⟩ := sIsValid
induction s0Steps  with
| refl =>
  simp [systemInits, networkInits] at s0Inits
  simp [inv4c, s0Inits] at ⊢
| trans s2 s3 s0Steps s2Step IH=>
  simp [systemIsValid, ] at (IH)
  have IHApp := IH s0; simp [s0Inits, s0Steps] at IHApp
  have s2Valid:(systemIsValid s2) := by (simp [systemIsValid]; grind)
  have p1:(∀ i , inv4c1 s2 i ):= by {intros i; exact (inv4c1Proof s2 i s2Valid)}
  have p2:(∀ i v, inv4c2 s2 i v) := by {intros i v; exact (inv4c2Proof s2 i v s2Valid)}
  have p3:(∀ i, inv4c3 s2 i):= by {intros i; exact (inv4c3Proof s2 i s2Valid)}
  have p4:(∀ i v id, inv43 s2 i v id) := by {intros i v id; exact (inv43Proof s2 v i id  s2Valid)}
  exact (inv4cProof_ind s2 s3 v id s2Step IHApp p1 p2 p3 p4)


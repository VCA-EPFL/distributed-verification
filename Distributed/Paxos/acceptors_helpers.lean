import Distributed.base_structures
import Distributed.Paxos.paxos_model
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Cases 

open Model
open PaxosModel
namespace PaxosProof

def inva4 (s: System a l p)  (j c: Fin p) :=
(s.proposers j).propId = (s.proposers c).propId
-> j = c


def inva3 (s: System a l p) (j: Fin p) :=
count (s.proposers j).propRec ≤ a / 2
-> ∀ v, Message.Accept ((s.proposers j).propId, v) ∉ s.network.messages



--INVA2
def inva2 (s: System a l p) (v: Value) (j: Fin p) :=
Message.Accept ((s.proposers j).propId, v) ∈ s.network.messages
-> a / 2 < count (s.proposers j).propRec
->  (s.proposers j).propVal = some v



theorem inva2Proof_ind (s1 s2: System a l p) (v: Value) (id: PropId) (j: Fin p) :
step s1 s2
-> inva2 s1 v j
-> (∀ j, inva3 s1 j)
-> (∀ i j, inva4 s1 i j)
-> inva2 s2 v j := by
simp [inva2]; intros step IH ia3 ia4 MAccInN countProp
cases step <;> rename_i stepRule <;> cases stepRule <;> (try (rename_i stepRule; simp at stepRule; grind))  <;> repeat (rename_i stepRule; rcases stepRule) <;> subst_vars
. simp [updateMap] at *; split <;> try grind
  rename_i eq; subst eq;simp at countProp
  rw [emptySetEqZero] at countProp
  omega
. rename_i i accId prop opt v1 pid  mInN idBound countBound noneImpX splitX 
  simp [updateMap] at * <;> split at MAccInN <;> split at splitX <;> subst splitX <;> rename_i a b <;> have contra := ia3 i countBound v <;> (try subst a) <;> (try simp [contra] at MAccInN) <;> try grind  
. rename_i a b c d e ;simp [updateMap] at *; split
  . split at e <;> try grind
  . rename_i neq; simp [neq] at *; clear neq;
    sorry
    
      
      
    
  
  



--INVA1
def inva1 (s: System a l p) (v1 v2: Value) (id: PropId):=
Message.Accept (id, v1) ∈ s.network.messages
-> Message.Accept (id, v2) ∈ s.network.messages
-> v1 = v2


theorem inva1Proof_ind (s1 s2: System a l p) (v1 v2: Value) (id: PropId) :
step s1 s2
-> inva1 s1 v1 v2 id
-> (∀ v j, inva2 s2 v j)
-> inva1 s2 v1 v2 id := by
simp [inva1]; intros step IH ia2 m1InN m2InN
cases step <;> rename_i stepRule <;> cases stepRule <;> try (rename_i stepRule; simp at stepRule; grind)
. simp at *; rename_i prop v net j stepRule;
  rcases stepRule with ⟨ bound,pNat, rest ⟩ ; subst pNat
  have c1 := ia2 v1 j ; have c2 := ia2 v2 j; simp [inva2, updateMap] at c1 c2; grind   


  
theorem inva1Proof (s: System a l p) (v1 v2: Value) (id: PropId) :
systemIsValid s
-> inva1 s v1 v2 id := by sorry

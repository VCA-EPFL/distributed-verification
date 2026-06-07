import Distributed.base_structures
import Distributed.paxos_model
import Mathlib.Tactic.ByContra

open Model
open PaxosModel
namespace PaxosProof

/--
def lemma1 (s: System a l p) (v: Value):
systemIsValid s
->  acceptorsAreEnoughOfValue s.acceptors v
-> ∀ j v1, (s.learners j).decide = some v1
-> v1 = v := by sorry
--/


-- Deinitions: definition of useful constructs used througth the proof
@[simp]
def learner_invariant (s1: System a l p) (learner: Learner a l) (n: Network) (v: Value) :=
(∃  (s: Set a), count s > a / 2 ∧  (∀ i, contains s i -> (learner.decMap i = v ∨ (@Message.Learn a (i, v) ∈  n.messages) ∨ (∃ id, (s1.acceptors i).accepted = some (v, id))))) 


def acceptorsAreEnoughOfValue (accs:  Map a (Acceptor a)) (v: Value) :=
(∃ (s1: Set a), count s1 > a / 2 ∧  (∀ (i : Fin a), contains s1 i = true ->  (∃ k, (accs i).accepted = some (v, k))))


-- SET SIZE: lemmas playing on the set size and equivalence of values at the end
def learnerAndAccImpSameVal (s: System a l p) (v1 v2: Value) (j: Fin l):
learner_invariant s (s.learners j) s.network v1
-> acceptorsAreEnoughOfValue s.acceptors v2
-> v1 = v2 := by
   simp [acceptorsAreEnoughOfValue]; intros set1 set1Count set1Contains set2 set2Count set2Contains
   have si:(∀ (i : Fin a),
      contains set2 i = true →
        (s.learners j).decMap i = some v2 ∨
          Message.Learn (i, v2) ∈ s.network.messages ∨ ∃ id, (s.acceptors i).accepted = some (v2, id)) := by {
        intros i set2Count
        have cc :=(set2Contains i set2Count)
        right; right; exact cc
        }
   have ⟨ i, conti1, conti2 ⟩  := setMaxContainsBoth set1 set2 set1Count set2Count
   have f1 := si i conti2
   have f2 := set1Contains i conti1
   
   
   simp [f1] at f2
   
   



def lemma31 (s: System a l p) (v1 v2: Value) (j: Fin l):
learner_invariant s (s.learners j) s.network v1
-> learner_invariant s (s.learners j) s.network v2
-> v1 = v2 := by
   intros acc1 acc2
   unfold learner_invariant at *; simp at *
   rcases acc1 with ⟨ set1, countSet1, set1Prop⟩
   rcases acc2 with ⟨ set2, countSet2, set2Prop⟩
   have finalC := setMaxContainsBoth set1 set2 countSet1 countSet2
   rcases finalC with ⟨ i, ⟨ set1Contains, set2Contains ⟩ ⟩
   have set2C := set2Prop i set2Contains ; have set1C := set1Prop i set1Contains; clear set2Prop set1Prop
   sorry
   

def lemma3 (s: System a l p) (v1 v2: Value):
systemIsValid s
-> acceptorsAreEnoughOfValue s.acceptors v1
-> acceptorsAreEnoughOfValue s.acceptors v2
-> v1 = v2 := by
   intros sIsValid acc1 acc2
   unfold acceptorsAreEnoughOfValue at *
   rcases acc1 with ⟨ set1, countSet1, set1Prop⟩
   rcases acc2 with ⟨ set2, countSet2, set2Prop⟩
   have finalC := setMaxContainsBoth set1 set2 countSet1 countSet2
   rcases finalC with ⟨ i, ⟨ set1Contains, set2Contains ⟩ ⟩
   have set2C := set2Prop i; have _ := (set2C set2Contains 0) 
   have set1C := set1Prop i ; have _ := (set1C set1Contains 0)
   grind

-- MAIN INVARIANT
def accept_inv (s1 s2: System a l p) (v: Value):
step s1 s2
-> (acceptorsAreEnoughOfValue s1.acceptors v)
-> (acceptorsAreEnoughOfValue s2.acceptors v) := by
   sorry


def lemma0 (s1 s2: System a l p) (v: Value):
step s1 s2
-> ¬ (acceptorsAreEnoughOfValue s2.acceptors v)
-> ¬ (acceptorsAreEnoughOfValue s1.acceptors v) := by
   intros s1Step notEnoughAcc
   have contra := accept_inv s1 s2 v s1Step
   grind

     

def lemma1 (s1 s2: System a l p) (v: Value):
step s1 s2
-> ¬ (acceptorsAreEnoughOfValue s1.acceptors v)
-> ∀ j, (s1.learners j).decide = none
-> (∀ v', ¬ (learner_invariant s1 (s1.learners j) s1.network v'))
-> (s2.learners j).decide = none ∧ (∀ v', ¬ (learner_invariant s2 (s2.learners j) s2.network v')):= by
   intros stepCase acceptorOfEnoughValu s1DecNone decNone learnInv
   cases stepCase with
   | failureStep stepRule =>
     cases stepRule with
     | lostmessage  m n1 stepRule =>
       constructor <;> try grind
       simp at *; intros v'' x xCounts
       sorry
   | workingStep stepRule =>
     cases stepRule with
     | receivelearner i l2 mess v' j stepRule =>
       rcases stepRule with ⟨messNat, messInN, learnIsNone, l2Nat ⟩
       constructor
       . simp [updateMap]; split <;> try grind
         sorry
       . subst_vars; simp at *
         intros v'' set1 countSet1
         have ⟨ x, xContains, xDecIsNone, messNotInN ⟩:= learnInv v'' set1 countSet1
         exists x; simp [xContains, messNotInN];
         simp [updateMap]; split <;> try grind
         sorry
     | choosefinalvalue l2 v' i stepRule =>
       simp at *
       rcases stepRule with ⟨s, countS, sNat, s1DecNone, l2Nat ⟩
       constructor <;> try grind
       . simp [updateMap]; split <;> try grind
         subst_vars; simp
         have cc := lemma31 s1 v' v i; simp at cc
         have ⟨x, xContains, xNat ⟩  := (learnInv v') s countS
         have res := sNat x xContains; simp [res] at xNat
       . intros v'' set1 countSet1
         have ⟨ x, xContains, xSome ⟩  := learnInv v'' set1 countSet1
         exists x; simp [updateMap]; split <;> try grind
         sorry
      | sendlearner => sorry
      | receiveacceptor id i j  v'' acc mess stepRule =>
        simp [acceptorsAreEnoughOfValue] at acceptorOfEnoughValu
        simp [decNone] at *
        rcases stepRule with ⟨ messIsAcc, accIsBound, accNat ⟩; subst accNat 
        intros v' set1 countSet1
        have ⟨ x, learnInv_⟩  := learnInv v' set1 countSet1; clear learnInv
        exists x; simp [learnInv_]; clear learnInv_
        have ⟨ x2, x2Contained, xAccepted ⟩  := acceptorOfEnoughValu set1 countSet1
        intros x1; simp [updateMap]; split
        . simp; intros eq; subst_vars
          
          grind
      | _ =>
        rename_i stepRule; simp at *
        rcases stepRule with ⟨mNat, accNat ⟩
        subst_vars
        constructor <;> try grind
        intros v'' x xCounts
        have ⟨set1, xTrue, xDecMapFails, xInMess, xNotSome ⟩ := learnInv v'' x xCounts
        grind

def lemma2 (s: System a l p) (v: Value):
systemIsValid s
->  ¬ (acceptorsAreEnoughOfValue s.acceptors v)
-> ∀ j, (s.learners j).decide = none ∧ (∀ v', ¬ (learner_invariant s (s.learners j) s.network v')):= by
   intros sIsValid notEnoughAcceptors j
   simp [systemIsValid] at sIsValid; rcases sIsValid with ⟨ s0, s0Inits, s0Steps⟩
   induction s0Steps with
   | refl =>
     unfold systemInits learnerInits networkInits acceptorInits at s0Inits; simp [s0Inits]
     intros v' x countX; 
     have contra := countSupImpContains (a/2) x; simp [s0Inits] at contra
     grind
   | trans s1 s2 s0Steps s1Step IH =>
     have l1 := lemma1 s1 s2 v
     have l2 := lemma0 s1 s2     
     grind
     
   
   




theorem learners_choice_is_unique (s : System a l p):
 ∀ i j v1 v2, systemIsValid s -> (s.learners i).decide = some v1 -> (s.learners j).decide = some v2 -> v1 = v2 := by
   intro i j v1 v2 sIsValid sDecV1 sDecV2
   by_cases c1:(acceptorsAreEnoughOfValue s.acceptors v1)
   . by_cases c2:(acceptorsAreEnoughOfValue s.acceptors v2)
     . have eqVal := lemma3 s v1 v2 sIsValid c1 c2; exact eqVal
     . have contra := lemma2 s v2 sIsValid c2; simp [contra] at sDecV2 
   . have contra := lemma2 s v1 sIsValid c1; simp [contra] at sDecV1
  
     
   
   
   
   

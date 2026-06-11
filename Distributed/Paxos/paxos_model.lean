-- Base model for the paxos consensus algorithm
import Distributed.base_structures
namespace PaxosModel
open Model

-- Type to represent the values chosen by the algorithm
def Value := Nat
deriving OfNat, BEq, DecidableEq, Ord, LT, LE

-- Type to represent the Id for the proposals issued by the proposers

def PropId := Nat
deriving OfNat, BEq, DecidableEq, Ord, LT, HAdd, HMul, HMod, LE

-- Type to represent the messages sent by the values
inductive Message where
| Prepare (propId: PropId) : Message
| Promise (propId: PropId) (acceptId: Fin a) (propVal: Option (Value × PropId)): Message
| Accept (a: PropId × Value): Message
| Learn (v: Fin a × Value × PropId )


structure Proposer (p a: Nat) where
id: Fin p
propVal: Option Value
propId: PropId
accPropId: PropId
propRec: Set a

def uniqueId (prop: Proposer p a): PropId :=
    (prop.propId * p + prop.id.toNat)

def idOf (id: PropId) (pp: NeZero p): Fin p :=
    Fin.ofNat p ((id % p) + 1)

structure Acceptor (a: Nat) where
id: Fin a
maxPrepareId: PropId
maxProp: Option Value
accepted: Option (Value × PropId)


structure Learner (a: Nat) (l: Nat) where
id: Fin l
decMap: (Fin a) -> Option (Value × PropId)
decide: Option Value

structure Network where
messages: List (Message)

structure System (a: Nat) (l: Nat) (p: Nat) where
learners: Map l (Learner a l)
acceptors: Map a (Acceptor a)
proposers: Map p (Proposer p a)
network: Network


-- Failure steps
@[simp]
-- Case if the message dissapears from the network
def MessageIsLost (m: Message) (n1: Network) (n2: Network): Prop :=
    n1.messages = m :: n2.messages  


-- In this case we do not add the possibility of a duplicate step since it is already covered by the base model (since messages are not deleted at reception they can be read multiple times by multiple endpoints)
inductive FailureStep: System a l p -> System a l p -> Prop where
| lostmessage : ∀ (s1: System a l p) m n2, MessageIsLost m s1.network n2
-> FailureStep s1 {s1 with network := n2}

-- Algorithm steps
@[simp]
-- A proposer sends a proposal in the network with a new Id
def ProposerSendsPrepare  (p1 p2: Proposer p a) (n1 n2: Network) (m: Message) := 
m = Message.Prepare (uniqueId p1)  ∧ n2.messages = m :: n1.messages ∧ p2 = {p1 with propId := uniqueId p1, propVal := none, propRec := emptySet, accPropId := 0 }

@[simp]
def AcceptorReceivesPrepare (n: PropId) (a1 a2: Acceptor a) (n1 n2: Network) (m: Message) :=
   (m ∈ n1.messages ∧ m = Message.Prepare n ∧ n > a1.maxPrepareId) ∧ a2 = {a1 with maxPrepareId := n} ∧ n2.messages = (Message.Promise n a1.id a1.accepted) :: n1.messages

@[simp]
def ProposerReceivesPromise (accId: Fin a) (p1 p2: Proposer p a) (n: Network) (m: Message) (opt : Option (Value × PropId)) (v : Value) (id : PropId):=
    m = Message.Promise p1.propId accId opt ∧  m ∈ n.messages ∧ p1.propId >= id ∧  (opt ≠ none -> opt = some (v, id)) ∧ 
    if (opt == none || (id.blt p1.accPropId))
    then p2 = {p1 with propRec := insertElem p1.propRec accId}
    else  p2 = {p1 with propRec := insertElem p1.propRec accId, accPropId := id, propVal := some v} 

@[simp]
def ProposerSendsAcceptor (v: Value) (p1 p2: Proposer p a) (n1 n2: Network) :=
    count p1.propRec > (a / 2) ∧ p2 = {p1 with propVal := v} ∧ 
    if p1.propVal == none then
      n2.messages = (Message.Accept (p1.propId, v)) :: n1.messages 
    else
      n2.messages = (Message.Accept (p1.propId, v)) :: n1.messages ∧ p1.propVal = some v
@[simp]
def AcceptorAccepts (id: PropId) (v: Value) (a1 a2: Acceptor a) (n: Network) (m: Message) :=
    m = Message.Accept (id, v) ∧ a1.maxPrepareId <= id ∧ m ∈ n.messages
    ∧ a2 = {a1 with accepted := some (v, id),  maxPrepareId := id}

@[simp]
def SendLearner (acc: Acceptor a) (n1 n2: Network) (v: Value) (id: PropId) :=
    acc.accepted = some (v, id) ∧ 
    n2.messages = (Message.Learn (acc.id, v, id)) :: n1.messages

@[simp]
def RecvLearner (n: Network) (l1 l2: Learner a l) (m: Message) (v: Value) (acc: Fin a) (id: PropId):=
    m = Message.Learn (acc, v, id) ∧ m ∈ n.messages ∧ l1.decide = none ∧
    l2 = {l1 with decMap := updateMap l1.decMap acc (some (v, id))} 

@[simp]
def ChooseVal (l1 l2: Learner a l) (v: Value) (id: PropId):=
    ∃ (s: Set a), count s > a / 2 ∧ (∀ i, contains s i -> l1.decMap i = (v, id))
    ∧ l1.decide = none ∧  l2 = {l1 with decide := some v}


inductive WorkingStep {a l p: Nat}: System a l p -> System a l p -> Prop where
| sendprepare: ∀ s n2 m i p2, ProposerSendsPrepare (s.proposers i) p2 s.network n2 m -> WorkingStep s {s with proposers := updateMap s.proposers i p2, network := n2}
| sendpromise: ∀ s i n m a2 n2, AcceptorReceivesPrepare n (s.acceptors i) a2 s.network n2 m -> WorkingStep s {s with network := n2,  acceptors := updateMap s.acceptors i a2}
| receivepromise: ∀ i s accId p2 m opt v id, ProposerReceivesPromise accId (s.proposers i)  p2 s.network m opt v id -> WorkingStep s {s with proposers := updateMap s.proposers i p2}
| sendacceptor : ∀ s v n2 i, ProposerSendsAcceptor v (s.proposers i) p2 s.network n2 -> WorkingStep s {s with network := n2, proposers := updateMap s.proposers i p2}
| receiveacceptor: ∀ id s i v a2 m, AcceptorAccepts id v (s.acceptors i) a2 s.network m -> WorkingStep s {s with acceptors := updateMap s.acceptors i a2}
| sendlearner: ∀ s i n2 v id, SendLearner (s.acceptors i) s.network n2 v id -> WorkingStep s {s with network := n2}
| receivelearner: ∀ s i l2 m v id acc, RecvLearner (s.network) (s.learners i) l2 m v acc id -> WorkingStep s {s with learners := updateMap s.learners i l2}
| choosefinalvalue: ∀ l2 v i id, ChooseVal (s.learners i) l2 v id -> WorkingStep s  {s with learners := updateMap s.learners i l2}
-- All possible steps merged
inductive step: System a l p -> System a l p -> Prop where
| workingStep : ∀ s1 s2, WorkingStep s1 s2 -> step s1 s2
--| failureStep: ∀ s1 s2, FailureStep s1 s2 -> step s1 s2
-- TODO: I commented the failure step t work with it, maybe revert later

inductive steps : System a l p -> System a l p -> Prop where
| refl : ∀ s1, steps s1 s1
| trans: ∀ s1 s2 s3, steps s1 s2 -> step s2 s3 -> steps s1 s3


def networkInits (n_ : Network) :=
    n_.messages = []


def proposerInits (p_: Proposer p a) (i: Fin p) :=
    p_.id = i ∧ p_.propVal = none ∧ p_.propId = p_.id.toNat ∧ p_.accPropId = 0 ∧ p_.propRec = emptySet


def acceptorInits (a_: Acceptor a) (i: Fin a) :=
    a_.id = i ∧ a_.maxPrepareId = 0 ∧ a_.maxProp = none ∧ a_.accepted = none


def learnerInits (l_: Learner a l) (i: Fin l) :=
    l_.id = i ∧ l_.decide = none ∧ l_.decMap = (λ _ => none)


-- Definition of a system that initiates well
def systemInits (s: System a l p) :=
   networkInits s.network
   ∧ (∀ i, proposerInits (s.proposers i) i)
   ∧ (∀ j, acceptorInits (s.acceptors j) j)
   ∧ (∀ k, learnerInits (s.learners k) k)
   ∧ (a >= 2 ∧ l > 0 ∧ p > 0)


def systemIsValid (s: System a l p) :=
    ∃ s0, systemInits s0 ∧ steps s0 s


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

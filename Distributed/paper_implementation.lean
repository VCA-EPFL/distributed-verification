-- Structures useful to define our data structure
namespace Model

def Set (n: Nat) (T: Type) := (Fin n) -> T

def updateSet [BEq T] (f: (Fin n) -> T) (i: Fin n) (t: T): (Fin n) -> T:=
    λ x => if i == x then t else f x


inductive Preference where 
| Yes : Preference
| No : Preference
deriving BEq, DecidableEq

inductive Decision where
| Abort: Decision
| Commit: Decision
deriving BEq, DecidableEq


inductive Message (n: Nat) where
| Vote : Preference -> (Fin n) -> Message n
| Decide : Decision -> Message n
deriving BEq, DecidableEq

structure Coordinator (n: Nat) where
numParticipants : Nat := n
decision: Option Decision
yesVotes: Array Bool
noVotes: Array Bool

structure Participant (n: Nat) where
hostid: (Fin n)
preference: Preference
decision: Option Decision
deriving BEq, DecidableEq

structure Network (n : Nat) where
network: List (Message n)

structure System where
n: Nat
coordinator: Coordinator n
participants: Set n (Participant n)
network: Network n


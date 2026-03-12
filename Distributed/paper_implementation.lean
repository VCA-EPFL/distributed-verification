-- Structures useful to define our data structure
namespace Model

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
yesVotes: List Nat
noVotes: List Nat

structure Participant (n: Nat) where
hostid: (Fin n)
preference: Preference
decision: Option Decision

structure Network (n : Nat) where
network: List (Message n)

structure System where
n: Nat
coordinator: Coordinator n
participants: (Fin n) -> Participant n
network: Network n


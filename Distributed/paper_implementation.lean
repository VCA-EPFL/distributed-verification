-- Structures useful to define our data structure
namespace Model

def Map (n: Nat) (T: Type) := (Fin n) -> T

def updateMap [BEq T] (f: Map n T) (i: Fin n) (t: T): (Fin n) -> T:=
    λ x => if i == x then t else f x

def Set (n: Nat) := Map n Bool

def emptySet : Set n:= λ _ => false

def insertElem (s: Set n) (i: Fin n) := updateMap s i true

def contains (s: Set n) (i: Fin n): Bool := s i


def count_ (s: Set n) (i: Nat) (h: NeZero n): Nat :=
  match i with
  | 0 => 0
  | a + 1 =>
    if s (Fin.ofNat n a) then 1 + count_ s a h else  count_ s a h
   

def count (s: Set n): Nat :=
  if h : (n ≠ 0) then
     have : NeZero n := ⟨h⟩ 
     count_ s n this
  else
        0



theorem fullSetImpN (s: Set n):
count s = n
-> n ≠ 0
-> ∀ i, s i = true := by sorry
   


theorem setLimit (s: Set n):
count s <= n := by
      induction n
      . unfold count count_; simp
      . rename_i n IH
        

theorem insertIncreasesCount (s: Set n):
count s <=  count (insertElem s i) := by
sorry
      
      
      
    
   
theorem fullSetCannotIncrease (s: Set n):
count s = n
-> ∀ i, count (insertElem s i) = n := by sorry


theorem fullSetCannotIncreaseContra (s: Set n):
∀ i, ¬(count (insertElem s i) = n)
-> ¬count s = n:= by
   have contr := fullSetCannotIncrease s; grind
   


   

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
yesVotes: Set n
noVotes: Set n

structure Participant (n: Nat) where
hostid: (Fin n)
preference: Preference
decision: Option Decision
deriving BEq, DecidableEq

structure Network (n : Nat) where
network: List (Message n)

structure System (n: Nat) where
coordinator: Coordinator n
participants: Map n (Participant n)
network: Network n




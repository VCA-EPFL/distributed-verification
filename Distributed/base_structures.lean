-- Structures useful to define our data structure
namespace Model

-- Definition of a Map Type
def Map (n: Nat) (T: Type _) := (Fin n) -> T


def updateMap (f: Map n T) (i: Fin n) (t: T): (Fin n) -> T:=
    λ x => if i == x then t else f x

-- Definition of a Set Type
def Set (n: Nat) := Map n Bool


@[simp]
def emptySet : Set n:= λ _ => false

@[simp]
def fullSet: Set n := (λ _ => true)

def insertElem (s: Set n) (i: Fin n) := updateMap s i true

def contains (s: Set n) (i: Fin n): Bool := s i


-- Function to count the number of elements inseide a Set
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




-- Useful theorems for our implementations of Set and Map
theorem fullSetImpN (s: Set n):
count s = n
-> n ≠ 0
-> ∀ i, s i = true := by
   induction n
   . simp
   . rename_i n IH
     intros count_neq_one n_neq_zero
     unfold count at *; simp at *
     sorry
     

theorem setLimit (s: Set n):
count s <= n := by
      induction n
      . unfold count count_; simp
      . rename_i n IH
        sorry
        

theorem insertIncreasesCount (s: Set n) (i: Fin n):
count s <=  count (insertElem s i) := by
sorry

theorem insertBoundsCount (s: Set n) (i: Fin n):
count (insertElem s i) <= count s +1 := by
sorry

      
      
    
   
theorem fullSetCannotIncrease (s: Set n):
count s = n
-> ∀ i, count (insertElem s i) = n := by
   sorry


theorem fullSetCannotIncreaseContra (s: Set n):
∀ i, ¬(count (insertElem s i) = n)
-> ¬count s = n:= by
   have contr := fullSetCannotIncrease s; grind



theorem fullSetCountsN (n: Nat):
count (@fullSet n) = n := by
  unfold fullSet count count_
  induction n
  . grind
  . rename_i n IH
    simp at *; split at IH; rw [<-IH]; simp [count_]
    split at IH; simp [count_]
    rename_i i a aNeq; simp [count_]
    sorry



theorem countSupImpContains (i: Nat) (s: Set a) :
0 < i
-> i < count s
-> ∃ j, contains s j == true := by sorry

theorem emptySetEqZero {a: Nat}:
@count a emptySet = 0 := by sorry


def setMaxContainsBoth (set1 set2: Set a):
count set1 > a / 2
-> count set2 > a / 2
-> ∃ i, contains set1 i ∧ contains set2 i := by
   intros countSet1 countSet2
   induction a
   sorry
   sorry
           

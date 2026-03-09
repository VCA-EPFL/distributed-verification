
namespace Paxos


def update_Fin {a: Type} (i' : Fin n)  (e : a) (f : Fin n -> a) : Fin n -> a :=
  fun i =>
    if i' == i then
      e
    else
      f i

@[simp]
theorem update_Fin_gso {a: Type} (i i' : Fin n)  (e : a) (f : Fin n -> a) :
  ¬(i' = i) -> update_Fin i' e f i = f i := by
    intro h1
    unfold update_Fin
    simp [*] at *

@[simp]
theorem update_Fin_gso2 {a: Type} (i i' : Fin n)  (e : a) (f : Fin n → a) :
  ¬(i = i') → update_Fin i' e f i = f i := by intros; simp [update_Fin, *]; intros; simp_all

@[simp]
theorem update_Fin_gss {a: Type} (i  : Fin n)  (e : a) (f : Fin n -> a) :
  update_Fin i e f i  = e := by
    unfold update_Fin
    simp

abbrev ballot := Nat
abbrev value := Nat
abbrev f := Nat
def n (f : Nat) : Nat := 2 * f + 1


structure Proposer (f : Nat) where
  proposer_id : Fin 2
  propose : value
  promise_collect : List (Fin (n f))
  hight_ballot : ballot


structure Acceptor (f : Nat) where
  acceptor_id : Fin (n f)
  promise : ballot
  accept : ballot × value

structure Learner (f: Nat) where
  accept_recived : (ballot × value) -> List (Fin (n f))
  decision: Option value


inductive message (f : Nat) where
| prepare (b : ballot)
| promise (b : ballot) (accept : ballot × value) (acceptor_id : Fin (n f))
| propose (proposal_b : ballot) (propsal_value : value) (proposer_id : Fin 2)
| accept (accept : ballot × value) (acceptor_id : Fin (n f))

structure Network (f : Nat) where
  network : List (message f)


structure system (f : Nat) where
  proposers: Fin 2 -> Proposer f
  acceptors : Fin (n f) -> Acceptor f
  learners : Fin (n f) -> Learner f
  network : Network f


inductive proposer_step (f : Nat ): Proposer f -> Network f -> Proposer f -> Network f -> Prop where
| send_prepare: ∀ p n,
    proposer_step f p n p
      { n with network := n.network ++ [message.prepare p.proposer_id]}
| send_propose: ∀ p n,
    p.promise_collect.length ≥ f + 1 ->
    proposer_step f p n p
      { n with network := n.network ++ [message.propose p.hight_ballot p.propose p.proposer_id ]}
--ad the start of each proposer p.hight_ballot = 0
| recive_promise: ∀ p n (j : Nat) b accept id,
    n.network[j]? = some (message.promise b accept id) ->
    b = p.proposer_id ->
    id ∉ p.promise_collect ->
    accept.1 ≤ p.hight_ballot ->
    proposer_step f p n
      { p with promise_collect := p.promise_collect ++ [id]}
      n
| recive_promise_update: ∀ p n (j : Nat) b accept id,
    n.network[j]? = some (message.promise b accept id) ->
    b = p.proposer_id ->
    id ∉ p.promise_collect ->
    accept.1 > p.hight_ballot ->
    proposer_step f p n
      { p with promise_collect := p.promise_collect ++ [id]
               hight_ballot := accept.1
               propose := accept.2}
      n


inductive acceptor_step (f : Nat ): Acceptor f -> Network f -> Acceptor f -> Network f -> Prop where
| recive_prepare: ∀ a n (j : Nat) b,
    n.network[j]? = some (message.prepare b) ->
    b > a.promise ->
    acceptor_step f a n
      { a with promise := b}
      { n with network := n.network ++ [message.promise b a.accept a.acceptor_id]}
| recive_propose: ∀ a n (j : Nat) b v id,
    n.network[j]? = some (message.propose b v id) ->
    b ≥ a.promise ->
    acceptor_step f a n
      { a with accept := (b, v)
               promise := b}
      { n with network := n.network ++ [message.accept (b, v) a.acceptor_id]}



inductive learner_step (f : Nat ): Learner f -> Network f -> Learner f -> Network f -> Prop where
| recive_accept: ∀ l n (j : Nat) acc id,
    n.network[j]? = some (message.accept acc id) ->
    id ∉ l.accept_recived acc ->
    learner_step f l n
      { l with accept_recived acc := l.accept_recived acc ++ [id]}
      n
| decision_accept: ∀ l n acc ,
    (l.accept_recived acc).length ≥ f + 1 ->
    learner_step f l n
      { l with decision := acc.2 }
      n


inductive paxos_step (f : Nat): system f -> system f -> Prop where
| proposer: ∀ s p' n' i,
    proposer_step f (s.proposers i) (s.network) p' n' ->
    paxos_step f s
      { s with proposers := update_Fin i p' s.proposers
               network := n' }
| acceptor: ∀ s a' i n',
    acceptor_step f (s.acceptors i) (s.network) a' n' ->
    paxos_step f s
      { s with acceptors := update_Fin i a' s.acceptors
               network := n' }
| learner: ∀ s l' i n',
    learner_step f (s.learners i) (s.network) l' n' ->
    paxos_step f s
      { s with learners := update_Fin i l' s.learners
               network := n'}


/-
# Correctness property
-/

def correctness {f : Nat} (s : system f) :=
  ∀ i j v v', i ≠ j -> (s.learners i).decision = some v -> (s.learners j).decision = some v' -> v = v'


-- def gold_invariant {f : Nat} (s : system f) :=
--   ∀ i v, (s.learners i).decision = some v -> ((s.proposer).promise_collect).length ≥ f + 1 ∧ (s.proposer).propose = v


def gold_invariant {f : Nat} (s : system f) :=
  ∀ v, (List.filter (fun i => (s.acceptors i).accept.2 = v) (List.finRange (n f))).length ≥ f + 1

-- def silver_invariant {f : Nat} (s : system f) :=
--    ∀ v, (List.filter (fun i => (s.acceptors i).accept.2 = v) (List.finRange (n f))).length ≥ f + 1 ->
--   (∀ i, (s.proposers i).promise_collect.length ≥ f + 1 ->
--   (s.proposers i).hight_ballot > ((List.finRange (n f)).filterMap fun i => if (s.acceptors i).accept.2 = v then some (s.acceptors i).accept.1 else none).min? ->
--   (s.proposers i).propose = v)

def silver_invariant {f : Nat} (s : system f) :=
   ∀ v, (List.filter (fun i => (s.acceptors i).accept.2 = v) (List.finRange (n f))).length ≥ f + 1 ->
  (∀ i, (s.proposers i).promise_collect.length ≥ f + 1 ->
  (s.proposers i).propose = v)

def bronze_invariant {f : Nat} (s : system f) :=
  (∀ (j : Nat) b v id , s.network.network[j]? = some (message.propose b v id) -> (s.proposers id).propose = v ∧ (s.proposers id).promise_collect.length ≥ f + 1 )

-- the idea is that if a value v is accepted by f+1 acceptors,
-- then any proposer that has received f+1 promises must have proposed v if the tra
def invariant {f : Nat} (s : system f) :=
  gold_invariant s
  ∧
  silver_invariant s
  ∧
  bronze_invariant s


theorem invaraint_preservation {f : Nat} :
  ∀ s s', invariant s -> paxos_step f s s' -> invariant s' := by
    intro s s' h1 hstep
    cases hstep
    . rename_i p n' i hstep
      cases hstep
      . admit
      . admit
      . have ⟨ h2, h3, h4 ⟩ := h1
        constructor
        . admit
        . constructor
          . unfold silver_invariant at *
            simp_all
            admit
      . have ⟨ h2, h3, h4 ⟩ := h1
        constructor
        . admit
        . constructor
          . -- work on this case
            unfold silver_invariant at *
            simp_all
            intro v H H1
            specialize h3 v H i
    . rename_i p n' i hstep
      cases hstep
      . admit
      . have ⟨ h2, h3, h4 ⟩ := h1
        constructor
        . unfold gold_invariant at *
          simp_all only [ ge_iff_le]
          unfold bronze_invariant at *
          rename_i H _
          specialize h4 _ _ _ _ H
          unfold silver_invariant at *
          simp_all only [ ge_iff_le]
          intro v; rename_i v' _ _
          cases(decEq v' v)
          . simp_all
            have ⟨ h4, h4' ⟩ := h4
            rename_i b id _ _ _
            specialize h3 v id h4'
            grind
          . simp_all
            admit
    . rename_i p n' i hstep
      cases hstep
      . unfold invariant at *
        have ⟨ h2, h3, h4 ⟩ := h1
        constructor
        . unfold gold_invariant at *
          simp_all
        . constructor
          . unfold silver_invariant at *
            simp_all; assumption
          . unfold bronze_invariant at *
            simp_all
            admit
      . admit

namespace TwoPhaseCommit


abbrev ParticipantId := Nat
abbrev CoordinatorId := Nat

inductive Preference where
  | Yes
  | No
  deriving DecidableEq, Repr

inductive Decision where
  | Commit
  | Abort
  deriving DecidableEq, Repr



inductive Message where
  | VOTE (v : Preference) (src : ParticipantId)
  | DECIDE (d : Decision)
  deriving DecidableEq, Repr

structure Coordinator where
  numParticipants : Nat
  decision : Decision
  yesVotes : List ParticipantId
  noVotes : List ParticipantId
  deriving Repr

structure Participant where
  hostId : ParticipantId
  preference : Option Preference
  decision : Decision
  deriving Repr

structure Network where
  network : List Message
  deriving Repr

structure System where
  coordinator : Coordinator
  participants : ParticipantId → Participant
  network : Network


def update_Fin {n : Nat} {a: Type} (i' : Fin n) (e : a) (f : Fin n → a) : Fin n → a :=
  fun i => if i' == i then e else f i

@[simp]
theorem update_Fin_gso {n : Nat} {a: Type} (i i' : Fin n) (e : a) (f : Fin n → a) :
  ¬(i' = i) → update_Fin i' e f i = f i := by
    intro h1; unfold update_Fin; simp [*] at *

@[simp]
theorem update_Fin_gss {n : Nat} {a: Type} (i : Fin n) (e : a) (f : Fin n → a) :
  update_Fin i e f i = e := by
    unfold update_Fin; simp

inductive coordinator_step : Coordinator → Network → Coordinator → Network → Prop where
| make_decision : ∀ c n,
    c.decision = Option.None ->
    let yesCount := c.yesVotes.length in
    let noCount := c.noVotes.length in
    (yesCount = c.numParticipants →
      coordinator_step c n { c with decision := Option.Some Decision.Commit } n)
    ∨ (noCount > 0 →
      coordinator_step c n { c with decision := Option.Some Decision.Abort } n)
    ∨ (¬(yesCount = c.numParticipants) ∧ noCount = 0 →
      coordinator_step c n c n)

| send_decide : ∀ c n d,
    c.decision = Option.Some d ->
    coordinator_step c n c { n with network := n.network ++ [Message.DECIDE d] }

inductive participant_step : Participant → Network → Participant → Network → Prop where
| send_prefrence : ∀ p n v,
    p.preference = Some preference ->
    participant_step p n { p with preference := Option.Some v } n
| receive_decision : ∀ p n (j : Nat) d,
    n.network[j]? = some (Message.DECIDE d) ->
    p.decision = Option.None ->
    participant_step p n { p with decision := Option.Some d } n

inductive system_step : System → System → Prop where
| coordinator : ∀ s c' n',
    coordinator_step s.coordinator s.network c' n' ->
    system_step s { s with coordinator := c', network := n' }

| participant : ∀ s i p' n',
    participant_step (s.participants i) s.network p' n' ->
    system_step s { s with participants := update_Fin i p' s.participants, network := n' }


end TwoPhaseCommit

-- Properties that check that the network is a valid network
import Distributed.paper_implementation

namespace Steps
open Model

-- Init properties: Check that the program has a valid init state
def coordinatorInits (c: Coordinator n) : Prop :=
    c.decision = none ∧ c.yesVotes = [] ∧ c.noVotes = []

def participantInits (p: Participant n): Prop :=
    p.decision = none

def networkInits (n: Network n): Prop :=
    n.network = []

def systemInits (s: System) : Prop :=
    networkInits s.network ∧ coordinatorInits s.coordinator ∧ ∀ i, participantInits (s.participants i)

-- Steps: list all possible steps

def ParticipantSendsPreference (p1: Participant n) (p2: Participant n) (snd: Message n) : Prop :=
snd = Message.Vote p1.preference p1.hostid ∧ p2 = p1

def CoordinatorReceivesPreference(c1: Coordinator n) (c2: Coordinator n) (rcv: Message n): Prop:= 
    ∃ (pref: Model.Preference) (id: Fin n), rcv = Message.Vote pref id
    ∧ if pref = Preference.Yes then
      c2 = {c1 with yesVotes := id :: c1.yesVotes}
    else
      c2 = {c1 with noVotes := id :: c1.noVotes}    


def CoordinatorMakesDecisionStep (c1: Coordinator n) (c2: Coordinator n) : Prop:=
c1.decision = none ∧
if c1.yesVotes.length == c1.numParticipants then
   c2 = {c1 with decision := some Decision.Commit}
else if c1.noVotes.length > 0 then
   c2 = {c1 with decision := some Decision.Abort}
else
   c2 = c1

def CoordinatorSendDecideStep (c1: Coordinator n) (c2: Coordinator n) (m: Message n) : Prop:=
∃ a, c1.decision = some a ∧ m = Message.Decide Decision.Abort

def ParticipantReceiveDecisionStep (p1: Participant n) (p2: Participant n) (m: Message n) : Prop:=
∃ a, m = Message.Decide a ∧ p1.decision = none ∧ p2 = {p1 with decision := some a}

def updateF (f: (Fin n) -> Participant n) (i: Fin n) (p': Participant n): (Fin n) -> Participant n :=
    λ x => if i == x then  p' else f x  

inductive step : System -> System -> Prop where
| partSendPref: ∀ (s: System) i p2 snd, ParticipantSendsPreference (s.participants i) p2 snd -> step s {s with participants := updateF s.participants i p2, network := {s.network with network := snd :: s.network.network}}
| coordRecvPref: ∀ (s: System) c2 rcv , CoordinatorReceivesPreference s.coordinator c2 rcv -> step s {s with coordinator := c2, network := {s.network with network := s.network.network.erase rcv}}
| coordMksDec: ∀ s c2, CoordinatorMakesDecisionStep s.coordinator c2 -> step s {s with coordinator := c2}
| coordSndDecStep: ∀ (s: System) c2 snd, CoordinatorSendDecideStep s.coordinator c2 snd -> step s {s with coordinator := c2, network := {s.network with network := snd :: s.network.network}}
| partRecvDec: ∀ s p2 i rcv, ParticipantReceiveDecisionStep (s.participants i) p2 rcv -> step s {s with participants := updateF s.participants i p2, network := {s.network with network := s.network.network.erase rcv}}

inductive steps : System -> System -> Prop where
| refl : ∀ s1, steps s1 s1
| trans: ∀ s1 s2 s3, steps s1 s2 -> step s2 s3 -> steps s1 s3 

def validSystem (s: System) :=
∃ s0, systemInits s0  ∧ steps s0 s

-- Final property we want to prove
theorem commitImpliesPreference (s: System) :
    validSystem s
    -> (∃ i, (s.participants i).decision = Decision.Commit)
    -> ∀ i, (s.participants i).preference = Preference.Yes := by
    intros validSystem existsI i; simp [Steps.validSystem] at validSystem
    rcases validSystem with ⟨s0, s0Inits, s0StepsS⟩
    
    sorry
    
    

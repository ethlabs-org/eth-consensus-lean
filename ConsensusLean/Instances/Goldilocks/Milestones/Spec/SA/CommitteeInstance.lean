module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.CommitteeSchedule
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.FamilyIdentity

@[expose] public section

namespace Consensus.Goldilocks.SA

/-! The schedule is fixed data, not sampled by a handler. State, messages, payloads,
frame operations, lock lifetimes and FG handoff are the stock ones. Only committee
admission/views, vote eligibility and the three absolute committee counts change.
No participation or correctness evidence is supplied by these definitions. -/

namespace Committee

variable {FGP : Type} (sp : SAParams) (K : CommitteeDict sp.n)

/-- A vote is qualified by its own slot, including votes carried by blocks. -/
def validMsg (v : Vote sp.n) : Prop := v.val ∈ K.committee v.slot

/-- Keep the stock payload form and support-subset checks; qualify every carried vote. -/
def validPayload (B : Blk sp.n FGP) : Prop :=
  SA.validPayload B ∧ ∀ v ∈ blockVotes B, validMsg sp K v

open Classical in
/-- Reject nonmembers before the stock slot, duplicate and two-vote admission checks. -/
noncomputable def admitVote (A : SAState sp.n) (t : Time) (v : Vote sp.n) : SAState sp.n :=
  if validMsg sp K v then SA.admitVote sp A t v else A

open Classical in
/-- The stock ordered view, restricted to votes qualified for the viewed slot. -/
noncomputable def voteViewList (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (s : Int) (cutoff : ETime) : List (Vote sp.n) × List (Vote sp.n) :=
  let votes := (SA.voteViewList A Φ s cutoff).1.filter
    (fun v => validMsg sp K v)
  (votes, votes.filter (fun v => resolutionTime A Φ v < cutoff))

/-- The committee-qualified ordered view as sets. -/
noncomputable def voteView (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (s : Int) (cutoff : ETime) : View sp.n :=
  View.ofLists (voteViewList sp K A Φ s cutoff)

/-- Stock latest-slot timing with the committee-qualified view. -/
noncomputable def latestView (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) : View sp.n × Int :=
  let s : Int := sp.slot t
  let s' : Int := if sp.ts s + 2 * sp.Δ ≤ t then s else s - 1
  (voteView sp K A Φ s' ⊤, s')

/-- Keep the stock freeze and proposal merge, qualifying votes by slot and committee. -/
noncomputable def mergedVoteView (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) : View sp.n :=
  let base := voteView sp K A Φ ((s : Int) - 1) (ETime.of (freeze sp s))
  { votes := base.votes ∪ {v | ∃ B ∈ Φ.tree, B.slot = s ∧ v ∈ blockVotes B ∧
      validMsg sp K v}
    support := base.support ∪ {v | ∃ B ∈ Φ.tree, B.slot = s ∧ v ∈ blockSupport B ∧
      v.slot + 1 = s ∧ validMsg sp K v ∧
      ∃ H ∈ Φ.tree, H.root = v.head ∧ H.slot + 1 ≤ s} }

/-- Absolute unlock threshold uses the committee of the vote label, not the lock label. -/
noncomputable def unlockTarget (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int)
    (B : Blk sp.n FGP) : Blk sp.n FGP :=
  (deepest Φ {B' | B' ∈ Φ.tree ∧ Φ.Anc B' B ∧
    2 * (opponents sp Φ V s B').ncard < K.card s.toNat}).getD Φ.F

/-- Stock live-lock movement with the committee unlock threshold. -/
noncomputable def unlock (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (s : Int)
    (V : View sp.n) : Set Lock :=
  {l' | ∃ l ∈ liveLocks sp L Φ t, ∃ B ∈ Φ.tree, B.root = l.block ∧
    l' = if (l.slot : Int) < s then
      { l with block := (unlockTarget sp K Φ V s B).root } else l}

/-- Stock head walk, anchor and tie-breaking, reading the qualified latest view. -/
noncomputable def acHead (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) : Blk sp.n FGP :=
  getHead sp A Φ t (Φ.viableTree Φ.tree) (latestView sp K A Φ t).1
    (latestView sp K A Φ t).2

/-- Distinct non-equivocating supporters in the qualified slot pool, at the stock cutoff. -/
noncomputable def confirmationScore (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat)
    (B : Blk sp.n FGP) : Nat :=
  let votes := {v | v ∈ A.pool s ∧ validMsg sp K v}
  let early := {v | v ∈ votes ∧ resolutionTime A Φ v < ETime.of (sp.ts s + 2 * sp.Δ)}
  (supporters Φ ⟨votes, early⟩ s B).ncard

/-- Dynamic majority remains over observed voters, not over the whole committee. -/
noncomputable def getConfirmation (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) :
    Option (Blk sp.n FGP) :=
  deepest Φ {B | B ∈ Φ.tree ∧ Φ.Anc Φ.F B ∧
    (voters {v | v ∈ A.pool s ∧ validMsg sp K v}).ncard <
      2 * confirmationScore sp K A Φ s B}

/-- Fast confirmation uses half of the slot committee, inclusive. -/
def FastTest (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat) (B : Blk sp.n FGP) : Prop :=
  K.card s ≤ 2 * confirmationScore sp K A Φ s B

open Classical in
/-- Stock record, veto, saved confirmations and lock writes with qualified counts. -/
noncomputable def updateConfirmation (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : SAState sp.n :=
  let C := getConfirmation sp K A Φ s
  let A₁ := { A with saved := Function.update A.saved s (C.map Block.root) }
  match C with
  | none => A₁
  | some C =>
    let A₂ := if conflictsWithLock sp A₁.locks Φ t C then A₁ else updateLatestConfirmed sp A₁ Φ C
    let path := {B | B ∈ confirmationPath sp Φ C ∧ ¬ conflictsWithLock sp A₁.locks Φ t B}
    let fast := FastTest sp K A Φ s
    let slow := fun B : Blk sp.n FGP => ∀ j : Int, (s : Int) - sp.k < j → j < s →
      ∃ S ∈ Φ.tree, A₁.saved j = some S.root ∧ Φ.Anc B S
    let D := deepest Φ {B | B ∈ path ∧ fast B}
    let X := deepest Φ {B | B ∈ path ∧ slow B}
    let N : Set (Nat × Bool × Nat) :=
      {p | (∃ B, D = some B ∧ p = (B.root, true, fastExpiry sp A₂.locks Φ t s)) ∨
        (∃ B, X = some B ∧ p = (B.root, false, s + sp.k))}
    { A₂ with locks := addLocks sp A₂.locks Φ t s N }

/-- Qualified distinct optimistic voters, with equivocators counted as in the stock rule. -/
def optimisticVoters (A : SAState sp.n) (Φ : Frm sp.n FGP) (s : Nat)
    (B : Blk sp.n FGP) : Set (Fin sp.n) :=
  {i | ∃ x ∈ A.pool s, validMsg sp K x ∧ x.val = i ∧ AncR Φ B x.head}

open Classical in
/-- Stock optimistic timing and veto; the absolute quorum is three quarters of K s. -/
noncomputable def optimisticSelect (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    Option (Blk sp.n FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t ∨ s = 0 ∨ sp.ts s + 2 * sp.Δ ≤ t then none
  else deepest Φ {B | B ∈ Φ.tree ∧ 3 * K.card s ≤ 4 * (optimisticVoters sp K A Φ s B).ncard ∧
    ¬ conflictsWithLock sp A.locks Φ t B}

/-- Stock optimistic write and expiry with the committee selection. -/
noncomputable def optimisticConfirmation (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    SAState sp.n :=
  match optimisticSelect sp K A Φ t with
  | none => A
  | some B =>
    updateLatestConfirmed sp
      { A with locks := addLocks sp A.locks Φ t (sp.slot t)
                  {(B.root, true, fastExpiry sp A.locks Φ t (sp.slot t))} } Φ B

/-- Stock common-ancestor confirmed output using the committee head. -/
noncomputable def acConfirmed (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) : Blk sp.n FGP :=
  let C := (lookup Φ A.latestConfirmed).getD Φ.F
  let H := acHead sp K A Φ t
  (deepest Φ {X | X ∈ Φ.tree ∧ Φ.Anc X C ∧ Φ.Anc X H}).getD Φ.F

open Classical in
/-- Stock maintenance for every node; only current-slot members emit and receipt an own vote. -/
noncomputable def tryVote (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    SAState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t ∨ A.votedSlot = s ∨ sp.ts s + sp.Δ < t then (A, [])
  else if t < sp.ts s + sp.Δ ∧ (s = 0 ∨ ¬ voteReady sp Φ s) then (A, [])
  else
    let V := mergedVoteView sp K A Φ s
    let A₁ := if 0 < s then { A with locks := unlock sp K A.locks Φ t ((s : Int) - 1) V } else A
    let dom := voteDomain sp A₁ Φ s
    let H := getHead sp A₁ Φ t (Φ.viableTree dom) V ((s : Int) - 1)
    let A₂ := { A₁ with votedSlot := s }
    if self ∈ K.committee s then
      let vote : Vote sp.n := { val := self, slot := s, head := H.root }
      let A₃ := optimisticConfirmation sp K (admitVote sp K A₂ t vote) Φ t
      (A₃, [{ msg := vote, readPoint := A₂,
              head := some { head := H, start := getAnchor sp A₁ Φ t, dom := dom } }])
    else (A₂, [])

/-- All nodes process admitted votes; voting eligibility is checked inside tryVote. -/
noncomputable def acOnMessage (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (v : Vote sp.n) : SAState sp.n × List (Em sp FGP) :=
  tryVote sp K self (optimisticConfirmation sp K (admitVote sp K A t v) Φ t) Φ t

/-- Stock block stamp and ordered receipts, with member-qualified admission. -/
noncomputable def blockReceipt (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) : SAState sp.n :=
  (blockVotes B).foldl (fun A v => admitVote sp K A t v)
    { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) }

/-- Stock receipt/update/vote ordering with the committee operations. -/
noncomputable def acOnBlock (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) : SAState sp.n × List (Em sp FGP) :=
  tryVote sp K self (optimisticConfirmation sp K (blockReceipt sp K A t B) Φ t) Φ t

open Classical in
/-- Stock tick timing; nonmembers still update confirmations. -/
noncomputable def acOnTick (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    SAState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t then (A, [])
  else
    let r := if t = sp.ts s + sp.Δ then tryVote sp K self A Φ t else (A, [])
    let A₂ := if t = sp.ts s + 2 * sp.Δ ∧ 0 < s then
      updateConfirmation sp K r.1 Φ t (s - 1) else r.1
    (A₂, r.2)

open Classical in
/-- Stock proposal ordering and payload, using qualified prior-slot votes and unlock. -/
noncomputable def acProposal (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    SAState sp.n × Option (DutyHead sp.n FGP (Payload sp.n) × Payload sp.n) :=
  if ¬ joined sp A t then (A, none)
  else
    let s : Int := sp.slot t
    let p := voteViewList sp K A Φ (s - 1) ⊤
    let V := View.ofLists p
    let A₁ := { A with locks := unlock sp K A.locks Φ t (s - 1) V }
    let H := getHead sp A₁ Φ t (Φ.viableTree Φ.tree) V (s - 1)
    (A₁, some (⟨H, getAnchor sp A₁ Φ t, Φ.tree⟩, p))

/-- Stock restart reset and parent-order replay, through committee block receipts. -/
noncomputable def acRestart (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : SAState sp.n × List (Em sp FGP) :=
  let A' : SAState sp.n := { SAState.initial sp.genesisRoot with
    locks := A.locks, latestConfirmed := A.latestConfirmed, restartTime := (t : WithBot Time) }
  (ro.order t Φ).foldl
    (fun acc B => let r := acOnBlock sp K self acc.1 Φ t B; (r.1, acc.2 ++ r.2)) (A', [])

/-- Concrete operations over the original SA carriers; no handler laws are assumed. -/
noncomputable def operations (ro : ReplayOrder sp FGP) :
    SAOperations sp FGP (SAState sp.n) (Vote sp.n) where
  validPayload := validPayload sp K
  validMsg := validMsg sp K
  holdsMsg := fun A v => v ∈ A.pool v.slot
  genesisPayload := ([], [])
  initial := SAState.initial sp.genesisRoot
  onMessage := acOnMessage sp K
  onBlock := acOnBlock sp K
  onTick := acOnTick sp K
  proposal := acProposal sp K
  toFG := SA.acToFG sp
  confirmed := acConfirmed sp K
  head := acHead sp K
  restart := acRestart sp K ro

/-- Reuse the family observation carrier without asserting stock-handler equality. -/
noncomputable def family (ro : ReplayOrder sp FGP) : SAFamily (operations sp K ro) ro where
  stateView := id
  voteEmbed := id
  voteView := some
  sg := Vote.val
  vote_retract := (goldilocksFamily sp FGP ro).vote_retract
  vote_signer := (goldilocksFamily sp FGP ro).vote_signer
  genesis := (goldilocksFamily sp FGP ro).genesis
  initial := (goldilocksFamily sp FGP ro).initial
  mode := WriteMode.parent sp

end Committee

/-- Stock Goldilocks available chain with fixed per-slot AC committees. -/
noncomputable def goldilocksSAK (sp : SAParams) (K : CommitteeDict sp.n) (FGP : Type)
    (ro : ReplayOrder sp FGP) : ACInterface sp.toParams FGP :=
  (Committee.operations sp K ro).toAC

end Consensus.Goldilocks.SA

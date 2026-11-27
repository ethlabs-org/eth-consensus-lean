module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GenericRun

public section

/-! # The run-facts bundle of a node run under growing faults (Option B)

`LocalRunCore u`: the facts the generic healing leaves read on a node run under growing faults,
for any node AC, abstracted over the FG finality update `u` (with `Store.FinalitySpec u`), so the
same proofs read the stock run (`Growing.LocalRun`, `u := Store.updateFinality`) and the shadow run
(`u := Store.updateFinality'`). Each field is a stock lemma's statement (named in its doc) at an
observation `t ≥ 0` after the cuts it reads (`∀ q < k, tr.time q ≤ t`) by a node honest at `t`,
the form the leaves read through `hrun.upTo t`. -/

namespace Consensus.Goldilocks.Generic

/-- **The core of a node run under growing faults** (any node AC). Fields taking
`NoCollRun dg tr` are the ones whose stock proofs need collision resistance; fields taking the
requirements and the genesis root are the proposal facts (C0.3). -/
structure LocalRunCore {P : Params} {A : NodeAC P}
    (u : Store P A.Payload → FG.ChainState P.n → Store P A.Payload)
    (proposer : Nat → Fin P.n) (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (tr : RunTrace A) (ini : Fin P.n → A.State) : Prop where
  finalitySpec : Store.FinalitySpec u
  antitone : Antitone H
  time_nonneg : ∀ i, 0 ≤ tr.time i
  time_mono : Monotone tr.time
  /-- `Compose.fg_reachable` on the prefix. -/
  reachable_at : ∀ {y k t}, 0 ≤ t → (∀ q < k, tr.time q ≤ t) → y ∈ H t →
    Store.ReachableWith u A.genesisPayload (tr.state y k).fg
  /-- `Compose.Growing.honest_blocks_coherent_local`. -/
  coherent : Compose.NoCollRun dg tr → Coherent (tr.HonestBlocksAt H)
  /-- `store_anc_of_honest_anc_at_from`. -/
  held_anc_at : Compose.NoCollRun dg tr → ∀ {y k t} {B W : A.Blk}, 0 ≤ t →
    (∀ q < k, tr.time q ≤ t) → y ∈ H t → Anc (tr.HonestBlocksAt H) B W →
    W ∈ (tr.state y k).fg.tree → (tr.state y k).fg.Anc B W
  /-- `Compose.tree_mono` on the prefix. -/
  tree_mono_at : ∀ {y k i t}, 0 ≤ t → (∀ q < i, tr.time q ≤ t) → y ∈ H t → k ≤ i →
    (tr.state y k).fg.tree ⊆ (tr.state y i).fg.tree
  /-- `Healing.tree_accepted` on the prefix. -/
  tree_accepted_at : ∀ {y i t} {W : A.Blk}, 0 ≤ t → (∀ q < i, tr.time q ≤ t) → y ∈ H t →
    W ∈ (tr.state y i).fg.tree →
    W = P.genesisBlock A.genesisPayload ∨ ∃ k < i, tr.AcceptAt y k W
  /-- `Growing.LocalRun.att_unforgeable`. -/
  att_unforgeable : ∀ y i a, y ∈ H (tr.time i) →
    (tr.AttCallAt y i a ∨ ∃ B, tr.BlockCallAt y i B ∧ a ∈ B.fgPayload) →
    a.val ∈ H (tr.time i) → ∃ j < i, tr.SignAt a.val j a
  /-- The cut law of a signing `fg_attest` (unchanged `Store.attest`). -/
  attest_some : ∀ {y k} {C : A.Blk} {a : FG.Att P.n}, tr.CallAt y k (.fg (.attest C (some a))) →
    y ∈ H (tr.time k) →
    (tr.state y k).fg.attest (tr.state y k).record y C = some (a, (tr.post k).record) ∧
      (tr.post k).fg = (tr.state y k).fg ∧ (tr.post k).ac = (tr.state y k).ac
  /-- The cut law of a refused `fg_attest`. -/
  attest_none : ∀ {y k} {C : A.Blk}, tr.CallAt y k (.fg (.attest C none)) → y ∈ H (tr.time k) →
    (tr.state y k).fg.attest (tr.state y k).record y C = none ∧ tr.post k = tr.state y k
  /-- `Healing.signAt_entry_from`. -/
  signAt_entry : ∀ {y k} {att : FG.Att P.n}, y ∈ H (tr.time k) → tr.SignAt y k att →
    ∃ E ∈ (tr.state y k).fg.tree, E.root = att.T ∧ ((tr.state y k).fg.σ E.root).h = att.h
  /-- `Healing.signed_before_attest` on the prefix. -/
  signed_before_attest : ∀ {y k} {C : A.Blk} {s : Option (FG.Att P.n)},
    y ∈ H (tr.time k) → tr.CallAt y k (.fg (.attest C s)) → ∀ {Y : A.Blk},
    Y ∈ (tr.state y k).fg.tree → ∀ {a : FG.Att P.n}, a ∈ Y.fgPayload → a.val ∈ H (tr.time k) →
    ∃ j, tr.SignAt a.val j a ∧ tr.time j < tr.time k
  /-- `Healing.client_record_origin_from` on the prefix. -/
  client_record_origin : ∀ {y i t}, 0 ≤ t → (∀ q < i, tr.time q ≤ t) → y ∈ H t → ∀ h r,
    ((tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.h = h ∧ att.T = r) ∧
    ((tr.state y i).record.lock h = some r →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.fin = some (h, r))
  /-- `Healing.sent_origin_from` on the prefix. -/
  sent_origin : ∀ {y i t}, 0 ≤ t → (∀ q < i, tr.time q ≤ t) → y ∈ H t → ∀ {b : FG.Content},
    b ∈ (tr.state y i).record.sent → ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.content = b
  /-- `Healing.signAt_wellFormed_from`. -/
  signAt_wellFormed : ∀ {y k} {att : FG.Att P.n}, y ∈ H (tr.time k) → tr.SignAt y k att →
    att.WellFormed
  /-- `Healing.accept_of_proposesAt_from` on the prefix. -/
  accept_of_proposesAt : Compose.NoCollRun dg tr →
    (P.genesisBlock A.genesisPayload).RootOk dg →
    (∀ y, ({ A with initial := ini y } : NodeAC P).Requirements) →
    ∀ {p k} {X : A.Blk}, p ∈ H (tr.time k) → tr.ProposesAt p k X →
      tr.AcceptAt p k X ∧ X ∈ (tr.state p (k + 1)).fg.tree ∧ tr.post k = tr.state p (k + 1)
  /-- `Healing.proposal_parent_held_from` on the prefix. -/
  proposal_parent_held : Compose.NoCollRun dg tr →
    (P.genesisBlock A.genesisPayload).RootOk dg →
    (∀ y, ({ A with initial := ini y } : NodeAC P).Requirements) →
    ∀ {p k} {X : A.Blk}, p ∈ H (tr.time k) → tr.ProposesAt p k X →
      ∃ Pr : A.Blk, X.parent = some Pr.root ∧ Pr ∈ (tr.state p k).fg.tree
  /-- `Healing.proposal_rows_placed_from` on the prefix, read in the node's store after the
  proposal cut (the FG projection's store there). -/
  proposal_rows_placed : Compose.NoCollRun dg tr →
    (P.genesisBlock A.genesisPayload).RootOk dg →
    (∀ y, ({ A with initial := ini y } : NodeAC P).Requirements) →
    ∀ {p kX} {X Pr : A.Blk}, p ∈ H (tr.time kX) → tr.ProposesAt p kX X →
      X.parent = some Pr.root → Pr ∈ (tr.state p kX).fg.tree →
      X ∈ (tr.state p (kX + 1)).fg.tree ∧ Pr ∈ (tr.state p (kX + 1)).fg.tree ∧
      (tr.post kX).fg.σ X.root = (tr.state p (kX + 1)).fg.σ X.root ∧
      (tr.state p kX).fg.σ Pr.root = (tr.state p (kX + 1)).fg.σ Pr.root ∧
      ∀ att, (∃ k' < kX, tr.ProcessAttAt p k' att) →
        att.h = ((tr.state p kX).fg.σ Pr.root).h → att.T = ((tr.state p kX).fg.σ Pr.root).Th →
        att ∈ X.fgPayload ∨ (tr.state p (kX + 1)).fg.OnChain Pr att

end Consensus.Goldilocks.Generic

end

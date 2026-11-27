module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Parametric
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay

public section

/-! # The run-facts bundles of a Goldilocks run (Option B)

The facts a Goldilocks node run provides to the healing, outage and report proofs, abstracted
over the FG finality update `u` (with `Store.FinalitySpec u`) and the node frame `frameOf`, so the
same proofs read the stock run (`u := Store.updateFinality`, `frameOf := Node.frame`) and the shadow
run (`u := Store.updateFinality'`, `frameOf := Node.frame'`); the two traces are the same type.

* `CutStepWith u frameOf`: the cut law with `Store.onBlockWith u` and `frameOf` (the stock
  `Node.CutStep` at `updateFinality`, `Node.frame`);
* `StaticRunCore`: a run with a fixed honest set (the prefix runs), its cut law, reachability,
  AC projection, trees, and the trace-level group facts its consumers read, stated over the trace,
  not over the node's handler;
* `GoldilocksRunCore`: a run under growing faults, with `upTo`, the static core of every prefix,
  and the growing facts (AC run, coherence, ancestry, finalization, relay and catch).

Each field is a stock lemma's statement (named in its doc); the stock and shadow instances fill
it from the proved lemmas. -/

namespace Consensus.Goldilocks

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The cut law with the FG finality update `u` and the node frame `frameOf` (`Node.CutStep` at
`Store.updateFinality` and `Node.frame`). -/
def CutStepWith
    (u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n))
    (frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n)))
    (self : Fin sp.n) (t : Time) (st : NodeState (goldilocksNode sp ro)) :
    Cut (goldilocksNode sp ro) → NodeState (goldilocksNode sp ro) → Prop
  | .ac ℓ, st' =>
      ℓ.frame = frameOf st ∧
        (goldilocksNode sp ro).step self st.ac ℓ.frame t ℓ.call = (st'.ac, ℓ.emits) ∧
        st'.fg = st.fg ∧ st'.record = st.record
  | .fg (.block B true), st' =>
      B.slot ≤ sp.toParams.slotOf t ∧ st.fg.onBlockWith u B = some st'.fg ∧ st'.ac = st.ac ∧
        st'.record = st.record
  | .fg (.block B false), st' => st.fg.onBlockWith u B = none ∧ st' = st
  | .fg (.attestation a), st' =>
      st'.fg = st.fg.onAttestation a ∧ st'.ac = st.ac ∧ st'.record = st.record
  | .fg (.attest C none), st' => st.fg.attest st.record self C = none ∧ st' = st
  | .fg (.attest C (some a)), st' =>
      st.fg.attest st.record self C = some (a, st'.record) ∧ st'.fg = st.fg ∧ st'.ac = st.ac

section CutStepWith

variable
    {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
    {frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n))}
    {self : Fin sp.n} {t : Time} {st st' : NodeState (goldilocksNode sp ro)}

theorem cutStepWith_ac (ℓ : ACLabel (goldilocksNode sp ro)) :
    CutStepWith u frameOf self t st (.ac ℓ) st' ↔
      ℓ.frame = frameOf st ∧
        (goldilocksNode sp ro).step self st.ac ℓ.frame t ℓ.call = (st'.ac, ℓ.emits) ∧
        st'.fg = st.fg ∧ st'.record = st.record := by
  rfl

theorem cutStepWith_block_true (B : AC.Blk sp.n (List (FG.Att sp.n))) :
    CutStepWith u frameOf self t st (.fg (.block B true)) st' ↔
      B.slot ≤ sp.toParams.slotOf t ∧ st.fg.onBlockWith u B = some st'.fg ∧ st'.ac = st.ac ∧
        st'.record = st.record := by
  rfl

theorem cutStepWith_block_false (B : AC.Blk sp.n (List (FG.Att sp.n))) :
    CutStepWith u frameOf self t st (.fg (.block B false)) st' ↔
      st.fg.onBlockWith u B = none ∧ st' = st := by
  rfl

theorem cutStepWith_attestation (a : FG.Att sp.n) :
    CutStepWith u frameOf self t st (.fg (.attestation a)) st' ↔
      st'.fg = st.fg.onAttestation a ∧ st'.ac = st.ac ∧ st'.record = st.record := by
  rfl

theorem cutStepWith_attest_none (C : AC.Blk sp.n (List (FG.Att sp.n))) :
    CutStepWith u frameOf self t st (.fg (.attest C none)) st' ↔
      st.fg.attest st.record self C = none ∧ st' = st := by
  rfl

theorem cutStepWith_attest_some (C : AC.Blk sp.n (List (FG.Att sp.n))) (a : FG.Att sp.n) :
    CutStepWith u frameOf self t st (.fg (.attest C (some a))) st' ↔
      st.fg.attest st.record self C = some (a, st'.record) ∧ st'.fg = st.fg ∧ st'.ac = st.ac := by
  rfl

end CutStepWith

/-- **The static core of a Goldilocks run** with the honest set `H`: the facts the healing,
outage and report proofs read on a run (or on a prefix of a run under growing faults). Fields
taking `NoCollRun dg tr` are the ones whose stock proofs need collision resistance. -/
structure StaticRunCore
    (u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n))
    (frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (H : Set (Fin sp.n)) (tr : GoldilocksTrace sp ro)
    (ini : Fin sp.n → (goldilocksNode sp ro).State) : Prop where
  /-- The finality update meets the stock update's specification. -/
  finalitySpec : Store.FinalitySpec u
  /-- The frame's finalized block is the store's. -/
  frameOf_F : ∀ st, (frameOf st).F = st.fg.F
  /-- The frame's tree is the store's tree above its finalized block. -/
  frameOf_tree : ∀ st B, B ∈ (frameOf st).tree ↔ B ∈ st.fg.tree ∧ st.fg.Anc st.fg.F B
  init : ∀ y ∈ H, tr.init y = Node.initWith (goldilocksNode sp ro) (ini y)
  time_nonneg : ∀ i, 0 ≤ tr.time i
  time_mono : Monotone tr.time
  vstart : ∀ y, AC.VoteStart sp.genesisRoot (ini y)
  root_ok : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg
  /-- The cut law of the honest nodes. -/
  cutLaw : ∀ y ∈ H, ∀ i c, tr.CallAt y i c →
    CutStepWith u frameOf y (tr.time i) (tr.state y i) c (tr.post i)
  /-- `LocalRun.att_unforgeable`. -/
  att_unforgeable : ∀ y ∈ H, ∀ i a,
    (tr.AttCallAt y i a ∨ ∃ B, tr.BlockCallAt y i B ∧ a ∈ B.fgPayload) → a.val ∈ H →
      ∃ j < i, tr.SignAt a.val j a
  /-- `LocalRun.awake_of_call`. -/
  awake_of_call : ∀ y ∈ H, ∀ i, tr.IsCall y i → tr.awake y (tr.time i)
  /-- `LocalRun.sleep_of_restart`. -/
  sleep_of_restart : ∀ y ∈ H, ∀ i, tr.RestartAt y i →
    ∃ u : Time, 0 ≤ u ∧ u < tr.time i ∧ ¬ tr.awake y u ∧ ∀ j < i, tr.IsCall y j → tr.time j < u
  /-- Honest signings are at public times (`FGLocalRun.attest_public` of the projection). -/
  sign_public : ∀ y ∈ H, ∀ k a, tr.SignAt y k a → sp.toParams.IsPublic (tr.time k)
  /-- The signings of an honest client are outputs of one client run over entry states
  (`Store.signed_run_of_exec` of the FG projection). -/
  signed_run : ∀ v ∈ H, ∀ i, ∃ inputs, FG.EntryInputs sp.toParams.fg inputs ∧
    ∀ j < i, ∀ a, tr.SignAt v j a → a ∈ (FG.Record.run v FG.Record.empty inputs).2
  /-- `Compose.fg_reachable`. -/
  reachable : ∀ y ∈ H, ∀ i,
    Store.ReachableWith u (goldilocksNode sp ro).genesisPayload (tr.state y i).fg
  /-- `Compose.frameOK_state`. -/
  frameOK : ∀ y ∈ H, ∀ i, FrameOK (frameOf (tr.state y i))
  /-- `Compose.projAC_state`. -/
  projAC_state : ∀ y ∈ H, ∀ i, tr.projAC.state y i = (tr.state y i).ac
  /-- `Compose.goldilocks_ac_projection_from`. -/
  acRun : Compose.NoCollRun dg tr → AC.ACRun proposer tr.projAC H (tr.HonestBlocks H) ini
  /-- `Compose.honest_blocks_coherent`. -/
  coherent : Compose.NoCollRun dg tr → Coherent (tr.HonestBlocks H)
  /-- `Compose.tree_mono`. -/
  tree_mono : ∀ y ∈ H, ∀ {k i}, k ≤ i → (tr.state y k).fg.tree ⊆ (tr.state y i).fg.tree
  /-- `Healing.tree_accepted`. -/
  tree_accepted : ∀ y ∈ H, ∀ {i W}, W ∈ (tr.state y i).fg.tree →
    W = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload ∨
      ∃ k < i, tr.AcceptAt y k W
  /-- `Healing.hj_mono`. -/
  hj_mono : ∀ y ∈ H, ∀ {i j}, i ≤ j → (tr.state y i).fg.hj ≤ (tr.state y j).fg.hj
  /-- `Healing.ac_block_after`: an acceptance is followed by the AC block call, at the same time,
  which is no restart. -/
  ac_block_after : ∀ y ∈ H, ∀ {k B}, tr.AcceptAt y k B →
    tr.projAC.AcceptAt y (k + 1) B ∧ tr.time (k + 1) = tr.time k ∧ ¬ tr.RestartAt y (k + 1)
  /-- `Compose.attest_source`: a signing `fg_attest` follows the `ac_to_fg` that returned its
  source, at the same time and FG state. -/
  attest_source : ∀ y ∈ H, ∀ {j C a}, tr.CallAt y j (.fg (.attest C (some a))) →
    ∃ j', j = j' + 1 ∧ ∃ ℓ : ACLabel (goldilocksNode sp ro), tr.CallAt y j' (.ac ℓ) ∧
      ℓ.call = .toFG ∧ tr.time j' = tr.time j ∧
      ((goldilocksNode sp ro).toFG (tr.state y j').ac ℓ.frame (tr.time j')).2 = some C ∧
      (tr.state y j).fg = (tr.state y j').fg
  /-- `Healing.toFG_attest`: an `ac_to_fg` returning a source is followed by the `fg_attest` on it,
  at the same time and FG state. -/
  report_attest : ∀ y ∈ H, ∀ {k} {ℓ : ACLabel (goldilocksNode sp ro)} {C},
    tr.CallAt y k (.ac ℓ) → ℓ.call = .toFG →
    ((goldilocksNode sp ro).toFG (tr.state y k).ac ℓ.frame (tr.time k)).2 = some C →
    ∃ s, tr.CallAt y (k + 1) (.fg (.attest C s)) ∧ tr.time (k + 1) = tr.time k ∧
      (tr.state y (k + 1)).fg = (tr.state y k).fg
  /-- The signing tick (`Compose.call_in_group`, `signed_only_in_ticks`, `exec_ac_call`,
  `Compose.before_tick`): a signing is in a tick starting at `j`, whose cuts up to the signing are
  at its time and deliver no message, and before which the node's cuts at that time are
  restarts. -/
  signed_tick : ∀ y ∈ H, ∀ {d C a}, tr.CallAt y d (.fg (.attest C (some a))) →
    ∃ j ≤ d, (∀ i, j ≤ i → i ≤ d → tr.time i = tr.time d ∧
        ∀ ℓ : ACLabel (goldilocksNode sp ro), tr.CallAt y i (.ac ℓ) → ∀ m, ℓ.call ≠ .message m) ∧
      ∀ i < j, ∀ c, tr.CallAt y i c → tr.time i = tr.time d →
        ∃ ℓ : ACLabel (goldilocksNode sp ro), c = .ac ℓ ∧ ℓ.call = .restart
  /-- The tick at an awake public time (`LocalRun.tick_of_awake`, `tick_first_cut`,
  `Compose.blockCall_cases`, `LocalRun.phase_order`): its first cut is the AC tick, before every
  acceptance at that time other than the node's own proposal. -/
  late_tick : ∀ y ∈ H, ∀ {t}, 0 ≤ t → sp.toParams.IsPublic t → tr.awake y t →
    ∃ jt, ∃ ℓ : ACLabel (goldilocksNode sp ro), tr.CallAt y jt (.ac ℓ) ∧ ℓ.call = .tick ∧
      tr.time jt = t ∧ ∀ i W, tr.AcceptAt y i W → tr.time i = t → ¬ Node.Proposes proposer y t →
        jt < i
  /-- `Compose.joined_projection_from` (the joined test at a call). -/
  joined_at_call : ∀ y ∈ H, ∀ i t, tr.IsCall y i → ¬ tr.RestartAt y i → tr.time i = t →
    (tr.JoinedAt y t ↔ AC.joined sp (tr.state y i).ac t)
  /-- `Healing.signed_before_attest`. -/
  signed_before_attest : ∀ y ∈ H, ∀ {k C s}, tr.CallAt y k (.fg (.attest C s)) →
    ∀ {Y}, Y ∈ (tr.state y k).fg.tree → ∀ {a}, a ∈ Y.fgPayload → a.val ∈ H →
      ∃ j, tr.SignAt a.val j a ∧ tr.time j < tr.time k
  /-- `Healing.accept_of_proposesAt`. -/
  accept_of_proposesAt : Compose.NoCollRun dg tr → ∀ {p k W}, p ∈ H → tr.ProposesAt p k W →
    tr.AcceptAt p k W ∧ W ∈ (tr.state p (k + 1)).fg.tree ∧ tr.post k = tr.state p (k + 1)
  /-- The payload of an honest proposal (`Compose.blockCall_cases`): the proposal attestations of
  the FG state at its cut, on its parent. -/
  proposal_payload : ∀ {p k W}, p ∈ H → tr.ProposesAt p k W →
    ∃ D, W.parent = some D.root ∧ W.fgPayload = (tr.state p k).fg.proposalAttestations D
  /-- `Healing.projection_driven_of_run`. -/
  driven : Compose.NoCollRun dg tr → AC.Driven proposer tr.projAC H
  /-- `Compose.lock_origin`. -/
  lock_origin : Compose.NoCollRun dg tr → ∀ y ∈ H, ∀ i,
    ∀ l ∈ (tr.state y i).ac.locks, ∃ L ∈ (tr.state y i).fg.tree, L.root = l.block ∧
      ∃ C, Compose.OriginBefore tr H C l.slot i ∧ Anc (tr.HonestBlocks H) L C
  /-- `Compose.vote_of_awake_joined`. -/
  vote_of_awake_joined : Compose.NoCollRun dg tr → ∀ y ∈ H, ∀ {s},
    (∀ i, (tr.state y i).ac.mayVote s = true) → tr.awake y (sp.ts s + sp.Δ) →
    tr.JoinedAt y (sp.ts s + sp.Δ) →
    ∃ k e, AC.VoteAt tr.projAC y k e ∧ e.msg.slot = s ∧ tr.projAC.time k ≤ sp.ts s + sp.Δ
  /-- `Compose.awake_participant_early`. -/
  awake_participant_early : Compose.NoCollRun dg tr → ∀ {s : Nat} {b : Time},
    AC.ServiceBefore H (tr.HonestBlocks H) b tr.projAC → sp.ts s + 2 * sp.Δ ≤ b →
    ∀ {X}, X ∈ H → ∀ {i₀} {ℓX : ACLabel (goldilocksNode sp ro)},
    AC.UpdateAt tr.projAC X i₀ s ℓX → ∀ y ∈ H, (∀ i, (tr.state y i).ac.mayVote s = true) →
    tr.awake y (sp.ts s + sp.Δ) → tr.JoinedAt y (sp.ts s + sp.Δ) →
    y ∈ AC.voters {v | v ∈ (tr.projAC.state X i₀).pool s}

/-- **The core of a Goldilocks run under growing faults**: `upTo`, the static core of every
prefix on the validators honest at its end, and the growing facts. -/
structure GoldilocksRunCore
    (u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n))
    (frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n)))
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (H : Time → Set (Fin sp.n)) (tr : GoldilocksTrace sp ro)
    (ini : Fin sp.n → (goldilocksNode sp ro).State) : Prop where
  finalitySpec : Store.FinalitySpec u
  frameOf_F : ∀ st, (frameOf st).F = st.fg.F
  frameOf_tree : ∀ st B, B ∈ (frameOf st).tree ↔ B ∈ st.fg.tree ∧ st.fg.Anc st.fg.F B
  antitone : Antitone H
  time_nonneg : ∀ i, 0 ≤ tr.time i
  time_mono : Monotone tr.time
  vstart : ∀ y, AC.VoteStart sp.genesisRoot (ini y)
  /-- Retention: the prefix through `d` is a static core on the validators honest at `d`
  (`Growing.GoldilocksRun.upTo`). -/
  upTo : ∀ {d}, 0 ≤ d → StaticRunCore u frameOf proposer dg (H d) (tr.upTo d) ini
  /-- The cut law of a node honest at its cut. -/
  cutLaw : ∀ y i c, tr.CallAt y i c → y ∈ H (tr.time i) →
    CutStepWith u frameOf y (tr.time i) (tr.state y i) c (tr.post i)
  /-- `Growing.LocalRun.att_unforgeable`. -/
  att_unforgeable : ∀ y i a, y ∈ H (tr.time i) →
    (tr.AttCallAt y i a ∨ ∃ B, tr.BlockCallAt y i B ∧ a ∈ B.fgPayload) →
    a.val ∈ H (tr.time i) → ∃ j < i, tr.SignAt a.val j a
  /-- `Growing.LocalRun.awake_of_call`. -/
  awake_of_call : ∀ y i, y ∈ H (tr.time i) → tr.IsCall y i → tr.awake y (tr.time i)
  /-- `Compose.Growing.goldilocks_ac_projection_from`. -/
  acRun : Compose.NoCollRun dg tr →
    AC.Growing.ACRun proposer tr.projAC H (tr.HonestBlocksAt H) ini
  /-- `Compose.Growing.honest_blocks_coherent`. -/
  coherent : Compose.NoCollRun dg tr → Coherent (tr.HonestBlocksAt H)
  /-- `Compose.Growing.held_anc_at`. -/
  held_anc_at : Compose.NoCollRun dg tr → ∀ {d y i} {A W : AC.Blk sp.n (List (FG.Att sp.n))},
    0 ≤ d → y ∈ H d → (∀ k < i, tr.time k ≤ d) → Anc (tr.HonestBlocksAt H) A W →
    W ∈ (tr.state y i).fg.tree → (tr.state y i).fg.Anc A W
  /-- `Compose.Growing.F_mono_at`. -/
  F_mono_at : ∀ {d y i k}, 0 ≤ d → y ∈ H d → (∀ q < i, tr.time q ≤ d) → k ≤ i →
    Anc (tr.HonestBlocksAt H) (tr.state y k).fg.F (tr.state y i).fg.F
  /-- `Growing.LocalRun.acRelayAt`. -/
  acRelayAt : ∀ {x y : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    {ℓ : ACLabel (goldilocksNode sp ro)} {σ : Time},
    x ∈ H (tr.time i) → tr.projAC.AcceptAt x i B → y ∈ H (tr.time j) →
    tr.projAC.CallAt y j ℓ → Anc (tr.HonestBlocksAt H) ℓ.frame.F B →
    (∀ k, tr.time k = tr.time i → x ∈ H (tr.time k) → tr.AcceptAt x k B →
      tr.IsCall y j → Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j σ B) →
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < tr.projAC.deadline y k σ
  /-- `Growing.LocalRun.acCatchAt`. -/
  acCatchAt : ∀ {g κ : Time}, Healing.Growing.CatchRun tr H g κ →
    ∀ {x y : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    {ℓ : ACLabel (goldilocksNode sp ro)},
    x ∈ H (tr.time i) → tr.projAC.AcceptAt x i B → tr.time i < AC.gbar g →
    y ∈ H (tr.time j) → tr.projAC.CallAt y j ℓ → AC.gbar g + κ ≤ tr.time j →
    Anc (tr.HonestBlocksAt H) ℓ.frame.F B →
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < AC.gbar g + κ

end Consensus.Goldilocks

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Node
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GenericRun
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Components

public section

/-! # Shadow P-U: the trace laws of a shadow run

The shadow node runs the stock node with the shadow FG store (`Store.onBlock'`, `Node.frame'`).
This file copies the stock trace laws that read the node's execution, over `goldilocksNode'`:

* the FG execution law `FGLabel.Step'` and the FG trace contract `FGLocalRun'` (static) and
  `Growing.FGLocalRun'`, copies of `FGLabel.Step`, `FGLocalRun` and `Growing.FGLocalRun` with
  `Store.onBlock'` in place of `Store.onBlock`;
* the component states `Compose.projAC_state'`, `Compose.projFG_state'`, the FG execution
  `Compose.fg_exec'` and the FG projection `Compose.fg_projection_from'`;
* the AC projection `Compose.goldilocks_ac_projection_from'`;
* the run laws under growing faults, `Growing.LocalRun'` and `Growing.GoldilocksRun'`, copies of
  `Growing.LocalRun` and `Growing.GoldilocksRun` with the shadow cut law and groups;
* the prefix transport `Growing.GoldilocksRun'.upTo`.

**Reused, not copied.** `goldilocksNode'` is the stock AC (`goldilocksAC`), so the AC trace contract
`ACLocalRun`, `SyncAC`, `AC.ACRun` and the projection `projAC` are the stock ones: they are generic
in the AC interface, and the shadow changes only the FG store and the frame. The AC projections here
conclude the stock `AC.ACRun`. The run carrier `RunTrace' = RunTrace` is shared, so the pure trace
predicates (`SyncRunAt`, `GSTRunAt`, `HealthyRunAt`, `CatchRun`, `NoCollRun`, `projAC_callAt`,
`projFG_callAt`, `HonestBlocks`, `Trace.upTo`, `projFG`) are reused as they are; only the lemmas
that read the run laws are copied.

**Open (shadow work in progress).** The proofs marked `sorry` are copies still to be written;
each is named after its stock counterpart with a prime. -/

namespace Consensus.Goldilocks

variable {P : Params} {ACP : Type}

/-- The shadow FG execution law of an FG call of validator `v` (stock `FGLabel.Step` with
`Store.onBlock'`). -/
def FGLabel.Step' (v : Fin P.n) (s : FGState P ACP) : FGLabel P ACP → FGState P ACP → Prop
  | .block B accepted, s' =>
      (accepted = true ∧ s.1.onBlock' B = some s'.1 ∧ s'.2 = s.2) ∨
      (accepted = false ∧ s.1.onBlock' B = none ∧ s' = s)
  | .attestation a, s' => s' = (s.1.onAttestation a, s.2)
  | .attest src signed, s' =>
      s'.1 = s.1 ∧
      match s.1.attest s.2 v src with
      | some (a, Λ') => signed = some a ∧ s'.2 = Λ'
      | none => signed = none ∧ s'.2 = s.2

theorem FGLabel.step'_block (v : Fin P.n) (s s' : FGState P ACP) (B : NodeBlock P ACP)
    (accepted : Bool) :
    FGLabel.Step' v s (.block B accepted) s' ↔
      (accepted = true ∧ s.1.onBlock' B = some s'.1 ∧ s'.2 = s.2) ∨
      (accepted = false ∧ s.1.onBlock' B = none ∧ s' = s) := by rfl

theorem FGLabel.step'_attestation (v : Fin P.n) (s s' : FGState P ACP) (a : FG.Att P.n) :
    FGLabel.Step' v s (.attestation a) s' ↔ s' = (s.1.onAttestation a, s.2) := by rfl

theorem FGLabel.step'_attest (v : Fin P.n) (s s' : FGState P ACP) (src : NodeBlock P ACP)
    (signed : Option (FG.Att P.n)) :
    FGLabel.Step' v s (.attest src signed) s' ↔
      s'.1 = s.1 ∧
      match s.1.attest s.2 v src with
      | some (a, Λ') => signed = some a ∧ s'.2 = Λ'
      | none => signed = none ∧ s'.2 = s.2 := by rfl

/-- The shadow FG trace contract (a copy of `FGLocalRun` with `FGLabel.Step'`). -/
structure FGLocalRun' (acp₀ : ACP) (H : Set (Fin P.n)) (U : Set (NodeBlock P ACP))
    (tr : FGTrace P ACP) : Prop where
  coherent : Coherent U
  init : ∀ y ∈ H, tr.init y = (Store.init acp₀, FG.Record.empty)
  exec : ∀ i ℓ, tr.label i = some ℓ → tr.node i ∈ H →
    FGLabel.Step' (tr.node i) (tr.state (tr.node i) i) ℓ (tr.post i)
  tree_subset : ∀ y ∈ H, ∀ i, (tr.store y i).tree ⊆ U
  time_nonneg : ∀ i, 0 ≤ tr.time i
  time_mono : Monotone tr.time
  attest_public : ∀ y ∈ H, ∀ i src signed, tr.CallAt y i (.attest src signed) →
    P.IsPublic (tr.time i)
  own_first : ∀ y ∈ H, ∀ i B, tr.CallAt y i (.block B true) → B.proposer = y →
    P.slotTime B.slot = tr.time i → ∀ k < i, ∀ ℓ, tr.CallAt y k ℓ → tr.time k < tr.time i
  attest_order : ∀ y ∈ H, ∀ j src signed, tr.CallAt y j (.attest src signed) →
    ∀ i ℓ, i < j → tr.CallAt y i ℓ → tr.time i = tr.time j →
      ∃ B acc, ℓ = .block B acc ∧ B.proposer = y ∧ P.slotTime B.slot = tr.time j
  own_payload : ∀ y ∈ H, ∀ i B, tr.CallAt y i (.block B true) → B.proposer = y →
    P.slotTime B.slot = tr.time i → ∀ a ∈ B.fgPayload, a ∈ (tr.store y i).atts
  unforgeable : ∀ y ∈ H, ∀ i a, tr.ProcessAt y i a → a.val ∈ H →
    ∃ j < i, tr.SignAt a.val j a

namespace Growing

/-- The shadow FG trace contract under growing faults (a copy of `Growing.FGLocalRun`). -/
structure FGLocalRun' (acp₀ : ACP) (H : Time → Set (Fin P.n)) (U : Set (NodeBlock P ACP))
    (tr : FGTrace P ACP) : Prop where
  antitone : Antitone H
  coherent : Coherent U
  init : ∀ y ∈ H 0, tr.init y = (Store.init acp₀, FG.Record.empty)
  exec : ∀ i ℓ, tr.label i = some ℓ → tr.node i ∈ H (tr.time i) →
    FGLabel.Step' (tr.node i) (tr.state (tr.node i) i) ℓ (tr.post i)
  tree_subset : ∀ y i t, 0 ≤ t → (∀ k < i, tr.time k ≤ t) → y ∈ H t → (tr.store y i).tree ⊆ U
  time_nonneg : ∀ i, 0 ≤ tr.time i
  time_mono : Monotone tr.time
  attest_public : ∀ y i src signed, y ∈ H (tr.time i) → tr.CallAt y i (.attest src signed) →
    P.IsPublic (tr.time i)
  own_first : ∀ y i B, y ∈ H (tr.time i) → tr.CallAt y i (.block B true) → B.proposer = y →
    P.slotTime B.slot = tr.time i → ∀ k < i, ∀ ℓ, tr.CallAt y k ℓ → tr.time k < tr.time i
  attest_order : ∀ y j src signed, y ∈ H (tr.time j) → tr.CallAt y j (.attest src signed) →
    ∀ i ℓ, i < j → tr.CallAt y i ℓ → tr.time i = tr.time j →
      ∃ B acc, ℓ = .block B acc ∧ B.proposer = y ∧ P.slotTime B.slot = tr.time j
  own_payload : ∀ y i B, y ∈ H (tr.time i) → tr.CallAt y i (.block B true) → B.proposer = y →
    P.slotTime B.slot = tr.time i → ∀ a ∈ B.fgPayload, a ∈ (tr.store y i).atts
  unforgeable : ∀ y i a, y ∈ H (tr.time i) → tr.ProcessAt y i a → a.val ∈ H (tr.time i) →
    ∃ j < i, tr.SignAt a.val j a

/-- **A shadow run of the node under growing faults** (a copy of `Growing.LocalRun` with the
shadow groups and cut law). -/
structure LocalRun' {A : NodeAC P} (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (sg : A.Msg → Fin P.n) (tr : RunTrace A)
    (ini : Fin P.n → A.State := fun _ => A.initial) : Prop where
  antitone : Antitone H
  init : ∀ y ∈ H 0, tr.init y = Node.initWith A (ini y)
  grouped : ∀ y i c, tr.CallAt y i c → y ∈ H (tr.time i) →
    ∃ j e, tr.InGroup' proposer dg y j i (tr.time i) e
  cutLaw : ∀ y i c, tr.CallAt y i c → y ∈ H (tr.time i) →
    Node.CutStep' y (tr.time i) (tr.state y i) c (tr.post i)
  wire : ∀ y j t e, y ∈ H t → tr.GroupAt' proposer dg y j t e → Node.WireOK dg e
  proposerCredential : ∀ y j t B, y ∈ H t → tr.GroupAt' proposer dg y j t (.block B) →
    B.proposer = proposer B.slot
  time_nonneg : ∀ i, 0 ≤ tr.time i
  time_mono : Monotone tr.time
  finite : ∀ T : Time, {i | tr.label i ≠ none ∧ tr.time i ≤ T}.Finite
  phase_order : ∀ y y' j j' t e e', y ∈ H t → y' ∈ H t → tr.GroupAt' proposer dg y j t e →
    tr.GroupAt' proposer dg y' j' t e' → j < j' →
    (y = y' ∨ ¬ tr.OwnPublicationAt' proposer dg y j t) → e.phase ≤ e'.phase
  tick_public : ∀ y j t, y ∈ H t → tr.TickAt' proposer dg y j t → P.IsPublic t
  tick_unique : ∀ y j j' t, y ∈ H t →
    tr.TickAt' proposer dg y j t → tr.TickAt' proposer dg y j' t → j = j'
  tick_of_awake : ∀ y t, y ∈ H t → 0 ≤ t → P.IsPublic t → tr.awake y t →
    ∃ j, tr.TickAt' proposer dg y j t
  awake_in_horizon : ∀ y t, y ∈ H t → tr.awake y t → tr.InHorizon t
  awake_of_call : ∀ y i, y ∈ H (tr.time i) → tr.IsCall y i → tr.awake y (tr.time i)
  restart_of_sleep : ∀ y i (u : Time), y ∈ H (tr.time i) → tr.IsCall y i → 0 ≤ u →
    u < tr.time i → ¬ tr.awake y u → (∀ j < i, tr.IsCall y j → tr.time j < u) →
    tr.RestartAt y i
  restart_at_wake : ∀ y (u v : Time), y ∈ H v → 0 ≤ u → u < v → ¬ tr.awake y u →
    tr.awake y v → ∃ k, tr.RestartAt y k ∧ u < tr.time k ∧ tr.time k ≤ v
  sleep_of_restart : ∀ y i, y ∈ H (tr.time i) → tr.RestartAt y i →
    ∃ u : Time, 0 ≤ u ∧ u < tr.time i ∧ ¬ tr.awake y u ∧
      ∀ j < i, tr.IsCall y j → tr.time j < u
  block_unforgeable : ∀ y i B, y ∈ H (tr.time i) → tr.BlockCallAt y i B →
    B.proposer ∈ H (tr.time i) → ∃ j ≤ i, tr.OwnBlockAt B.proposer j B
  att_unforgeable : ∀ y i a, y ∈ H (tr.time i) →
    (tr.AttCallAt y i a ∨ ∃ B, tr.BlockCallAt y i B ∧ a ∈ B.fgPayload) →
    a.val ∈ H (tr.time i) → ∃ j < i, tr.SignAt a.val j a
  msg_unforgeable : ∀ y i m, y ∈ H (tr.time i) → tr.MsgCallAt y i m →
    sg m ∈ H (tr.time i) → ∃ j < i, tr.EmitAt (sg m) j m

end Growing

end Consensus.Goldilocks

namespace Consensus.Goldilocks.Growing

open AC (ACParams ReplayOrder Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **A shadow Goldilocks run under growing faults** (a copy of `Growing.GoldilocksRun`). -/
structure GoldilocksRun' (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Time → Set (Fin sp.n))
    (tr : GoldilocksTrace' sp ro)
    (ini : Fin sp.n → (goldilocksNode' sp ro).State :=
      fun _ => (goldilocksNode' sp ro).initial) : Prop
    extends Growing.LocalRun' proposer dg H (fun v : Vote sp.n => v.val) tr ini where
  genesis_root_ok : (sp.toParams.genesisBlock (goldilocksNode' sp ro).genesisPayload).RootOk dg
  vstart : ∀ y, AC.VoteStart sp.genesisRoot (ini y)

end Consensus.Goldilocks.Growing

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P}
variable {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- **The AC projection's state is the AC part of the run's state** (honest node; a copy of
`projAC_state`). -/
theorem projAC_state' (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    (i : Nat) :
    tr.projAC.state y i = (tr.state y i).ac := by
  induction i with
  | zero => simp [Trace.state, RunTrace.projAC, h.init y hy]
  | succ i ih =>
    by_cases hn : tr.node i = y
    · cases hl : tr.label i with
      | none =>
        rw [tr.state_succ_of_not fun ℓ hc => by simp [hc.2] at hl]
        rw [← ih]
        simp [Trace.state, RunTrace.projAC, hl]
      | some c =>
        have hc : tr.CallAt y i c := ⟨hn, hl⟩
        have hlaw := h.cutLaw y hy i c hc
        rw [tr.state_succ_of_call hc]
        cases c with
        | ac ℓ => simp [Trace.state, RunTrace.projAC, hn, hl, RunTrace.acLabel]
        | fg ℓ =>
          rw [show (tr.post i).ac = (tr.state y i).ac by
            cases ℓ with
            | block B acc =>
              cases acc
              · rw [((cutStep'_block_false _ _ _ _ _).1 hlaw).2]
              · exact ((cutStep'_block_true _ _ _ _ _).1 hlaw).2.2.1
            | attestation a => exact ((cutStep'_attestation _ _ _ _ _).1 hlaw).2.1
            | attest C s =>
              cases s
              · rw [((cutStep'_attest_none _ _ _ _ _).1 hlaw).2]
              · exact ((cutStep'_attest_some _ _ _ _ _ _).1 hlaw).2.2, ← ih]
          simp [Trace.state, RunTrace.projAC, hl, RunTrace.acLabel]
    · rw [tr.state_succ_of_not fun ℓ hc => hn hc.1, ← ih]
      simp [Trace.state, RunTrace.projAC, hn]

/-- **The FG projection's state is the FG part and the record of the run's state** (honest
node; a copy of `projFG_state`). -/
theorem projFG_state' (h : Node.LocalRun' proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    (i : Nat) : tr.projFG.state y i = ((tr.state y i).fg, (tr.state y i).record) := by
  induction i with
  | zero => simp [Trace.state, RunTrace.projFG, h.init y hy]
  | succ i ih =>
    by_cases hn : tr.node i = y
    · cases hl : tr.label i with
      | none =>
        rw [tr.state_succ_of_not fun ℓ hc => by simp [hc.2] at hl, ← ih]
        simp [Trace.state, RunTrace.projFG, hl]
      | some c =>
        have hc : tr.CallAt y i c := ⟨hn, hl⟩
        have hlaw := h.cutLaw y hy i c hc
        rw [tr.state_succ_of_call hc]
        cases c with
        | fg ℓ => simp [Trace.state, RunTrace.projFG, hn, hl, RunTrace.fgLabel]
        | ac ℓ =>
          have hlaw := (cutStep'_ac _ _ _ _ _).1 hlaw
          rw [hlaw.2.2.1, hlaw.2.2.2, ← ih]
          simp [Trace.state, RunTrace.projFG, hl, RunTrace.fgLabel]
    · rw [tr.state_succ_of_not fun ℓ hc => hn hc.1, ← ih]
      simp [Trace.state, RunTrace.projFG, hn]

/-- **The FG projection executes the shadow FG** at the honest nodes (a copy of `fg_exec`). -/
theorem fg_exec' (h : Node.LocalRun' proposer dg H sg tr ini) :
    (∀ y ∈ H, tr.projFG.init y = (Store.init A.genesisPayload, FG.Record.empty)) ∧
    ∀ i ℓ, tr.projFG.label i = some ℓ → tr.projFG.node i ∈ H →
      FGLabel.Step' (tr.projFG.node i) (tr.projFG.state (tr.projFG.node i) i) ℓ
        (tr.projFG.post i) := by
  refine ⟨fun y hy => by simp [RunTrace.projFG, h.init y hy, Node.initWith], fun i ℓ hl hH => ?_⟩
  have hH : tr.node i ∈ H := hH
  have hc : tr.CallAt (tr.node i) i (.fg ℓ) := projFG_callAt.1 ⟨rfl, hl⟩
  have hlaw := h.cutLaw _ hH i _ hc
  change FGLabel.Step' (tr.node i) (tr.projFG.state (tr.node i) i) ℓ
    ((tr.post i).fg, (tr.post i).record)
  rw [projFG_state' h hH]
  cases ℓ with
  | block B acc =>
    rw [FGLabel.step'_block]
    cases acc with
    | true =>
      have hlaw := (cutStep'_block_true _ _ _ _ _).1 hlaw
      exact Or.inl ⟨rfl, hlaw.2.1, hlaw.2.2.2⟩
    | false =>
      have hlaw := (cutStep'_block_false _ _ _ _ _).1 hlaw
      exact Or.inr ⟨rfl, hlaw.1, by rw [hlaw.2]⟩
  | attestation a =>
    have hlaw := (cutStep'_attestation _ _ _ _ _).1 hlaw
    rw [FGLabel.step'_attestation]
    exact Prod.ext hlaw.1 hlaw.2.2
  | attest C s =>
    rw [FGLabel.step'_attest]
    cases s with
    | none =>
      have hlaw := (cutStep'_attest_none _ _ _ _ _).1 hlaw
      refine ⟨by rw [hlaw.2], ?_⟩
      simp only [hlaw.1]
      exact ⟨trivial, by rw [hlaw.2]⟩
    | some a =>
      have hlaw := (cutStep'_attest_some _ _ _ _ _ _).1 hlaw
      exact ⟨hlaw.2.1, by simp [hlaw.1]⟩

/-- **The honest blocks of a shadow run are coherent** under `NoColl` (a copy of
`honest_blocks_coherent`). -/
theorem honest_blocks_coherent' (h : Node.LocalRun' proposer dg H sg tr ini)
    (hnc : NoCollRun dg tr) : Coherent (tr.HonestBlocks H) := by
  sorry

/-- The tick order through the FG calls for a shadow run: the FG laws `attest_public`,
`own_first`, `attest_order` and `own_payload` of the projection (copies of `attestCall_tick`,
`own_accept`, `before_tick` and `fg_before_attest` over the shadow groups). -/
theorem fg_tick_order' (hq : ∀ y ∈ H, ({ A with initial := ini y } : NodeAC P).Requirements)
    (hg₀ : (P.genesisBlock A.genesisPayload).RootOk dg)
    (h : Node.LocalRun' proposer dg H sg tr ini) (hnc : NoCollRun dg tr) :
    (∀ y ∈ H, ∀ i src signed, tr.projFG.CallAt y i (.attest src signed) →
      P.IsPublic (tr.projFG.time i)) ∧
    (∀ y ∈ H, ∀ i B, tr.projFG.CallAt y i (.block B true) → B.proposer = y →
      P.slotTime B.slot = tr.projFG.time i → ∀ k < i, ∀ ℓ, tr.projFG.CallAt y k ℓ →
        tr.projFG.time k < tr.projFG.time i) ∧
    (∀ y ∈ H, ∀ j src signed, tr.projFG.CallAt y j (.attest src signed) →
      ∀ i ℓ, i < j → tr.projFG.CallAt y i ℓ → tr.projFG.time i = tr.projFG.time j →
        ∃ B acc, ℓ = .block B acc ∧ B.proposer = y ∧ P.slotTime B.slot = tr.projFG.time j) ∧
    (∀ y ∈ H, ∀ i B, tr.projFG.CallAt y i (.block B true) → B.proposer = y →
      P.slotTime B.slot = tr.projFG.time i → ∀ a ∈ B.fgPayload,
        a ∈ (tr.projFG.store y i).atts) := by
  sorry

/-- **C0.5 (c), the shadow FG projection**, from any starts `ini` at which the AC meets the
requirements (a copy of `fg_projection_from`). -/
theorem fg_projection_from' (hq : ∀ y ∈ H, ({ A with initial := ini y } : NodeAC P).Requirements)
    (hg₀ : (P.genesisBlock A.genesisPayload).RootOk dg) (h : Node.LocalRun' proposer dg H sg tr ini)
    (hnc : NoCollRun dg tr) : FGLocalRun' A.genesisPayload H (tr.HonestBlocks H) tr.projFG := by
  obtain ⟨hpub, hfirst, horder, hpay⟩ := fg_tick_order' hq hg₀ h hnc
  refine
    { coherent := honest_blocks_coherent' h hnc
      init := (fg_exec' h).1
      exec := (fg_exec' h).2
      tree_subset := fun y hy i X hX => ⟨y, hy, i, by
        rw [FGTrace.store, projFG_state' h hy] at hX
        exact hX⟩
      time_nonneg := h.time_nonneg
      time_mono := h.time_mono
      attest_public := hpub
      own_first := hfirst
      attest_order := horder
      own_payload := hpay
      unforgeable := fun y hy i a ⟨ℓ, hc, ha⟩ hv => ?_ }
  have hc := projFG_callAt.1 hc
  have hpr : tr.AttCallAt y i a ∨ ∃ B, tr.BlockCallAt y i B ∧ a ∈ B.fgPayload := by
    cases ℓ with
    | block B acc =>
      cases acc with
      | true => exact Or.inr ⟨B, ⟨true, hc⟩, ha⟩
      | false => cases ha
    | attestation a' =>
      rw [FGLabel.processed, List.mem_singleton] at ha
      subst ha
      exact Or.inl hc
    | attest C s => cases ha
  obtain ⟨j, hj, src, hs⟩ := h.att_unforgeable y hy i a hpr hv
  exact ⟨j, hj, src, projFG_callAt.2 hs⟩

end Consensus.Goldilocks.Compose

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace' sp ro} {ini : Fin sp.n → (goldilocksNode' sp ro).State}

/-- **The honest-object facts of a shadow run's AC projection**, from starts up to the vote
permission (a copy of `goldilocks_ac_projection_from`; it concludes the stock `AC.ACRun`, the AC
being the stock one). -/
theorem goldilocks_ac_projection_from' (hrun : GoldilocksRun' proposer dg H tr ini)
    (hnc : NoCollRun dg tr) :
    AC.ACRun proposer tr.projAC H (tr.HonestBlocks H) ini := by
  sorry

end Consensus.Goldilocks.Compose

namespace Consensus.Goldilocks.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace' sp ro}

/-- **Retention** for shadow runs: the prefix through `d` of a shadow run under growing faults is
a static shadow run for the validators honest at `d`, from the same starts (a copy of
`Growing.GoldilocksRun.upTo`). -/
theorem GoldilocksRun'.upTo {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (h : Growing.GoldilocksRun' proposer dg H tr ini) {d : Time} (hd : 0 ≤ d) :
    Consensus.Goldilocks.GoldilocksRun' proposer dg (H d) (tr.upTo d) ini := by
  sorry

end Consensus.Goldilocks.Growing

end

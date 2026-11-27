module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Node
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GenericRun
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Components
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo

public section

/-! # Shadow P-U: the trace laws of a shadow run

The shadow node runs the stock node with the shadow FG store (`Store.onBlock'`, `Node.frame'`).
This file copies the stock trace laws that read the node's execution, over `goldilocksNode'`:

* the FG execution law `FGLabel.Step'` and the FG trace contract `FGLocalRun'` (static) and
  `Growing.FGLocalRun'`, copies of `FGLabel.Step`, `FGLocalRun` and `Growing.FGLocalRun` with
  `Store.onBlock'` in place of `Store.onBlock`;
* the component state `Compose.projFG_state'` (`Compose.projAC_state'` and
  `Compose.honest_blocks_coherent'` are in `Shadow/PU/Node`), the FG execution
  `Compose.fg_exec'` (the FG projection `Compose.fg_projection_from'` is in
  `Shadow/PU/FGProjection`);
* (the AC projection `Compose.goldilocks_ac_projection_from'` is in `Shadow/PU/ACProjection`);
* the run laws under growing faults, `Growing.LocalRun'` and `Growing.GoldilocksRun'`, copies of
  `Growing.LocalRun` and `Growing.GoldilocksRun` with the shadow cut law and groups;
* the prefix transport `Growing.GoldilocksRun'.upTo`.

**Reused, not copied.** `goldilocksNode'` is the stock AC (`goldilocksAC`), so the AC trace contract
`ACLocalRun`, `SyncAC`, `AC.ACRun` and the projection `projAC` are the stock ones: they are generic
in the AC interface, and the shadow changes only the FG store and the frame. The AC projections here
conclude the stock `AC.ACRun`. The run carrier `RunTrace' = RunTrace` is shared, so the pure trace
predicates (`SyncRunAt`, `GSTRunAt`, `HealthyRunAt`, `CatchRun`, `NoCollRun`, `projAC_callAt`,
`projFG_callAt`, `HonestBlocks`, `Trace.upTo`, `projFG`) are reused as they are; only the lemmas
that read the run laws are copied. -/

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

end Consensus.Goldilocks.Compose

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} (tr : RunTrace A) {d : Time}

/-- A shadow group of the prefix is a shadow group of the run at a time `≤ d`, and conversely (a
copy of `upTo_groupAt`). -/
theorem upTo_groupAt' (hmono : Monotone tr.time) {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {y : Fin P.n} {j : Nat} {t : Time}
    {e : Node.Event A} :
    (tr.upTo d).GroupAt' proposer dg y j t e ↔ t ≤ d ∧ tr.GroupAt' proposer dg y j t e := by
  rw [groupAt'_iff, groupAt'_iff]
  constructor
  · rintro ⟨hne, hcuts, hev⟩
    have h0 := hcuts 0 (List.length_pos_of_ne_nil hne)
    have ht : tr.time j = t := h0.2.1
    have hl : (tr.upTo d).label j ≠ none := by
      change (tr.upTo d).label (j + 0) ≠ none
      rw [h0.2.2.2.2]
      exact Option.some_ne_none _
    have hjd : tr.time j ≤ d := by
      by_contra hc
      exact hl (by simp [RunTrace.upTo, Trace.upTo_label, hc])
    have hs := upTo_state_of_le (y := y) hmono hjd
    rw [hs] at hne hcuts hev
    refine ⟨ht ▸ hjd, hne, fun k hk => ?_, hev⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hcuts k hk
    have hkd : tr.time (j + k) ≤ d := by
      rw [show tr.time (j + k) = t from h2, ← ht]
      exact hjd
    exact ⟨h1, h2, h3, h4, by simpa [RunTrace.upTo, Trace.upTo_label, hkd] using h5⟩
  · rintro ⟨htd, hne, hcuts, hev⟩
    have h0 := hcuts 0 (List.length_pos_of_ne_nil hne)
    have ht : tr.time j = t := h0.2.1
    have hs := upTo_state_of_le (y := y) hmono (d := d) (ht ▸ htd)
    refine ⟨?_, fun k hk => ?_, ?_⟩
    · rw [hs]; exact hne
    · rw [hs] at hk
      obtain ⟨h1, h2, h3, h4, h5⟩ := hcuts k hk
      have hkd : tr.time (j + k) ≤ d := by
        rw [show tr.time (j + k) = t from h2]
        exact htd
      refine ⟨h1, h2, h3, h4, ?_⟩
      simp only [RunTrace.upTo, Trace.upTo_label, hkd, ite_true]
      rw [h5]
      simp [hs]
    · rw [hs]; exact hev

theorem upTo_inGroup' (hmono : Monotone tr.time) {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {y : Fin P.n} {j i : Nat} {t : Time}
    {e : Node.Event A} (htd : t ≤ d) (h : tr.InGroup' proposer dg y j i t e) :
    (tr.upTo d).InGroup' proposer dg y j i t e := by
  rw [inGroup'_iff] at h ⊢
  obtain ⟨hg, hji, hlt⟩ := h
  have hne := ((groupAt'_iff _ _ _ _ _ _ _).1 hg).1
  have ht : tr.time j = t :=
    (((groupAt'_iff _ _ _ _ _ _ _).1 hg).2.1 0 (List.length_pos_of_ne_nil hne)).2.1
  refine ⟨(upTo_groupAt' tr hmono).mpr ⟨htd, hg⟩, hji, ?_⟩
  rwa [upTo_state_of_le hmono (ht ▸ htd)]

theorem upTo_tickAt' (hmono : Monotone tr.time) {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {y : Fin P.n} {j : Nat} {t : Time} :
    (tr.upTo d).TickAt' proposer dg y j t ↔ t ≤ d ∧ tr.TickAt' proposer dg y j t := by
  simp only [tickAt'_iff, upTo_groupAt' tr hmono, exists_and_left]

/-- A shadow own publication of the run at a time `≤ d` is one of the prefix (a copy of
`upTo_ownPublicationAt`). -/
theorem upTo_ownPublicationAt' (hmono : Monotone tr.time) {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {y : Fin P.n} {j : Nat} {t : Time}
    (htd : t ≤ d) (h : tr.OwnPublicationAt' proposer dg y j t) :
    (tr.upTo d).OwnPublicationAt' proposer dg y j t := by
  rw [ownPublicationAt'_iff] at h ⊢
  obtain ⟨a, hg, hav, hn, j₀, x, f, hg₀, hle, hk⟩ := h
  have hg1 := (groupAt'_iff _ _ _ _ _ _ _).1 hg
  have hg01 := (groupAt'_iff _ _ _ _ _ _ _).1 hg₀
  have hj : tr.time j = t := (hg1.2.1 0 (List.length_pos_of_ne_nil hg1.1)).2.1
  have hj₀ : tr.time j₀ = t := (hg01.2.1 0 (List.length_pos_of_ne_nil hg01.1)).2.1
  have hs := upTo_state_of_le (y := y) hmono (d := d) (hj ▸ htd)
  have hs₀ := upTo_state_of_le (y := y) hmono (d := d) (hj₀ ▸ htd)
  refine ⟨a, (upTo_groupAt' tr hmono).mpr ⟨htd, hg⟩, hav, hs ▸ hn, j₀, x, f,
    (upTo_groupAt' tr hmono).mpr ⟨htd, hg₀⟩, hs₀ ▸ hle, fun k hk₁ hk₂ => ?_⟩
  obtain ⟨hnk, b, hb, hl⟩ := hk k (hs₀ ▸ hk₁) hk₂
  exact ⟨hnk, b, hb, (Trace.upTo_label_eq_some _).mpr
    ⟨(hmono hk₂.le).trans (hj ▸ htd), hl⟩⟩

end Consensus.Goldilocks.RunTrace

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
  have hm := h.time_mono
  have anti : ∀ {t}, t ≤ d → H d ⊆ H t := fun ht => h.antitone ht
  refine
    { init := fun y hy => h.init y (anti hd hy)
      grouped := fun y hy i c hc => ?_
      cutLaw := fun y hy i c hc => ?_
      wire := fun y hy j t e he => ?_
      proposerCredential := fun y hy j t B hB => ?_
      time_nonneg := h.time_nonneg
      time_mono := hm
      finite := fun T => (h.finite T).subset fun i ⟨hl, hT⟩ => ⟨fun hn => hl (by
        simp [Trace.upTo_label, hn]), hT⟩
      phase_order := fun y hy y' hy' j j' t e e' he he' hjj hop => ?_
      tick_public := fun y hy j t ht => ?_
      tick_unique := fun y hy j j' t ht ht' => ?_
      tick_of_awake := fun y hy t ht hp ha => ?_
      awake_in_horizon := fun y hy t ha => ?_
      awake_of_call := fun y hy i hc => ?_
      restart_of_sleep := fun y hy i u hc hu hui hs hb => ?_
      restart_at_wake := fun y hy u v hu huv hs hv => ?_
      sleep_of_restart := fun y hy i hr => ?_
      block_unforgeable := fun y hy i B hB hp => ?_
      att_unforgeable := fun y hy i a ha hv => ?_
      msg_unforgeable := fun y hy i m hc hs => ?_
      vstart := h.vstart
      genesis_root_ok := h.genesis_root_ok }
  · obtain ⟨hid, hc⟩ := (Trace.upTo_callAt _).mp hc
    obtain ⟨j, e, hg⟩ := h.grouped y i c hc (anti hid hy)
    exact ⟨j, e, RunTrace.upTo_inGroup' _ hm hid hg⟩
  · obtain ⟨hid, hc⟩ := (Trace.upTo_callAt _).mp hc
    rw [RunTrace.upTo_state_of_le hm hid]
    exact h.cutLaw y i c hc (anti hid hy)
  · obtain ⟨htd, he⟩ := (RunTrace.upTo_groupAt' _ hm).mp he
    exact h.wire y j t e (anti htd hy) he
  · obtain ⟨htd, hB⟩ := (RunTrace.upTo_groupAt' _ hm).mp hB
    exact h.proposerCredential y j t B (anti htd hy) hB
  · obtain ⟨htd, he⟩ := (RunTrace.upTo_groupAt' _ hm).mp he
    obtain ⟨-, he'⟩ := (RunTrace.upTo_groupAt' _ hm).mp he'
    exact h.phase_order y y' j j' t e e' (anti htd hy) (anti htd hy') he he' hjj
      (hop.imp_right fun hn hp => hn (RunTrace.upTo_ownPublicationAt' _ hm htd hp))
  · obtain ⟨htd, ht⟩ := (RunTrace.upTo_tickAt' _ hm).mp ht
    exact h.tick_public y j t (anti htd hy) ht
  · obtain ⟨htd, ht⟩ := (RunTrace.upTo_tickAt' _ hm).mp ht
    obtain ⟨-, ht'⟩ := (RunTrace.upTo_tickAt' _ hm).mp ht'
    exact h.tick_unique y j j' t (anti htd hy) ht ht'
  · obtain ⟨ha, htd⟩ := ha
    obtain ⟨j, hj⟩ := h.tick_of_awake y t (anti htd hy) ht hp ha
    exact ⟨j, (RunTrace.upTo_tickAt' _ hm).mpr ⟨htd, hj⟩⟩
  · obtain ⟨ha, htd⟩ := ha
    exact RunTrace.upTo_inHorizon htd (h.awake_in_horizon y t (anti htd hy) ha)
  · obtain ⟨hid, hc⟩ := (RunTrace.upTo_isCall _).mp hc
    exact ⟨h.awake_of_call y i (anti hid hy) hc, hid⟩
  · obtain ⟨hid, hc⟩ := (RunTrace.upTo_isCall _).mp hc
    refine (RunTrace.upTo_restartAt _).mpr ⟨hid, h.restart_of_sleep y i u (anti hid hy) hc hu hui
      (fun ha => hs ⟨ha, hui.le.trans hid⟩) fun j hj hcj => hb j hj ?_⟩
    exact (RunTrace.upTo_isCall _).mpr ⟨(hm hj.le).trans hid, hcj⟩
  · obtain ⟨hv, hvd⟩ := hv
    obtain ⟨k, hk, huk, hkv⟩ := h.restart_at_wake y u v (anti hvd hy) hu huv
      (fun ha => hs ⟨ha, huv.le.trans hvd⟩) hv
    exact ⟨k, (RunTrace.upTo_restartAt _).mpr ⟨hkv.trans hvd, hk⟩, huk, hkv⟩
  · obtain ⟨hid, hr⟩ := (RunTrace.upTo_restartAt _).mp hr
    obtain ⟨u, hu, hui, hs, hb⟩ := h.sleep_of_restart y i (anti hid hy) hr
    refine ⟨u, hu, hui, fun ha => hs ha.1, fun j hj hcj => hb j hj ?_⟩
    exact ((RunTrace.upTo_isCall _).mp hcj).2
  · obtain ⟨hid, hB⟩ := (RunTrace.upTo_blockCallAt _).mp hB
    obtain ⟨j, hji, hj⟩ := h.block_unforgeable y i B (anti hid hy) hB (anti hid hp)
    exact ⟨j, hji, (RunTrace.upTo_ownBlockAt _).mpr ⟨(hm hji).trans hid, hj⟩⟩
  · have hid : tr.time i ≤ d := by
      rcases ha with ha | ⟨B, hB, _⟩
      exacts [((RunTrace.upTo_attCallAt _).mp ha).1, ((RunTrace.upTo_blockCallAt _).mp hB).1]
    have ha' : tr.AttCallAt y i a ∨ ∃ B, tr.BlockCallAt y i B ∧ a ∈ B.fgPayload := by
      rcases ha with ha | ⟨B, hB, haB⟩
      exacts [Or.inl ((RunTrace.upTo_attCallAt _).mp ha).2,
        Or.inr ⟨B, ((RunTrace.upTo_blockCallAt _).mp hB).2, haB⟩]
    obtain ⟨j, hji, hj⟩ := h.att_unforgeable y i a (anti hid hy) ha' (anti hid hv)
    exact ⟨j, hji, (RunTrace.upTo_signAt _).mpr ⟨(hm hji.le).trans hid, hj⟩⟩
  · obtain ⟨hid, hc⟩ := (RunTrace.upTo_msgCallAt _).mp hc
    obtain ⟨j, hji, hj⟩ := h.msg_unforgeable y i m (anti hid hy) hc (anti hid hs)
    exact ⟨j, hji, (RunTrace.upTo_emitAt _).mpr ⟨(hm hji.le).trans hid, hj⟩⟩

end Consensus.Goldilocks.Growing

end

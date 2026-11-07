module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run

public section

/-! # Node-local run facts under growing faults, for the network transport

The node-local facts of a Goldilocks run that the network transport uses, for a run under growing
faults, each at a cut at which its node is honest. Each is the static fact on the prefix through
that cut's time (`Growing.GoldilocksRun.upTo`), where the node is honest throughout:

* `projAC_state_at`, `sendOrAdmit_forward_source_at`: the AC projection holds the node's AC state,
  and a send or fresh admission is an emission, a message or a block-carried vote;
* `run_F_mono_at`: `Σ.F` moves only to descendants, inside the blocks held while honest;
* `acBlock_prev_at`, `accept_next_at`: an AC block call follows its FG acceptance at the same time;
* `sleepyServiceBefore_of_message_relay_at`: the finite Sleepy service from SA message service and
  node acceptance relay. -/

namespace Consensus.Goldilocks.Obligations.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The AC projection holds the AC state of a node honest at the cut. -/
theorem projAC_state_at (hrun : Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) : tr.projAC.state y i = (tr.state y i).ac := by
  have h := Compose.projAC_state (hrun.upTo (hrun.time_nonneg i)).toLocalRun hy i
  rwa [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC y (fun k hk => hrun.time_mono hk.le),
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

/-- A send or fresh admission of a node honest at its cut is an emission, or a received message or
block-carried vote that the node did not hold before the cut and holds after it. -/
theorem sendOrAdmit_forward_source_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) {m : SA.Vote sp.n}
    (h : tr.projAC.SendOrAdmit y k m) :
    tr.EmitAt y k m ∨
      ((tr.MsgCallAt y k m ∨ ∃ ℓ B, tr.CallAt y k (.ac ℓ) ∧ ℓ.call = .block B ∧
          m ∈ SA.blockVotes B) ∧
        m ∉ (tr.state y k).ac.pool m.slot ∧ m ∈ (tr.post k).ac.pool m.slot) := by
  have hr := hrun.upTo (hrun.time_nonneg k)
  have hs := RunTrace.upTo_state_of_le (y := y) hrun.time_mono (d := tr.time k) le_rfl
  have hsA : (tr.projAC.upTo (tr.time k)).state y k = tr.projAC.state y k :=
    Trace.upTo_state tr.projAC y (fun j hj => hrun.time_mono hj.le)
  have h' : (tr.upTo (tr.time k)).projAC.SendOrAdmit y k m := by
    obtain ⟨ℓ, hc, hm⟩ := h
    refine ⟨ℓ, ?_, ?_⟩
    · rw [RunTrace.upTo_projAC]
      exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hc
    · rw [RunTrace.upTo_projAC, hsA]
      exact hm
  rcases Compose.sendOrAdmit_forward_source hr hy h' with he | ⟨hc, hn, hp⟩
  · exact Or.inl ((RunTrace.upTo_emitAt tr).mp he).2
  · refine Or.inr ⟨?_, by rwa [hs] at hn, hp⟩
    rcases hc with hc | ⟨ℓ, B, hc, hb, hm⟩
    · exact Or.inl ((RunTrace.upTo_msgCallAt tr).mp hc).2
    · exact Or.inr ⟨ℓ, B, ((Trace.upTo_callAt _).mp hc).2, hb, hm⟩

/-- `Σ.F` of a node honest at cut `i'` moves only to descendants up to `i'`, inside the blocks held
while honest. -/
theorem run_F_mono_at (hrun : Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n} {i i' : Nat}
    (hy : y ∈ H (tr.time i')) (hii : i ≤ i') :
    Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F (tr.state y i').fg.F := by
  have hr := (hrun.upTo (hrun.time_nonneg i')).toLocalRun
  have h := Healing.run_F_mono hr hy hii
  rw [RunTrace.upTo_state_of_le hrun.time_mono (hrun.time_mono hii),
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h
  exact h.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono (hrun.time_nonneg i'))

/-- An AC block call of a node honest at it follows the FG acceptance of the block at the same
time. -/
theorem acBlock_prev_at (hrun : Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    {B : (goldilocksNode sp ro).Blk} (hc : tr.CallAt y i (.ac ℓ)) (hb : ℓ.call = .block B) :
    ∃ i', i = i' + 1 ∧ tr.CallAt y i' (.fg (.block B true)) ∧ tr.time i' = tr.time i := by
  have hr := (hrun.upTo (hrun.time_nonneg i)).toLocalRun
  obtain ⟨i', rfl, hc', ht⟩ := Compose.acBlock_prev hr hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc) hb
  exact ⟨i', rfl, ((Trace.upTo_callAt _).mp hc').2, ht⟩

/-- An FG acceptance of a node honest at it is followed at once by the AC block call. -/
theorem accept_next_at (hrun : Growing.GoldilocksRun proposer dg H tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {B : (goldilocksNode sp ro).Blk}
    (hc : tr.CallAt y i (.fg (.block B true))) :
    ∃ ℓ : ACLabel (goldilocksNode sp ro), tr.CallAt y (i + 1) (.ac ℓ) ∧ ℓ.call = .block B ∧
      tr.time (i + 1) = tr.time i := by
  have hr := (hrun.upTo (hrun.time_nonneg i)).toLocalRun
  obtain ⟨ℓ, hc', hb, ht⟩ := Compose.accept_next hr hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
  exact ⟨ℓ, ((Trace.upTo_callAt _).mp hc').2, hb, ht⟩

/-- **The finite Sleepy service under growing faults** from SA message service and node
acceptance relay (senders honest at the send, recipients at the reading call); the AC acceptance
relay follows through the AC block cut after each acceptance. -/
theorem sleepyServiceBefore_of_message_relay_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    {b : Time}
    (message : ∀ x i v, x ∈ H (tr.time i) → tr.projAC.SendOrAdmit x i v → 0 ≤ tr.time i →
      ∀ y j ℓ, y ∈ H (tr.time j) → tr.projAC.CallAt y j ℓ →
        tr.projAC.deadline y j (tr.time i) ≤ b → tr.projAC.deadline y j (tr.time i) ≤ tr.time j →
        SA.MessageServedBefore tr.projAC y j (tr.time i) v)
    (relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → 0 ≤ tr.time i →
      ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.deadline y j (tr.time i) sp.Δ ≤ b →
        tr.deadline y j (tr.time i) sp.Δ ≤ tr.time j →
        Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
        tr.BlockAcceptedBy y j (tr.time i) B) :
    Compose.Growing.SleepyServiceBefore tr H sp.Δ b := by
  refine ⟨sp.toParams.hΔ, message, ?_, relay⟩
  intro x i B hx hacc hai y j ℓ hy hc hdb hdl hanc
  obtain ⟨ℓ₀, hc₀, hb⟩ := hacc
  have hc := Compose.projAC_callAt.mp hc
  obtain ⟨i', rfl, hi', hti⟩ := acBlock_prev_at hrun hx (Compose.projAC_callAt.mp hc₀) hb
  have hfr : ℓ.frame.F = (tr.state y j).fg.F := by
    rw [(hrun.cutLaw y j _ hc hy).1]
    rfl
  obtain ⟨k, hkj, hk, hlt⟩ := relay x i' B (hti ▸ hx) hi' (hti ▸ hai) y j hy ⟨_, hc⟩
    (by rw [hti, ← Compose.projAC_deadline]; exact hdb)
    (by rw [hti, ← Compose.projAC_deadline]; exact hdl) (hfr ▸ hanc)
  obtain ⟨ℓ', hc', hb', htk⟩ := accept_next_at hrun
    (hrun.antitone (hrun.time_mono hkj) hy) hk
  have hkj' : k + 1 ≤ j := by
    rcases Nat.lt_or_eq_of_le hkj with hlt' | rfl
    · omega
    · cases Option.some.inj (hk.2.symm.trans hc.2)
  have hnr : ¬ tr.RestartAt y (k + 1) := fun ⟨ℓr, hcr, hrestart⟩ => by
    cases Option.some.inj (hc'.2.symm.trans hcr.2)
    rw [hb'] at hrestart
    cases hrestart
  refine ⟨k + 1, hkj', ⟨ℓ', Compose.projAC_callAt.mpr hc', hb'⟩, ?_⟩
  rw [Compose.projAC_deadline, htk, ← hti]
  simp only [RunTrace.deadline, RunTrace.lastWake, hnr, ite_false] at hlt ⊢
  exact hlt

end Consensus.Goldilocks.Obligations.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay
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
* `sleepyServiceBefore_of_message_relay_at`: the finite Sleepy service from AC message service and
  node acceptance relay. -/

namespace Consensus.Goldilocks.Growing.LocalRun

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- Lift node acceptance service to the following AC block call, at the same deadline. -/
private theorem acRelayBefore (hrun : LocalRun proposer dg H sg tr ini) {b : Time}
    (relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → 0 ≤ tr.time i →
      ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.deadline y j (tr.time i) P.Δ ≤ b →
        tr.deadline y j (tr.time i) P.Δ ≤ tr.time j →
        Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
        tr.BlockAcceptedBy y j (tr.time i) B)
    {x : Fin P.n} {i : Nat} {B : A.Blk} (hx : x ∈ H (tr.time i))
    (hacc : tr.projAC.AcceptAt x i B) (hai : 0 ≤ tr.time i)
    {y : Fin P.n} {j : Nat} {ℓ : ACLabel A} (hy : y ∈ H (tr.time j))
    (hc : tr.projAC.CallAt y j ℓ) (hdb : tr.projAC.deadline y j (tr.time i) ≤ b)
    (hdl : tr.projAC.deadline y j (tr.time i) ≤ tr.time j)
    (hanc : Anc (tr.HonestBlocksAt H) ℓ.frame.F B) :
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < tr.projAC.deadline y k (tr.time i) := by
  apply hrun.acRelayAt hx hacc hy hc hanc
  intro k hki hx' hk hj hF
  rw [← hki]
  exact relay x k B hx' hk (hki ▸ hai) y j hy hj
    (by rw [hki, ← Compose.projAC_deadline]; exact hdb)
    (by rw [hki, ← Compose.projAC_deadline]; exact hdl) hF

end Consensus.Goldilocks.Growing.LocalRun

namespace Consensus.Goldilocks.Obligations.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}

/-- The AC projection holds the AC state of a node honest at the cut. -/
theorem projAC_state_at (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) : tr.projAC.state y i = (tr.state y i).ac := by
  have h := Compose.projAC_state (hrun.upTo (hrun.time_nonneg i)).toLocalRun hy i
  rwa [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC y (fun k hk => hrun.time_mono hk.le),
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

/-- A send or fresh admission of a node honest at its cut is an emission, or a received message
that the node did not hold before the cut and holds after it. -/
theorem sendOrAdmit_forward_source_at (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) {m : AC.Vote sp.n}
    (h : tr.projAC.SendOrAdmit y k m) :
    tr.EmitAt y k m ∨
      (tr.MsgCallAt y k m ∧ m ∉ (tr.state y k).ac.pool m.slot ∧
        m ∈ (tr.post k).ac.pool m.slot) := by
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
  · exact Or.inr ⟨((RunTrace.upTo_msgCallAt tr).mp hc).2, by rwa [hs] at hn, hp⟩

/-- `Σ.F` of a node honest at cut `i'` moves only to descendants up to `i'`, inside the blocks held
while honest. -/
private theorem run_F_mono_at (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {i i' : Nat}
    (hy : y ∈ H (tr.time i')) (hii : i ≤ i') :
    Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F (tr.state y i').fg.F :=
  hrun.toLocalRun.finalized_mono hy hii

/-- An AC block call of a node honest at it follows the FG acceptance of the block at the same
time. -/
theorem acBlock_prev_at (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp)}
    {B : (goldilocksNode sp).Blk} (hc : tr.CallAt y i (.ac ℓ)) (hb : ℓ.call = .block B) :
    ∃ i', i = i' + 1 ∧ tr.CallAt y i' (.fg (.block B true)) ∧ tr.time i' = tr.time i :=
  hrun.toLocalRun.acBlock_prev hy hc hb

/-- An FG acceptance of a node honest at it is followed at once by the AC block call. -/
theorem accept_next_at (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {B : (goldilocksNode sp).Blk}
    (hc : tr.CallAt y i (.fg (.block B true))) :
    ∃ ℓ : ACLabel (goldilocksNode sp), tr.CallAt y (i + 1) (.ac ℓ) ∧ ℓ.call = .block B ∧
      tr.time (i + 1) = tr.time i :=
  hrun.toLocalRun.accept_next hy hc

/-- **The finite Sleepy service under growing faults** from AC message service and node
acceptance relay (senders honest at the send, recipients at the reading call); the AC acceptance
relay follows through the AC block cut after each acceptance. -/
theorem sleepyServiceBefore_of_message_relay_at
    (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {b : Time}
    (message : ∀ x i v, x ∈ H (tr.time i) → tr.projAC.SendOrAdmit x i v → 0 ≤ tr.time i →
      ∀ y j ℓ, y ∈ H (tr.time j) → tr.projAC.CallAt y j ℓ →
        tr.projAC.deadline y j (tr.time i) ≤ b → tr.projAC.deadline y j (tr.time i) ≤ tr.time j →
        AC.MessageServedBefore tr.projAC y j (tr.time i) v)
    (relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → 0 ≤ tr.time i →
      ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.deadline y j (tr.time i) sp.Δ ≤ b →
        tr.deadline y j (tr.time i) sp.Δ ≤ tr.time j →
        Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
        tr.BlockAcceptedBy y j (tr.time i) B) :
    Compose.Growing.SleepyServiceBefore tr H sp.Δ b := by
  refine ⟨sp.toParams.hΔ, message, ?_, relay⟩
  intro x i B hx hacc hai y j ℓ hy hc hdb hdl hanc
  exact hrun.toLocalRun.acRelayBefore relay hx hacc hai hy hc hdb hdl hanc

end Consensus.Goldilocks.Obligations.Growing

end

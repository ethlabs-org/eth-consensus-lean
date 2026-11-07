module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection

public section

/-! # Frame relay with independently honest senders and receivers

The source's acceptance is read on its own prefix; the receiving call's laws
are read on the recipient's prefix. Service is never restricted to a surviving cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- GST relay on the AC projection preserves a historical sender's obligation. -/
theorem ResetPremisesUpTo.frame_relay_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (hacc : tr.projAC.AcceptAt x i B) (hgi : g ≤ tr.time i)
    (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y j ell)
    (hdl : tr.projAC.deadline y j (tr.time i) ≤ tr.time j)
    (hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧
      tr.time k < tr.projAC.deadline y k (tr.time i) := by
  have hri := hp.run.upTo (hp.run.time_nonneg i)
  have ha' : (tr.upTo (tr.time i)).projAC.AcceptAt x i B := by
    rw [RunTrace.upTo_projAC]
    exact (ACTrace.upTo_acceptAt).mpr ⟨le_rfl, hacc⟩
  obtain ⟨q, hiq, hq, hqt⟩ := Healing.fg_accept_before hri.toLocalRun hx ha'
  have hq₀ : tr.AcceptAt x q B := (RunTrace.upTo_acceptAt tr).mp hq |>.2
  have hqt₀ : tr.time q = tr.time i := hqt
  have hrj := hp.run.upTo (hp.run.time_nonneg j)
  have hc' : (tr.upTo (tr.time j)).projAC.CallAt y j ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  have hfr : ell.frame.F = (tr.state y j).fg.F := by
    rw [(hrj.toLocalRun.cutLaw y hy j _ (Compose.projAC_callAt.mp hc')).1,
      RunTrace.upTo_state_of_le hp.run.time_mono le_rfl]
    rfl
  have hxy : x ∈ H (tr.time q) := hqt₀ ▸ hx
  obtain ⟨k, hkj, hak, hkt⟩ := hp.sync.relay x q B hxy hq₀ (hqt₀ ▸ hgi)
    y j hy ⟨_, Compose.projAC_callAt.mp hc⟩ (by
      rw [hqt₀, max_eq_left hgi, ← Compose.projAC_deadline]
      exact hdl) (hfr ▸ hFB)
  have hkj' : k < j := by
    rcases hkj.lt_or_eq with h | rfl
    · exact h
    · cases Option.some.inj (hak.2.symm.trans (Compose.projAC_callAt.mp hc).2)
  have hkjtime : tr.time k ≤ tr.time j := hp.run.time_mono hkj
  have hak' : (tr.upTo (tr.time j)).AcceptAt y k B :=
    (RunTrace.upTo_acceptAt tr).mpr ⟨hkjtime, hak⟩
  obtain ⟨hAC, htAC, hnr⟩ := Healing.ac_block_after hrj.toLocalRun hy hak'
  have hAC₀ : tr.projAC.AcceptAt y (k + 1) B := by
    rw [RunTrace.upTo_projAC] at hAC
    exact (ACTrace.upTo_acceptAt.mp hAC).2
  have hnr₀ : ¬ tr.RestartAt y (k + 1) := by
    intro h
    apply hnr
    exact (RunTrace.upTo_restartAt tr).mpr
      ⟨(show tr.time (k + 1) = tr.time k from htAC) ▸ hkjtime, h⟩
  refine ⟨k + 1, by omega, hAC₀, ?_⟩
  rw [Compose.projAC_deadline, show tr.time (k + 1) = tr.time k from htAC]
  rw [hqt₀, max_eq_left hgi] at hkt
  simpa only [RunTrace.deadline, RunTrace.lastWake, hnr₀, ite_false] using hkt

end Consensus.Goldilocks.Healing.Growing

end

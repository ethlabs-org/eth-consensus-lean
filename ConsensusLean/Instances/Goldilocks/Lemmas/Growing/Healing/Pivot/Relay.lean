module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.CoreStock

public section

/-! # Frame relay with independently honest senders and receivers

The source's acceptance is read on its own prefix; the receiving call's laws
are read on the recipient's prefix. Service is never restricted to a surviving cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
variable {hold : Time}
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n))}

/-- GST relay on the AC projection preserves a historical sender's obligation. -/
theorem ResetRunCore.frame_relay_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetRunCore tr H u frameOf proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (hacc : tr.projAC.AcceptAt x i B) (hgi : g ≤ tr.time i)
    (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y j ell)
    (hdl : tr.projAC.deadline y j (tr.time i) ≤ tr.time j)
    (hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧
      tr.time k < tr.projAC.deadline y k (tr.time i) := by
  have rc := hp.core
  apply rc.acRelayAt (σ := tr.time i) hx hacc hy hc hFB
  intro q hqt hx' hq hj hF
  have hgq : g ≤ tr.time q := hqt ▸ hgi
  have he : max (tr.time q) g = tr.time i := (max_eq_left hgq).trans hqt
  simpa only [he] using hp.sync.relay x q B hx' hq hgq y j hy hj
    (by rw [he, ← Compose.projAC_deadline]; exact hdl) hF

/-- GST relay on the AC projection preserves a historical sender's obligation. -/
theorem ResetPremisesUpTo.frame_relay_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (hacc : tr.projAC.AcceptAt x i B) (hgi : g ≤ tr.time i)
    (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y j ell)
    (hdl : tr.projAC.deadline y j (tr.time i) ≤ tr.time j)
    (hFB : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧
      tr.time k < tr.projAC.deadline y k (tr.time i) :=
  hp.toCore.frame_relay_at hx hacc hgi hy hc hdl hFB

end Consensus.Goldilocks.Healing.Growing

end

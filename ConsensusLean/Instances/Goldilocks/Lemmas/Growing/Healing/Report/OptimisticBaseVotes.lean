module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.EarlyWitnessBoundary
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.ServiceCarry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Optimistic
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote

public section

/-! # The optimistic next-vote base under growing faults

The growing form of `Healing.optimistic_next_votes_of_early_witness` (`Healing/OptimisticBase`):
an actual optimistic write of slot `s` by a node honest at its write, with an early-held
floor witness of the prefix, makes every next-slot vote of a node honest at its cast extend the
prefix. The witness/relay induction is the common `next_votes_of_early_witness_at`; the
lock-specific step carries the writer's counted votes to the voter (`carry_of_service_senders`
over the writer's own sends and acceptances, `optimistic_writer_votes_at`) and transfers them at
the voter's cut (`SA.Growing.optimistic_transfer_stored`, faults charged at the vote). The
writer, the witness holder and each voter are honest at their own cuts only. -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An optimistic write propagates an arbitrary viable prefix to next-slot votes. The transfer
is at the full committee (`hstock`, §S.2 scope-(ii) item). -/
theorem optimistic_next_votes_of_early_witness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} (hm : gbar g ≤ sp.ts s)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {kindJ : Prop} {J X Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) floor kindJ J)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c)) {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocksAt H) X D)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q) (hstock : sp.committeeSize = sp.n) :
    ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e →
      e.msg.slot = s + 1 → SA.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  apply next_votes_of_early_witness_at hrun hnc hsvc hawake hf hcatch hm le_rfl hmb hframe hw
    hat hcw hQw hh hJ hXQ
  intro y i ell e hy hcast hs hhi hFX hviab ih
  have hmono := hrun.time_mono
  have ht0 := hrun.time_nonneg i
  have hib : tr.time i ≤ b := hhi.trans hmb
  -- the voter's frame is its node frame
  have hfr : ell.frame = Node.frame (tr.state y i) := by
    have h := Compose.frame_of_projAC (hrun.upTo ht0) hy
      (by rw [RunTrace.upTo_projAC]; exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hcast.1⟩)
    rwa [RunTrace.upTo_state_of_le hmono le_rfl] at h
  have hFX' : Anc (tr.HonestBlocksAt H) ell.frame.F X := by rw [hfr]; exact hFX
  -- the writer's counted votes reach the voter
  have hcarry := carry_of_service_senders hrun hnc hsvc hcatch hm hy hcast hs
    (CV := CV) fun v hv => by
      obtain ⟨hvs, ⟨k, hk, hsend, hlo, hhi'⟩, Hv, -, hroot, hanc, hacc⟩ :=
        Compose.Growing.optimistic_writer_votes_at hrun hnc hx hopt v hv
      refine ⟨hvs, ⟨x, k, hk, hsend, hlo, hhi'⟩, Hv, hroot, (hFX'.trans hXD).trans hanc, ?_⟩
      exact hacc.imp_right fun ⟨k', hk', hacc', htime⟩ => ⟨x, k', hk', hacc', htime⟩
  have hhalf : 2 * (H (tr.time i))ᶜ.ncard < sp.n := by
    have hbound := hf _ ht0 hib
    have hn : 0 < sp.n := sp.toParams.hn
    omega
  exact SA.Growing.optimistic_transfer_stored
    (Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc) _
    (fun _ => SA.CommitteeP.full) (fun _ => SA.CommitteeT.full) (SA.size_binding_full hstock)
    hx hopt hXD (SA.cs2_full hstock hhalf) (SA.cs2_full hstock hhalf) hy hcast hs hcarry
    hviab
    (fun z k hki hz ev hv hes => ih z k ev hki hz hv hes)

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

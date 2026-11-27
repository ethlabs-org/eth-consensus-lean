module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.LockLocal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.StockWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RegularLater
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Outage
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Shadow P-U: proposal lock cases (`KernelProof.proposal_lock_prefix_cases_at`)

The stock `Report/ProposalLocks` statement over the P-U window `FrameWindow'`. The live lock's
write origin and the unlocked image are `LockLocal`'s; the regular write reads
`Healing.PU.regular_later_heads_at`, and the older optimistic write reads the writer's own P-U
viable head as an early witness. The P-U window pins `h_max`, so no contest/gap residue arises. -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload gbar)
open Compose.Growing

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
variable {hold : Time}

/-- **Proposal lock cases over the P-U window** (`proposal_lock_prefix_cases_at` with
`FrameWindow'`): a warm live lock is below the root, followed by votes, or from a current
optimistic write. The P-U window pins `h_max`, so the writer's P-U viable head is a window
witness and no contest/gap residue arises. -/
theorem proposal_lock_prefix_cases_window_at
    {g ΔF b : Time} {s₀ s M : Nat} {isTop : Prop}
    {J X B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {z : Fin sp.n} {i : Nat} (hz : z ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt z i ell)
    (hti : tr.time i = sp.ts (s + 1 : Nat))
    {l : AC.Lock} (hl : l ∈ AC.liveLocks sp (tr.projAC.state z i).locks ell.frame (tr.time i))
    (hwarm : s₀ + sp.k ≤ l.slot) (hpos : 0 < l.slot)
    (hpred : s₀ ≤ l.slot - 1) (hold : l.slot < s + 1)
    (hB : B ∈ ell.frame.tree) (hBr : B.root = l.block) (hXB : ell.frame.Anc X B)
    (hK : CommitteeHalfUpTo tr H K g b) :
    Anc (tr.HonestBlocksAt H) X ell.frame.fcRoot ∨
      (∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → e.msg.slot = s →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg X) ∨
      ∃ a < i, ∃ D CV, z ∈ H (tr.time a) ∧ AC.OptimisticLockAt tr.projAC z a s D CV ∧
        Anc (tr.HonestBlocksAt H) X D := by
  have rc := hrun.toCore
  have hPhi := rc.frameIn_at hnc hz hc
  have hΔ := sp.toParams.hΔ
  have hi : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ := by rw [hti]; linarith only [hΔ]
  obtain ⟨a, hai, ellw, D, hza, ha, hD, hBA, ho⟩ :=
    live_lock_selection_origin_at' hrun hnc hz hc hl hB hBr
  let A := ellw.frame.viableAncestor D
  have hXA : Anc (tr.HonestBlocksAt H) X A := (Anc.mono hPhi.2 hXB).trans hBA
  have hW := rc.frameIn_at hnc hza ha
  have hAD : Anc (tr.HonestBlocksAt H) A D :=
    Anc.mono hW.2 (AC.viableAncestor_anc hW.1 hD).2
  have hregular (ho : (∃ CV, AC.FastUpdateAt tr.projAC z a l.slot D CV) ∨
      AC.SlowLockAt tr.projAC z a l.slot D) :
      ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → e.msg.slot = s →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
    obtain ⟨ell', hu⟩ : ∃ ell', AC.UpdateAt tr.projAC z a l.slot ell' := by
      rcases ho with ⟨CV, ell', C, hu, -⟩ | ⟨ell', C, hu, -⟩ <;> exact ⟨ell', hu⟩
    have hgap : l.slot + 2 ≤ s + 1 := by
      have ht := hu.2.2.1
      change tr.time a = _ at ht
      have htime := rc.time_mono hai.le
      rw [hti] at htime
      by_contra hn
      have he : s + 1 = l.slot + 1 := by omega
      rw [he] at htime
      simp only [ACParams.ts] at ht htime
      push_cast at htime
      linarith only [hΔ, ht, htime]
    have hall := (Healing.PU.regular_later_heads_at hframe hrun hnc hsvc hawake hf
      hcatch hnr hwarm hpos hpred hm hgap hmb hza ho hK s (by omega) (by omega)).1
    intro y j e hy hv hs
    obtain ⟨R, hR, hRr, hDR⟩ := hall y j e hy hv hs
    exact ⟨R, hR, hRr, (hXA.trans hAD).trans hDR⟩
  rcases ho with hfast | hslow | ⟨CV, hop⟩
  · exact Or.inr (Or.inl (hregular (Or.inl hfast)))
  · exact Or.inr (Or.inl (hregular (Or.inr hslow)))
  by_cases hs : l.slot = s
  · exact Or.inr (Or.inr ⟨a, hai, D, CV, hza, hs ▸ hop, hXA.trans hAD⟩)
  have hlabel : s₀ ≤ l.slot := by omega
  have hts : sp.ts s₀ ≤ sp.ts l.slot := (AC.ts_le_iff sp).2 (by exact_mod_cast hlabel)
  have hlw : sp.ts l.slot ≤ tr.time a := by
    obtain ⟨_, _, _, ht, -⟩ := hop
    change sp.slot (tr.time a) = l.slot at ht
    exact (AC.ts_le_iff_le_slot sp (rc.time_nonneg a) _).2 (by rw [ht])
  have halo : sp.ts s₀ ≤ tr.time a := hts.trans hlw
  have hahi : tr.time a ≤ sp.ts (s + 1 : Nat) + sp.Δ := (rc.time_mono hai.le).trans hi
  rcases (AC.viableAncestor_spec hW.1 hD).2.1 with hbelow | hAv
  · exact Or.inl (unlocked_image_below_write_root_at' hrun hnc hz hai.le ha hc hXB hBA hbelow)
  obtain ⟨Q, hQ, hvQ, hAQ⟩ := hAv.2.2
  have hat : tr.time a < sp.ts l.slot + 2 * sp.Δ := by
    obtain ⟨ell', A', hp, hsl, hsel, -⟩ := hop
    unfold AC.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel with hn
    exact lt_of_not_ge (fun ht => hn (Or.inr (Or.inr (Or.inl (hsl ▸ ht)))))
  have hall := (Shadow.PU.Growing.optimistic_later_heads_of_early_witness_at hrun hnc hsvc
    hawake hf hcatch hnr (by linarith only [hm, hts, hΔ]) hmb (hframe.mono hts le_rfl) hza hop
    hAD hza hlw hat ha hQ hvQ (Anc.mono hW.2 hAQ) hK s (by omega) (by omega)).1
  refine Or.inr (Or.inl ?_)
  intro y j e hy hv hes
  obtain ⟨R, hR, hRr, hAR⟩ := hall y j e hy hv hes
  exact ⟨R, hR, hRr, hXA.trans hAR⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

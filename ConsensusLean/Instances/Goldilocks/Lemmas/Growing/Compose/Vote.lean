module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Persist
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Next
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Sync
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Joined
import ConsensusLean.Lemmas.Tactic.Linarith

public section

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- Compatible caches and the height lead give viability at an honest vote. -/
theorem vote_viable (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hcache : Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F B ∧
      Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.J B)
    (hK2 : (∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
        Anc (tr.HonestBlocksAt H) B D ∧ (tr.state y k).fg.IsViable D) ∨
      Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocksAt H := by
    rcases hr.frameLaw y k ℓ hy hc.1 with
      ⟨_, Φ₀, _, _, h⟩ | ⟨j, ℓ', _, _, _, h⟩ <;> exact h.1
  have hfr := (hrun.cutLaw y k _ (Compose.projAC_callAt.mp hc.1) hy).1
  have hcomp : Compatible (tr.HonestBlocksAt H) ℓ.frame.fcRoot B := by
    rw [hfr]
    change Compatible _ (tr.state y k).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs
    · exact hcache.2
    · exact hcache.1
  rcases hK2 with ⟨D, hD, hBD, hvD⟩ | h
  · rcases hcomp with hfB | hBf
    · have hDt : D ∈ ℓ.frame.tree := hD.1
      have hFB := (Anc.mono hΦU hΦ.F_anc_fcRoot).trans hfB
      have hBt := SA.frame_mem_of_between sp hU hΦ hΦU hDt hBD hFB
      have hΦBD := SA.anc_tree_of_anc_U hU hΦ hΦU hBt hBD hDt
      have hΦfB := SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBt
      have hp := hr.upTo (hr.time_nonneg k)
      have hc' := SA.upTo_castAt.mpr (show tr.projAC.time k ≤ tr.time k ∧
        SA.CastAt tr.projAC y k ℓ e from ⟨le_rfl, hc⟩)
      refine Or.inl ⟨SA.voterBlockTree_anc hp hy hc' D hD B hΦBD,
        hΦfB, D, hD, ?_, hΦBD⟩
      have hfD := hΦfB.trans hΦBD
      rw [hfr] at hDt hfD ⊢
      exact ⟨hDt.1, hDt.2, Anc.mono (fun X hX => hX.1) hfD, hvD⟩
    · exact Or.inr hBf
  · exact Or.inr h

/-- Transfer at a vote counts only votes emitted while honest. -/
theorem vote_extends (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {ΔF : Time} {x : Fin sp.n} {i₀ s m : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hp : PersistPremises tr H dg ΔF x i₀ s m B CV) {y : Fin sp.n} {k : Nat}
    (hy : y ∈ H (tr.time k)) {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y k ℓ e)
    (hs : s < e.msg.slot) (hsm : e.msg.slot ≤ m)
    (hviab : B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocksAt H) B ℓ.frame.fcRoot)
    (hprior : ∀ z j, j < k → z ∈ H (tr.time j) → ∀ e', SA.VoteAt tr.projAC z j e' →
      s < e'.msg.slot → e'.msg.slot ≤ m → SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B) :
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  classical
  have hrun' := goldilocks_ac_projection sp ro dg H tr proposer hrun hp.noColl
  have hr := hrun'.localRun
  have hrk := hr.upTo (hr.time_nonneg k)
  have hc' := SA.upTo_castAt.mpr ⟨le_rfl, hc⟩
  obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, hle⟩ := Compose.cast_head_fcRoot hrk hy hc'
  obtain ⟨_, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocksAt H := by
    rcases hr.frameLaw y k ℓ hy hc.1 with
      ⟨_, Φ₀, _, _, h⟩ | ⟨j, ℓ', _, _, _, h⟩ <;> exact h.1
  rcases hviab with hv | hBf
  swap
  · exact ⟨Hd, hΦU hHd, hHdr, hBf.trans (Anc.mono hΦU hfHd)⟩
  have hslot : e.msg.slot = sp.slot (tr.time k) := (SA.castAt_spec hrk hy hc').2.1
  have h0 := hrun.time_nonneg k
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts e.msg.slot ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp h0 _).mpr (by rw [hslot])
  have htm : tr.time k ≤ sp.ts m + sp.Δ := by
    have := (SA.ts_le_iff sp).mpr (Int.ofNat_le.mpr hsm)
    change tr.time k ≤ sp.ts e.msg.slot + sp.Δ at hle
    linarith
  have hsk : sp.ts s < tr.time k := by
    have := (SA.ts_lt_iff sp).mpr (Int.ofNat_lt.mpr hs)
    linarith
  have hfault : SA.FaultBoundAt tr.projAC H (tr.time k) (tr.time k) := by
    have h := hp.faultBound y k e hy ⟨ℓ, hc.1, hc.2⟩ hsk htm
    unfold SA.FaultBoundAt
    rw [← (joined_projection sp ro dg H tr proposer hrun).2]
    exact h
  have hearlier : SA.EarlierVotesExtendAt tr.projAC H (tr.HonestBlocksAt H) k e.msg.slot B :=
    fun z j hj hz e' hv hsl => hprior z j hj hz e' hv (hsl ▸ hs) (hsl ▸ hsm)
  by_cases h1 : e.msg.slot = s + 1
  · obtain ⟨ℓw, D, hcw, hflD, hBD⟩ := hp.fastLock
    have hΦwU : ℓw.frame.tree ⊆ tr.HonestBlocksAt H := by
      rcases hr.frameLaw x i₀ ℓw hp.writer_honest hcw with
        ⟨_, Φ₀, _, _, h⟩ | ⟨j, ℓ', _, _, _, h⟩ <;> exact h.1.2
    refine SA.Growing.first_transfer_stored hrun' hp.writer_honest hflD
      (hBD ▸ Anc.mono hΦwU (SA.anc_viableAncestor ℓw.frame D)) hy hc h1
      ?_ (hp.carry y k e hy ⟨ℓ, hc.1, hc.2⟩ h1) hfault ?_ ?_
    · have hsync := sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
        tr proposer ΔF (sp.ts s) (sp.ts m + sp.Δ) hrun.toLocalRun hp.sync
      exact ⟨fun x i v hx hv ha hb => hsync.1 x i v hx hv ha (hb.trans htm),
        fun x i X hx hX ha hb => hsync.2 x i X hx hX ha (hb.trans htm)⟩
    · rw [← h1]; exact Or.inl hv
    · rw [← h1]; exact hearlier
  · obtain ⟨m', hm'⟩ : ∃ m', e.msg.slot = m' + 1 := ⟨e.msg.slot - 1, by omega⟩
    have hsm' : s < m' := by omega
    apply SA.Growing.next_transfer sp _ ro H _ tr.projAC proposer hrun' m' y k B ℓ e hy hc hm'
    · intro z j e' hz hv hsl
      have hjk : j < k := by
        by_contra hjk
        obtain ⟨ℓ', hcj, he'⟩ := hv
        have h₁ := (SA.castAt_spec (hr.upTo (hr.time_nonneg j)) hz
          (SA.upTo_castAt.mpr ⟨le_rfl, hcj, he'⟩)).2.1
        have h₂ := SA.slot_mono sp h0 (hrun.time_mono (not_lt.mp hjk))
        change e'.msg.slot = sp.slot (tr.time j) at h₁
        omega
      exact hprior z j hjk hz e' hv (by omega) (by omega)
    · have half := hp.halfCommittee m' hsm' (by omega)
      apply half.trans
      apply Nat.mul_le_mul_left
      apply Set.ncard_le_ncard (ht := Set.toFinite _)
      rintro z ⟨hz, hv⟩
      exact ⟨hrun.antitone (by rw [← hm']; exact hle) hz, hv⟩
    · exact hp.carryLater m' hsm' (by omega) y k e hy ⟨ℓ, hc.1, hc.2⟩ hm'
    · exact hfault
    · rw [← hm']; exact Or.inl hv
    · rw [← hm']; exact hearlier

end Consensus.Goldilocks.Compose.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLaterBoundary
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # An optimistic supporter's anchor and the later honest calls, under growing faults

The supporter `x` is honest at its slot-`s` cast `i` and,
independently, at its optimistic write `a`. Its frame at the cast supplies the early viable
witness: the cast's anchor `L` has a viable head above it in the supporter's own frame
(`proposal_root_viable_at`), read at the cast. The optimistic later-head propagation
(`optimistic_later_heads_of_early_witness_at`) then carries `L` to every later vote and proposal
of a node honest at its own call. -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- **The fork-choice root of a call is in its frame's viable tree**, for a node honest at the
call: in kind J the justified block itself, otherwise the cache's `hmax` block, is a viable head
above it. -/
theorem proposal_root_viable_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    (hf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell) :
    ell.frame.fcRoot ∈ ell.frame.viableTree ell.frame.tree := by
  have hm := hrun.time_mono
  have ht := hrun.time_nonneg i
  have hb : ∀ q < i, tr.time q ≤ tr.time i := fun _ hq => hm hq.le
  have hfr : ell.frame = Node.frame (tr.state y i) := by
    have h := Compose.frame_of_projAC (hrun.upTo ht) hy
      (by rw [RunTrace.upTo_projAC]; exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩)
    rwa [RunTrace.upTo_state_of_le hm le_rfl] at h
  have hR := fg_reachable_at hrun ht hb hy
  have hΦ := (Store.frame_realization _ _ _ _ hR).1
  obtain ⟨-, hJ, -, ⟨B, hB, hBJ, hBh⟩, -, ⟨Q, hQ, hQh⟩, -⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hR
  rw [hfr]
  suffices ∃ W ∈ (Node.frame (tr.state y i)).tree,
      W ∈ (Node.frame (tr.state y i)).viableHeads ∧
      (Node.frame (tr.state y i)).Anc (Node.frame (tr.state y i)).fcRoot W by
    obtain ⟨W, hW, hv, ha⟩ := this
    exact ⟨hΦ.fcRoot_mem, .refl, W, hW, hv, ha⟩
  by_cases hk : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
      ¬(tr.state y i).fg.Contest
  · obtain ⟨E, hE, hEr, hh⟩ := Healing.J_entry_h hR hB
    have hcoh := (Goldilocks.Store.accepted_tree _ _ _ _ hR).2.1
    obtain rfl : E = (tr.state y i).fg.J := hcoh.1 hE hJ (hEr.trans hBJ)
    obtain ⟨htr, ha, hv⟩ := floor_ancestor_mem_frame_at hrun hnc hy hy hf hJ
      (by simp only [Goldilocks.Store.headHeightFloor, hk.2, ↓reduceIte, hk.1]
          omega) (fun _ _ => .refl) hJ .refl
    exact ⟨_, htr, hv, ha⟩
  · obtain ⟨htr, ha, hv⟩ := floor_ancestor_mem_frame_at hrun hnc hy hy hf hQ
      ((Goldilocks.Store.headHeightFloor_bounds _).2.trans_eq hQh.symm)
      (fun hm' hn => (hk ⟨hm', hn⟩).elim) hQ .refl
    exact ⟨Q, htr, hv, ha⟩

/-- **An optimistic anchor at an honest supporter propagates to independently honest later
calls**, under growing faults. -/
theorem optimistic_supporter_later_heads_at {s₀ s N floor : Nat}
    {kindJ : Prop} {J L D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g ≤ sp.ts s) (hs₀ : s₀ ≤ s) (hsN : s + 1 ≤ N)
    (hmb : sp.ts N + sp.Δ ≤ b)
    {x : Fin sp.n} {i a : Nat} (hx : x ∈ H (tr.time i)) (hxa : x ∈ H (tr.time a))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC x i ell e) (hes : e.msg.slot = s)
    (hanchor : L = SA.getAnchor sp e.readPoint ell.frame (tr.time i))
    {CV : Set (SA.Vote sp.n)} (hop : SA.OptimisticLockAt tr.projAC x a s D CV)
    (hLD : Anc (tr.HonestBlocksAt H) L D) (hstock : sp.committeeSize = sp.n) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y j ev, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j ev → ev.msg.slot = r →
        SA.VoteExtends (tr.HonestBlocksAt H) ev.msg L) ∧
      (∀ y j ell', y ∈ H (tr.time j) → tr.projAC.CallAt y j ell' → ell'.call = .proposal →
        tr.time j = sp.ts r → ∀ d pay,
        (SA.acProposal sp (tr.projAC.state y j) ell'.frame (tr.time j)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) L d.head) := by
  have hmono := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have ht0 := hrun.time_nonneg i
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time i)) (tr.upTo (tr.time i))
    proposer (hrun.upTo ht0) (hnc.upTo _)).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc' : SA.CastAt (tr.projAC.upTo (tr.time i)) x i ell e :=
    SA.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have subU := RunTrace.honestBlocks_upTo_subset hmono (H := H) ht0
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hx hc'.1
  have hPhiU' := hPhiU.trans subU
  have hslot := (SA.castAt_spec hr hx hc').2.1.symm.trans hes
  change sp.slot (tr.time i) = s at hslot
  have hlo : sp.ts s ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp ht0 _).2 (by rw [hslot])
  have hhi : tr.time i ≤ sp.ts s + sp.Δ := by
    have h := SA.vote_time_le hr hx ⟨ell, hc'⟩
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at h
    rwa [hslot] at h
  have hts : sp.ts s₀ ≤ sp.ts s := (SA.ts_le_iff sp).2 (by exact_mod_cast hs₀)
  have htN : sp.ts s ≤ sp.ts N :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast (show s ≤ N by omega))
  have hib : tr.time i ≤ b := by linarith only [hhi, htN, hmb, hΔ]
  have hmf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have h3 := hf _ ht0 hib
    have hn := sp.toParams.hn
    have he : sp.n = sp.toParams.n := rfl
    change (H (tr.time i))ᶜ.ncard < 2 * ((2 * sp.toParams.n + 2) / 3) - sp.n
    omega
  have hfr : ell.frame = Node.frame (tr.state x i) := by
    have h := Compose.frame_of_projAC (hrun.upTo ht0) hx
      (by rw [RunTrace.upTo_projAC]; exact hc'.1)
    rwa [RunTrace.upTo_state_of_le hmono le_rfl] at h
  have hroot : ell.frame.Anc ell.frame.fcRoot L := by
    rw [hanchor]; exact SA.fcRoot_anc_getAnchor hPhi _ _
  -- the anchor is viable in the supporter's frame at its cast
  have hvL : L ∈ ell.frame.viableTree ell.frame.tree := by
    have hR := proposal_root_viable_at hrun hnc hx hmf hc.1
    have he : L = ell.frame.fcRoot ∨
        L ∈ SA.liveLockBlocks sp e.readPoint.locks ell.frame (tr.time i) := by
      rw [hanchor]
      unfold SA.getAnchor
      cases hd : SA.deepest ell.frame _ with
      | none => exact Or.inl rfl
      | some B =>
        rcases (SA.deepest_mem hd).1 with h | h
        · exact Or.inr h
        · exact Or.inl (Set.mem_singleton_iff.mp h)
    rcases he with he | h
    · exact he ▸ hR
    rcases SA.liveLockBlock_candidate hPhi h with hv | hb
    · exact hv
    · have he := Anc.antisymm hPhi.coherent hb hroot
      exact he ▸ hR
  obtain ⟨Q, hQ, hvQ, hLQ⟩ := hvL.2.2
  have hwin : sp.ts s₀ ≤ tr.time i ∧ tr.time i ≤ sp.ts N + sp.Δ :=
    ⟨hts.trans hlo, by linarith only [hhi, htN]⟩
  have hh : floor ≤ ((tr.state x i).fg.σ Q.root).h := by
    rw [← hframe.floor_eq x i hx hwin.1 hwin.2]
    rw [hfr] at hvQ
    exact hvQ.2.2.2
  have hJ : kindJ → Anc (tr.HonestBlocksAt H) J L := by
    intro hk
    have hki := (hframe.kind_iff x i hx hwin.1 hwin.2).mpr hk
    have hroot' := hroot.mono hPhiU'
    rw [hfr] at hroot'
    change Anc (tr.HonestBlocksAt H) (tr.state x i).fg.fcRoot L at hroot'
    have he : (tr.state x i).fg.fcRoot = (tr.state x i).fg.J := ite_eq_left hki
    rw [he, hframe.root_eq x i hx hwin.1 hwin.2 hk] at hroot'
    exact hroot'
  have hsub : FrameWindow tr H (sp.ts s) (sp.ts N + sp.Δ) floor kindJ J :=
    ⟨fun y j hy hl hh' => hframe.floor_eq y j hy (hts.trans hl) hh',
      fun y j hy hl hh' => hframe.kind_iff y j hy (hts.trans hl) hh',
      fun y j hy hl hh' => hframe.root_eq y j hy (hts.trans hl) hh'⟩
  exact optimistic_later_heads_of_early_witness_at hrun hnc hsvc hawake hf hcatch hnr hm hmb
    hsub hxa hop hLD hx (by linarith only [hhi, hΔ]) hc.1 hQ hh hJ (hLQ.mono hPhiU') hstock

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

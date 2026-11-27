module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFamily
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.SignCalendar
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.StockWindow
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.SignedTick
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FollowWrite
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowSigned
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RegularLater
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Outage
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.OutageCount
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ACProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AnchorPrefix
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Proposal report follow over the shadow run (interface)

The stock suppliers `proposal_report_follow_at` (`FollowEndpoint`) and
`proposal_report_follow_delayed_at` (`FollowSigned`), restated over `Growing.GoldilocksRun'` and
`Healing.FrameWindow' … M isTop J`. Their proofs compose `CandidateReport` (`Deep`), the
early-witness family (`WitnessFamily`) and the regular and optimistic later-head suppliers
(`FollowHeads`, `FollowWrite`, `RegularLater`). The later-head pair
(`toFG_later_proposal_head_after_at'`, `_within_at'`) is proved here from `RegularLater`'s
`regular_later_heads_at'` and `optimistic_write_later_proposal_head_at'`; it is unresolved while
those are. The two endpoints have no proof yet.

The milestone form reads the stock window (`Generic.FrameWindow … floor kindJ J`):
`proposal_report_follow_stock_at'` and `proposal_report_follow_delayed_stock_at'` reduce it to the
P-U window (`StockWindow`) in the J-kind and in a contest-free non-J-kind window; the remaining
case, a contest outside the J-kind, is open (the early-witness transfer reads a constant `h_max`
and top).

The signing calendar of a shadow run, `RunTrace.SignCalendarAt'`, is in `SignCalendar`. -/

namespace Consensus.Goldilocks.Shadow.PU.Growing

open AC (ACParams ReplayOrder Payload gbar)
open Consensus.Goldilocks.Healing.Growing (ResetService CatchRun NoRestartAfter
  CommitteeHalfUpTo)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro} {hold : Time}

/-- The actual candidate behind a report (`toFG_fast_candidate_origin_at` over the shadow run):
its own earlier fast write, or a deep candidate under a deep anchor whose live locks are slow. -/
private theorem toFG_fast_candidate_origin_at'
    {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode' sp ro)}
    {R : AC.Blk sp.n (List (FG.Att sp.n))} (hto : AC.ToFGAt tr.projAC y i ell R) :
    (∃ a < i, ∃ j ellw D CV, y ∈ H (tr.time a) ∧
      tr.projAC.CallAt y a ellw ∧ D ∈ ellw.frame.tree ∧
      AC.FastLockAt tr.projAC y a j D CV ∧
      Anc (tr.HonestBlocksAt H) R (ellw.frame.viableAncestor D)) ∨
    ∃ D a, sp.deepDepth = some D ∧
      AC.deepest ell.frame (AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i)) =
        none ∧
      AC.deepAnchor sp (tr.projAC.state y i) ell.frame (tr.time i) = some a ∧
      R ∈ AC.toFGDeepCandidates sp D a (tr.projAC.state y i) ell.frame (tr.time i) ∧
      ∀ l ∈ AC.liveLocks sp (tr.projAC.state y i).locks ell.frame (tr.time i),
        l.block = a.root → l.fast = false := by
  have hac := Compose.Growing.goldilocks_ac_projection_from' hrun hnc
  have hr := (hac.upTo (hrun.time_nonneg i)).localRun
  have hc := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hto.1⟩
  have hs := Trace.upTo_state tr.projAC y (d := tr.time i) (i := i)
    (fun k hk => hrun.time_mono hk.le)
  have hΦ := AC.frameIn_of_callAt hr hy hc
  have fast : ∀ l ∈ AC.liveLocks sp (tr.projAC.state y i).locks ell.frame (tr.time i),
      l.fast = true → ∀ Y ∈ ell.frame.tree, Y.root = l.block → ell.frame.Anc R Y →
      ∃ a < i, ∃ j ellw D CV, y ∈ H (tr.time a) ∧
        tr.projAC.CallAt y a ellw ∧ D ∈ ellw.frame.tree ∧
        AC.FastLockAt tr.projAC y a j D CV ∧
        Anc (tr.HonestBlocksAt H) R (ellw.frame.viableAncestor D) := by
    intro l hl hlf Y hY hYl hRY
    obtain ⟨l₀, hl₀, B, hB, hBr, _, heq⟩ := hl
    have hf₀ : l₀.fast = true := by rw [heq] at hlf; exact hlf
    have hl₀' : l₀ ∈ ((tr.projAC.upTo (tr.time i)).state y i).locks := by
      rwa [hs]
    obtain ⟨a, hai, ellw, D, ha, hD, ho, L, hL, hLr, hLA⟩ :=
      AC.lock_selection_candidate_provenance hr hrun.vstart hy i l₀ hl₀'
    have hRB : Anc (tr.HonestBlocksAt H) R B := by
      have he : Y = ell.frame.viableAncestor B := hΦ.1.coherent.1 hY
        (AC.viableAncestor_anc hΦ.1 hB).1 (hYl.trans (congrArg AC.Lock.block heq))
      rw [he] at hRY
      have hRB' : ell.frame.Anc R B := hRY.trans (AC.viableAncestor_anc hΦ.1 hB).2
      exact hRB'.mono hΦ.2
    obtain rfl : L = B := hac.localRun.coherent.1 hL (hΦ.2 hB) (hLr.trans hBr.symm)
    have hfast : ∃ CV, AC.FastLockAt (tr.projAC.upTo (tr.time i)) y a l₀.slot D CV := by
      rcases ho with ⟨_, CV, ho⟩ | ⟨hn, _⟩
      · exact ⟨CV, ho⟩
      · simp [hf₀] at hn
    obtain ⟨CV, ho⟩ := hfast
    exact ⟨a, hai, l₀.slot, ellw, D, CV, hrun.antitone (hrun.time_mono hai.le) hy,
      ((Trace.upTo_callAt tr.projAC).mp ha).2, hD,
      ((AC.upTo_fastLockAt hrun.time_mono).mp ho).2, hRB.trans hLA⟩
  obtain ⟨-, hRc | ⟨D, a, hD, ha, hn, hR⟩⟩ := AC.toFG_source (A := tr.projAC.state y i) hto.2.2
  · obtain ⟨hv, l, hl, hlr, hlf, _⟩ := hRc
    exact Or.inl (fast l hl hlf R hv.1 hlr.symm Relation.ReflTransGen.refl)
  · by_cases hslow : ∀ l ∈ AC.liveLocks sp (tr.projAC.state y i).locks ell.frame (tr.time i),
        l.block = a.root → l.fast = false
    · exact Or.inr ⟨D, a, hD, hn, ha, hR, hslow⟩
    · push Not at hslow
      obtain ⟨l, hl, hla, hlf⟩ := hslow
      have hat : a ∈ ell.frame.tree := (AC.deepest_mem ha).1.1
      exact Or.inl (fast l hl (by simpa using hlf) a hat hla.symm hR.2.1)

/-- The raw fast selection's block is no newer than its lock label (`fast_selection_slot_le`
over the static shadow run). -/
private theorem fast_selection_slot_le' {H₀ : Set (Fin sp.n)}
    {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : GoldilocksRun' proposer dg H₀ tr ini)
    (hnc : Compose.NoCollRun dg tr) {K : AC.CommitteeDict sp.n}
    (hPK : AC.CommitteeP K tr.projAC H₀)
    {x : Fin sp.n} (hx : x ∈ H₀) {a j : Nat}
    {D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (ho : AC.FastLockAt tr.projAC x a j D CV)
    (hcs2 : 2 * (K.committee j ∩ H₀ᶜ).ncard < sp.committeeSize) : D.slot ≤ j := by
  have hac := Compose.goldilocks_ac_projection_from' hrun hnc
  obtain ⟨y, hy, i, e, hv, hs, W, hW, hWr, hDW⟩ :=
    AC.fastLock_honest_vote hac K hPK hx ho hcs2
  obtain ⟨W', hW', hW'r, hWs⟩ := AC.honest_headU hac.toU hy hv
  obtain rfl : W' = W := hac.localRun.coherent.1 hW' hW (hW'r.trans hWr.symm)
  exact (Anc.slot_le hac.localRun.coherent hDW).1.trans (hWs.trans_eq hs)

/-- Frame blocks of an honest call are no newer than its slot (`frame_slot_le_at`). -/
private theorem frame_slot_le_at' {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode' sp ro)}
    (hc : tr.projAC.CallAt y i ℓ) : ∀ B ∈ ℓ.frame.tree, B.slot ≤ sp.slot (tr.time i) :=
  AC.frame_slot_leU sp (Shadow.PU.acRun_upTo' hrun hnc (hrun.time_nonneg i)).localRun.toU hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)

/-- **A later honest proposal head extends an actual report above a slot-`u` block**
(`FrameWindow.toFG_later_proposal_head_after_at` over the shadow run). -/
theorem toFG_later_proposal_head_after_at'
    {g ΔF b : Time} {s₀ u N M : Nat} {isTop : Prop}
    {J P R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s₀) (sp.ts N + sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hmb : sp.ts N + sp.Δ ≤ b)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode' sp ro)} (hto : AC.ToFGAt tr.projAC y i ell R)
    (hPs : P.slot = u) (hPR : Anc (tr.HonestBlocksAt H) P R)
    (hihi : tr.time i ≤ sp.ts N + sp.Δ)
    {r : Nat} (ht : tr.time i < sp.ts r) (hrN : r ≤ N)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c))
    {ellp : ACLabel (goldilocksNode' sp ro)} (hcp : tr.projAC.CallAt z c ellp)
    (hcall : ellp.call = .proposal) (hti : tr.time c = sp.ts r)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (AC.acProposal sp (tr.projAC.state z c) ellp.frame (tr.time c)).2 =
      some (d, pay)) (hK : CommitteeHalfUpTo tr H K g b) :
    Anc (tr.HonestBlocksAt H) R d.head := by
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hk := sp.two_le_k
  have hU := Coherence.honestBlocksAt_coherent' hrun hnc
  obtain ⟨a, hai, j, ellw, D, CV, hya, ha, hD, hfast, hRA⟩ | ⟨Dd, A, -, -, hanc, hRdeep, hslow⟩
    := toFG_fast_candidate_origin_at' hrun hnc hy hto
  swap
  · -- A deep source under a deep anchor whose live locks are slow (stock argument).
    have hi0 := hrun.time_nonneg i
    have hr := Shadow.PU.acRun_upTo' hrun hnc hi0
    obtain ⟨hΦ, hΦU⟩ := Shadow.PU.frameIn_at' hrun hnc hy hto.1
    obtain ⟨hRv, hRA, -, -⟩ := hRdeep
    obtain ⟨hAt, l, hl, hlA⟩ := (AC.deepest_mem hanc).1
    have hlf := hslow l hl hlA
    have hstate := Shadow.PU.projAC_upTo_state' hrun (y := y) (le_refl (tr.time i))
    have hwf : AC.LocksWF sp (tr.projAC.state y i).locks := by
      have h := AC.locksWF_state hr.localRun hr.vstart hy i
      rwa [hstate] at h
    have hslot := hwf.slot_le_of_live hl
    obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
    change sp.slot (tr.time i) ≤ l₀.slot + sp.k at hslot
    change l₀.fast = false at hlf
    obtain ⟨k, hki, D', ⟨ℓu, C, hu, hC, hD'⟩, L, hL, hLr, hLD⟩ :=
      AC.slow_lock_provenance hr.localRun hr.vstart hy i l₀ (hstate.symm ▸ hl₀) hlf
    obtain ⟨hkt, hu⟩ := (AC.upTo_updateAt hrun.time_mono).1 hu
    change tr.time k ≤ tr.time i at hkt
    have hs : (tr.projAC.upTo (tr.time i)).state y k = tr.projAC.state y k :=
      Trace.upTo_state _ y fun _ hq => (hrun.time_mono hq.le).trans hkt
    rw [hs] at hC hD'
    rw [Trace.upTo_time] at hD'
    have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono hi0
    obtain rfl : A = ell.frame.viableAncestor B₀ :=
      hΦ.coherent.1 hAt (AC.viableAncestor_anc hΦ hB₀).1 hlA.symm
    obtain rfl : B₀ = L := hU.1 (hΦU hB₀) (hsub hL) (hB₀r.trans hLr.symm)
    have hRD : Anc (tr.HonestBlocksAt H) R D' :=
      (Anc.mono hΦU (hRA.trans (AC.viableAncestor_anc hΦ hB₀).2)).trans (hLD.mono hsub)
    have hPR' := (Anc.slot_le hU hPR).1
    have hRs := frame_slot_le_at' hrun hnc hy hto.1 R hRv.1
    have hsr : l₀.slot + 2 ≤ r := by
      by_contra hn
      have hlo := hts (show r ≤ l₀.slot + 1 by omega)
      have hstep := AC.ts_succ l₀.slot (sp := sp)
      have hwrite : tr.time k = sp.ts l₀.slot + 6 * sp.Δ := hu.2.2.1
      push_cast at hstep hlo
      linarith only [hlo, hstep, hwrite, hkt, ht, sp.toParams.hΔ]
    exact hRD.trans ((Healing.PU.regular_later_heads_at' hframe hrun hnc hsvc hawake hf hcatch
      hnr (s := l₀.slot) (by omega) (by omega) (by omega) hm (by omega) hmb
      (hrun.antitone hkt hy) (Or.inr ⟨ℓu, C, hu, hC, hD'⟩) hK r (by omega) hrN).2 hsr
      z c ellp hz hcp hcall hti d pay hd)
  have hac := Compose.Growing.goldilocks_ac_projection_from' hrun hnc
  have hr := hac.upTo (hrun.time_nonneg a)
  have ha' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, ha⟩
  have hW := AC.frameIn_of_callAt hr.localRun hya ha'
  have hAD := (AC.viableAncestor_anc hW.1 hD).2.mono hW.2
  have hRD := hRA.trans hAD
  have hatime := hrun.time_mono hai.le
  have hfast' := (AC.upTo_fastLockAt (d := tr.time a) hrun.time_mono).mpr ⟨le_rfl, hfast⟩
  have hfast'' : AC.FastLockAt (tr.upTo (tr.time a)).projAC y a j D CV := by
    simpa only [RunTrace.upTo_projAC] using hfast'
  have hjtime : sp.ts j ≤ tr.time a := by
    rcases hfast with ⟨_, _, hu, _⟩ | ⟨_, _, _, hs, _⟩
    · have he : tr.time a = sp.ts j + 6 * sp.Δ := hu.2.2.1
      linarith only [he, sp.toParams.hΔ]
    · have hs' : sp.slot (tr.time a) = j := hs
      exact (AC.ts_le_iff_le_slot sp (hrun.time_nonneg a) _).2 (by rw [hs'])
  have hPD := (Anc.slot_le hac.localRun.coherent (hPR.trans hRD)).1
  have hs₀j : sp.ts s₀ ≤ sp.ts j := by
    have hDa := frame_slot_le_at' hrun hnc hya ha D hD
    have hsa : sp.slot (tr.time a) ≤ j + 1 := by
      rcases hfast with ⟨_, _, hu, _⟩ | ⟨_, _, _, hs, _⟩
      · have he : tr.time a = sp.ts j + 6 * sp.Δ := hu.2.2.1
        by_contra hn
        have h2 := (AC.ts_le_iff_le_slot sp (hrun.time_nonneg a) ((j + 2 : Nat) : Int)).2
          (by push_cast; omega)
        have h8 : sp.ts ((j + 2 : Nat) : Int) = sp.ts j + 8 * sp.Δ := by
          simp only [ACParams.ts]; push_cast; ring
        linarith only [he, h2, h8, sp.toParams.hΔ]
      · have hs' : sp.slot (tr.time a) = j := hs
        omega
    exact hts (by omega)
  have hDj := fast_selection_slot_le' (hrun.upTo (hrun.time_nonneg a)) (hnc.upTo _)
    (by
      rw [RunTrace.upTo_projAC]
      exact AC.CommitteePAt.upTo hrun.time_mono hrun.antitone hK.facts.hP _)
    hya hfast'' (hK.cs2 j (by linarith only [hm, hs₀j, sp.toParams.hΔ])
      (hjtime.trans (hatime.trans (hihi.trans hmb)))
      (tr.time a) (hrun.time_nonneg a) (hatime.trans (hihi.trans hmb)))
  have hjlo : u ≤ j := by omega
  have hjr : j < r := by
    by_contra hn
    exact (not_lt_of_ge ((hts (by omega : r ≤ j)).trans (hjtime.trans hatime))) ht
  rcases hfast with hreg | hopt
  · have hjr₂ : j + 2 ≤ r := by
      by_contra hn
      have hlo := hts (show r ≤ j + 1 by omega)
      have hstep := AC.ts_succ j (sp := sp)
      obtain ⟨_, _, hu, _⟩ := hreg
      have hwrite : tr.time a = sp.ts j + 6 * sp.Δ := hu.2.2.1
      push_cast at hstep hlo
      linarith only [hlo, hstep, hwrite, hatime, ht, sp.toParams.hΔ]
    exact hRD.trans ((Healing.PU.regular_later_heads_at' hframe hrun hnc hsvc hawake hf hcatch
      hnr (by omega) (by omega) (by omega) hm (by omega) hmb hya
      (Or.inl ⟨CV, hreg⟩) hK r (by omega) hrN).2 (by omega) z c ellp hz hcp hcall hti d pay
      hd)
  · have halo : sp.ts s₀ ≤ tr.time a := hs₀j.trans hjtime
    have ho := (AC.upTo_optimisticLockAt hrun.time_mono).mpr ⟨le_rfl, hopt⟩
    have hat := (AC.optimisticLockAt_spec hr hya ho (AC.CommitteeDict.full sp.n)
      (fun _ _ _ => AC.mem_full _ _)).1
    apply optimistic_write_later_proposal_head_at' hframe hrun hnc hsvc hawake hf hcatch hnr
      (by linarith only [hm, sp.toParams.hΔ]) hmb (by omega) hya ha halo hat hopt hRA hAD
      ?_ (by omega) hrN hz hcp hcall hti hd hK
    rcases (AC.viableAncestor_spec hW.1 hD).2.1 with hbelow | hAv
    · have hfe : ellw.frame.fcRoot = ellw.frame.F := by
        rw [frame_of_projAC_at' hrun hya ha, Node.frame'_eq, Store.toFrame'_fcRoot,
          Store.toFrame'_F]
      exact Or.inl (by rw [← hfe]; exact hbelow)
    · obtain ⟨Q, hQ, hvQ, hAQ⟩ := hAv.2.2
      exact Or.inr ⟨Q, hvQ, hAQ⟩

/-- Reports up to `e` slots after `t_{u+1} + 2Δ` precede proposals from slot `u + 3 + e`
(`FrameWindow.toFG_later_proposal_head_within_at` over the shadow run). -/
theorem toFG_later_proposal_head_within_at'
    {g ΔF b : Time} {s₀ u N M e : Nat} {isTop : Prop}
    {J P R : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s₀) (sp.ts N + sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hmb : sp.ts N + sp.Δ ≤ b)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode' sp ro)} (hto : AC.ToFGAt tr.projAC y i ell R)
    (hPs : P.slot = u) (hPR : Anc (tr.HonestBlocksAt H) P R)
    (hihi : tr.time i ≤ sp.ts N + sp.Δ)
    (ht : tr.time i ≤ sp.ts (u + 1 + e : Nat) + 2 * sp.Δ)
    {r : Nat} (hrlo : u + 3 + e ≤ r) (hrN : r ≤ N)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c))
    {ellp : ACLabel (goldilocksNode' sp ro)} (hcp : tr.projAC.CallAt z c ellp)
    (hcall : ellp.call = .proposal) (hti : tr.time c = sp.ts r)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (AC.acProposal sp (tr.projAC.state z c) ellp.frame (tr.time c)).2 =
      some (d, pay)) (hK : CommitteeHalfUpTo tr H K g b) :
    Anc (tr.HonestBlocksAt H) R d.head := by
  have hlo : sp.ts (u + 1 + e + 1 : Nat) ≤ sp.ts r :=
    (AC.ts_le_iff sp).2 (by push_cast; omega)
  have hstep := AC.ts_succ (u + 1 + e) (sp := sp)
  have hlt : tr.time i < sp.ts r := by
    push_cast at hlo hstep ht
    linarith only [ht, hlo, hstep, sp.toParams.hΔ]
  exact toFG_later_proposal_head_after_at' hframe hrun hnc hsvc hawake hf hcatch hnr hm hwarm
    hmb hy hto hPs hPR hihi hlt hrN hz hcp hcall hti hd hK

/-- At a public signing time after a warm update deadline, a node honest then executes a joined
`ac_to_fg` call (`toFG_call_of_sign_at` over the shadow run and its calendar). -/
theorem toFG_call_of_sign_at' {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {g : Time} (hnr : NoRestartAfter tr H (gbar g))
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt' proposer dg H sign)
    {y : Fin sp.n} {t : Time} {u : Nat} (hy : y ∈ H t) (hgu : gbar g ≤ sp.ts u)
    (ht : sp.ts u + 6 * sp.Δ ≤ t) (hpub : sp.toParams.IsPublic t) (hawake : tr.awake y t)
    (hsign : sign y t = true) :
    ∃ i ell, tr.projAC.CallAt y i ell ∧ ell.call = .toFG ∧ tr.time i = t ∧
      AC.joined sp (tr.projAC.state y i) (tr.time i) := by
  have hΔ := sp.toParams.hΔ
  have ht0 : 0 ≤ t := by
    have hu0 : 0 ≤ sp.ts u := by simp only [ACParams.ts]; positivity
    linarith
  obtain ⟨j, hj⟩ := signTickAt_of_calendar_at' hrun hcal hy ht0 hpub hawake hsign
  obtain ⟨x, hg⟩ := (RunTrace.signTickAt'_iff tr proposer dg y j t).1 hj
  obtain ⟨k, ell, hc, hcall, htime⟩ := Healing.toFG_call_of_signing_tick' hg
  exact ⟨j + k, ell, hc, hcall, htime, joined_of_restart_le_at' hrun hnc hy (by linarith)
    (fun r _ hyr hrs => (hnr y r hyr hrs).trans hgu) htime⟩

/-- A block of an honest frame above a non-genesis block is not genesis
(`root_ne_genesis_of_anc` over the shadow run). -/
private theorem root_ne_genesis_of_anc' {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode' sp ro)} (hc : tr.projAC.CallAt y i ell)
    {P B : AC.Blk sp.n (List (FG.Att sp.n))} (hPg : P.root ≠ sp.genesisRoot)
    (hPB : Anc (tr.HonestBlocksAt H) P B) (hB : B ∈ ell.frame.tree) :
    B.root ≠ sp.genesisRoot := by
  intro hg
  have hr := (Compose.goldilocks_ac_projection_from' (hrun.upTo (hrun.time_nonneg i))
    (hnc.upTo (tr.time i))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc' : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc⟩
  obtain ⟨G, hGU, hGr, hGp⟩ := AC.genesis_mem_of_callU sp hr.toU hy _ _ hc'
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono (hrun.time_nonneg i)
  have hU := Coherence.honestBlocksAt_coherent' hrun hnc
  have hBU : B ∈ tr.HonestBlocksAt H := hsub ((AC.frameIn_of_callAt hr hy hc').2 hB)
  obtain rfl : B = G := hU.1 hBU (hsub hGU) (hg.trans hGr.symm)
  rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hPB with h | ⟨c, -, hcG⟩
  · exact hPg (by rw [← h]; exact hg)
  · simp [hcG.2.2] at hGp

/-- **The fresh candidate yields an actual report**, followed by later honest proposal heads
(`proposal_report_follow_at` over the shadow run). -/
theorem proposal_report_follow_at'
    {g ΔF b : Time} {s₀ u N M : Nat} {isTop : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt' proposer dg H sign)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ))
    (hsign : sign y (sp.ts (u + 1 : Nat) + 2 * sp.Δ) = true)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ i ell R, y ∈ H (tr.time i) ∧ AC.ToFGAt tr.projAC y i ell R ∧
      sp.ts u ≤ tr.time i ∧ tr.time i ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ ∧
      Anc (tr.HonestBlocksAt H) P R ∧
      ∀ x, u + 3 ≤ x → x ≤ N → ∀ w c ellp, w ∈ H (tr.time c) →
        tr.projAC.CallAt w c ellp → ellp.call = .proposal → tr.time c = sp.ts x →
        ∀ d pay, (AC.acProposal sp (tr.projAC.state w c) ellp.frame (tr.time c)).2 =
          some (d, pay) → Anc (tr.HonestBlocksAt H) R d.head := by
  sorry

/-- **The delayed report follow** at signing gap `G` (`proposal_report_follow_delayed_at` over the
shadow run). -/
theorem proposal_report_follow_delayed_at'
    {g ΔF b t₀ : Time} {s₀ u N M G : Nat} {isTop : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Healing.FrameWindow' tr H (sp.ts s₀)
      (max (sp.ts N + 2 * sp.Δ) (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ))
      M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N)
    (hmb : max (sp.ts N + 2 * sp.Δ) (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ) ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt' proposer dg H sign)
    (hgap : SignGapAt sp.toParams sign G t₀) (ht₀ : t₀ ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ))
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ i ell R, y ∈ H (tr.time i) ∧ AC.ToFGAt tr.projAC y i ell R ∧
      sp.ts u ≤ tr.time i ∧ tr.time i ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ ∧
      Anc (tr.HonestBlocksAt H) P R ∧
      ∀ x, u + 3 + (G + 3) / 4 ≤ x → x ≤ N → ∀ w c ellp, w ∈ H (tr.time c) →
        tr.projAC.CallAt w c ellp → ellp.call = .proposal → tr.time c = sp.ts x →
        ∀ d pay, (AC.acProposal sp (tr.projAC.state w c) ellp.frame (tr.time c)).2 =
          some (d, pay) → Anc (tr.HonestBlocksAt H) R d.head := by
  sorry

/-- **The report follow over the stock window** (`proposal_report_follow_at` with the shadow
run): the stock window's J-kind, or its non-J-kind without a contest, is a P-U window
(`StockWindow`), where `proposal_report_follow_at'` applies. -/
theorem proposal_report_follow_stock_at'
    {g ΔF b : Time} {s₀ u N floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt' proposer dg H sign)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ))
    (hsign : sign y (sp.ts (u + 1 : Nat) + 2 * sp.Δ) = true)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ i ell R, y ∈ H (tr.time i) ∧ AC.ToFGAt tr.projAC y i ell R ∧
      sp.ts u ≤ tr.time i ∧ tr.time i ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ ∧
      Anc (tr.HonestBlocksAt H) P R ∧
      ∀ x, u + 3 ≤ x → x ≤ N → ∀ w c ellp, w ∈ H (tr.time c) →
        tr.projAC.CallAt w c ellp → ellp.call = .proposal → tr.time c = sp.ts x →
        ∀ d pay, (AC.acProposal sp (tr.projAC.state w c) ellp.frame (tr.time c)).2 =
          some (d, pay) → Anc (tr.HonestBlocksAt H) R d.head := by
  by_cases hk : kindJ
  · exact proposal_report_follow_at' (Healing.toFrameWindow'_of_kind hframe hk)
      hrun hnc hsvc hawake hf hcatch hnr hm hwarm hN hmb hz hdes hP hPs hcal hy hsign hK
  by_cases hnoC : ∀ y i, y ∈ H (tr.time i) → sp.ts s₀ ≤ tr.time i →
      tr.time i ≤ sp.ts N + 2 * sp.Δ → ¬ (tr.state y i).fg.Contest
  · exact proposal_report_follow_at' (Healing.toFrameWindow'_of_noContest hrun hframe hk hnoC)
      hrun hnc hsvc hawake hf hcatch hnr hm hwarm hN hmb hz hdes hP hPs hcal hy hsign hK
  -- A contest outside the J-kind: `h_max` and the top are not constant in the window, and the
  -- early-witness transfer (`Healing.witness_frame_at'`) reads both. Unresolved.
  sorry

/-- **The delayed report follow over the stock window** (`proposal_report_follow_delayed_at`
with the shadow run), by the same reduction to `proposal_report_follow_delayed_at'`. -/
theorem proposal_report_follow_delayed_stock_at'
    {g ΔF b t₀ : Time} {s₀ u N floor G : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s₀)
      (max (sp.ts N + 2 * sp.Δ) (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ))
      floor kindJ J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N)
    (hmb : max (sp.ts N + 2 * sp.Δ) (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ) ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {sign : Fin sp.n → Time → Bool} (hcal : tr.SignCalendarAt' proposer dg H sign)
    (hgap : SignGapAt sp.toParams sign G t₀) (ht₀ : t₀ ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ))
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ i ell R, y ∈ H (tr.time i) ∧ AC.ToFGAt tr.projAC y i ell R ∧
      sp.ts u ≤ tr.time i ∧ tr.time i ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ ∧
      Anc (tr.HonestBlocksAt H) P R ∧
      ∀ x, u + 3 + (G + 3) / 4 ≤ x → x ≤ N → ∀ w c ellp, w ∈ H (tr.time c) →
        tr.projAC.CallAt w c ellp → ellp.call = .proposal → tr.time c = sp.ts x →
        ∀ d pay, (AC.acProposal sp (tr.projAC.state w c) ellp.frame (tr.time c)).2 =
          some (d, pay) → Anc (tr.HonestBlocksAt H) R d.head := by
  by_cases hk : kindJ
  · exact proposal_report_follow_delayed_at' (Healing.toFrameWindow'_of_kind hframe hk)
      hrun hnc hsvc hawake hf hcatch hnr hm hwarm hN hmb hz hdes hP hPs hcal hgap ht₀ hy hK
  by_cases hnoC : ∀ y i, y ∈ H (tr.time i) → sp.ts s₀ ≤ tr.time i →
      tr.time i ≤ max (sp.ts N + 2 * sp.Δ) (sp.ts (u + 1 : Nat) + 2 * sp.Δ + (G : Time) * sp.Δ) →
      ¬ (tr.state y i).fg.Contest
  · exact proposal_report_follow_delayed_at'
      (Healing.toFrameWindow'_of_noContest hrun hframe hk hnoC)
      hrun hnc hsvc hawake hf hcatch hnr hm hwarm hN hmb hz hdes hP hPs hcal hgap ht₀ hy hK
  -- A contest outside the J-kind: `h_max` and the top are not constant in the window, and the
  -- early-witness transfer (`Healing.witness_frame_at'`) reads both. Unresolved.
  sorry

end Consensus.Goldilocks.Shadow.PU.Growing

end

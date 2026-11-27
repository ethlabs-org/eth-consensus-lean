module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SelectionCompatibility
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SelectionCover
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SelectionPool
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UnanimousPool
public import
    ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.OperationalReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CandidateReport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HigherReports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HeldRoots
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierViews
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RootProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.ProposalFrame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.ProposalViable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.StopAtParent
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.SuffixBest
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.CallLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Pivot
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UpdateCalls
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SignedToFG
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Timing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HeldRoots
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.OperationalReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting

import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesRelay

public section

/-! # Reports above a unanimous slot, under growing faults

`report_cover_of_unanimous_at`, the growing form of `Obligations.UpTo.report_cover_of_unanimous`:
after the drain, every node honest at the update deadline `t_u + 6Δ` of a unanimous slot `u` reports
a descendant of its proposal `P` by then, unless a node honest at its report and at `c_z` already
reports a strictly higher descendant. Each node is honest at its own cut, and a held state is read
at a time after the state's cuts.

The update of the node honest at `t_u + 6Δ` holds `P` (`unanimous_head_held_at_call_at`), with
finality below `P` (`finality_alternative_before_update_at`), in its full viable tree
(`unanimous_viable_or_higher_report_at`, `held_target_viable_or_higher_report_covered_at`). Its pool
counts every validator honest at the update, so it confirms `P` and reports it at the adjacent
`ac_to_fg` call (`report_of_viable_unanimous_pool_at`).

The unanimous-slot selection helpers are imported from their growing proof homes. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-! ### Calls of a node honest at them -/

/-- The frame of an AC call of a node honest at it is its store's frame. -/
private theorem frame_eq_at {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ℓ) : ℓ.frame = Node.frame (tr.state y k) := by
  have hc' : (tr.upTo (tr.time k)).projAC.CallAt y k ℓ := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hc
  rw [Compose.frame_of_projAC (hrun.upTo (hrun.time_nonneg k)) hy hc',
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl]

/-- The cuts before `k` are at or before `tr.time k`. -/
private theorem before_cut {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (k : Nat) : ∀ q < k, tr.time q ≤ tr.time k := fun _ hq => hrun.time_mono hq.le

/-- An AC call frame of a node honest at it lies in the blocks held while honest. -/
private theorem frame_subset_at {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y k ℓ) :
    ℓ.frame.tree ⊆ tr.HonestBlocksAt H := fun _ hX =>
  ⟨y, k, tr.time k, hrun.time_nonneg k, before_cut hrun k, hy,
    (frame_tree_subset_at hrun hnc hy hc).2 hX⟩

/-! ### The held target at the update -/

/-- **The unanimous head is held at a later call** of a node honest at it, when the call's finality
is below the head: the node's own slot-`u` vote names `P`, held from then on. -/
theorem unanimous_head_held_at_call_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b) (hFP : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F P) :
    P ∈ ell.frame.tree := by
  have hrun := hp.run
  have hΔ := sp.toParams.hΔ
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hub : sp.ts u + sp.Δ ≤ b := by linarith
  -- an honest member of the slot-`u` committee votes for `P` by `t_u + Δ`
  obtain ⟨w, hwK, hw⟩ := hp.committee_honest_nonempty_at (s := u) (by linarith)
    (by linarith) (by linarith [AC.gbar_nonneg g]) hub
  obtain ⟨q, e, ⟨ellv, hv⟩, hs, hq⟩ := honest_votes_in_slot_at hp hgu hR hub w hw hwK
  have hwq : w ∈ H (tr.time q) := hrun.antitone hq hw
  have hd := hrun.time_nonneg q
  have hr := (Compose.goldilocks_ac_projection_from (hrun.upTo hd) (hp.noColl.upTo _)).localRun
  have hv' : AC.CastAt (tr.upTo (tr.time q)).projAC w q ellv e := by
    rw [RunTrace.upTo_projAC]
    exact ⟨(Trace.upTo_callAt_of_le _ le_rfl).mpr hv.1, hv.2⟩
  obtain ⟨⟨Hd, hHd, he, _⟩, _⟩ :=
    Compose.cast_head_fcRoot hr (hrun.upTo hd).vstart hwq hv'
  obtain rfl : Hd = P := hU.1 (frame_subset_at hrun hp.noColl hwq hv.1 hHd) hP
    (he.trans (hun w q e hwq ⟨ellv, hv⟩ (hq.trans hub) hs))
  -- the voter's frame relays `P` to the caller
  have hF : Anc (tr.HonestBlocksAt H) ell.frame.F Hd := by
    rw [frame_eq_at hrun hy hcall]
    exact hFP
  exact frame_relay_before_at hrun hp.noColl hp.sync hp.catchUp hwq hy
    (fun r hrj hrs => hp.noRestart y r (hrun.antitone (hrun.time_mono hrj) hy) hrs
      ((hrun.time_mono hrj).trans hjb)) hv.1 hcall hHd (by linarith) (by linarith) hF

/-- The viability alternative, given the high-height root comparison and the higher report below
the head-height floor. -/
private theorem held_target_viableHeads_or_higher_report_of_cases
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    (hib : tr.time i ≤ b) {P S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ (Node.frame (tr.state y i)).tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hhighroot : ¬ (tr.state y i).fg.hj ≤ HZ tr H g →
      Compatible (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).fcRoot P)
    (hfloorrep : ((tr.state y i).fg.σ P.root).h < (tr.state y i).fg.headHeightFloor →
      ∃ x r ell' C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
        AC.ToFGAt tr.projAC x r ell' C ∧ Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) :
    (P ∈ (Node.frame (tr.state y i)).tree ∧
      (Node.frame (tr.state y i)).Anc (Node.frame (tr.state y i)).fcRoot P ∧
      P ∈ (Node.frame (tr.state y i)).viableHeads) ∨
      ∃ x r ell' C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
        AC.ToFGAt tr.projAC x r ell' C ∧ Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  have hrun := hp.run
  have hy := hrun.antitone (le_max_right _ _) hyz
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hd := hrun.time_nonneg i
  have hle := before_cut hrun i
  have hPhi := (Store.frame_realization _ _ _ _ (fg_reachable_at hrun hd hle hy)).1
  have hPhiU : (Node.frame (tr.state y i)).tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => ⟨y, i, tr.time i, hd, hle, hy, hX.1⟩
  have hPy := hPt.1
  have hcz := ProposalImpl.cutZ_lt_of_anc_at hp hseed (by rwa [max_comm]) hPy hSP
  have hroot : Compatible (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).fcRoot P := by
    by_cases hlow : (tr.state y i).fg.hj ≤ HZ tr H g
    · exact hp.low_root_of_held_seed_at hy hib hseed hqb
        (mem_of_honest_anc_at hrun hp.noColl hd hle hy hSP hPy) hlow (Or.inr hSP)
        (fun _ => hPt)
    · exact hhighroot hlow
  by_cases hrootP : Anc (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).fcRoot P
  · by_cases hfloor : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ P.root).h
    · have hrootf := AC.anc_tree_of_anc_U hU hPhi hPhiU hPhi.fcRoot_mem hrootP hPt
      exact Or.inl ⟨hPt, hrootf, hPy, hPt.2,
        hrootf.mono (fun X hX => hX.1), hfloor⟩
    · exact Or.inr (hfloorrep (lt_of_not_ge hfloor))
  · have hPR := hroot.resolve_left hrootP
    have hne : P ≠ (Node.frame (tr.state y i)).fcRoot := fun he => hrootP (he ▸ .refl)
    have hJ : (Node.frame (tr.state y i)).fcRoot = (tr.state y i).fg.J := by
      have hFP := (hPhi.rooted.2 P hPt).mono hPhiU
      change ¬ Anc (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot P at hrootP
      change Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F P at hFP
      change (tr.state y i).fg.fcRoot = _
      unfold Store.fcRoot at hrootP ⊢
      split_ifs at hrootP ⊢ with hactive
      · rfl
      · exact False.elim (hrootP hFP)
    have hf : (H (tr.time i))ᶜ.ncard < sp.toParams.fg.q := by
      have hf := hp.faults _ hd hib
      have hn : 0 < sp.n := sp.toParams.hn
      change (H (tr.time i))ᶜ.ncard < (2 * sp.n + 2) / 3
      omega
    obtain ⟨x, hx, r, hri, d, _, att, ell', C, _, _, _, _, hto, _, hJx, hJC, _, hCh, hPh⟩ :=
      cache_ahead_report_at hrun hp.noColl hy hf (Or.inr hJ) hPy hPR hne
    have hxle : ∀ k < r, tr.time k ≤ tr.time i := fun k hk => hrun.time_mono (by omega)
    have hPx := mem_of_honest_anc_at hrun hp.noColl hd hxle hx hPR hJx
    have hσ := σ_eq_honest_at hrun hp.noColl hd hle hy hd hxle hx hPy hPx
    exact Or.inr ⟨x, r, ell', C,
      hrun.antitone (max_le hcz.le (hrun.time_mono hri.le)) hx, hri, hto,
      hPR.trans hJC, by rw [← hσ, hCh]; exact hPh⟩

/-- **A held target above a high seed is fully viable, or an earlier strictly higher report
extends it**, for a target compatible with the earlier high origins and, under the high-source
cover, the healed members up to the slot of the cut written before it. -/
theorem held_target_viableHeads_or_higher_report_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    (hib : tr.time i ≤ b) {P S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ (Node.frame (tr.state y i)).tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hcompare : ResetPremisesUpTo.CompatibleWithOrigins tr H g a b i (sp.slot (tr.time i)) P) :
    (P ∈ (Node.frame (tr.state y i)).tree ∧
      (Node.frame (tr.state y i)).Anc (Node.frame (tr.state y i)).fcRoot P ∧
      P ∈ (Node.frame (tr.state y i)).viableHeads) ∨
      ∃ x r ell' C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
        AC.ToFGAt tr.projAC x r ell' C ∧ Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h :=
  have hy := hp.run.antitone (le_max_right _ _) hyz
  have hrun := hp.run
  held_target_viableHeads_or_higher_report_of_cases hp hyz hib hPt hseed hqb hSP
    (fun _ => hp.high_J_root_of_held_before_covered_at hy hPt.1 hy hib (by omega) hcompare)
    (fun hfl => hp.held_target_high_floor_report_before_covered_at hy hib hPt.1 hseed hSP
      (fun x r l B hri ho x' r' l' B' hr'i ho' => hp.origins_compatible_at ho
        ((hrun.time_mono hri.le).trans hib) ho' ((hrun.time_mono hr'i.le).trans hib))
      (fun x r l B hri ho => hp.origins_compatible_at hseed hqb ho
        ((hrun.time_mono hri.le).trans hib)) hcompare hfl)

/-- The any-cut viability alternative read through the frame of an AC call, for a target
compatible with the earlier high origins and, under the high-source cover, the healed members up
to the slot of the cut. -/
theorem held_target_viable_or_higher_report_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    {ell : ACLabel (goldilocksNode sp ro)} (hcall : tr.projAC.CallAt y i ell)
    (hib : tr.time i ≤ b) {P S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hPt : P ∈ ell.frame.tree) (hseed : HighOrigin tr H g v q m S)
    (hqb : tr.time q ≤ b) (hSP : Anc (tr.HonestBlocksAt H) S P)
    (hcompare : ResetPremisesUpTo.CompatibleWithOrigins tr H g a b i (sp.slot (tr.time i)) P) :
    P ∈ ell.frame.viableTree ell.frame.tree ∨
      ∃ x r ell' C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < i ∧
        AC.ToFGAt tr.projAC x r ell' C ∧ Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  rw [frame_eq_at hp.run (hp.run.antitone (le_max_right _ _) hyz) hcall] at hPt ⊢
  rcases held_target_viableHeads_or_higher_report_covered_at hp hyz hib hPt hseed hqb hSP
      hcompare with ⟨hPt, hroot, hhead⟩ | hreport
  · exact Or.inl ⟨hPt, hroot, P, hPt, hhead, .refl⟩
  · exact Or.inr hreport

/-- **At the update deadline, finality below the unanimous head gives full viability or an
earlier higher report**: the update of a node honest at `t_u + 6Δ` holds `P`, above a reset seed
and compatible with every earlier high origin. -/
theorem unanimous_viable_or_higher_report_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocksAt H)
    (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)} (hcall : tr.projAC.CallAt y j ell)
    (ht : tr.time j = sp.ts u + 6 * sp.Δ)
    (hFP : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F P) :
    P ∈ ell.frame.viableTree ell.frame.tree ∨
      ∃ x r e C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < j ∧
        AC.ToFGAt tr.projAC x r e C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
        Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  have hjb : tr.time j ≤ b := ht ▸ hTb
  have hcz : cutZ sp.toParams g ≤ tr.time j := by
    have hk := sp.two_le_k
    have hts := hp.clean_window_timing_at (s := u) (by
      rw [Healing.cleanLabel_eq]
      rw [Healing.drainTime_eq] at hR
      have := (AC.ts_le_iff sp).1 hR
      push_cast at this
      omega) u (by omega)
    rw [ht]
    linarith [sp.toParams.hΔ]
  have hPt := unanimous_head_held_at_call_at hp hP hun hgu hR hy hcall
    (by rw [ht]; linarith [sp.toParams.hΔ]) hjb hFP
  obtain ⟨v, q, m, S, ho, hqb, _, hqt⟩ := hp.reset_seed_before_slot_at hR
  have hSP := high_origins_before_next_slot_below_at hp hP hun hgu hR
    (by linarith [sp.toParams.hΔ]) ho hqt hqb
  have hslotj : sp.slot (tr.time j) = u + 1 := by
    rw [ht]
    apply AC.slot_of_mem sp (u + 1)
    · simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ]
    · simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ]
  have hcompare : ResetPremisesUpTo.CompatibleWithOrigins tr H g a b j (sp.slot (tr.time j)) P :=
    ResetPremisesUpTo.compatibleWithOrigins_iff.2
      ⟨fun x r l B hrj horig =>
        (high_origin_compatible_before_update_at hp hP hslot hu hun hgu hR hTb
          horig ((hp.run.time_mono hrj.le).trans ht.le)).symm,
      fun hc D l hD hl =>
        (healed_member_compatible_before_update_at hp hc hP hslot hu hun hgu hR hTb D l
          hD.healedOrigin (by omega)).symm⟩
  rcases held_target_viable_or_higher_report_covered_at hp (by rwa [max_eq_right hcz]) hcall
      hjb hPt ho hqb hSP hcompare with
    hv | ⟨x, r, e, C, hx, hrj, hto, hPC, hh⟩
  · exact Or.inl hv
  · exact Or.inr ⟨x, r, e, C, hx, hrj, hto, (hp.run.time_mono hrj.le).trans ht.le, hPC, hh⟩

/-- **Finite deadline alternative**: finality at a cut after the reset, by the update deadline, is
below `P`, or an earlier report extends `P` with a strictly greater height. -/
theorem finality_alternative_before_update_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocksAt H)
    (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    (ha : a ≤ tr.time k) (ht : tr.time k ≤ sp.ts u + 6 * sp.Δ) :
    Anc (tr.HonestBlocksAt H) (tr.state y k).fg.F P ∨
      ∃ z r ell C, z ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ r < k ∧
        AC.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
        Anc (tr.HonestBlocksAt H) P C ∧
        ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h := by
  rcases hp.finality_below_or_higher_report_at hy (ht.trans hTb)
      (finalized_compatible_before_update_at hp hP hslot hu hun hgu hR hTb hy ha ht) with
    h | ⟨z, r, ell, C, hz, hrk, hto, hPC, hlt⟩
  · exact Or.inl h
  · exact Or.inr ⟨z, r, ell, C, hz, hrk, hto, (hp.run.time_mono hrk.le).trans ht, hPC, hlt⟩

/-! ### The report -/

/-- **A full viable unanimous pool at an update gives a report** at or before the adjacent
`ac_to_fg` call, for a node honest at the update. -/
theorem report_of_viable_unanimous_pool_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {j u : Nat} (hy : y ∈ H (tr.time j)) (hjb : tr.time j ≤ b)
    {ell ell' : ACLabel (goldilocksNode sp ro)} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hu : AC.UpdateAt tr.projAC y j u ell)
    (hc : tr.projAC.CallAt y (j + 1) ell') (hto : ell'.call = .toFG)
    (hframe : ell'.frame = ell.frame) (htime : tr.time (j + 1) = tr.time j)
    (hjoin : AC.joined sp (tr.projAC.state y (j + 1)) (tr.time (j + 1)))
    (hPg : P.root ≠ sp.genesisRoot) (hPv : P ∈ ell.frame.viableTree ell.frame.tree)
    (hgu : AC.gbar g ≤ sp.ts u)
    (hpool : ∀ v, v ∈ H (tr.time j) → v ∈ (Generic.dictOfTime sp cm).committee u →
      ∃ vote ∈ (tr.projAC.state y j).pool u,
      vote.val = v ∧ vote.head = P.root ∧
      AC.resolutionTime (tr.projAC.state y j) ell.frame vote < AC.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ vote' ∈ (tr.projAC.state y j).pool u, vote'.val = v → vote' = vote)
    (hlocks : ∀ L ∈ AC.liveLockBlocks sp (tr.projAC.state y j).locks ell.frame (tr.time j),
      Compatible (tr.HonestBlocksAt H) L P)
    (hnext : ∀ C ∈ AC.toFGCandidates sp (tr.projAC.state y (j + 1)) ell'.frame (tr.time (j + 1)),
      Compatible (tr.HonestBlocksAt H) C P)
    (hlive : sp.slot (tr.time j) ≤ u + sp.k) (hage : sp.slot (tr.time j) ≤ u + 2) :
    ∃ r e R, AC.ToFGAt tr.projAC y r e R ∧ tr.time r ≤ tr.time (j + 1) ∧
      Anc (tr.HonestBlocksAt H) P R := by
  obtain ⟨hconf, hnv, hfast, hpost, _⟩ :=
    hp.ready_update_selection_of_pool_at hy hjb hgu hu hPv.1 hPg hpool hlocks
  have hr := (Compose.goldilocks_ac_projection_from
    (hp.run.upTo (hp.run.time_nonneg j)) (hp.noColl.upTo (tr.time j))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hwf := AC.locksWF_state hr hp.run.vstart hy j
  rw [Trace.upTo_state tr.projAC y (fun _ hq => hp.run.time_mono hq.le)] at hwf
  have hPc := Obligations.UpTo.candidate_at_adjacent_call hu.1
    (frame_tree_subset_at hp.run hp.noColl hy hu.1).1 hframe htime hPv hconf hnv hfast hpost
    hlive hage (fun l hl => hwf.cap hl)
  exact report_of_compatible_candidate_of_run_at hp.run hp.noColl (htime ▸ hy) hc hto hjoin hPg
    hPc hnext

/-- **The report at the update deadline**, for a node honest there with adjacent joined update
and `ac_to_fg` calls: it reports a descendant of `P` by `t_u + 6Δ`, or a node honest at its
report and at `c_z` reports a strictly higher descendant of `P` by then. -/
theorem report_at_update_of_unanimous_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) {y : Fin sp.n} (hy : y ∈ H (sp.ts u + 6 * sp.Δ))
    {j : Nat} {ell ell' : ACLabel (goldilocksNode sp ro)} (hup : AC.UpdateAt tr.projAC y j u ell)
    (hto : tr.projAC.CallAt y (j + 1) ell') (htoeq : ell'.call = .toFG)
    (hnexttime : tr.time (j + 1) = sp.ts u + 6 * sp.Δ) (hframe : ell'.frame = ell.frame)
    (hjoined : AC.joined sp (tr.projAC.state y (j + 1)) (tr.time (j + 1))) :
    (∃ r e R, AC.ToFGAt tr.projAC y r e R ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P R) ∨
    (∃ x r e C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ AC.ToFGAt tr.projAC x r e C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) := by
  by_cases hescape : ∃ x r e C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧
      AC.ToFGAt tr.projAC x r e C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h
  · exact Or.inr hescape
  left
  have hrun := hp.run
  have hd := sp.toParams.hΔ
  have hub : sp.ts u + sp.Δ ≤ b := by linarith only [hTb, hd]
  have hjtime : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  have hyj : y ∈ H (tr.time j) := hjtime ▸ hy
  have hyj' : y ∈ H (tr.time (j + 1)) := hnexttime ▸ hy
  have hjb : tr.time j ≤ b := hjtime ▸ hTb
  have hnextb : tr.time (j + 1) ≤ b := hnexttime ▸ hTb
  have hRT : drainTime sp a ≤ sp.ts u + 6 * sp.Δ := by
    simp only [AC.ACParams.ts] at hR ⊢
    push_cast at hR ⊢
    linarith only [hR, hd]
  have hca := hp.cutZ_lt_reset_at
  have ha0 : 0 ≤ a := by
    have h1 := Healing.lt_cutZ sp g
    have h2 := AC.gbar_nonneg g
    linarith only [h1, h2, hca, hd]
  have haT : a ≤ sp.ts u + 6 * sp.Δ := by
    have hanext : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (AC.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    have hle : sp.ts ((sp.slot a : Int) + 1) ≤ drainTime sp a := by
      rw [Healing.drainTime_eq]
      exact (AC.ts_le_iff sp).2 (by push_cast; omega)
    exact (hanext.le.trans hle).trans hRT
  have hFP : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F P := by
    rcases finality_alternative_before_update_at hp hP hslot hu hun hgu hR hTb hyj
        (hjtime ▸ haT) hjtime.le with h | ⟨x, r, e, C, hx, _, hto, ht, hPC, hh⟩
    · exact h
    · exact False.elim (hescape ⟨x, r, e, C, hx, hto, ht, hPC, hh⟩)
  have hPv : P ∈ ell.frame.viableTree ell.frame.tree := by
    rcases unanimous_viable_or_higher_report_at hp hP hslot hu hun hgu hR hTb hyj
        hup.1 hjtime hFP with h | ⟨x, r, e, C, hx, _, hto, ht, hPC, hh⟩
    · exact h
    · exact False.elim (hescape ⟨x, r, e, C, hx, hto, ht, hPC, hh⟩)
  have hpool := unanimous_pool_at hp hun hgu hR hyj hup.1
    (by rw [hjtime]; linarith only [hd]) hjb hPv.1
  have hts : cutZ sp.toParams g ≤ sp.ts u := by
    have hk := sp.two_le_k
    apply hp.clean_window_timing_at (s := u) ?_ u (by omega)
    rw [Healing.cleanLabel_eq]
    rw [Healing.drainTime_eq] at hR
    have := (AC.ts_le_iff sp).1 hR
    push_cast at this
    omega
  obtain ⟨w, hwK, hw⟩ := hp.committee_honest_nonempty_at (s := u)
    (by linarith [sp.toParams.hΔ]) (by linarith [sp.toParams.hΔ])
    (by linarith [AC.gbar_nonneg g, sp.toParams.hΔ]) hub
  obtain ⟨q, e, ⟨ellv, hv⟩, hs, hq⟩ := honest_votes_in_slot_at hp hgu hR hub w hw hwK
  have hvote : ∃ z q ell e, z ∈ H (tr.time q) ∧ AC.CastAt tr.projAC z q ell e ∧
      tr.time q ≤ b ∧ e.msg.slot = u :=
    ⟨w, q, ellv, e, hrun.antitone hq hw, hv, hq.trans hub, hs⟩
  have hlocks := hp.call_locks_compatible_of_unanimous_at hP hts hun hvote hyj hup.1 hjb
    (hjtime ▸ hRT) hjtime.le (fun r hr B CV ho =>
      unanimous_next_optimistic_compatible_at hp hP hslot hu hun hgu hR hub
        (hrun.antitone (hrun.time_mono hr.le) hyj) ho ((hrun.time_mono hr.le).trans hjb))
  have hnextlocks := hp.call_locks_compatible_of_unanimous_at hP hts hun hvote hyj' hto
    hnextb (hnexttime ▸ hRT) hnexttime.le (fun r hr B CV ho =>
      unanimous_next_optimistic_compatible_at hp hP hslot hu hun hgu hR hub
        (hrun.antitone (hrun.time_mono hr.le) hyj') ho ((hrun.time_mono hr.le).trans hnextb))
  have hsl : sp.slot (tr.time j) = u + 1 := by
    rw [hjtime]
    apply AC.slot_of_mem sp (u + 1)
    · simp only [AC.ACParams.ts]; push_cast; linarith only [hd]
    · simp only [AC.ACParams.ts]; push_cast; linarith only [hd]
  obtain ⟨r, e, R, hr, ht, hPR⟩ := report_of_viable_unanimous_pool_at hp hyj hjb hup hto htoeq
    hframe (hnexttime.trans hjtime.symm) hjoined hPg hPv (by linarith [sp.toParams.hΔ]) hpool
    hlocks
    (fun C hC => by
      obtain ⟨hCv, l, hl, he, _⟩ := hC
      exact hnextlocks C ⟨hCv.1, l, hl, he⟩)
    (by rw [hsl]; have := sp.two_le_k; omega) (by rw [hsl]; omega)
  exact ⟨r, e, R, hr, ht.trans hnexttime.le, hPR⟩

/-- **The report of a signing tick at the update deadline.** A node honest at `t_u + 6Δ` whose
tick there signs reports a descendant of a unanimous post-drain proposal `P` by then, or a node
honest at its report and at `c_z` reports a strict height increase above `P` by then. The tick's
adjacent update and `ac_to_fg` cuts are the shared ones (`update_toFG_of_signTick_at`); only this
tick need sign. -/
theorem report_of_signTick_unanimous_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) {y : Fin sp.n} (hy : y ∈ H (sp.ts u + 6 * sp.Δ)) {j : Nat}
    (hsj : tr.SignTickAt proposer dg y j (sp.ts u + 6 * sp.Δ)) :
    (∃ r e R, AC.ToFGAt tr.projAC y r e R ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P R) ∨
    (∃ x r e C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ AC.ToFGAt tr.projAC x r e C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) := by
  have hjoin : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) ≤ sp.ts u := by
    have hbase := (AC.ts_le_iff_le_slot sp (AC.gbar_nonneg g) (sp.slot (AC.gbar g))).2 (by rfl)
    simp only [AC.ACParams.ts] at hbase ⊢
    simp only [AC.ACParams.ts] at hgu
    push_cast at hbase hgu ⊢
    linarith only [hbase, hgu]
  obtain ⟨ell, ell', hup, hto, htoeq, hnexttime, hframe, hjoined⟩ :=
    update_toFG_of_signTick_at hp.run hy hsj fun i hi =>
      hp.joined_at_of_ready hy hjoin le_rfl hTb hi
  exact report_at_update_of_unanimous_at hp hP hslot hu hPg hun hgu hR hTb hy hup hto htoeq
    hnexttime hframe hjoined

/-- **Reports above a unanimous post-drain proposal `P` of slot `u` by `t_u + 6Δ`** under growing
faults: every node honest at `t_u + 6Δ` reports a descendant of `P` by then, or a node honest at
its report and at `c_z` reports a strict height increase above `P`. This is the all-signing
calendar's case of `report_of_signTick_unanimous_at`: under `GrowingAllTicksSign` the tick of every
honest awake node at `t_u + 6Δ` signs. -/
theorem report_cover_of_unanimous_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    (hsign : tr.GrowingAllTicksSign proposer dg H)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) :
    (∀ y, y ∈ H (sp.ts u + 6 * sp.Δ) → ∃ r e R, AC.ToFGAt tr.projAC y r e R ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P R) ∨
    (∃ x r e C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧ AC.ToFGAt tr.projAC x r e C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) := by
  classical
  by_cases hescape : ∃ x r e C, x ∈ H (max (cutZ sp.toParams g) (tr.time r)) ∧
      AC.ToFGAt tr.projAC x r e C ∧ tr.time r ≤ sp.ts u + 6 * sp.Δ ∧
      Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h
  · exact Or.inr hescape
  left
  intro y hy
  -- the all-signing calendar: the tick at the deadline signs
  have hΔ := sp.toParams.hΔ
  have hd0 : 0 ≤ sp.ts u + 6 * sp.Δ := by simp only [AC.ACParams.ts]; positivity
  obtain ⟨j, x, f, hg⟩ := hp.run.tick_of_awake y _ hy hd0
    ⟨4 * (u : Int) + 6, by simp only [AC.ACParams.ts]; ring⟩
    (hp.awake y _ hy (by linarith) hTb)
  exact (report_of_signTick_unanimous_at hp hP hslot hu hPg hun hgu hR hTb hy
    (RunTrace.growingAllTicksSign_iff.mp hsign y j _ hy ⟨x, f, hg⟩)).resolve_right hescape

end Consensus.Goldilocks.Healing.Growing

end

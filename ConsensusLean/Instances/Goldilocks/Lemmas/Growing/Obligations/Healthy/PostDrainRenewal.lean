module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReportCover
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.UnanimousNext
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.FoundationSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SelectionMembers
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Ancestry
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.CarryServed
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ETimeOrder
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Carry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.SeedCandidacy
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FastLockRenewal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLocal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVeto
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UpdateCalls
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local

public section

/-! # Post-drain per-slot fast-lock renewal

After the drain, a unanimous slot-`u` proposal `P` keeps being extended: every honest vote of
every later slot extends `P` (`post_drain_votes_extend_at`), every node honest at the update of
a slot `r ≥ u` writes a fast lock of slot `r` on a block extending `P`
(`fast_lock_renewal_post_at`), and every `ac_to_fg` call after `t_{u+1} + 2Δ` has a candidate
extending `P` (`toFG_candidate_post_at`), unless a node honest at its report and at `c_z` has
already reported a strictly higher descendant of `P` (`HigherReportBy`). No honest proposer is
needed in the slots after `u`.

The step from slot `m` to slot `m + 1` (`extend_next_votes_core_at`) generalizes
`unanimous_next_votes_extend_core_at`: its counted votes only need to extend `P`, not to name it,
and the viability of `P` at the slot-`(m+1)` casts is an input. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-- A member written before the reader has a same-label supporter before that reader. -/
private theorem member_supporter_before_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {s k : Nat}
    (hcut : cutZ sp.toParams g ≤ sp.ts s) (hC : HealedMemberBefore tr H g a b C s k) :
    ∃ z q e, q < k ∧ z ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC z q e ∧
      e.msg.slot = s ∧ AC.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
  have source {x r O CV} (hrk : r < k) (hx : x ∈ H (tr.time r)) (hrb : tr.time r ≤ b)
      (ho : AC.ResultAt tr.projAC x r s O CV ∨ AC.OptimisticLockAt tr.projAC x r s O CV)
      (hCO : Anc (tr.HonestBlocksAt H) C O) :
      ∃ z q e, q < k ∧ z ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC z q e ∧
        e.msg.slot = s ∧ AC.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
    rcases ho with hres | hop
    · obtain ⟨z, hz, q, hqr, e, hv, _, hs, hVC⟩ :=
        ProposalImpl.result_supporter_at hp hx hres hCO hrb hcut
      exact ⟨z, q, e, by omega, hp.run.antitone (hp.run.time_mono hqr.le) hz, hv, hs, hVC⟩
    · obtain ⟨_, z, q, hz, hqr, e, hv, hs, B, hB, hBr, hOB⟩ :=
        hp.optimistic_supporter_at hx hrb (by linarith [lt_cutZ sp g, sp.toParams.hΔ]) hop
      exact ⟨z, q, e, by omega, hp.run.antitone (hp.run.time_mono hqr) hz, hv, hs,
        B, hB, hBr, hCO.trans hOB⟩
  rcases healedMemberBefore_iff.1 hC with
    ⟨_, x, r, CV, hrk, hx, hrb, ho⟩ | ⟨_, x, r, hrk, hx, hrb, hl⟩ | ⟨x, r, hrk, hrb, ho⟩
  · exact source hrk hx hrb ho .refl
  · obtain ⟨O, CV, ho, hCO⟩ := Compose.Growing.lock_below_origin_at hp.run hp.noColl hx hl
    exact source hrk hx hrb ho hCO
  · obtain ⟨CV, ell, D, hc, hf, hC⟩ := ho.2.2.1
    have hx := hp.run.antitone (le_max_right _ _) ho.1
    obtain ⟨O, OV, ho, hDO⟩ := Compose.Growing.lock_below_origin_at hp.run hp.noColl hx
      (Or.inl ⟨CV, hf⟩)
    have hPhiU := (frame_tree_subset_at hp.run hp.noColl hx hc).2
    have hsub : ell.frame.tree ⊆ tr.HonestBlocksAt H := fun B hB =>
      ⟨x, r, tr.time r, hp.run.time_nonneg r, fun _ hq => hp.run.time_mono hq.le, hx, hPhiU hB⟩
    apply source hrk hx hrb ho
    rw [hC]
    exact ((AC.anc_viableAncestor ell.frame D).mono hsub).trans hDO

/-- **The higher-report escape by `T`**: a node honest at its report and at `c_z` reports, by
`T`, a descendant of `P` at a strictly greater height than `P` (in its store at the report). -/
def HigherReportBy (tr : GoldilocksTrace sp) (H : Time → Set (Fin sp.n)) (g : Time)
    (P : AC.Blk sp.n (List (FG.Att sp.n))) (T : Time) : Prop :=
  ∃ x q e C, x ∈ H (max (cutZ sp.toParams g) (tr.time q)) ∧ AC.ToFGAt tr.projAC x q e C ∧
    tr.time q ≤ T ∧ Anc (tr.HonestBlocksAt H) P C ∧
    ((tr.state x q).fg.σ P.root).h < ((tr.state x q).fg.σ C.root).h

/-- `HigherReportBy` unfolded. -/
theorem higherReportBy_iff {P : AC.Blk sp.n (List (FG.Att sp.n))} {T : Time} :
    HigherReportBy tr H g P T ↔ ∃ x q e C, x ∈ H (max (cutZ sp.toParams g) (tr.time q)) ∧
      AC.ToFGAt tr.projAC x q e C ∧ tr.time q ≤ T ∧ Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state x q).fg.σ P.root).h < ((tr.state x q).fg.σ C.root).h :=
  Iff.rfl

/-- The escape persists to later horizons. -/
theorem HigherReportBy.mono {P : AC.Blk sp.n (List (FG.Att sp.n))} {T T' : Time}
    (h : HigherReportBy tr H g P T) (hT : T ≤ T') : HigherReportBy tr H g P T' :=
  let ⟨x, q, e, C, hx, hto, hq, hPC, hh⟩ := h
  ⟨x, q, e, C, hx, hto, hq.trans hT, hPC, hh⟩

/-! ### Under the reset premises -/

/-- CS2 at the slot-`(m+1)` committee at every cut from `t_{m+1}` through `b`. -/
private theorem next_cs2 {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) {m : Nat}
    (hgm : AC.gbar g + 4 * sp.Δ ≤ sp.ts m) :
    ∀ i, sp.ts (m + 1 : Nat) ≤ tr.time i → tr.time i ≤ b →
      2 * ((Generic.dictOfTime sp cm).committee (m + 1) ∩ (H (tr.time i))ᶜ).ncard <
        sp.committeeSize := fun i hti hib =>
  hp.committee_cs2_at
    (by have := (AC.ts_le_iff sp).2 (show (m : Int) ≤ (m + 1 : Nat) by omega)
        linarith [sp.toParams.hΔ]) (hti.trans hib) (hp.run.time_nonneg i) hib

/-- **A high origin of a slot whose honest votes extend `P` is compatible with `P`**: origins
written before `t_{u+1}` are below `P`; a later origin is a fast lock of a slot `l ≥ u` whose
lock block has an honest supporting vote of slot `l`, no later than the lock, that extends it;
that vote also extends `P` (it names `P` when `l = u`, and `hext` when `l > u`). -/
theorem high_origin_compatible_post_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b) {x : Fin sp.n} {r l : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l B) (hrb : tr.time r ≤ b)
    (hext : ∀ z q e, q ≤ r → z ∈ H (tr.time q) → AC.VoteAt tr.projAC z q e →
      e.msg.slot = l → u + 1 ≤ l → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P) :
    Compatible (tr.HonestBlocksAt H) B P := by
  have hΔ := sp.toParams.hΔ
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  by_cases ht : tr.time r < sp.ts (u + 1 : Nat)
  · exact Or.inl (high_origins_before_next_slot_below_at hp hP hun hgu hR hub ho ht hrb)
  have hcz := hp.cutZ_le_ts_of_highOrigin_at ho
  obtain ⟨hxz, -, ⟨CV, ell, D, hcall, hfl, hB⟩, -⟩ := ho
  have hx := hp.run.antitone (le_max_right _ _) hxz
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hts1 : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  -- the honest slot-`l` votes up to the lock extend `P`
  have hvl : u ≤ l → ∀ z q e, q ≤ r → z ∈ H (tr.time q) → AC.VoteAt tr.projAC z q e →
      e.msg.slot = l → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
    intro hul z q e hq hz hv hs
    rcases Nat.eq_or_lt_of_le hul with rfl | hlt
    · exact ⟨P, hP, (hun z q e hz hv ((hp.run.time_mono hq).trans hrb) hs).symm, .refl⟩
    · exact hext z q e hq hz hv hs hlt
  have hDP : Compatible (tr.HonestBlocksAt H) D P := by
    have below : u ≤ l → ∀ z q, q ≤ r → z ∈ H (tr.time q) → ∀ e, AC.VoteAt tr.projAC z q e →
        e.msg.slot = l → AC.VoteExtends (tr.HonestBlocksAt H) e.msg D →
        Compatible (tr.HonestBlocksAt H) D P := by
      rintro hul z q hqr hz e hv hes ⟨Hd, hHd, hHdr, hDHd⟩
      obtain ⟨Hd', hHd', hHd'r, hPHd'⟩ := hvl hul z q e hqr hz hv hes
      obtain rfl : Hd = Hd' := hU.1 hHd hHd' (hHdr.trans hHd'r.symm)
      exact AC.anc_total hU hDHd hPHd'
    rcases hfl with ⟨ell', C, hupd, hC, hD, _⟩ | hop
    · have htime : tr.time r = sp.ts l + 6 * sp.Δ := hupd.2.2.1
      have hul : u ≤ l := by
        by_contra hlu
        have := (AC.ts_le_iff sp).2 (show ((l + 1 : Nat) : Int) ≤ u by omega)
        have hl1 : sp.ts (l + 1 : Nat) = sp.ts l + 4 * sp.Δ := by
          simp only [ACParams.ts]; push_cast; ring
        exact ht (by linarith)
      have hr := hac.localRun.upTo (hp.run.time_nonneg r)
      have hcu := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hupd.1)
      obtain ⟨z, hz, q, hqr, e, hv, _, hes, he⟩ := ProposalImpl.result_supporter_at hp hx
        ⟨ell', hupd, hC, rfl⟩ ((AC.deepest_mem hD).1.1.2.2.mono
          (AC.frameIn_of_callAt hr hx hcu).2) hrb hcz
      exact below hul z q hqr.le (hp.run.antitone (hp.run.time_mono hqr.le) hz) e hv hes he
    · obtain ⟨-, z, q, hz, hqr, e, hv, hes, he⟩ :=
        hp.optimistic_supporter_at hx hrb (Healing.gbar_le_of_cutZ_le sp hcz) hop
      have hul : u ≤ l := by
        obtain ⟨-, -, -, hsl, -⟩ := id hop
        change sp.slot (tr.time r) = l at hsl
        have := (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg r) ((u + 1 : Nat) : Int)).1
          (not_lt.mp ht)
        omega
      exact below hul z q hqr (hp.run.antitone (hp.run.time_mono hqr) hz) e hv hes he
  obtain ⟨hPhi, hsub⟩ : FrameOK ell.frame ∧ ell.frame.tree ⊆ tr.HonestBlocksAt H := by
    rcases hac.localRun.frameLaw x r ell hx hcall with
      ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.1
  have hBD := (AC.anc_viableAncestor ell.frame D).mono hsub
  rw [← hB] at hBD
  rcases hDP with h | h
  · exact Or.inl (hBD.trans h)
  · exact AC.anc_total hU hBD h

/-- **The reset's slot is warm and drains before slot `u + 1`**: the reset is before the next
slot, which starts after `ḡ + 4Δ` (the reset is after `c_z`), and the drain ending by `t_{u+1}`
leaves `2k + 4` slots before `u`. -/
theorem warm_slot_after_reset {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) {u : Nat}
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) :
    a < sp.ts (sp.slot a + 1 : Nat) ∧ AC.gbar g + 4 * sp.Δ ≤ sp.ts (sp.slot a + 1 : Nat) ∧
      sp.slot a + 2 * sp.k + 4 ≤ u := by
  have hz := hp.cutZ_lt_reset_at
  have := Healing.lt_cutZ sp g
  have ha0 : 0 ≤ a := by linarith [Healing.gbar_nonneg g, sp.toParams.hΔ]
  have hlt : a < sp.ts (sp.slot a + 1 : Nat) := not_le.1 fun h => by
    have := (AC.ts_le_iff_le_slot sp ha0 _).1 h
    push_cast at this
    omega
  rw [Healing.drainTime_eq] at hR
  have := (AC.ts_le_iff sp).1 hR
  push_cast at this
  exact ⟨hlt, by linarith [sp.toParams.hΔ], by omega⟩

/-- The reset is at or before the slot `u` when its drain ends by `t_{u+1}`. -/
theorem reset_le_ts_of_drain {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) {u : Nat}
    (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) : a ≤ sp.ts u := by
  obtain ⟨hlt, -, hu⟩ := warm_slot_after_reset hp hR
  exact hlt.le.trans ((AC.ts_le_iff sp).2 (by omega))

/-- Pre-cut members are compared using pre-cut supporters, never future writes. -/
private theorem member_compatible_post_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    (hc : HighSourceCover tr H g a b)
    {u m k : Nat} {P C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b)
    (hext : ∀ s, u + 1 ≤ s → s ≤ m → ∀ z q e, q < k → z ∈ H (tr.time q) →
      AC.VoteAt tr.projAC z q e → e.msg.slot = s →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    {s : Nat} (hC : HealedMemberBefore tr H g a b C s k) (hsm : s ≤ m) :
    Compatible (tr.HonestBlocksAt H) C P := by
  by_cases hsu : s ≤ u
  · exact Or.inl (healed_members_through_slot_below_at hp hc hP hun hgu hR hub
      C s hC.healedOrigin hsu)
  have hcz : cutZ sp.toParams g ≤ sp.ts s := by
    have := hp.cutZ_lt_reset_at
    have := reset_le_ts_of_drain hp hR
    have hts := (AC.ts_le_iff sp).2 (show (u : Int) ≤ s by omega)
    linarith
  obtain ⟨z, q, e, hqk, hz, hv, hs, B, hB, hBr, hCB⟩ :=
    member_supporter_before_at hp hcz hC
  obtain ⟨B', hB', hB'r, hPB'⟩ := hext s (by omega) hsm z q e hqk hz hv hs
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  obtain rfl : B' = B := hU.1 hB' hB (hB'r.trans hBr.symm)
  exact AC.anc_total hU hCB hPB'

/-- **Finality below `P` after the drain**, unless a strictly higher report extends `P` by then:
at a cut of a node honest at it from `t_u` on, before the slot `M + 1` whose earlier slots'
honest votes extend `P`, the finalized block is below a high origin written by the cut, which is
compatible with `P` (`high_origin_compatible_post_at`). -/
theorem finalized_below_post_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u M : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hub : sp.ts u + sp.Δ ≤ b)
    {y : Fin sp.n} {k : Nat}
    (hext : ∀ s, u + 1 ≤ s → s ≤ M → ∀ z q e, z ∈ H (tr.time q) → AC.VoteAt tr.projAC z q e →
      tr.time q ≤ tr.time k → e.msg.slot = s → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hy : y ∈ H (tr.time k)) (hk : sp.ts u ≤ tr.time k)
    (hkM : tr.time k < sp.ts (M + 1 : Nat)) (hkb : tr.time k ≤ b) :
    HigherReportBy tr H g P (tr.time k) ∨
      Anc (tr.HonestBlocksAt H) (tr.state y k).fg.F P := by
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have ha : a ≤ tr.time k := (reset_le_ts_of_drain hp hR).trans hk
  have hFc : Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F P := by
    rcases ProposalImpl.finalized_below_high_origin_or_covered_before_at hp hy ha hkb with
      ⟨x, r, l, B, ho, hrk, hrb, hFB⟩ | hcov
    · have hBP := high_origin_compatible_post_at hp hP hun hgu hR hub ho hrb
        fun z q e hqr hz hv hs hl => by
          obtain ⟨-, -, ⟨CV, ell, D, -, hfl, -⟩, -⟩ := ho
          have hlr := ProposalImpl.ts_le_of_fastLock_at hp.run hfl
          have hlM : l ≤ M := by
            have := (AC.ts_lt_iff sp).1
              (show sp.ts l < sp.ts (M + 1 : Nat) by linarith)
            omega
          exact hext l hl hlM z q e hz hv ((hp.run.time_mono hqr).trans hrk) hs
      rcases hBP with h | h
      · exact Or.inl (hFB.trans h)
      · exact AC.anc_total hU hFB h
    · obtain ⟨hc, C, s, hC, hsk, hFC⟩ := coveredBefore_iff.1 hcov
      have hsM : s ≤ M := by
        have := (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg k) (M + 1 : Nat)).not.mp
          (not_le.mpr hkM)
        omega
      have hCP := member_compatible_post_at hp hc hP hun hgu hR hub
        (fun s hs hsM z q e hq hz hv hes =>
          hext s hs hsM z q e hz hv (hp.run.time_mono hq.le) hes) hC hsM
      rcases hCP with h | h
      · exact Or.inl (hFC.trans h)
      · exact AC.anc_total hU hFC h
  rcases hp.finality_below_or_higher_report_at hy hkb hFc with
    h | ⟨z, r, l, C, hz, hrk, hto, hPC, hlt⟩
  · exact Or.inr h
  · exact Or.inl ⟨z, r, l, C, hz, hto, hp.run.time_mono hrk.le, hPC, hlt⟩

/-- **A slot-`(m+1)` cast after a run of slots extending `P` has `P` above its finality and
viable**, or a higher report extends `P` by the cast. Compare finality using the pre-slot
sources, then use the earlier votes of slot `m+1` for the held-target viability comparison. -/
theorem cast_viable_or_escape_post_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u m : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocksAt H)
    (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hum : u + 1 ≤ m)
    {y : Fin sp.n} {j : Nat}
    (hprev : ∀ s, u + 1 ≤ s → s ≤ m → ∀ y' j' e, y' ∈ H (tr.time j') →
      AC.VoteAt tr.projAC y' j' e → tr.time j' ≤ tr.time j → e.msg.slot = s →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y j ell e)
    (hs : e.msg.slot = m + 1) (hjb : tr.time j ≤ b)
    (hearlier : ∀ x q e', q < j → x ∈ H (tr.time q) → AC.VoteAt tr.projAC x q e' →
      e'.msg.slot = m + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e'.msg P) :
    HigherReportBy tr H g P (tr.time j) ∨
      (Anc (tr.HonestBlocksAt H) ell.frame.F P ∧ AC.ViableAtVote ell e (m + 1) P) := by
  have hrun := hp.run
  have hm := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have hd := hrun.time_nonneg j
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hstep {s : Nat} : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hum1 := hts (show u + 1 ≤ m + 1 by omega)
  obtain ⟨hjlo, hjhi⟩ := castAt_time_bounds hp.run hp.noColl hy hc
  rw [hs] at hjlo hjhi
  have hub : sp.ts u + sp.Δ ≤ b := by have := @hstep u; linarith
  have hRm : drainTime sp a ≤ sp.ts (m + 1 : Nat) := hR.trans hum1
  -- every high origin written by the cast, earlier or before slot `m + 1`, is compatible with `P`
  have hbefore : ∀ x r l B, HighOrigin tr H g x r l B → tr.time r ≤ tr.time j →
      (r < j ∨ tr.time r < sp.ts (m + 1 : Nat)) → Compatible (tr.HonestBlocksAt H) B P := by
    intro x r l B ho hrj hr
    refine high_origin_compatible_post_at hp hP hun hgu hR hub ho (hrj.trans hjb)
      fun z q e' hqr hz hv hs' hl => ?_
    obtain ⟨-, -, ⟨CV, ell', D, -, hfl, -⟩, -⟩ := ho
    have hlr := ProposalImpl.ts_le_of_fastLock_at hp.run hfl
    by_cases hlm : l ≤ m
    · exact hprev l hl hlm z q e' hz hv ((hm hqr).trans hrj) hs'
    have hl' : l = m + 1 := by
      have := (AC.ts_lt_iff sp).1 (show sp.ts l < sp.ts (m + 1 + 1 : Nat) by
        have := @hstep (m + 1); linarith)
      omega
    rcases hr with hrj' | hlt
    · exact hearlier z q e' (lt_of_le_of_lt hqr hrj') hz hv (hl' ▸ hs')
    · exact absurd (hl' ▸ hlr) (not_le.mpr hlt)
  have hfr := Outcome.frame_of_call hrun hy hc.1
  have hFeq : ell.frame.F = (tr.state y j).fg.F := congrArg Frame.F hfr
  have hFc : Compatible (tr.HonestBlocksAt H) (tr.state y j).fg.F P := by
    rcases hp.reset_vote_finality_source_or_covered_at hRm hy hc hs hjb with
      hg | ⟨v, r, l, O, ho, hrt, _, hO⟩ | ⟨hcover, C, s, hC, hsm, hRC⟩
    · have hFm := (Store.cache_invariants _ _ _ _ (fg_reachable_at hrun hd
        (fun _ hq => hm hq.le) hy)).1
      exact Or.inl (ProposalImpl.genesis_root_anc_at hrun hp.noColl
        ⟨y, j, tr.time j, hd, fun _ hq => hm hq.le, hy, hFm⟩ hg hP)
    · rcases hbefore v r l O ho (by linarith) (Or.inr hrt) with h | h
      · exact Or.inl (hO.trans h)
      · exact AC.anc_total hU hO h
    · have hCP := member_compatible_post_at hp hcover hP hun hgu hR hub
        (fun s hs hsm z q e hq hz hv hes =>
          hprev s hs hsm z q e hz hv (hm hq.le) hes) hC (by omega)
      rcases hCP with h | h
      · exact Or.inl (hRC.trans h)
      · exact AC.anc_total hU hRC h
  rcases hp.finality_below_or_higher_report_at hy hjb hFc with
    hFP | ⟨x, r, ell', C, hx, hrj, hto, hPC, hlt⟩
  swap
  · exact Or.inl ⟨x, r, ell', C, hx, hto, hm hrj.le, hPC, hlt⟩
  have hFP' : Anc (tr.HonestBlocksAt H) ell.frame.F P := hFeq ▸ hFP
  have hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time j)) := by
    have hcz := hp.cutZ_lt_reset_at.le.trans ((reset_le_ts_of_drain hp hR).trans
      ((hts (show u ≤ m + 1 by omega)).trans hjlo))
    rwa [max_eq_right hcz]
  have hPv : P ∈ AC.voterBlockTree sp e.readPoint ell.frame (m + 1) := by
    have hnr : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ AC.gbar g := fun r hrj hrs =>
      hp.noRestart y r (hrun.antitone (hm hrj) hy) hrs ((hm hrj).trans hjb)
    obtain ⟨k', hk'j, ha', hk't⟩ := unanimous_head_accepted_core_at hp.run hp.noColl hp.sync
      hp.catchUp hP hslot hu hun (by linarith [Healing.le_gbar g]) hy hc.1
      (by have := @hstep u; linarith) hjb hnr (exists_honest_slot_vote_at hp hgu hR hub)
      hFP'
    have hr := (acRun_upTo_time hrun hp.noColl j).localRun
    have hc' := castAt_upTo_of_le le_rfl hc
    have ha'' : (tr.upTo (tr.time j)).projAC.AcceptAt y k' P := by
      rw [RunTrace.upTo_projAC]
      exact (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _)).mpr ⟨hm hk'j, ha'⟩
    have hPp : P ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)) := by
      obtain ⟨ella, hca, hba⟩ := ha''
      exact (AC.frameIn_of_callAt hr hy hca).2
        ((AC.accept_new sp hr hy ⟨ella, hca, hba⟩).1 ella hca)
    have hFPp := RunTrace.anc_upTo_of_right hrun.toLocalRun hp.noColl hd hPp hFP'
    have hacc : AC.AcceptedBefore (tr.upTo (tr.time j)).projAC y P (sp.ts m + 3 * sp.Δ) :=
      Or.inr ⟨k', ha'', by change tr.time k' < _; linarith [hts (show u ≤ m by omega)]⟩
    exact Compose.accepted_voter_tree (hrun.upTo hd) (hp.noColl.upTo _) hy hc' hs hPp hacc hFPp
  have hPt : P ∈ (Node.frame (tr.state y j)).tree := hfr ▸ hPv.1
  obtain ⟨v, q, l, S, hseed, hqb, -, hqt⟩ := hp.reset_seed_before_slot_at hR
  have hSP := high_origins_before_next_slot_below_at hp hP hun hgu hR hub hseed hqt hqb
  rcases held_target_viableHeads_or_higher_report_covered_at hp hyz hjb hPt hseed hqb hSP
    (ResetPremisesUpTo.compatibleWithOrigins_iff.2 ⟨
      fun x r l B hrj ho => (hbefore x r l B ho (hm hrj.le) (Or.inl hrj)).symm,
      fun hcover C s hC hsm => (member_compatible_post_at hp hcover hP hun hgu hR hub
        (m := m + 1) (fun s hs hsm z q e hq hz hv hes => by
          by_cases hsm' : s ≤ m
          · exact hprev s hs hsm' z q e hz hv (hm hq.le) hes
          · exact hearlier z q e hq hz hv (by convert hes using 1; omega))
        hC (by
          have := (AC.ts_le_iff_le_slot sp hd (m + 2 : Nat)).not.mp
            (not_le.mpr (by have := @hstep (m + 1); linarith))
          omega)).symm⟩) with ⟨_, hroot, hhead⟩ | ⟨x, r, ell', C, hx, hrj, hto, hPC, hlt⟩
  · exact Or.inr ⟨hFP', Or.inl ⟨hPv, hfr.symm ▸ hroot, P, hPv, hfr.symm ▸ hhead, .refl⟩⟩
  · exact Or.inl ⟨x, r, ell', C, hx, hto, hm hrj.le, hPC, hlt⟩

/-- The reset service through `b` holds through any earlier horizon. -/
private theorem resetService_mono {T hold : Time} (hs : ResetService tr H g ΔF b hold)
    (hTb : T ≤ b) : ResetService tr H g ΔF T hold :=
  ⟨hs.deltaF, hs.message, hs.block, hs.relay, fun x i att hx hsg hxh y j hy hj hjT =>
    hs.signedRow x i att hx hsg hxh y j hy hj (hjT.trans hTb), hs.hold_le⟩

/-- **Every honest vote by `T` of every slot `r ∈ [u + 1, N]` extends the unanimous post-drain
proposal `P`**, unless a node honest at its report and at `c_z` reports a strictly higher
descendant of `P` by `T`: by induction on `r`, the slot-`(u+1)` votes by
`unanimous_next_votes_extend_core_at`, each later slot by `extend_next_votes_core_at` through `T`,
with no honest proposer needed. -/
theorem post_drain_votes_extend_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u N : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocksAt H)
    (hslot : P.slot = u) (hu : 0 < u)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hNb : sp.ts N ≤ b) {T : Time} (hTb : T ≤ b) :
    HigherReportBy tr H g P T ∨ ∀ r, u + 1 ≤ r → r ≤ N →
      ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ T →
        e.msg.slot = r → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  classical
  by_cases hesc : HigherReportBy tr H g P T
  · exact Or.inl hesc
  right
  have hΔ := sp.toParams.hΔ
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hstep {m : Nat} : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  -- the induction carries every slot from `u + 1` through `r`
  suffices hall : ∀ r, u + 1 ≤ r → r ≤ N → ∀ s, u + 1 ≤ s → s ≤ r → ∀ y j e,
      y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ T → e.msg.slot = s →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg P from
    fun r hr hrN => hall r hr hrN r hr le_rfl
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    intro hrN s hs1 hs2 y j e hy hv hjT hs
    have hub : sp.ts u + sp.Δ ≤ b := by
      have := hts (show u + 1 ≤ N by omega); have := @hstep u; linarith
    obtain rfl : s = u + 1 := by omega
    exact unanimous_next_votes_extend_core_at hp.run hp.noColl hp.sync hp.catchUp hP hslot hu
      hun (by linarith) hp.committeeFacts.hP
      (hp.committeeFacts.committeeTAt hp.run hp.noColl) hp.committeeFacts.hsize hp.noRestart
      (exists_honest_slot_vote_at hp hgu hR hub)
      (committee_voted_in_slot_at hp hgu hR hub) (faultBoundK_after_slot_at hp hgu hR)
      (next_cs2 hp hgu)
      (fun _ _ _ _ hy hcast hs hjb =>
        hp.reset_vote_finality_below_bound_at hR hP
        (fun _ _ _ _ ho ht hrb => high_origins_before_next_slot_below_at hp hP hun hgu hR hub
          ho ht hrb)
        (fun hc C s hC hs => healed_members_through_slot_below_at hp hc hP hun hgu hR hub
          C s hC.healedOrigin (by omega)) hy hcast hs hjb)
      (fun _ _ _ _ hy hcast hs hjb hstore =>
        hp.reset_vote_viable_above_old_or_covered_at hy hR hcast hs hjb
        hstore (fun _ _ _ _ ho ht hrb => high_origins_before_next_slot_below_at hp hP hun hgu hR
          hub ho ht hrb)
        (fun hc C s hC hs => healed_members_through_slot_below_at hp hc hP hun hgu hR hub
          C s hC.healedOrigin (by omega))) y j e hy hv (hjT.trans hTb) hs
  | succ m hum ih =>
    intro hmN
    have hprev := ih (by omega)
    have hm1 := hts (show m + 1 ≤ N by omega)
    have hmb : sp.ts m + sp.Δ ≤ b := by have := @hstep m; linarith
    have hgm : AC.gbar g + 4 * sp.Δ ≤ sp.ts m := (hgu.trans (hts (by omega)))
    have hRm : drainTime sp a ≤ sp.ts (m + 1 : Nat) := hR.trans (hts (by omega))
    have hnext := extend_next_votes_core_at hp.run hp.noColl (resetService_mono hp.sync hTb)
      hp.catchUp (hprev m hum le_rfl) (by linarith [Healing.le_gbar g]) hp.committeeFacts.hP
      (hp.committeeFacts.committeeTAt hp.run hp.noColl) hp.committeeFacts.hsize
      (committee_voted_in_slot_at hp hgm hRm hmb)
      (fun i hi hiT => faultBoundK_after_slot_at hp hgm hRm i hi (hiT.trans hTb))
      (fun i hi hiT => next_cs2 hp hgm i hi (hiT.trans hTb))
      (fun y j ell e hy hc hs hjT hearlier => by
        rcases cast_viable_or_escape_post_at hp hP hslot hu hun hgu hR hum
            (fun s h1 h2 y' j' e' hy' hv' hj' hs' =>
              hprev s h1 h2 y' j' e' hy' hv' (hj'.trans hjT) hs') hy hc hs
            (hjT.trans hTb) hearlier with h | h
        · exact absurd (h.mono hjT) hesc
        · exact h)
    intro s hs1 hs2
    rcases Nat.lt_or_ge s (m + 1) with hlt | hge
    · exact hprev s hs1 (by omega)
    · obtain rfl : s = m + 1 := by omega
      exact hnext

/-! ### Fresh fast locks and report candidates -/

/-- **A fresh fast lock extending `P` at every slot `r ∈ [u, N]`**: every node honest at the update
`t_r + 6Δ` of slot `r` writes there, by the fast test, a fast lock of slot `r` on a block extending
the unanimous post-drain proposal `P`, unless a node honest at its report and at `c_z` reports a
strictly higher descendant of `P` by then. The honest slot-`r` votes extend `P`
(`post_drain_votes_extend_at`) and are resolved before `t_r + 2Δ` at the updater, whatever the
slot-`r` proposer; no live lock vetoes `P`. -/
theorem fast_lock_renewal_post_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u N : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocksAt H)
    (hslot : P.slot = u) (hu : 0 < u) (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hNb : sp.ts N + 6 * sp.Δ ≤ b) :
    ∀ r, u ≤ r → r ≤ N → HigherReportBy tr H g P (sp.ts r + 6 * sp.Δ) ∨
      ∀ y, y ∈ H (sp.ts r + 6 * sp.Δ) → ∃ j D CV, AC.FastUpdateAt tr.projAC y j r D CV ∧
        Anc (tr.HonestBlocksAt H) P D := by
  intro r hur hrN
  by_cases hesc : HigherReportBy tr H g P (sp.ts r + 6 * sp.Δ)
  · exact Or.inl hesc
  right
  intro y hy
  have hΔ := sp.toParams.hΔ
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hstep {m : Nat} : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hur' := hts hur
  have hrNt := hts hrN
  have hTb : sp.ts r + 6 * sp.Δ ≤ b := by linarith
  have hub : sp.ts u + sp.Δ ≤ b := by linarith
  have hgr : AC.gbar g + 4 * sp.Δ ≤ sp.ts r := by linarith
  have hnr : NoRestartUpTo tr H (AC.gbar g) b := noRestartUpTo_iff.mpr hp.noRestart
  -- the honest votes of slots `u + 1 … r + 1` cast by the update extend `P`
  have hvotes : ∀ s, u + 1 ≤ s → s ≤ r + 1 → ∀ x i e, x ∈ H (tr.time i) →
      AC.VoteAt tr.projAC x i e → tr.time i ≤ sp.ts r + 6 * sp.Δ → e.msg.slot = s →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg P :=
    (post_drain_votes_extend_at hp hP hslot hu hun hgu hR (N := r + 1)
      (by have := @hstep r; linarith) hTb).resolve_left hesc
  -- every honest vote of slots `r` and `r + 1` extends `P`
  have hext_of : ∀ s, r ≤ s → s ≤ r + 1 → ∀ x i e, x ∈ H (tr.time i) →
      AC.VoteAt tr.projAC x i e → e.msg.slot = s →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
    intro s hrs hsr x i e hx hv hes
    have hi := (castAt_time_bounds hp.run hp.noColl hx hv.choose_spec).2
    rw [hes] at hi
    have his : tr.time i ≤ sp.ts r + 6 * sp.Δ := by
      have := hts hsr; have := @hstep r; linarith
    rcases Nat.eq_or_lt_of_le (hur.trans hrs) with rfl | hlt
    · exact ⟨P, hP, (hun x i e hx hv (his.trans hTb) hes).symm, .refl⟩
    · exact hvotes s hlt hsr x i e hx hv his hes
  -- finality below `P` through the update
  have hfin : ∀ x q, x ∈ H (tr.time q) → sp.ts r ≤ tr.time q →
      tr.time q ≤ sp.ts r + 6 * sp.Δ → tr.time q ≤ b →
        Anc (tr.HonestBlocksAt H) (tr.state x q).fg.F P := by
    intro x q hx hlo hhi hqb
    refine (finalized_below_post_at hp hP hun hgu hR hub (M := r + 1)
      (fun s h1 h2 z q' e hz hv hq' hs => hvotes s h1 h2 z q' e hz hv (hq'.trans hhi) hs)
      hx (hur'.trans hlo) (by have := @hstep (r + 1); have := @hstep r; linarith) hqb
      ).resolve_left fun h => hesc (h.mono hhi)
  -- the update of slot `r`, joined
  have hjoinu : sp.ts (sp.slot (AC.gbar g) + 1 : Nat) ≤ sp.ts r := by
    have hbase := (AC.ts_le_iff_le_slot sp (Healing.gbar_nonneg g) (sp.slot (AC.gbar g))).2 (by rfl)
    simp only [AC.ACParams.ts] at hbase hgr ⊢
    push_cast at hbase hgr ⊢
    linarith only [hbase, hgr, hΔ]
  obtain ⟨k, ell, hu⟩ := hp.update_call_of_awake hy hjoinu hTb
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hk' : tr.time k = sp.ts (s + 1 : Nat) + 6 * sp.Δ := hu.2.2.1
  have hyk : y ∈ H (tr.time k) := by rw [hk']; exact hy
  have hkb : tr.time k ≤ b := hk' ▸ hTb
  obtain ⟨-, hs₀, hsa⟩ := warm_slot_after_reset hp hR
  have hjoin := fun w hw => joined_voteTime_of_warm_frame_upTo_at hp.run hnr hs₀
    (show sp.slot a + 1 + 1 ≤ s + 1 by omega) (by have := @hstep (s + 1); linarith) (y := w) hw
  have hext1 := hext_of (s + 1) le_rfl (by omega)
  have hext2 := hext_of (s + 1 + 1) (by omega) le_rfl
  have hklo : sp.ts (s + 1 : Nat) ≤ tr.time k := by rw [hk']; linarith
  obtain ⟨C, hconf, hPC, D, hfs, hPD⟩ := update_result_extends_of_finalized_at hp.run hp.noColl
    hp.sync hp.awake hp.faults hp.catchUp hnr hgr hjoin hfin hPg hext1 hyk hu hklo hk'.le hkb
    hp.committeeHalf
  have hlocks := update_locks_compatible_of_finalized_at hp.run hp.noColl hp.sync hp.awake
    hp.faults hp.catchUp hnr hgr le_rfl hjoin hfin hPg hext1 hext2 hyk hu hk'.le hkb
    hp.committeeHalf
  have hFP : Anc (tr.HonestBlocksAt H) ell.frame.F P := by
    rw [Compose.Growing.frame_of_projAC_at hp.run hyk hu.1]
    exact hfin y k hyk hklo hk'.le hkb
  exact ⟨k, fast_update_of_compatible_locks_at hp.run hp.noColl hyk hu hconf hfs hFP hPg
    hPC hPD hlocks⟩

/-- **`P` is a viable head of every honest store after the drain**, unless a strictly higher
report extends `P` by `T`: at a cut of a node honest at it from `t_u + Δ` through `T`, holding `P`,
when the honest votes of the slots after `u` cast by `T` extend `P`, `P` is in the store frame,
above its finalized-chain root, and among its viable heads. -/
theorem viable_head_post_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocksAt H)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    {T : Time} (hTb : T ≤ b)
    (hext : ∀ s, u + 1 ≤ s → ∀ x q e, x ∈ H (tr.time q) → AC.VoteAt tr.projAC x q e →
      tr.time q ≤ T → e.msg.slot = s → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) (hk : sp.ts u + sp.Δ ≤ tr.time k)
    (hkT : tr.time k ≤ T) (hPy : P ∈ (tr.state y k).fg.tree) :
    HigherReportBy tr H g P T ∨
      (P ∈ (Node.frame (tr.state y k)).tree ∧
        (Node.frame (tr.state y k)).Anc (Node.frame (tr.state y k)).fcRoot P ∧
        P ∈ (Node.frame (tr.state y k)).viableHeads) := by
  have hrun := hp.run
  have hm := hrun.time_mono
  have hd := hrun.time_nonneg k
  have hle : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => hm hq.le
  have hkb := hkT.trans hTb
  have hub : sp.ts u + sp.Δ ≤ b := hk.trans hkb
  have hΔ := sp.toParams.hΔ
  -- finality is below `P`
  have hσ : tr.time k < sp.ts (sp.slot (tr.time k) + 1 : Nat) := not_le.1 fun h => by
    have := (AC.ts_le_iff_le_slot sp hd _).1 h
    push_cast at this
    omega
  rcases finalized_below_post_at hp hP hun hgu hR hub (M := sp.slot (tr.time k))
      (fun s hs _ z q e hz hv hq hes => hext s hs z q e hz hv (hq.trans hkT) hes) hy
      (by linarith) hσ hkb with hesc | hFP
  · exact Or.inl (hesc.mono hkT)
  have hPt : P ∈ (Node.frame (tr.state y k)).tree :=
    ⟨hPy, store_anc_of_honest_anc_at hrun hp.noColl hd hle hy hFP hPy⟩
  -- a seed below `P`, and the earlier high origins compatible with `P`
  obtain ⟨v, q, l, S, hseed, hqb, -, hqt⟩ := hp.reset_seed_before_slot_at hR
  have hSP := high_origins_before_next_slot_below_at hp hP hun hgu hR hub hseed hqt hqb
  have hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time k)) := by
    have hz := hp.cutZ_lt_reset_at
    have := reset_le_ts_of_drain hp hR
    rwa [max_eq_right (by linarith)]
  rcases held_target_viableHeads_or_higher_report_covered_at hp hyz hkb hPt hseed hqb hSP
      (ResetPremisesUpTo.compatibleWithOrigins_iff.2 ⟨
        fun x r l B hrk ho => (high_origin_compatible_post_at hp hP hun hgu hR hub ho
        ((hm hrk.le).trans hkb) fun z q e hqr hz hv hs hl =>
          hext l hl z q e hz hv ((hm hqr).trans ((hm hrk.le).trans hkT)) hs).symm,
        fun hc C s hC hsm => (member_compatible_post_at hp hc hP hun hgu hR hub
          (fun s hs _ z q e hq hz hv hes =>
            hext s hs z q e hz hv ((hm hq.le).trans hkT) hes) hC hsm).symm⟩) with
    h | ⟨x, r, ell', C, hx, hrk, hto, hPC, hlt⟩
  · exact Or.inr h
  · exact Or.inl ⟨x, r, ell', C, hx, hto, (hm hrk.le).trans hkT, hPC, hlt⟩

/-- **Every `ac_to_fg` call after `t_{u+1} + 2Δ` has a candidate extending `P`**, for a node
honest at it, through slot `N + 2`, unless a node honest at its report and at `c_z` reports a
strictly higher descendant of `P` by the call: the fast lock of slot `max u (slot(t) − 2)`
(`fast_lock_renewal_post_at`) is live and within the two-slot window of `toFGCandidates` at the
call, on a block of the full viable tree. -/
theorem toFG_candidate_post_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {u N : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocksAt H)
    (hslot : P.slot = u) (hu : 0 < u) (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat)) :
    ∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell → ell.call = .toFG →
      sp.ts (u + 1 : Nat) + 2 * sp.Δ < tr.time i → sp.slot (tr.time i) ≤ N + 2 →
      tr.time i ≤ b → HigherReportBy tr H g P (tr.time i) ∨
        ∃ B ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i),
          Anc (tr.HonestBlocksAt H) P B := by
  intro y i ell hy hc _ hlo hσN hib
  by_cases hesc : HigherReportBy tr H g P (tr.time i)
  · exact Or.inl hesc
  right
  have hΔ := sp.toParams.hΔ
  have hm := hp.run.time_mono
  have hi0 := hp.run.time_nonneg i
  let σ := sp.slot (tr.time i)
  have hσlo : sp.ts σ ≤ tr.time i := (AC.ts_le_iff_le_slot sp hi0 _).2 le_rfl
  have huσ : u + 1 ≤ σ := by
    exact_mod_cast (AC.ts_le_iff_le_slot sp hi0 _).1
      (show sp.ts (u + 1 : Nat) ≤ tr.time i by linarith)
  have hvotes : ∀ s, u + 1 ≤ s → ∀ x q e, x ∈ H (tr.time q) → AC.VoteAt tr.projAC x q e →
      tr.time q ≤ tr.time i → e.msg.slot = s → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
    intro s hs x q e hx hv hq hes
    have ht := (castAt_time_bounds hp.run hp.noColl hx hv.choose_spec).1
    rw [hes] at ht
    have hsσ : s ≤ σ := by exact_mod_cast (AC.ts_le_iff_le_slot sp hi0 _).1 (ht.trans hq)
    exact ((post_drain_votes_extend_at hp hP hslot hu hun hgu hR (N := σ) (hσlo.trans hib) hib
      ).resolve_left hesc) s hs hsσ x q e hx hv hq hes
  let r := max u (σ - 2)
  have hur : u ≤ r := le_max_left _ _
  have hupd : sp.ts r + 6 * sp.Δ < tr.time i := by
    by_cases h : σ - 2 ≤ u
    · simpa only [r, max_eq_left h] using (show
        sp.ts u + 6 * sp.Δ < tr.time i by linarith [AC.ts_succ (sp := sp) u])
    · rw [show r = σ - 2 from max_eq_right (by omega)]
      have h1 := AC.ts_succ (sp := sp) (σ - 2)
      have h2 := AC.ts_succ (sp := sp) (σ - 1)
      rw [show σ - 2 + 1 = σ - 1 by omega] at h1
      rw [show σ - 1 + 1 = σ by omega] at h2
      linarith
  obtain ⟨j, D, CV, hfu, hPD⟩ :=
    ((fast_lock_renewal_post_at hp hP hslot hu hPg hun hgu hR (N := r)
      (hupd.le.trans hib) r hur le_rfl).resolve_left fun h => hesc (h.mono hupd.le)) y
      (hp.run.antitone hupd.le hy)
  obtain ⟨ellj, C, hu', hconf, hD, hCV⟩ := id hfu
  have hjt : tr.time j = sp.ts r + 6 * sp.Δ := hu'.2.2.1
  have hji : j < i := lt_of_not_ge fun h => hupd.not_ge (hjt ▸ hm h)
  have hyj := hp.run.antitone (hm hji.le) hy
  have hDj := (AC.deepest_mem hD).1.1.1
  rw [Compose.Growing.frame_of_projAC_at hp.run hyj hu'.1] at hDj
  have hPyj := mem_of_honest_anc_at hp.run hp.noColl (hp.run.time_nonneg j)
    (fun q hq => hm hq.le) hyj hPD hDj.1
  have hur' := Compose.ts_le_ts (sp := sp) hur
  refine toFG_candidate_of_viable_head_at hp.run hp.noColl hp.committeeHalf
    (by linarith [AC.ts_succ (sp := sp) r]) hfu hPD hy hc hji
    (fun x q e hx hv hs hq => hvotes (r + 1) (by omega) x q e hx hv hq hs) ?_ hib
    (by dsimp [σ, r] at *; omega)
  intro k hjk hki
  have hyk := hp.run.antitone (hm hki) hy
  have hPk := Compose.Growing.tree_mono_at hp.run (hp.run.time_nonneg k) hyk
    (fun q hq => hm hq.le) hjk hPyj
  exact (viable_head_post_at hp hP hun hgu hR hib hvotes hyk
    (by linarith [hm hjk]) (hm hki) hPk).resolve_left hesc

end Consensus.Goldilocks.Healing.Growing

end

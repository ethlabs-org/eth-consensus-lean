module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReportCover
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.UnanimousNext
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

open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-- **The higher-report escape by `T`**: a node honest at its report and at `c_z` reports, by
`T`, a descendant of `P` at a strictly greater height than `P` (in its store at the report). -/
def HigherReportBy (tr : GoldilocksTrace sp ro) (H : Time → Set (Fin sp.n)) (g : Time)
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

/-! ### The carried slot-`m` votes -/

/-- **The slot-`u` votes of nodes honest at their casts, each extending `P`, are carried** to a
slot-`(u+1)` cast of a node honest at it, when `P` is above the cast's `Σ.F` and `ḡ ≤ t_u`: as
`unanimous_carry_votes_core_at`, with each counted head extending `P` instead of being `P`. -/
theorem extend_carry_votes_core_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hext : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hg : AC.gbar g ≤ sp.ts u)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hcast : AC.CastAt tr.projAC y i ell e)
    (hs : e.msg.slot = u + 1) (hib : tr.time i ≤ b)
    (hFP : Anc (tr.HonestBlocksAt H) ell.frame.F P) :
    AC.CarryAt tr.projAC (tr.HonestBlocksAt H) y i e u (Compose.Growing.honestVotes tr H u) := by
  have hm := hrun.time_mono
  have hmA : Monotone tr.projAC.time := hm
  have hd := hrun.time_nonneg i
  have hΔ := sp.toParams.hΔ
  have hgg := AC.le_gbar g
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hm hd
  have hr := (acRun_upTo_time hrun hnc i).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time i)) y i ell e := AC.upTo_castAt.mpr ⟨le_rfl, hcast⟩
  have hts1 : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hti : sp.ts (u + 1 : Nat) ≤ tr.time i := by
    have h := (AC.castAt_specU hr.toU hy hc').2.1
    change e.msg.slot = sp.slot (tr.time i) at h
    exact (AC.ts_le_iff_le_slot sp hd _).2 (by omega)
  have hcarry := Compose.carryAt_of_served hr
    (acRun_upTo_time hrun hnc i).vstart (Compose.frame_anc_acceptedU hr.toU hy) hy hc' hs
    (CV := Compose.Growing.honestVotes tr H u) fun v hv => by
    obtain ⟨z, q, e', hz, ⟨ell', hcz⟩, rfl, hsl⟩ := hv
    have hdq := hrun.time_nonneg q
    have hrq := (acRun_upTo_time hrun hnc q).localRun
    have hcz' := castAt_upTo_of_le le_rfl hcz
    have hslq := (AC.castAt_specU hrq.toU hz hcz').2.1
    change e'.msg.slot = sp.slot (tr.time q) at hslq
    have hqts : sp.ts u ≤ tr.time q := (AC.ts_le_iff_le_slot sp hdq _).2 (by omega)
    obtain ⟨⟨Hd, hHd, hHdr, _⟩, hqt⟩ := Compose.cast_head_fcRoot hrq (acRun_upTo_time hrun
      hnc q).vstart hz hcz'
    rw [hsl] at hqt
    change tr.time q ≤ _ at hqt
    have hqi : tr.time q ≤ tr.time i := by linarith
    have hHdp := (AC.frameIn_of_callAt hrq hz hcz'.1).2 hHd
    have hsubq := RunTrace.honestBlocks_upTo_subset (H := H) hm hdq
    obtain ⟨Hd', hHd', hHd'r, hPHd'⟩ := hext z q e' hz ⟨ell', hcz⟩ (hqi.trans hib) hsl
    obtain rfl : Hd = Hd' := hU.1 (hsubq hHdp) hHd' (hHdr.trans hHd'r.symm)
    have hFHd : Anc (tr.HonestBlocksAt H) ell.frame.F Hd := hFP.trans hPHd'
    refine ⟨hsl, ⟨tr.time q, hqts, by linarith, fun hdl => ?_⟩, Hd, hHdr, ?_⟩
    · rw [ACTrace.upTo_deadline (d := tr.time i) hmA le_rfl] at hdl
      exact (AC.upTo_messageServedBefore hmA le_rfl).mpr
        (served_of_resetService hsvc hz hcz (hgg.trans (hg.trans hqts)) hy hcast.1 hdl)
    rcases Compose.frame_anc_acceptedU hrq.toU hz q ell' hcz'.1 Hd hHd Hd .refl
        with h0 | ⟨k, hk, ha⟩
    · exact Or.inr (Or.inl h0)
    rw [RunTrace.upTo_projAC] at ha
    obtain ⟨hkq, ha⟩ := (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _ ro)).mp ha
    change tr.time k ≤ tr.time q at hkq
    have hzk := hrun.antitone hkq hz
    by_cases hkg : AC.gbar g ≤ tr.time k
    · refine Or.inl ⟨tr.time k, by linarith, fun hdl => ?_⟩
      rw [ACTrace.upTo_deadline (d := tr.time i) hmA le_rfl] at hdl
      obtain ⟨ky, hky, hacc, hkyt⟩ := relayed_of_resetService hrun hsvc hzk ha (hgg.trans hkg) hy
        hcast.1 hdl hFHd
      have hkyd : tr.time ky ≤ tr.time i := hm hky
      exact ⟨ky, hky, (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _ ro)).mpr ⟨hkyd, hacc⟩,
        by rw [ACTrace.upTo_deadline hmA hkyd]; exact hkyt⟩
    · obtain ⟨ky, hky, hacc, hkyt⟩ := caught_of_catchRun hrun hc hzk ha (not_le.mp hkg) hy
        hcast.1 (by linarith) hFHd
      exact Or.inr (Or.inr ⟨ky, (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _ ro)).mpr
        ⟨hm hky, hacc⟩, by change tr.time ky < _; linarith⟩)
  refine ⟨hcarry.awake.1, hcarry.joined, fun v hv => ?_, hcarry.holds⟩
  obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads v hv
  refine ⟨Hv, hsub hHv, hHvr, fun X hX => ?_⟩
  exact (hacc X (RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hHv hX)).imp_right
    fun ⟨k, hk, hkt⟩ => ⟨k, ((ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _ ro)).mp hk).2, hkt⟩

/-! ### The step from slot `m` to slot `m + 1` -/

/-- **Every slot-`(m+1)` vote of a node honest at it extends `P`** when every slot-`m` vote of a
node honest at it does, by strong induction on the vote's cut. As in
`unanimous_next_votes_extend_core_at`, the batch is counted at the voter's cut (`hvotes`,
`hfault`, `hcs2`); the slot-`m` votes are carried (`extend_carry_votes_core_at`); `P` is above the
caster's finality and viable at its cast (`hcast`, which may use the earlier slot-`(m+1)` votes). -/
theorem extend_next_votes_core_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hc : CatchRun tr H g (2 * sp.Δ)) {m : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hext : ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = m → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hg : AC.gbar g ≤ sp.ts m) {K : AC.CommitteeDict sp.n}
    (hPK : AC.CommitteePAt K tr.projAC H) (hTK : AC.CommitteeTAt K tr.projAC H)
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize)
    (hvotes : ∀ x, x ∈ H (sp.ts (m + 1 : Nat)) → x ∈ K.committee m → ∃ q e,
      AC.VoteAt tr.projAC x q e ∧ e.msg.slot = m ∧ tr.time q ≤ sp.ts m + sp.Δ)
    (hfault : ∀ i, sp.ts (m + 1 : Nat) ≤ tr.time i → tr.time i ≤ b →
      AC.FaultBoundK K m tr.projAC (H (tr.time i)) (tr.time i))
    (hcs2 : ∀ i, sp.ts (m + 1 : Nat) ≤ tr.time i → tr.time i ≤ b →
      2 * (K.committee (m + 1) ∩ (H (tr.time i))ᶜ).ncard < sp.committeeSize)
    (hcast : ∀ y j ell e, y ∈ H (tr.time j) → AC.CastAt tr.projAC y j ell e →
      e.msg.slot = m + 1 → tr.time j ≤ b →
      (∀ x q e', q < j → x ∈ H (tr.time q) → AC.VoteAt tr.projAC x q e' →
        e'.msg.slot = m + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e'.msg P) →
      Anc (tr.HonestBlocksAt H) ell.frame.F P ∧ AC.ViableAtVote ell e (m + 1) P) :
    ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = m + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  have hΔ := sp.toParams.hΔ
  have hts1 : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hacr := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have all : ∀ j, tr.time j ≤ b → ∀ y e, y ∈ H (tr.time j) →
      AC.VoteAt tr.projAC y j e → e.msg.slot = m + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      rintro hjb y e hy ⟨ell, hc'⟩ hs
      have htime : sp.ts (m + 1 : Nat) ≤ tr.time j := by
        have := (castAt_time_bounds hrun hnc hy hc').1
        rwa [hs] at this
      obtain ⟨hFP, hvi⟩ := hcast y j ell e hy hc' hs hjb
        fun x q e' hq hx hv hvs => ih q hq ((hrun.time_mono hq.le).trans hjb) x e' hx hv hvs
      have hcarry := extend_carry_votes_core_at hrun hnc hsvc hc hext hg hy hc' hs hjb hFP
      have hf := hfault j htime hjb
      have hhalf : sp.committeeSize ≤ 2 * {x | x ∈ H (tr.time j) ∧ ∃ q e', x ∈ H (tr.time q) ∧
          AC.VoteAt tr.projAC x q e' ∧ e'.msg.slot = m}.ncard := by
        have hsub : K.committee m ∩ H (tr.time j) ⊆ {x | x ∈ H (tr.time j) ∧ ∃ q e',
            x ∈ H (tr.time q) ∧ AC.VoteAt tr.projAC x q e' ∧ e'.msg.slot = m} := by
          rintro x ⟨hxK, hx⟩
          obtain ⟨q, e', hv, hvs, hq⟩ := hvotes x (hrun.antitone htime hx) hxK
          exact ⟨hx, q, e', hrun.antitone (by linarith) hx, hv, hvs⟩
        have h₁ := Set.ncard_le_ncard hsub
        have h₂ := Set.ncard_le_ncard (s := K.committee m ∩ {y | y ∈ H (tr.time j) ∧
            tr.projAC.awake y (tr.time j) ∧ AC.JoinedAt tr.projAC y (tr.time j)})
          (t := K.committee m ∩ H (tr.time j)) (fun x hx => ⟨hx.1, hx.2.1⟩)
        have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (K.committee m) (H (tr.time j))
          (Set.toFinite _)
        rw [hsize m, Set.sdiff_eq_compl_inter, Set.inter_comm (H (tr.time j))ᶜ] at hsplit
        unfold AC.FaultBoundK at hf
        omega
      refine AC.Growing.next_transfer_from hacr K hPK hTK hsize hy hc' hs ?_ hhalf hcarry hf
        (hcs2 j htime hjb) hvi ?_
      · intro x q e' hx hv hvs
        have hq := (castAt_time_bounds hrun hnc hx hv.choose_spec).2
        rw [hvs] at hq
        exact hext x q e' hx hv (by linarith) hvs
      · intro x q hq hx e' hv hvs
        exact ih q hq ((hrun.time_mono hq.le).trans hjb) x e' hx hv hvs
  exact fun y j e hy hv hjb hs => all j hjb y e hy hv hs

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
  have ha0 : 0 ≤ a := by linarith [AC.gbar_nonneg g, sp.toParams.hΔ]
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
  obtain ⟨x, r, l, B, ho, hrk, hrb, hFB⟩ :=
    ProposalImpl.finalized_below_high_origin_at hp hy ha hkb
  have hBP := high_origin_compatible_post_at hp hP hun hgu hR hub ho hrb
    fun z q e hqr hz hv hs hl => by
      obtain ⟨-, -, ⟨CV, ell, D, -, hfl, -⟩, -⟩ := ho
      have hlr := ProposalImpl.ts_le_of_fastLock_at hp.run hfl
      have hlM : l ≤ M := by
        have := (AC.ts_lt_iff sp).1 (show sp.ts l < sp.ts (M + 1 : Nat) by linarith)
        omega
      exact hext l hl hlM z q e hz hv ((hp.run.time_mono hqr).trans hrk) hs
  have hFc : Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F P := by
    rcases hBP with h | h
    · exact Or.inl (hFB.trans h)
    · exact AC.anc_total hU hFB h
  rcases hp.finality_below_or_higher_report_at hy hkb hFc with
    h | ⟨z, r, l, C, hz, hrk, hto, hPC, hlt⟩
  · exact Or.inr h
  · exact Or.inl ⟨z, r, l, C, hz, hto, hp.run.time_mono hrk.le, hPC, hlt⟩

/-- **A slot-`(m+1)` cast after a run of slots extending `P` has `P` above its finality and
viable**, or a higher report extends `P` by the cast, given that the earlier honest slot-`(m+1)`
votes extend `P`. Every high origin written before the cast is compatible with `P`
(`high_origin_compatible_post_at`), so the fork-choice root, below such an origin or genesis, is
compatible with `P`. If it is below `P`, the caster accepted `P` before `t_u + 3Δ`
(`unanimous_head_accepted_core_at`), so `P` is in the voter block tree, and it is a viable head
unless the head-height floor passed it, which a strictly higher report causes. Otherwise `P` is
below the root, and the caster's finality, below the root too, is below `P` unless a strictly
higher report finalized above it. -/
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
    (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
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
  -- the call frame
  obtain ⟨hPhi, hPhiS⟩ := frame_tree_subset_at hrun hp.noColl hy hc.1
  have hPhiU : ell.frame.tree ⊆ tr.HonestBlocksAt H :=
    fun _ hX => ⟨y, j, tr.time j, hd, fun _ hq => hm hq.le, hy, hPhiS hX⟩
  have hFr : Anc (tr.HonestBlocksAt H) ell.frame.F ell.frame.fcRoot :=
    hPhi.F_anc_fcRoot.mono hPhiU
  have hFeq : ell.frame.F = (tr.state y j).fg.F := by
    have hc' : (tr.upTo (tr.time j)).projAC.CallAt y j ell := by
      rw [RunTrace.upTo_projAC]
      exact (Trace.upTo_callAt_of_le _ le_rfl).mpr hc.1
    rw [Compose.frame_of_projAC (hrun.upTo hd) hy hc',
      RunTrace.upTo_state_of_le hm le_rfl]
    rfl
  -- the fork-choice root is compatible with `P`
  have hroot : Compatible (tr.HonestBlocksAt H) ell.frame.fcRoot P := by
    rcases hp.reset_vote_root_source_at hRm hy hc hs hjb with hg | ⟨v, r, l, O, ho, hrt, -, hO⟩
    · exact Or.inl (ProposalImpl.genesis_root_anc_at hp.run hp.noColl (hPhiU hPhi.fcRoot_mem)
        hg hP)
    · rcases hbefore v r l O ho (by linarith) (Or.inr hrt) with h | h
      · exact Or.inl (hO.trans h)
      · exact AC.anc_total hU hO h
  by_cases hrootP : Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P
  · -- `P` is accepted before the freeze, so it is in the voter block tree
    have hnr : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ AC.gbar g := fun r hrj hrs =>
      hp.noRestart y r (hrun.antitone (hm hrj) hy) hrs ((hm hrj).trans hjb)
    obtain ⟨k', hk'j, ha', hk't⟩ := unanimous_head_accepted_core_at hp.run hp.noColl hp.sync
      hp.catchUp hP hslot hu hun (by linarith [AC.le_gbar g]) hy hc.1
      (by have := @hstep u; linarith) hjb hnr (exists_honest_slot_vote_at hp hgu hR hub)
      (hFr.trans hrootP)
    have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hm hd
    have hr := (acRun_upTo_time hrun hp.noColl j).localRun
    have hc' := castAt_upTo_of_le le_rfl hc
    obtain ⟨hPhi', hPhiU'⟩ := AC.frameIn_of_callAt hr hy hc'.1
    have ha'' : (tr.upTo (tr.time j)).projAC.AcceptAt y k' P := by
      rw [RunTrace.upTo_projAC]
      exact (ACTrace.upTo_acceptAt (A := AC.goldilocksAC sp _ ro)).mpr ⟨hm hk'j, ha'⟩
    have hPp : P ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)) := by
      obtain ⟨ella, hca, hba⟩ := ha''
      exact (AC.frameIn_of_callAt hr hy hca).2
        ((AC.accept_new sp hr hy ⟨ella, hca, hba⟩).1 ella hca)
    have hrootp := RunTrace.anc_upTo_of_right hrun.toLocalRun hp.noColl hd hPp hrootP
    have hFP := (hPhi'.F_anc_fcRoot.mono hPhiU').trans hrootp
    have hacc : AC.AcceptedBefore (tr.upTo (tr.time j)).projAC y P (sp.ts m + 3 * sp.Δ) :=
      Or.inr ⟨k', ha'', by change tr.time k' < _; linarith [hts (show u ≤ m by omega)]⟩
    have hPt := Compose.accepted_voter_tree (hrun.upTo hd) (hp.noColl.upTo _) hy hc' hs hPp
      hacc hFP
    have hfr := Compose.frame_of_projAC (hrun.upTo hd) hy hc'.1
    have hst := RunTrace.upTo_state_of_le (y := y) hm (le_refl (tr.time j))
    have hstore : P ∈ (tr.state y j).fg.tree := by
      have hmem := hPt.1
      rw [hfr, hst] at hmem
      exact hmem.1
    by_cases hfloor : (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ P.root).h
    · -- `P` is a viable head of the voter block tree
      refine Or.inr ⟨Anc.mono hsub hFP, Or.inl ?_⟩
      have hroot' := AC.anc_tree_of_anc_U hr.coherent hPhi' hPhiU' hPhi'.fcRoot_mem hrootp hPt.1
      refine ⟨hPt, hroot', P, hPt, ?_, .refl⟩
      have hmem := hPt.1
      rw [hfr, hst] at hmem hroot' ⊢
      exact ⟨hmem.1, hmem.2, hroot'.mono (fun X hX => hX.1), hfloor⟩
    · -- the floor passed `P`: a strictly higher report
      obtain ⟨v, q, l, S, hseed, hqb, -, hqt⟩ := hp.reset_seed_before_slot_at hR
      have hSP := high_origins_before_next_slot_below_at hp hP hun hgu hR hub hseed hqt hqb
      obtain ⟨x, r, ell', C, hx, hrj, hto, hPC, hlt⟩ :=
        hp.held_target_high_floor_report_before_at hy hjb hstore hseed hSP
          (fun x r l B hrj ho x' r' l' B' hr'j ho' => hp.origins_compatible_at ho
            ((hm hrj.le).trans hjb) ho' ((hm hr'j.le).trans hjb))
          (fun x r l B hrj ho => hp.origins_compatible_at hseed hqb ho ((hm hrj.le).trans hjb))
          (fun x r l B hrj ho => (hbefore x r l B ho (hm hrj.le) (Or.inl hrj)).symm)
          (lt_of_not_ge hfloor)
      exact Or.inl ⟨x, r, ell', C, hx, hto, hm hrj.le, hPC, hlt⟩
  · -- `P` is below the root; the finality is below `P` or a higher report finalized above it
    have hPR := hroot.resolve_left hrootP
    have hFc : Compatible (tr.HonestBlocksAt H) (tr.state y j).fg.F P :=
      hFeq ▸ AC.anc_total hU hFr hPR
    rcases hp.finality_below_or_higher_report_at hy hjb hFc with
      hFP | ⟨z, r, l, C, hz, hrj, hto, hPC, hlt⟩
    · refine Or.inr ⟨hFeq ▸ hFP, Or.inr ?_⟩
      have hPt := unanimous_head_held_at_call_at hp hP hun hgu hR hy hc.1
        (by have := @hstep u; linarith) hjb hFP
      exact AC.anc_tree_of_anc_U hU hPhi hPhiU hPt hPR hPhi.fcRoot_mem
    · exact Or.inl ⟨z, r, l, C, hz, hto, hm hrj.le, hPC, hlt⟩

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
      (fun _ _ _ _ hy hcast hs hjb => hp.reset_vote_root_below_bound_at hR hP
        (fun _ _ _ _ ho ht hrb => high_origins_before_next_slot_below_at hp hP hun hgu hR hub
          ho ht hrb) hy hcast hs hjb)
      (fun _ _ _ _ hy hcast hs hjb hstore => hp.reset_vote_floor_above_old_at hy hR hcast hs hjb
        hstore (fun _ _ _ _ ho ht hrb => high_origins_before_next_slot_below_at hp hP hun hgu hR
          hub ho ht hrb)) y j e hy hv (hjT.trans hTb) hs
  | succ m hum ih =>
    intro hmN
    have hprev := ih (by omega)
    have hm1 := hts (show m + 1 ≤ N by omega)
    have hmb : sp.ts m + sp.Δ ≤ b := by have := @hstep m; linarith
    have hgm : AC.gbar g + 4 * sp.Δ ≤ sp.ts m := (hgu.trans (hts (by omega)))
    have hRm : drainTime sp a ≤ sp.ts (m + 1 : Nat) := hR.trans (hts (by omega))
    have hnext := extend_next_votes_core_at hp.run hp.noColl (resetService_mono hp.sync hTb)
      hp.catchUp (hprev m hum le_rfl) (by linarith [AC.le_gbar g]) hp.committeeFacts.hP
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
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
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
    have hbase := (AC.ts_le_iff_le_slot sp (AC.gbar_nonneg g) (sp.slot (AC.gbar g))).2 (by rfl)
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
  -- the deepest unvetoed fast block of the path extends `P`
  have hr := (Compose.goldilocks_ac_projection_from (hp.run.upTo (hp.run.time_nonneg k))
    (hp.noColl.upTo (tr.time k))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc' : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩
  have hPhi := AC.frameIn_of_callAt hr hyk hc'
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hp.run.time_mono
    (hp.run.time_nonneg k)
  have hΦU : ell.frame.tree ⊆ tr.HonestBlocksAt H := fun Q hQ => hsub (hPhi.2 hQ)
  have hfr := (hp.run.cutLaw y k (.ac ell) (Compose.projAC_callAt.mp hu.1) hyk).1
  have hFe : ell.frame.F = (tr.state y k).fg.F := by rw [hfr]; rfl
  have hFP : Anc (tr.HonestBlocksAt H) ell.frame.F P := by
    rw [hFe]; exact hfin y k hyk hklo hk'.le hkb
  obtain ⟨⟨hDt, -, -⟩, hDf⟩ := (AC.deepest_mem hfs).1
  have hCt := (AC.deepest_mem hconf).1.1
  have hPt : P ∈ ell.frame.tree := AC.frame_mem_of_between sp hU hPhi.1 hΦU hDt hPD hFP
  have hPDf : ell.frame.Anc P D := AC.anc_tree_of_anc_U hU hPhi.1 hΦU hPt hPD hDt
  have hPCf : ell.frame.Anc P C := AC.anc_tree_of_anc_U hU hPhi.1 hΦU hPt hPC hCt
  have hPf : AC.FastTest sp (tr.projAC.state y k) ell.frame (s + 1) P :=
    hDf.trans (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard
      (AC.supporters_antitone sp _ ell.frame _ _ P D hPDf) (Set.toFinite _)))
  exact ⟨k, fast_update_of_unvetoed_at hyk hp.run hp.noColl hu hconf hPt hPg hPCf
    (no_veto_of_lock_roots_compatible_at hp.run hp.noColl hyk hu.1 hPt hlocks) hPf⟩

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
  rcases held_target_viableHeads_or_higher_report_at hp hyz hkb hPt hseed hqb hSP
      (fun x r l B hrk ho => (high_origin_compatible_post_at hp hP hun hgu hR hub ho
        ((hm hrk.le).trans hkb) fun z q e hqr hz hv hs hl =>
          hext l hl z q e hz hv ((hm hqr).trans ((hm hrk.le).trans hkT)) hs).symm) with
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
  intro y i ell hy hc hto hlo hσN hib
  by_cases hesc : HigherReportBy tr H g P (tr.time i)
  · exact Or.inl hesc
  right
  have hΔ := sp.toParams.hΔ
  have hm := hp.run.time_mono
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hstep {m : Nat} : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hi0 := hp.run.time_nonneg i
  -- the slot of the call
  set σ := sp.slot (tr.time i) with hσ
  have hσlo : sp.ts σ ≤ tr.time i := (AC.ts_le_iff_le_slot sp hi0 _).2 le_rfl
  have huσ : u + 1 ≤ σ := by
    by_contra hn
    have := hts (show σ ≤ u by omega)
    have := hts (show σ + 1 ≤ u + 1 by omega)
    have hlt : tr.time i < sp.ts (σ + 1 : Nat) := by
      by_contra h
      have := (AC.ts_le_iff_le_slot sp hi0 ((σ + 1 : Nat) : Int)).1 (not_lt.1 h)
      omega
    have := @hstep u
    linarith
  -- the honest votes cast by the call extend `P`
  have hvotes : ∀ s, u + 1 ≤ s → ∀ x q e, x ∈ H (tr.time q) → AC.VoteAt tr.projAC x q e →
      tr.time q ≤ tr.time i → e.msg.slot = s → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
    intro s hs x q e hx hv hq hes
    have hsσ : s ≤ σ := by
      have := (castAt_time_bounds hp.run hp.noColl hx hv.choose_spec).1
      rw [hes] at this
      exact (AC.ts_le_iff_le_slot sp hi0 _).1 (this.trans hq) |> fun h => by exact_mod_cast h
    exact ((post_drain_votes_extend_at hp hP hslot hu hun hgu hR (N := σ) (hσlo.trans hib) hib
      ).resolve_left hesc) s hs hsσ x q e hx hv hq hes
  -- the fast lock of slot `r = max u (σ − 2)`, written strictly before the call
  obtain ⟨r, hur, hupd, hσr, hrσ⟩ : ∃ r, u ≤ r ∧
      sp.ts r + 6 * sp.Δ < tr.time i ∧ σ ≤ r + 2 ∧ r + 1 ≤ σ := by
    by_cases h2 : u + 2 ≤ σ
    · refine ⟨σ - 2, by omega, ?_, by omega, by omega⟩
      have h1 := @hstep (σ - 2)
      have h2' := @hstep (σ - 1)
      rw [show σ - 2 + 1 = σ - 1 by omega] at h1
      rw [show σ - 1 + 1 = σ by omega] at h2'
      linarith
    · exact ⟨u, le_rfl, by have := @hstep u; linarith, by omega, by omega⟩
  have hyr : y ∈ H (sp.ts r + 6 * sp.Δ) := hp.run.antitone hupd.le hy
  obtain ⟨j, D, CV, hfu, hPD⟩ :=
    ((fast_lock_renewal_post_at hp hP hslot hu hPg hun hgu hR (N := r)
      (hupd.le.trans hib) r hur le_rfl).resolve_left
      fun h => hesc (h.mono hupd.le)) y hyr
  have hjt : tr.time j = sp.ts r + 6 * sp.Δ := by
    obtain ⟨_, _, hu', _⟩ := hfu
    exact hu'.2.2.1
  have hji : j < i := by
    by_contra hn
    have := hm (show i ≤ j by omega)
    linarith
  -- `P` is held from the update on
  have hyj : y ∈ H (tr.time j) := hp.run.antitone (hm hji.le) hy
  have hFPj : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F P :=
    (finalized_below_post_at hp hP hun hgu hR (by linarith [hts (show u ≤ r from hur)])
      (M := σ) (fun s h1 _ x q e hx hv hq hs => hvotes s h1 x q e hx hv (hq.trans (hm hji.le)) hs)
      hyj (by rw [hjt]; linarith [hts hur]) (by
        have := @hstep σ
        have : sp.ts (σ + 1 : Nat) ≤ sp.ts (σ + 1 : Nat) := le_rfl
        have hσ1 : tr.time i < sp.ts (σ + 1 : Nat) := by
          by_contra h
          have := (AC.ts_le_iff_le_slot sp hi0 ((σ + 1 : Nat) : Int)).1 (not_lt.1 h)
          omega
        linarith [hm hji.le]) ((hm hji.le).trans hib)).resolve_left
      fun h => hesc (h.mono (hm hji.le))
  obtain ⟨ellj, C, hu', hconf, hD, hCV⟩ := hfu
  have hfrj := Compose.Growing.frame_of_projAC_at hp.run hyj hu'.1
  obtain ⟨hΦj, hΦjU⟩ := Compose.Growing.frameIn_at hp.run hp.noColl hyj hu'.1
  have hPj : P ∈ ellj.frame.tree := AC.frame_mem_of_between sp hU hΦj hΦjU
    (AC.deepest_mem hD).1.1.1 hPD (by rw [hfrj]; exact hFPj)
  have hPyj : P ∈ (tr.state y j).fg.tree := by rw [hfrj] at hPj; exact hPj.1
  refine toFG_candidate_of_viable_head_at hp.run hp.noColl hp.committeeHalf
    (by have := @hstep r; linarith [hts hur, AC.le_gbar g]) ⟨ellj, C, hu', hconf, hD, hCV⟩ hPD hy hc
    hji (fun x q e hx hv hs hq => hvotes (r + 1) (by omega) x q e hx hv hq hs) ?_ hib (by omega)
  intro k hjk hki
  have hyk := hp.run.antitone (hm hki) hy
  have hPk := Compose.Growing.tree_mono_at hp.run (hp.run.time_nonneg k) hyk
    (fun q hq => hm hq.le) hjk hPyj
  exact (viable_head_post_at hp hP hun hgu hR hib
    (fun s hs x q e hx hv hq hes => hvotes s hs x q e hx hv hq hes) hyk
    (by linarith [hm hjk, hts hur]) (hm hki) hPk).resolve_left hesc

end Consensus.Goldilocks.Healing.Growing

end

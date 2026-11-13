module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.HeldRow
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote

public section

/-! # Goldilocks under `Sleepy`: the source labels at a vote

At an honest slot-`(s+1)` vote, every honest attestation on a block the voter holds has a source
below an origin of label at most `s` (`vote_row_source`). An origin of label `s + 1` is optimistic
and would precede a held row (`no_optimistic_before_held_row_of`, from the steps of `HeldRow`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- `no_optimistic_before_held_row` with `2|K(s+1) ∩ Hᶜ| < committeeSize`, for a member `y` of the
slot-`(s+1)` committee. -/
theorem no_optimistic_before_held_row_of {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (K : SA.CommitteeDict sp.n) (hP : SA.CommitteeP K tr.projAC H)
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {s : Nat}
    (hfK : 2 * (K.committee (s + 1) ∩ Hᶜ).ncard < sp.committeeSize) {y : Fin sp.n} (hy : y ∈ H)
    (hyK : y ∈ K.committee (s + 1)) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} {m : Nat} (hm : tr.AcceptAt y m X) (hmi : m < i)
    {a : FG.Att sp.n} (hav : a.val ∈ H) {k : Nat} (hkm : k < m) (hsg : tr.SignAt a.val k a)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (hck : c < k) {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (Vote sp.n)} (hO : SA.OptimisticLockAt tr.projAC z c (s + 1) C CV) : False := by
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  have hmono := hrun.time_mono
  obtain ⟨-, -, -, hslc, -⟩ := id hO
  rcases held_row_sign_time hrun hav hsg (hr.time_nonneg c) hslc (hmono hck.le)
      ((hmono hkm.le).trans ((hmono hmi.le).trans
        (by rw [← hs]; exact (cast_head_fcRoot_from hr hrun.vstart hy hc).2))) with ⟨hT0, -⟩ | hT
  · -- at `t_{s+1}`: a one-member committee, and the voter has a second slot-`(s+1)` vote by
    -- the check
    obtain ⟨u, hu, hall, j', hj', e', hv', hs'⟩ :=
      held_row_early_count hrun hnc K hP hsize hfK hav hsg hT0 hz hck hO
    obtain rfl : u = y := (hall y hyK).symm
    have := (SA.one_vote_per_slotU sp _ ro H _ tr.projAC hr.toU u hu j' i e' e hv' ⟨ℓ, hc.1, hc.2⟩
      (hs'.trans hs.symm)).1
    omega
  · -- at `t_{s+1} + Δ`: the voter's own tick there votes before the block arrives
    exact held_row_late_absurd hrun hnc hy hc hs hm hmi hkm hT

/-- **Sources at a vote have labels at most `s`** (R4):
at an honest slot-`(s+1)` vote, every honest attestation on a block the voter holds has
a source below an origin of label at most `s`. A regular origin of label `l` is written at
`t_l + 6Δ`, after the vote unless `l < s`; an optimistic one of label `l ≥ s + 2` after
`t_{s+2}`; label `s + 1` is `no_optimistic_before_held_row`. -/
theorem vote_row_source {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    (K : SA.CommitteeDict sp.n) (hP : SA.CommitteeP K tr.projAC H)
    (hsize : ∀ σ, (K.committee σ).ncard = sp.committeeSize) {s : Nat}
    (hfK : 2 * (K.committee (s + 1) ∩ Hᶜ).ncard < sp.committeeSize) {y : Fin sp.n} (hy : y ∈ H)
    (hyK : y ∈ K.committee (s + 1)) {i : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hs : e.msg.slot = s + 1)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y i).fg.tree)
    {a : FG.Att sp.n} (ha : a ∈ X.fgPayload) (hav : a.val ∈ H) :
    ∃ D ∈ tr.HonestBlocks H, IsHonestSource tr H D a.T ∧
      ∃ C j, OriginBefore tr H C j i ∧ j ≤ s ∧ Anc (tr.HonestBlocks H) D C := by
  have hr := (goldilocks_ac_projection_from hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨m, hmi, hm, k, hkm, hsg⟩ := honest_row_signed_before hrun hnc hy hX ha hav
  obtain ⟨D, hDU, hDs, C, l, hC, hDC⟩ := attestation_source hrun hnc hav hsg
  obtain ⟨z, hz, c, hck, CV, hRO⟩ := originBefore_iff.1 hC
  refine ⟨D, hDU, hDs, C, l, originBefore_iff.2 ⟨z, hz, c, by omega, CV, hRO⟩, ?_, hDC⟩
  -- the vote is cast by `t_{s+1} + Δ`, after the origin's event
  have hti : tr.time i ≤ sp.ts s + 5 * sp.Δ := by
    have h : tr.time i ≤ sp.ts (e.msg.slot : Int) + sp.Δ :=
      (cast_head_fcRoot_from hr hrun.vstart hy hc).2
    rw [hs] at h
    simp only [SAParams.ts] at h ⊢
    push_cast at h
    linarith only [h]
  have hci : tr.time c ≤ tr.time i := hrun.time_mono (by omega)
  by_contra hl
  have hl' : (s : Int) + 1 ≤ (l : Int) := by exact_mod_cast Nat.lt_of_not_le hl
  rcases hRO with ⟨ℓR, ⟨-, -, htR, -⟩, -⟩ | hO
  · -- a regular origin of label `l > s` is written at `t_l + 6Δ ≥ t_{s+1} + 6Δ`
    have htR' : tr.time c = sp.ts (l : Int) + 6 * sp.Δ := htR
    simp only [SAParams.ts] at htR' hti
    linarith only [htR', hti, hci, hΔ, mul_le_mul_of_nonneg_left hl' hΔ.le]
  · rcases Nat.lt_or_ge l (s + 2) with hl2 | hl2
    · obtain rfl : l = s + 1 := by omega
      exact no_optimistic_before_held_row_of hrun hnc K hP hsize hfK hy hyK hc hs hm hmi hav hkm
        hsg hz hck hO
    · -- an optimistic origin of label `l ≥ s + 2` is selected from `t_l ≥ t_s + 8Δ` on
      obtain ⟨ℓO, A, -, hslot, -⟩ := hO
      have h := (SA.ts_le_iff_le_slot sp (hr.time_nonneg c) (l : Int)).2
        (le_of_eq (by rw [hslot]))
      have h' : sp.ts (l : Int) ≤ tr.time c := h
      have hl2' : (s : Int) + 2 ≤ (l : Int) := by exact_mod_cast hl2
      simp only [SAParams.ts] at h' hti
      linarith only [h', hti, hci, hΔ, mul_le_mul_of_nonneg_left hl2' hΔ.le]

end Consensus.Goldilocks.Compose

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.SignUnique
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.VoteDelivery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.SlotStart
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The source of a delivered row precedes the voter's label

The counted signer remains honest at the reader observation. This permits
retaining the two local executions for causal ordering, not their dynamic
cache invariants or historical high origins.
-/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

private theorem optimistic_upTo {t : Time}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {v : Fin sp.n} {r l : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hrt : tr.time r ≤ t)
    (h : SA.OptimisticLockAt tr.projAC v r l D CV) :
    SA.OptimisticLockAt (tr.upTo t).projAC v r l D CV := by
  rw [RunTrace.upTo_projAC]
  obtain ⟨ell, A, ⟨hc, hpt⟩, hsl, hsel, hCV⟩ := h
  have he := Trace.upTo_state tr.projAC v
    (fun k (hk : k < r) => (hrun.time_mono hk.le).trans hrt)
  refine ⟨ell, A, ⟨(Trace.upTo_callAt tr.projAC).mpr ⟨hrt, hc⟩, ?_⟩, hsl, hsel, hCV⟩
  simpa only [he, Trace.upTo_time] using hpt

/-- A row delivered before the cast cannot follow a same-slot optimistic write.
The signer is selected from the reader's honest cohort. -/
theorem row_origin_not_current_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y v : Fin sp.n} {k d r : Nat}
    (hy : y ∈ H (tr.time k)) (hv : v ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    (hs : tr.SignAt v d att) (hdk : d < k) (hrd : r < d)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)} :
    ¬ SA.OptimisticLockAt tr.projAC v r e.msg.slot D CV := by
  intro hopt
  have ht := hrun.time_nonneg k
  have hr₀ := hrun.upTo ht
  have hc' : (tr.upTo (tr.time k)).projAC.CallAt y k ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc.1⟩
  have hcast : SA.CastAt (tr.upTo (tr.time k)).projAC y k ell e := ⟨hc', hc.2⟩
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time k)) _ proposer
    hr₀ (hnc.upTo _)).localRun
  have he := Trace.upTo_state tr y (fun q (hq : q < k) => hrun.time_mono hq.le)
  have hW' : W ∈ ((tr.upTo (tr.time k)).state y k).fg.tree := by rwa [he]
  rcases Healing.tree_accepted hr₀.toLocalRun hy hW' with rfl | ⟨i, hik, hA⟩
  · cases ha
  have hA' := ((RunTrace.upTo_acceptAt tr).mp hA).2
  obtain ⟨src, hcd⟩ := hs
  have hs' := (RunTrace.upTo_signAt tr).mpr ⟨hrun.time_mono hdk.le, ⟨src, hcd⟩⟩
  have hav : att.val = v := by
    have hcAtt := (hr₀.cutLaw v hv d _ hs'.choose_spec).1
    unfold Store.attest at hcAtt
    unfold FG.Record.createAtt at hcAtt
    split at hcAtt
    · cases hcAtt
    · dsimp only at hcAtt
      split_ifs at hcAtt
      exact (congrArg FG.Att.val (Prod.mk.inj (Option.some.inj hcAtt)).1).symm
  obtain ⟨d₀, hd₀, hs₀⟩ := hrun.toLocalRun.att_unforgeable y i att
    (hrun.antitone (hrun.time_mono hik.le) hy) (Or.inr ⟨W, ⟨true, hA'⟩, ha⟩)
    (hav ▸ hrun.antitone (hrun.time_mono hik.le) hv)
  rw [hav] at hs₀
  have heq : d₀ = d := sign_unique_at hrun ht hv
    (hrun.time_mono (hd₀.trans hik).le) (hrun.time_mono hdk.le) hs₀ ⟨src, hcd⟩
  subst d₀
  have hkt : tr.time k ≤ sp.ts e.msg.slot + sp.Δ := (Compose.cast_head_fcRoot hr hy hcast).2
  have hrt : sp.ts e.msg.slot ≤ tr.time r := by
    obtain ⟨-, -, -, hsl, -⟩ := hopt
    change sp.slot (tr.time r) = e.msg.slot at hsl
    exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg r) _).2
      (by change (e.msg.slot : Int) ≤ sp.slot (tr.time r); rw [hsl])
  have h₁ := hrun.time_mono hrd.le
  have h₂ := hrun.time_mono hd₀.le
  have h₃ := hrun.time_mono hik.le
  obtain ⟨c, hcTime⟩ := Compose.sign_public hr₀ hv hs'.choose_spec
  change tr.time d = sp.Δ * c at hcTime
  have hDelta : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts e.msg.slot = sp.Δ * (4 * (e.msg.slot : Int)) := by
    simp only [SAParams.ts]; ring
  have hc₁ : 4 * (e.msg.slot : Int) ≤ c :=
    le_of_mul_le_mul_left (show sp.Δ * (4 * (e.msg.slot : Int)) ≤ sp.Δ * c by
      linarith only [hrt, hcTime, hts, h₁]) hDelta
  have hc₂ : c ≤ 4 * (e.msg.slot : Int) + 1 :=
    le_of_mul_le_mul_left (show sp.Δ * c ≤ sp.Δ * (4 * (e.msg.slot : Int) + 1) by
      rw [mul_add, mul_one]; linarith only [hkt, hcTime, hts, h₂, h₃]) hDelta
  obtain hcc | hcc : c = 4 * (e.msg.slot : Int) ∨ c = 4 * (e.msg.slot : Int) + 1 := by omega
  · obtain ⟨hn1, j', hj', e', hve', hes⟩ := slot_start_optimistic hr₀ (hnc.upTo _) hv hs'
      (by change tr.time d = _; rw [hcTime, hcc, hts]) hrd
      (optimistic_upTo hrun ((hrun.time_mono hrd.le).trans (hrun.time_mono hdk.le)) hopt)
    obtain rfl : v = y := Fin.ext (by have := v.2; have := y.2; omega)
    have := ((SA.one_vote_per_slot sp) _ ro (H (tr.time k)) _ _ hr v hy j' k e' e hve'
      ⟨ell, hcast⟩ hes).1
    omega
  · apply vote_before_late_delivery_at hrun hnc hy hc hA' hik
    have : tr.time d = sp.ts e.msg.slot + sp.Δ := by
      rw [hcTime, hcc, hts]; ring
    linarith only [hkt, h₂, h₃, this]

/-- The source label of a counted row is strictly below the actual cast's label. -/
theorem row_origin_label_lt_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g : Time} {y v : Fin sp.n} {k d r l : Nat}
    (hy : y ∈ H (tr.time k)) (hv : v ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    (hs : tr.SignAt v d att) (hdk : d < k) (hrd : r < d)
    {O : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g v r l O) :
    l < e.msg.slot := by
  have hc' : (tr.upTo (tr.time k)).projAC.CallAt y k ell := by
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc.1⟩
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time k)) _ proposer
    (hrun.upTo (hrun.time_nonneg k)) (hnc.upTo _)).localRun
  obtain ⟨CV, ellw, D, _, hfl, _⟩ := ho.2.2.1
  have hk := (SA.castAt_spec hr hy ⟨hc', hc.2⟩).2.1
  change e.msg.slot = sp.slot (tr.time k) at hk
  have htr : tr.time r ≤ tr.time k := hrun.time_mono (by omega)
  rcases hfl with ⟨ell', C, ⟨-, -, ht, -⟩, -, -, -, -⟩ | hopt
  · change tr.time r = sp.ts l + 6 * sp.Δ at ht
    have hDelta := sp.toParams.hΔ
    have h₁ : sp.ts (l + 1 : Nat) ≤ tr.time k := by
      have he : sp.ts (l + 1 : Nat) = sp.ts l + 4 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      rw [he]
      linarith only [hDelta, htr, ht]
    have h₂ := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg k) _).mp h₁
    omega
  · have hl : l ≤ e.msg.slot := by
      obtain ⟨-, -, -, hsl, -⟩ := hopt
      change sp.slot (tr.time r) = l at hsl
      rw [hk, ← hsl]
      exact SA.slot_mono sp (hrun.time_nonneg r) htr
    rcases hl.lt_or_eq with hl | rfl
    · exact hl
    · exact absurd hopt
        (row_origin_not_current_at hrun hnc hy hv hc hW ha hs hdk hrd)

end Consensus.Goldilocks.Healing.Growing.Outcome

end

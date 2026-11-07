module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.RowStart
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.RowLate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.RowSign
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run

public section

/-! # Causal labels of historically honest rows at a vote

The signer is read on its signing prefix, the voter on its voting prefix.
Neither is required to survive to the other's observation.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

private theorem signer_eq
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {v : Fin sp.n} {d : Nat} {att : FG.Att sp.n}
    (hv : v ∈ H (tr.time d)) (hs : tr.SignAt v d att) : att.val = v := by
  obtain ⟨C, hc⟩ := hs
  have hh := (hp.run.upTo (hp.run.time_nonneg d)).cutLaw v hv d _
    ((Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩)
  have he := hh.1
  unfold Store.attest FG.Record.createAtt at he
  split at he
  · cases he
  · dsimp only at he
    split_ifs at he
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj he)
    rfl

/-- A historically honest signing carried by a held row precedes that row's acceptance. -/
private theorem sign_before_accept
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y v : Fin sp.n} {i d : Nat} {att : FG.Att sp.n}
    {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (ha : att ∈ W.fgPayload) (hA : tr.AcceptAt y i W)
    (hv : v ∈ H (tr.time d)) (hs : tr.SignAt v d att) : d < i := by
  have hav := signer_eq hp hv hs
  by_contra h
  have hid : i ≤ d := by omega
  have hvi := hp.run.antitone (hp.run.time_mono hid) hv
  obtain ⟨d₀, hd₀, hs₀⟩ := hp.run.att_unforgeable y i att hy
    (Or.inr ⟨W, ⟨true, hA⟩, ha⟩) (hav ▸ hvi)
  rw [hav] at hs₀
  have hrun := hp.run.upTo (hp.run.time_nonneg d)
  have hs' := (RunTrace.upTo_signAt tr).mpr (And.intro le_rfl hs)
  have hs₀' := (RunTrace.upTo_signAt tr).mpr
    (And.intro (hp.run.time_mono (hd₀.le.trans hid)) hs₀)
  have := sign_unique hrun hv hs₀' hs'
  omega

/-- No row held before a slot's vote comes from a same-slot optimistic write. -/
theorem row_origin_not_current_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} {d : Nat} (hv : v ∈ H (tr.time d)) (hs : tr.SignAt v d att)
    {r : Nat} (hrd : r < d) {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} : ¬ SA.OptimisticLockAt tr.projAC v r e.msg.slot D CV := by
  intro hopt
  have hm := hp.run.time_mono
  have hrunK := hp.run.upTo (hp.run.time_nonneg k)
  have hncK := hp.noColl.upTo (tr.time k)
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := (hac.upTo (hp.run.time_nonneg k)).localRun
  have hc' := SA.upTo_castAt.mpr (And.intro le_rfl hc)
  have hW' : W ∈ ((tr.upTo (tr.time k)).state y k).fg.tree := by
    rwa [RunTrace.upTo_state_of_le hm le_rfl]
  rcases tree_accepted hrunK.toLocalRun hy hW' with rfl | ⟨i, hik, hA⟩
  · cases ha
  have hA₀ := (RunTrace.upTo_acceptAt tr).mp hA |>.2
  have hd₀ := sign_before_accept hp (hp.run.antitone (hm hik.le) hy) ha hA₀ hv hs
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hkt : tr.time k ≤ sp.ts e.msg.slot + sp.Δ := (Compose.cast_head_fcRoot hr hy hc').2
  have hrt : sp.ts e.msg.slot ≤ tr.time r := by
    obtain ⟨-, -, -, hsl, -⟩ := hopt
    change sp.slot (tr.time r) = e.msg.slot at hsl
    exact (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg r) _).2 (by rw [hsl])
  obtain ⟨C, hcd⟩ := hs
  have hsD := hp.run.upTo (hp.run.time_nonneg d)
  obtain ⟨c, hcτ⟩ := Compose.sign_public hsD hv
    ((Trace.upTo_callAt tr).mpr ⟨le_rfl, hcd⟩)
  have hcτ' : tr.time d = sp.Δ * c := hcτ
  have hts : sp.ts e.msg.slot = sp.Δ * (4 * (e.msg.slot : Int)) := by
    simp only [SAParams.ts]; ring
  have h₁ := hm hrd.le
  have h₂ := hm hd₀.le
  have h₃ := hm hik.le
  have hc₁ : 4 * (e.msg.slot : Int) ≤ c := le_of_mul_le_mul_left
    (show sp.Δ * (4 * (e.msg.slot : Int)) ≤ sp.Δ * c by linarith only [hrt, hcτ', hts, h₁]) hΔ
  have hc₂ : c ≤ 4 * (e.msg.slot : Int) + 1 := le_of_mul_le_mul_left
    (show sp.Δ * c ≤ sp.Δ * (4 * (e.msg.slot : Int) + 1) by
      rw [mul_add, mul_one]; linarith only [hkt, hcτ', hts, h₂, h₃]) hΔ
  obtain hcc | hcc : c = 4 * (e.msg.slot : Int) ∨ c = 4 * (e.msg.slot : Int) + 1 := by omega
  · have hs' := (RunTrace.upTo_signAt tr).mpr (And.intro le_rfl ⟨C, hcd⟩)
    have hop' : SA.OptimisticLockAt (tr.upTo (tr.time d)).projAC v r e.msg.slot D CV := by
      rw [RunTrace.upTo_projAC]
      exact (SA.upTo_optimisticLockAt hm).mpr ⟨hm hrd.le, hopt⟩
    obtain ⟨hn1, j', hj', e', hve', hes⟩ := slot_start_optimistic hsD (hp.noColl.upTo _) hv hs'
      (by change tr.time d = _; rw [hcτ', hcc, hts]) hrd hop'
    obtain rfl : v = y := Fin.ext (by have := v.2; have := y.2; omega)
    have hve₀ : SA.VoteAt tr.projAC v j' e' := by
      rw [RunTrace.upTo_projAC] at hve'
      exact (SA.upTo_voteAt.mp hve').2
    have hveK := SA.upTo_voteAt.mpr (And.intro (hm (by omega : j' ≤ k)) hve₀)
    have := ((SA.one_vote_per_slot sp) _ ro _ _ _ hr v hy j' k e' e hveK
      ⟨ell, hc'.1, hc'.2⟩ hes).1
    omega
  · have hcK : SA.CastAt (tr.upTo (tr.time k)).projAC y k ell e := by
      rw [RunTrace.upTo_projAC]; exact hc'
    apply vote_before_late_delivery hrunK hncK hy hcK hA hik
    change tr.time i = _
    have : tr.time d = sp.ts e.msg.slot + sp.Δ := by rw [hcτ', hcc, hts]; ring
    linarith only [hkt, h₃, h₂, this]

/-- The source of a held honest row has a label strictly below the vote's slot. -/
theorem row_origin_label_lt_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} {d : Nat} (hv : v ∈ H (tr.time d)) (hs : tr.SignAt v d att)
    (hdk : d < k) {r l : Nat} (hrd : r < d) {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g v r l O) : l < e.msg.slot := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := (hac.upTo (hp.run.time_nonneg k)).localRun
  have hc' := SA.upTo_castAt.mpr (And.intro le_rfl hc)
  have hk : e.msg.slot = sp.slot (tr.time k) := (SA.castAt_spec hr hy hc').2.1
  have htr : tr.time r ≤ tr.time k := hp.run.time_mono (by omega)
  obtain ⟨_, _, ⟨CV, ellw, D, _, hfl, _⟩, _⟩ := ho
  rcases hfl with ⟨ell', C, ⟨-, -, ht, -⟩, -⟩ | hopt
  · have h₁ : sp.ts (l + 1 : Nat) ≤ tr.time k := by
      have : sp.ts (l + 1 : Nat) = sp.ts l + 4 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      rw [this]
      change tr.time r = sp.ts l + 6 * sp.Δ at ht
      linarith [sp.toParams.hΔ]
    have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg k) _).mp h₁
    omega
  · have hl : l ≤ e.msg.slot := by
      obtain ⟨-, -, -, hsl, -⟩ := hopt
      rw [hk, ← hsl]
      exact SA.slot_mono sp (hp.run.time_nonneg r) htr
    rcases hl.lt_or_eq with hl | rfl
    · exact hl
    · exact absurd hopt (row_origin_not_current_at hp hy hc hW ha hv hs hrd)

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

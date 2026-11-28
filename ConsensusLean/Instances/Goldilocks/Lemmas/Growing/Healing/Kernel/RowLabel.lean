module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.RowLate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.RowSign
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.CoreStock
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.PrefixSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Base
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Causal labels of historically honest rows at a vote

The signer is read on its signing prefix, the voter on its voting prefix.
Neither is required to survive to the other's observation.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

private theorem signer_eq_core
    {u frameOf ini} (rc : GoldilocksRunCore u frameOf proposer dg H tr ini)
    {v : Fin sp.n} {d : Nat} {att : FG.Att sp.n}
    (hv : v ∈ H (tr.time d)) (hs : tr.SignAt v d att) : att.val = v := by
  obtain ⟨C, hc⟩ := hs
  have hh := (rc.upTo (rc.time_nonneg d)).cutLaw v hv d _
    ((Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩)
  have he := ((cutStepWith_attest_some C att).mp hh).1
  unfold Store.attest FG.Record.createAtt at he
  split at he
  · cases he
  · dsimp only at he
    split_ifs at he
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj he)
    rfl

/-- A historically honest signing carried by a held row precedes that row's acceptance. -/
private theorem sign_before_accept_core
    {u frameOf ini}
    (rc : GoldilocksRunCore u frameOf proposer dg H tr ini)
    {y v : Fin sp.n} {i d : Nat} {att : FG.Att sp.n}
    {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (ha : att ∈ W.fgPayload) (hA : tr.AcceptAt y i W)
    (hv : v ∈ H (tr.time d)) (hs : tr.SignAt v d att) : d < i := by
  have hav := signer_eq_core rc hv hs
  by_contra h
  have hid : i ≤ d := by omega
  have hvi := rc.antitone (rc.time_mono hid) hv
  obtain ⟨d₀, hd₀, hs₀⟩ := rc.att_unforgeable y i att hy
    (Or.inr ⟨W, ⟨true, hA⟩, ha⟩) (hav ▸ hvi)
  rw [hav] at hs₀
  have := sign_unique_at_core rc hv (hd₀.le.trans hid) hs₀ hs
  omega

/-- No row held before a slot's vote comes from a same-slot optimistic write. -/
theorem row_origin_not_current_at_core
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {u frameOf} (hp : ResetRunCore tr H u frameOf proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} {d : Nat} (hv : v ∈ H (tr.time d)) (hs : tr.SignAt v d att)
    {r : Nat} (hrd : r < d) {D : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (AC.Vote sp.n)} : ¬ AC.OptimisticLockAt tr.projAC v r e.msg.slot D CV := by
  intro hopt
  have rc := hp.core
  have hm := rc.time_mono
  have hac := rc.acRun hp.noColl
  have hW' : W ∈ ((tr.upTo (tr.time k)).state y k).fg.tree := by
    rwa [RunTrace.upTo_state_of_le hm le_rfl]
  rcases (rc.upTo (rc.time_nonneg k)).tree_accepted y hy hW' with
    rfl | ⟨i, hik, hA⟩
  · cases ha
  have hA₀ := (RunTrace.upTo_acceptAt tr).mp hA |>.2
  have hd₀ := sign_before_accept_core rc (rc.antitone (hm hik.le) hy) ha hA₀ hv hs
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hkt : tr.time k ≤ sp.ts e.msg.slot + sp.Δ :=
    (rc.cast_head_fcRoot_at hp.noColl hy hc).2
  have hrt : sp.ts e.msg.slot ≤ tr.time r := by
    obtain ⟨-, -, -, hsl, -⟩ := hopt
    change sp.slot (tr.time r) = e.msg.slot at hsl
    exact (AC.ts_le_iff_le_slot sp (rc.time_nonneg r) _).2 (by rw [hsl])
  obtain ⟨C, hcd⟩ := hs
  have hsD := rc.upTo (rc.time_nonneg d)
  obtain ⟨c, hcτ⟩ := hsD.sign_public v hv d _
    ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, ⟨C, hcd⟩⟩)
  have hcτ' : tr.time d = sp.Δ * c := hcτ
  have hts : sp.ts e.msg.slot = sp.Δ * (4 * (e.msg.slot : Int)) := by
    simp only [ACParams.ts]; ring
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
    have hop' : AC.OptimisticLockAt (tr.upTo (tr.time d)).projAC v r e.msg.slot D CV := by
      rw [RunTrace.upTo_projAC]
      exact (AC.upTo_optimisticLockAt hm).mpr ⟨hm hrd.le, hopt⟩
    obtain ⟨hn1, j', hj', e', hve', hes⟩ := Healing.slot_start_optimistic_core hsD
      (hp.noColl.upTo _) hv hs' (by change tr.time d = _; rw [hcτ', hcc, hts]) hrd hop'
      hp.committee_pos
    -- the slot's committee has at most one member, and both the signer and the voter are members
    have hmem : ∀ {x : Fin sp.n} {q : Nat} {ℓq : ACLabel (goldilocksNode sp)}
        {eq : AC.Em sp (List (FG.Att sp.n))}, x ∈ H (tr.time q) → AC.CastAt tr.projAC x q ℓq eq →
        x ∈ (Generic.dictOfTime sp cm).committee eq.msg.slot := by
      intro x q ℓq eq hx hcq
      have hrq := (hac.upTo (rc.time_nonneg q)).localRun
      have hcq' := AC.upTo_castAt.mpr (And.intro le_rfl hcq)
      have hmay := AC.mayVote_of_castAt hrq hx hcq'
      rw [Trace.upTo_state tr.projAC x (fun j hj => hm hj.le),
        rc.projAC_state_at hx] at hmay
      exact (hp.committeeFacts.hGate _ (rc.time_nonneg _) _ hx _
        (fun _ hk => hm hk.le) _).1 hmay
    have hve₀ : AC.VoteAt tr.projAC v j' e' := by
      rw [RunTrace.upTo_projAC] at hve'
      exact AC.upTo_voteAt.mp hve' |>.2
    obtain ⟨ℓv, hcv⟩ := hve₀
    have hvj := rc.antitone (hm (by omega : j' ≤ d)) hv
    have hvK := hmem hvj hcv
    rw [hes] at hvK
    have hvy : v = y := (Set.ncard_le_one (Set.toFinite _)).1
      (by rw [hp.committeeFacts.hsize]; exact hn1) v hvK y (hmem hy hc)
    subst v
    have hmax : y ∈ H (max (tr.time j') (tr.time k)) := by
      rcases le_total (tr.time j') (tr.time k) with h | h
      · simpa only [max_eq_right h] using hy
      · simpa only [max_eq_left h] using hvj
    have hrmax := (hac.upTo (d := max (tr.time j') (tr.time k))
      ((rc.time_nonneg j').trans (le_max_left _ _))).localRun
    have := (AC.one_vote_per_slotU sp _ _ _ _ hrmax.toU y hmax j' k e' e
      (AC.upTo_voteAt.mpr ⟨le_max_left _ _, ℓv, hcv⟩)
      (AC.upTo_voteAt.mpr ⟨le_max_right _ _, ell, hc⟩) hes).1
    omega
  · apply vote_before_late_delivery_at_core rc hp.noColl hy hc hA₀ hik
    have : tr.time d = sp.ts e.msg.slot + sp.Δ := by rw [hcτ', hcc, hts]; ring
    linarith only [hkt, h₃, h₂, this]

/-- The source of a held honest row has a label strictly below the vote's slot. -/
theorem row_origin_label_lt_at_core
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {u frameOf} (hp : ResetRunCore tr H u frameOf proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} {d : Nat} (hv : v ∈ H (tr.time d)) (hs : tr.SignAt v d att)
    (hdk : d < k) {r l : Nat} (hrd : r < d) {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g v r l O) : l < e.msg.slot := by
  have rc := hp.core
  have hr := ((rc.acRun hp.noColl).upTo (rc.time_nonneg k)).localRun
  have hc' := AC.upTo_castAt.mpr (And.intro le_rfl hc)
  have hk : e.msg.slot = sp.slot (tr.time k) := (AC.castAt_specU hr.toU hy hc').2.1
  have htr : tr.time r ≤ tr.time k := rc.time_mono (by omega)
  obtain ⟨_, _, ⟨CV, ellw, D, _, hfl, _⟩, _⟩ := ho
  rcases hfl with ⟨ell', C, ⟨-, -, ht, -⟩, -⟩ | hopt
  · have h₁ : sp.ts (l + 1 : Nat) ≤ tr.time k := by
      have : sp.ts (l + 1 : Nat) = sp.ts l + 4 * sp.Δ := by
        simp only [ACParams.ts]; push_cast; ring
      rw [this]
      change tr.time r = sp.ts l + 6 * sp.Δ at ht
      linarith [sp.toParams.hΔ]
    have := (AC.ts_le_iff_le_slot sp (rc.time_nonneg k) _).mp h₁
    omega
  · have hl : l ≤ e.msg.slot := by
      obtain ⟨-, -, -, hsl, -⟩ := hopt
      rw [hk, ← hsl]
      exact AC.slot_mono sp (rc.time_nonneg r) htr
    rcases hl.lt_or_eq with hl | rfl
    · exact hl
    · exact absurd hopt (row_origin_not_current_at_core hp hy hc hW ha hv hs hrd)

/-- Stock specialization of the shared row-origin exclusion. -/
theorem row_origin_not_current_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} {d : Nat} (hv : v ∈ H (tr.time d)) (hs : tr.SignAt v d att)
    {r : Nat} (hrd : r < d) {D : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (AC.Vote sp.n)} : ¬ AC.OptimisticLockAt tr.projAC v r e.msg.slot D CV :=
  row_origin_not_current_at_core hp.toCore hy hc hW ha hv hs hrd

/-- Stock specialization of the shared strict label bound. -/
theorem row_origin_label_lt_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} {d : Nat} (hv : v ∈ H (tr.time d)) (hs : tr.SignAt v d att)
    (hdk : d < k) {r l : Nat} (hrd : r < d) {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g v r l O) : l < e.msg.slot :=
  row_origin_label_lt_at_core hp.toCore hy hc hW ha hv hs hdk hrd ho

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

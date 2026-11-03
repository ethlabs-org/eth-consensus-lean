module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedC4
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Goldilocks Refinement: the Healed bundle through a finite horizon (WI-17, #137)

consensus-lean#137 (finite-horizon port). `Healed` needs the
whole-run `ResetPremises`, whose `HealthyRun` asks every honest node to be awake at all
`t ≥ ḡ`. A finite trace (simTrace) is not awake after its horizon, so a finite query cannot
supply them. This module states the bundle through a horizon `b` (`HealedUpTo`) and proves it
from `ResetPremisesUpTo … b` and Catch(2Δ). The conclusions are restricted to the horizon:

* records: rows signed at `time d ≤ b`, locks and R0 at cuts `time i ≤ b`; the entries are
  high entries whose origin is written by `b` (`Healing.HighEntryUpTo`);
* C3: proposals of slots `s` with `t_s ≤ b`. No other reserve: the lock write and the call are
  before `t_s`, so `t_s ≤ b` bounds every cut that the proof uses;
* C4: later proposals of slots `s'` with `t_{s'} ≤ b`, and for the adjacent pair `s' = s + 1`
  also the service reserve `t_s + 6Δ ≤ b` (`t_{s+1} = t_s + 4Δ` does not give it). For
  `s' ≥ s + 2` the reserve follows from `t_{s'} = t_s + 4(s' - s)Δ ≥ t_s + 8Δ`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- `Z` is an entry of the high chain at height `h` through the horizon `b`: `HighEntry`, with
the high origin written at a cut by `b`. -/
structure HighEntryUpTo (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (g b : Time)
    (h : Nat) (Z : SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  origin : ∃ x i j B, HighOrigin tr H g x i j B ∧ tr.time i ≤ b ∧ Anc (tr.HonestBlocks H) Z B
  held : ∃ z ∈ H, ∃ m, Z ∈ (tr.state z m).fg.tree ∧ ((tr.state z m).fg.σ Z.root).h = h ∧
    ((tr.state z m).fg.σ Z.root).Th = Z.root

/-- **The record half of the Healed bundle through the horizon `b`.** `HealedRecords` with the
rows signed by `b` and the locks and R0 at cuts by `b`. -/
structure HealedRecordsUpTo (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (g b : Time)
    (h₀ : Nat) (E : Nat → SA.Blk sp.n (List (FG.Att sp.n))) : Prop where
  /-- RH: `h₀` is above the reset height. -/
  rh : HZ tr H g + 1 ≤ h₀
  /-- C2*⁺ (i): every honest row signed by `b` at a height `≥ h₀` names the entry. -/
  rows : ∀ v ∈ H, ∀ d att, tr.SignAt v d att → tr.time d ≤ b → h₀ ≤ att.h →
    att.T = (E att.h).root
  /-- C2*⁺ (ii): at a cut by `b`, every honest lock at a height `≥ h₀` is `⊥` or the entry. -/
  locks : ∀ y ∈ H, ∀ i h, tr.time i ≤ b → h₀ ≤ h →
    (tr.state y i).record.lock h = none ∨ (tr.state y i).record.lock h = some (E h).root
  /-- R0: at a cut by `b`, every honest record permits the entry at `h₀`. -/
  r0 : ∀ y ∈ H, ∀ i, tr.time i ≤ b → (tr.state y i).record.permits h₀ (E h₀).root

/-- C2*⁺ (i) through the horizon, for a `HighEntryUpTo`. -/
theorem ResetPremisesUpTo.high_row_entry_of_upTo
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {v : Fin sp.n} (hv : v ∈ H)
    {d : Nat} {att : FG.Att sp.n} (hs : tr.SignAt v d att) (hdb : tr.time d ≤ b)
    (hh : HZ tr H g + 1 ≤ att.h) {E : SA.Blk sp.n (List (FG.Att sp.n))}
    (hE : HighEntryUpTo tr H g b att.h E) : att.T = E.root := by
  obtain ⟨⟨xo, io, jo, B, ho, hiob, hEB⟩, ⟨z, hz, m, hEm, hEh, hET⟩⟩ := hE
  exact hp.high_row_entry hv hs hdb hh ho hiob hEB hz hEm hEh hET

/-- R0 through the horizon, for a `HighEntryUpTo`. -/
theorem ResetPremisesUpTo.permits_high_entry_of_upTo
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {y : Fin sp.n} (hy : y ∈ H)
    {i h : Nat} (hib : tr.time i ≤ b) (hh : HZ tr H g + 1 ≤ h)
    {E : SA.Blk sp.n (List (FG.Att sp.n))} (hE : HighEntryUpTo tr H g b h E) :
    (tr.state y i).record.permits h E.root := by
  obtain ⟨⟨xo, io, jo, B, ho, hiob, hEB⟩, ⟨z, hz, m, hEm, hEh, hET⟩⟩ := hE
  exact hp.permits_high_entry hy hib hh ho hiob hEB hz hEm hEh hET

/-- C2*⁺ (ii) through the horizon, for a `HighEntryUpTo`. -/
theorem ResetPremisesUpTo.high_lock_entry_of_upTo
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {y : Fin sp.n} (hy : y ∈ H)
    {i h : Nat} (hib : tr.time i ≤ b) (hh : HZ tr H g + 1 ≤ h)
    {E : SA.Blk sp.n (List (FG.Att sp.n))} (hE : HighEntryUpTo tr H g b h E) :
    (tr.state y i).record.lock h = none ∨ (tr.state y i).record.lock h = some E.root :=
  (hp.permits_high_entry_of_upTo hy hib hh hE).2.2

/-- **A high entry through the horizon from an honest row signed by `b`.** The origin of the
row's source is written before the row (`high_row_source`). -/
theorem ResetPremisesUpTo.highEntryUpTo_of_row
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {v : Fin sp.n} (hv : v ∈ H)
    {d : Nat} {att : FG.Att sp.n} (hs : tr.SignAt v d att) (hdb : tr.time d ≤ b)
    (hh : HZ tr H g + 1 ≤ att.h) :
    ∃ E, HighEntryUpTo tr H g b att.h E ∧ E.root = att.T := by
  obtain ⟨r, hrd, l, O, hO, E, hE, hEO, hEr, hEh, hET⟩ := hp.high_row_source hv hs hh
  exact ⟨E, ⟨⟨v, r, l, O, hO, (hp.run.time_mono hrd.le).trans hdb,
    hEO.mono fun D hD => ⟨v, hv, r, hD⟩⟩, ⟨v, hv, r, hE, hEh, hET⟩⟩, hEr⟩

/-- **A high entry through the horizon from an honest record entry at a cut by `b`.** The
target, timeout or lock entry `r` at a height `h ≥ H_z + 1` comes from an earlier row of the
node (`client_record_origin_of_run`); for a lock, the finality pair of that row is below the
row's entry (`signed_fin_pair_entry_of_run`). -/
theorem ResetPremisesUpTo.highEntryUpTo_of_record
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {y : Fin sp.n} (hy : y ∈ H)
    {i h r : Nat} (hib : tr.time i ≤ b) (hh : HZ tr H g + 1 ≤ h)
    (hr : (tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h ∨
      (tr.state y i).record.lock h = some r) :
    ∃ E, HighEntryUpTo tr H g b h E ∧ E.root = r := by
  rcases hr with hr | hr | hr
  · obtain ⟨k, hki, att, hs, rfl, rfl⟩ := (client_record_origin_of_run hp.run hy h r i).1
      (Or.inl hr)
    exact hp.highEntryUpTo_of_row hy hs ((hp.run.time_mono hki.le).trans hib) hh
  · obtain ⟨k, hki, att, hs, rfl, rfl⟩ := (client_record_origin_of_run hp.run hy h r i).1
      (Or.inr hr)
    exact hp.highEntryUpTo_of_row hy hs ((hp.run.time_mono hki.le).trans hib) hh
  · obtain ⟨k, hki, att, hs, hfin⟩ := (client_record_origin_of_run hp.run hy h r i).2 hr
    have hkb := (hp.run.time_mono hki.le).trans hib
    obtain ⟨J, hJ, E, hE, hEr, hJE, hJr, hJh, hJT⟩ :=
      signed_fin_pair_entry_of_run hp.run hy hs hfin
    obtain ⟨E', hE', hE'r, hE'h⟩ := signAt_entry hp.run hy hs
    have hU : Coherent (tr.HonestBlocks H) := hp.honest_coherent
    obtain rfl : E' = E := hU.1 ⟨y, hy, k, hE'⟩ ⟨y, hy, k, hE⟩ (hE'r.trans hEr.symm)
    have hJE' := σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun hy k) hJE
    obtain ⟨E'', ⟨⟨x, i', j, B, ho, hi'b, hE''B⟩, ⟨z, hz, m, hE''m, -, -⟩⟩, hE''r⟩ :=
      hp.highEntryUpTo_of_row hy hs hkb (by omega)
    obtain rfl : E'' = E' := hU.1 ⟨z, hz, m, hE''m⟩ ⟨y, hy, k, hE'⟩ (hE''r.trans hE'r.symm)
    exact ⟨J, ⟨⟨x, i', j, B, ho, hi'b,
      (Anc.mono (fun D (hD : D ∈ (tr.state y k).fg.tree) =>
        (⟨y, hy, k, hD⟩ : D ∈ tr.HonestBlocks H)) hJE).trans hE''B⟩, ⟨y, hy, k, hJ, hJh, hJT⟩⟩, hJr⟩

/-- **The canonical entry family through the horizon `b`.** At a height with a
`HighEntryUpTo`, a chosen one; at any other height the default block `Z₀`. -/
noncomputable def canonicalEntryUpTo (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (g b : Time) (Z₀ : SA.Blk sp.n (List (FG.Att sp.n))) (h : Nat) :
    SA.Blk sp.n (List (FG.Att sp.n)) := by
  classical
  exact if hx : ∃ E, HighEntryUpTo tr H g b h E then Classical.choose hx else Z₀

/-- At a height with a `HighEntryUpTo`, the canonical entry is one. -/
theorem canonicalEntryUpTo_highEntry {Z₀ : SA.Blk sp.n (List (FG.Att sp.n))} {h : Nat}
    (hx : ∃ E, HighEntryUpTo tr H g b h E) :
    HighEntryUpTo tr H g b h (canonicalEntryUpTo tr H g b Z₀ h) := by
  classical
  have hc := Classical.choose_spec hx
  simpa only [canonicalEntryUpTo, hx, ↓reduceDIte] using hc

/-- **The record half of the Healed bundle through the horizon, canonical form.** From
`ResetPremisesUpTo … b` and RH alone. -/
theorem healed_records_of_reset_canonical_upTo
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {h₀ : Nat} (hrh : HZ tr H g + 1 ≤ h₀) (Z₀ : SA.Blk sp.n (List (FG.Att sp.n))) :
    HealedRecordsUpTo tr H g b h₀ (canonicalEntryUpTo tr H g b Z₀) where
  rh := hrh
  rows _ hv _ _ hs hdb hh := by
    obtain ⟨E, hE, -⟩ := hp.highEntryUpTo_of_row hv hs hdb (hrh.trans hh)
    exact hp.high_row_entry_of_upTo hv hs hdb (hrh.trans hh) (canonicalEntryUpTo_highEntry ⟨E, hE⟩)
  locks _ hy i h hib hh := by
    rcases hl : (tr.state _ i).record.lock h with _ | r
    · exact Or.inl rfl
    · obtain ⟨E, hE, -⟩ := hp.highEntryUpTo_of_record hy hib (hrh.trans hh) (Or.inr (Or.inr hl))
      rw [← hl]
      exact hp.high_lock_entry_of_upTo hy hib (hrh.trans hh) (canonicalEntryUpTo_highEntry ⟨E, hE⟩)
  r0 y hy i hib := by
    by_cases hx : ∃ E, HighEntryUpTo tr H g b h₀ E
    · exact hp.permits_high_entry_of_upTo hy hib hrh (canonicalEntryUpTo_highEntry hx)
    · have no : ∀ r, ¬ ((tr.state y i).record.target h₀ = some r ∨
          r ∈ (tr.state y i).record.timeout h₀ ∨ (tr.state y i).record.lock h₀ = some r) :=
        fun r hr => hx ((hp.highEntryUpTo_of_record hy hib hrh hr).imp fun _ h => h.1)
      refine ⟨?_, fun r hr => absurd (Or.inr (Or.inl hr)) (no r), ?_⟩
      · rcases ht : (tr.state y i).record.target h₀ with _ | r
        · exact Or.inl rfl
        · exact absurd (Or.inl ht) (no r)
      · rcases hl : (tr.state y i).record.lock h₀ with _ | r
        · exact Or.inl rfl
        · exact absurd (Or.inr (Or.inr hl)) (no r)

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Refinement

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- **The Healed bundle through the horizon `b`** (`Healed` with b-bounded conclusions). C3
for proposals of slots `s` with `t_s ≤ b`; C4 for later proposals of slots `s'` with
`t_{s'} ≤ b`, and for `s' = s + 1` the service reserve `t_s + 6Δ ≤ b`. -/
structure HealedUpTo (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (g tH b : Time) (h₀ : Nat)
    (E : Nat → SA.Blk sp.n (List (FG.Att sp.n))) : Prop
    extends Healing.HealedRecordsUpTo tr H g b h₀ E where
  /-- C3 (A-safe) for proposals by the horizon. -/
  c3 : ∀ y ∈ H, ∀ k ℓ, tr.projAC.CallAt y k ℓ → tH ≤ tr.time k →
    ∀ l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k), l.fast = true →
    ∀ X ∈ ℓ.frame.tree, X.root = l.block →
    ∀ s P, Healing.HonestProposalRun tr H proposer s P → tr.time k + sp.Δ ≤ sp.ts s →
      sp.ts s ≤ b →
      ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) X Pr
  /-- C4 (no reorg) by the horizon, with the reserve for the adjacent pair. -/
  c4 : ∀ s P s' P', Healing.HonestProposalRun tr H proposer s P →
    Healing.HonestProposalRun tr H proposer s' P' → sp.slot tH < s → s < s' →
      sp.ts s' ≤ b → (s' = s + 1 → sp.ts s + 6 * sp.Δ ≤ b) →
      Anc (tr.HonestBlocks H) P P'

/-- **C3 through the horizon.** C3 from `ResetPremisesUpTo … b`, for proposals of
slots `s` with `t_s ≤ b`. -/
theorem c3_of_reset_upTo (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {tH : Time}
    (hR : Healing.drainTime sp a ≤ tH) :
    ∀ y ∈ H, ∀ k ℓ, tr.projAC.CallAt y k ℓ → tH ≤ tr.time k →
      ∀ l ∈ SA.liveLocks sp (tr.projAC.state y k).locks ℓ.frame (tr.time k), l.fast = true →
      ∀ X ∈ ℓ.frame.tree, X.root = l.block →
      ∀ s P, Healing.HonestProposalRun tr H proposer s P → tr.time k + sp.Δ ≤ sp.ts s →
        sp.ts s ≤ b →
        ∃ Pr ∈ tr.HonestBlocks H, P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) X Pr := by
  intro y hy k ℓ hck htk l hl hlf X hX hXr s P hP hks hsb
  obtain ⟨l₀, hl₀, B, hB, hBr, hlive, rfl⟩ := hl
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hck
  have hvB := SA.viableAncestor_anc hPhi hB
  obtain rfl : X = ℓ.frame.viableAncestor B := hU.1 (hPhiU hX) (hPhiU hvB.1) hXr
  obtain ⟨r, hrk, CV, ℓ', D, hcr, hfl, L, hL, hLr, hLD⟩ :=
    Healing.stored_fast_lock_provenance hr hy k l₀ hl₀ hlf
  rw [hU.1 hL (hPhiU hB) (hLr.trans hBr.symm)] at hLD
  obtain ⟨ell', hc', hD⟩ := Healing.fastLock_mem hfl
  obtain rfl : ell' = ℓ' := Option.some.inj (hc'.2.symm.trans hcr.2)
  obtain ⟨hPhi', hPhiU'⟩ := SA.frameIn_of_callAt hr hy hc'
  have hXD : Anc (tr.HonestBlocks H) (ℓ.frame.viableAncestor B) D :=
    (hvB.2.mono hPhiU).trans (hLD.trans ((SA.viableAncestor_anc hPhi' hD).2.mono hPhiU'))
  obtain ⟨hpH, i, ell, d, pay, hci, hcall, hd, hti, hpar, -⟩ := hP
  -- the horizon bounds
  have hib : tr.time i ≤ b := hti ▸ hsb
  have hk0 := hp.run.time_nonneg k
  have hrt : tr.time r ≤ tr.time k := hp.run.time_mono hrk.le
  have hrb : tr.time r ≤ b := by linarith
  -- the slot bounds
  have hRk : Healing.drainTime sp a ≤ tr.time k := hR.trans htk
  rw [Healing.drainTime_eq] at hRk
  have hsk := (SA.ts_le_iff_le_slot sp hk0 _).1 hRk
  have hks' : ¬ sp.ts s ≤ tr.time k := by linarith
  rw [SA.ts_le_iff_le_slot sp hk0] at hks'
  have hlab : Healing.cleanLabel sp a + sp.k + 2 ≤ l₀.slot := by
    rw [Healing.cleanLabel_eq]; omega
  have hRs : Healing.drainTime sp a ≤ sp.ts s := by
    rw [Healing.drainTime_eq]; exact (SA.ts_le_iff sp).2 (by push_cast; omega)
  have hQ : Anc (tr.HonestBlocks H) D d.head → ∃ Pr ∈ tr.HonestBlocks H,
      P.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) (ℓ.frame.viableAncestor B) Pr := by
    intro hDQ
    obtain ⟨hPhiP, hPhiPU⟩ := SA.frameIn_of_callAt hr hpH hci
    obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhiP hd
    have hQt : d.head ∈ ell.frame.tree := by
      rcases eq_or_ne d.start d.head with he | he
      · exact he ▸ hst
      · exact (Anc.mem hsQ he).2
    exact ⟨d.head, hPhiPU hQt, hpar, hXD.trans hDQ⟩
  have hclean : l₀.slot + 2 ≤ s → Anc (tr.HonestBlocks H) D d.head := fun h2 =>
    hp.clean_source_proposal_parent_before hc hy hpH (Or.inl ⟨CV, hfl⟩) hlab h2 hrb hRs
      hci hcall hd hti hib
  rcases hfl with hup | hop
  · obtain ⟨-, -, ⟨-, -, ht, -⟩, -⟩ := hup
    have ht' : tr.time r = sp.ts l₀.slot + 6 * sp.Δ := ht
    have h2 : l₀.slot + 2 ≤ s := by
      have hlt : sp.ts (l₀.slot + 1 : Nat) < sp.ts s := by
        have : sp.ts (l₀.slot + 1 : Nat) = sp.ts l₀.slot + 4 * sp.Δ := by
          simp only [SA.SAParams.ts]; push_cast; ring
        linarith
      have := (SA.ts_lt_iff sp).1 hlt
      omega
    exact hQ (hclean h2)
  · rcases Nat.lt_or_ge (l₀.slot + 1) s with h2 | h1
    · exact hQ (hclean (by omega))
    · have hsl : sp.slot (tr.time r) = l₀.slot := hop.choose_spec.choose_spec.2.1
      have hsm := SA.slot_mono sp (hp.run.time_nonneg r) hrt
      obtain rfl : s = l₀.slot + 1 := by omega
      exact hQ (hp.clean_optimistic_proposal_parent hc hy hpH hop hlab hrb hRs hci hcall hd
        hti hib)

/-- The honest proposal `P'` of `s'` is the child of the duty head of its proposal call. -/
private theorem honest_proposal_child (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {s' : Nat} {P P' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP' : Healing.HonestProposalRun tr H proposer s' P')
    (hPd : ∀ {i ell} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay},
      tr.projAC.CallAt (proposer s') i ell → ell.call = .proposal →
      (SA.acProposal sp (tr.projAC.state (proposer s') i) ell.frame (tr.time i)).2 =
        some (d, pay) → tr.time i = sp.ts s' → Anc (tr.HonestBlocks H) P d.head) :
    Anc (tr.HonestBlocks H) P P' := by
  obtain ⟨hy, i, ell, d, pay, hci, hcall, hd, hti, hpar, -, -, -, j, -, hacc, -⟩ := hP'
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hci
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hQt : d.head ∈ ell.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem hsQ he).2
  have hBU : P' ∈ tr.HonestBlocks H := ⟨_, hy, j, hp.acceptAt_mem hy hacc⟩
  exact (hPd hci hcall hd hti).trans (.single ⟨hPhiU hQt, hBU, hpar⟩)

/-- **No reorg two slots on, through the horizon.** From
`ResetPremisesUpTo … b` for a later slot `s' ≥ s + 2` with `t_{s'} ≤ b`. -/
theorem honest_proposal_below_later_upTo
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {s s' : Nat}
    {P P' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.HonestProposalRun tr H proposer s P) (hR : Healing.drainTime sp a ≤ sp.ts s)
    (hP' : Healing.HonestProposalRun tr H proposer s' P') (hss : s + 2 ≤ s')
    (hb : sp.ts s' ≤ b) : Anc (tr.HonestBlocks H) P P' := by
  obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun hp.run hP
  obtain ⟨-, -, -, -, -, -, -, -, -, hPs, -⟩ := hP.2
  have hΔ := sp.toParams.hΔ
  have h2 : sp.ts (s + 2 : Nat) ≤ sp.ts s' := (SA.ts_le_iff sp).2 (by push_cast; omega)
  have he : sp.ts (s + 2 : Nat) = sp.ts s + 8 * sp.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  have hTb : sp.ts s + 6 * sp.Δ ≤ b := by linarith
  exact honest_proposal_child hp hP' fun hci hcall hd hti =>
    UpTo.operational_proposal_below_later_parent hp hc hP.1 rfl hk hPs hR hTb hP'.1 hss
      hci hcall hd hti (hti ▸ hb)

/-- **No reorg one slot on, through the horizon.** From
`ResetPremisesUpTo … b`, with the service reserve `t_s + 6Δ ≤ b`. -/
theorem honest_proposal_below_next_upTo
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {s : Nat}
    {P P' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : Healing.HonestProposalRun tr H proposer s P) (hR : Healing.drainTime sp a ≤ sp.ts s)
    (hP' : Healing.HonestProposalRun tr H proposer (s + 1) P')
    (hTb : sp.ts s + 6 * sp.Δ ≤ b) : Anc (tr.HonestBlocks H) P P' := by
  obtain ⟨k, hk⟩ := proposesAt_of_honestProposalRun hp.run hP
  obtain ⟨-, -, -, -, -, -, -, -, -, hPs, -⟩ := hP.2
  exact honest_proposal_child hp hP' fun hci hcall hd hti =>
    UpTo.operational_proposal_below_next_parent hp hc hP.1 rfl hk hPs hR hTb hP'.1
      hci hcall hd hti

/-- **C4 through the horizon.** Under `ResetPremisesUpTo … b` and Catch(2Δ) with the drain
over by `t_{slot(tH)+1}`: the C4 field of `HealedUpTo`. -/
theorem c4_of_reset_upTo (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {tH : Time}
    (hR : Healing.drainTime sp a ≤ sp.ts (sp.slot tH + 1)) :
    ∀ s P s' P', Healing.HonestProposalRun tr H proposer s P →
      Healing.HonestProposalRun tr H proposer s' P' → sp.slot tH < s → s < s' →
        sp.ts s' ≤ b → (s' = s + 1 → sp.ts s + 6 * sp.Δ ≤ b) →
        Anc (tr.HonestBlocks H) P P' := by
  intro s P s' P' hP hP' hs hss hb hadj
  have hRs : Healing.drainTime sp a ≤ sp.ts s := hR.trans ((SA.ts_le_iff sp).2 (by omega))
  rcases Nat.lt_or_ge (s + 1) s' with h2 | h1
  · exact honest_proposal_below_later_upTo hp hc hP hRs hP' (by omega) hb
  · obtain rfl : s' = s + 1 := by omega
    exact honest_proposal_below_next_upTo hp hc hP hRs hP' (hadj rfl)

/-- **Healed through the horizon, canonical form** (from
`ResetPremisesUpTo … b`). Under the bounded reset premises and Catch(2Δ) with the drain over
by the heal time, `HealedUpTo` holds for the canonical entries through `b`. -/
theorem healed_of_reset_canonical_full_upTo
    (hp : Healing.ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : Healing.CatchRun tr H g (2 * sp.Δ)) {tH : Time} {h₀ : Nat}
    (hrh : Healing.HZ tr H g + 1 ≤ h₀) (Z₀ : SA.Blk sp.n (List (FG.Att sp.n)))
    (hR : Healing.drainTime sp a ≤ tH) :
    HealedUpTo tr H proposer g tH b h₀ (Healing.canonicalEntryUpTo tr H g b Z₀) := by
  have h0 : 0 ≤ tH := by
    refine le_trans ?_ hR
    rw [Healing.drainTime_eq]; simp only [SA.SAParams.ts]
    exact mul_nonneg (by linarith [sp.toParams.hΔ]) (by positivity)
  have hR' : Healing.drainTime sp a ≤ sp.ts (sp.slot tH + 1) := by
    refine hR.trans (le_of_lt (not_le.1 fun h => ?_))
    have := (SA.ts_le_iff_le_slot sp h0 _).1 h
    omega
  exact { Healing.healed_records_of_reset_canonical_upTo hp hrh Z₀ with
    c3 := c3_of_reset_upTo hp hc hR, c4 := c4_of_reset_upTo hp hc hR' }

end Consensus.Goldilocks.Refinement

end

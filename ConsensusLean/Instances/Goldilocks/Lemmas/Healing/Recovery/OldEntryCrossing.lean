module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.FromHighFinality
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Rise
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotSupport
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.TwoWindow
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Recovery: bounded old-entry crossing (C1.3, C2)

`old_entry_crossing`: from a high post-drain ready proposal `P` of slot `s` inside the pattern
stretch, the chain above `P` enters the next height at an honest ready proposal `U` of the
stretch, with `s < U.slot ≤ s + δ_t ≤ s + r_old`, and `U` is an actual run entry of height
`σ[P].h + 1`.

* The report supply covers `P` by `t_s + 6Δ` (inclusive). If some honest report `C ⪰ P` is
  already higher than `P`, `C` is an actual honest block above `P` (it is used only as such, not
  as a justification). Otherwise every honest validator signs the row `(σ[P].h, σ[P].T_h)` at
  its report (`row_of_high_report`: `client_progress_of_lock`, with the lock at the high height
  free or the entry by `ResetPremisesUpTo.record_entry_eq`).
* The stretch's ready proposal `X` of slot `s + δ_t` sits on a parent above the high origin of a
  report (`high_report_origin`, `ResetPremisesUpTo.reset_proposal_passes`), and `round_cross`
  (M1) lifts it at least one height above `P` (`6Δ + Δ_F ≤ 4Δ c_F ≤ 4Δ δ_t`).
* The first crossing on `P ⪯ D` is a block of a stretch slot, hence the stretch's ready proposal
  of that slot, and an entry accepted by its proposer. Replay-state heights are transported
  between the stores explicitly (`σ_eq_honest`). -/

namespace Consensus.Goldilocks.Healing.Recovery

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- **The row at a high report** (as `row_or_high_of_report` in `M1/Rise`, with the lock clause
from high-record uniqueness instead of the frame kind). An honest report `R ⪰ P` at cut `i`, `P`
high: `y` signed the row `(σ[P].h, σ[P].T_h)` by `t_i`, or `σ[R].h > σ[P].h`. -/
private theorem row_of_high_report (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {R P : SA.Blk sp.n (List (FG.Att sp.n))} (hR : SA.ToFGAt tr.projAC y i ell R)
    (hPR : Anc (tr.HonestBlocks H) P R)
    (hPh : HZ tr H g + 1 ≤ ((tr.state y i).fg.σ P.root).h) :
    P ∈ (tr.state y i).fg.tree ∧ R ∈ (tr.state y i).fg.tree ∧
      ((∃ k att, tr.SignAt y k att ∧ tr.time k ≤ tr.time i ∧
        att.h = ((tr.state y i).fg.σ P.root).h ∧ att.T = ((tr.state y i).fg.σ P.root).Th) ∨
      ((tr.state y i).fg.σ P.root).h < ((tr.state y i).fg.σ R.root).h) := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hRm := toFG_mem_tree hrun hy hR
  have hPm := mem_of_honest_anc hrun hnc hy hPR hRm
  have hr := Compose.fg_reachable hrun.toLocalRun hy i
  have hPRs := store_anc_of_honest_anc hrun hnc hy hPR hRm
  have hle := h_le_of_store_anc hr hPRs
  refine ⟨hPm, hRm, ?_⟩
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inr hlt
  left
  obtain ⟨io, -, jo, B, ho, hRB⟩ := high_report_origin hp hy hR (heq ▸ hPh)
  obtain ⟨hc, hto, hres⟩ := hR
  rw [Compose.projAC_state hrun.toLocalRun hy] at hres
  obtain ⟨sg, hatt, ht, hfg⟩ :=
    toFG_attest hrun.toLocalRun hy (Compose.projAC_callAt.mp hc) hto hres
  obtain ⟨⟨E, hE, hEr, hER, hEh, hETh⟩, -⟩ :=
    Goldilocks.Store.entry_state_of_source _ _ _ _ hr R hRm
  have hEnt : EntryOf (tr.state y (i + 1)).fg R E ((tr.state y i).fg.σ P.root).h := by
    rw [hfg]
    exact ⟨⟨hE, hETh.trans hEr.symm⟩, hEh.trans heq.symm, hER⟩
  have hCh : ((tr.state y (i + 1)).fg.σ R.root).h = ((tr.state y i).fg.σ P.root).h := by
    rw [hfg]; exact heq.symm
  have hTh : E.root = ((tr.state y i).fg.σ P.root).Th :=
    hEr.trans (Th_eq_of_anc hr hPRs heq.symm)
  -- the lock at the high height is free or the entry: high records name one entry
  have hEB : Anc (tr.HonestBlocks H) E B :=
    (hER.mono fun X hX => (⟨y, hy, i, hX⟩ : X ∈ tr.HonestBlocks H)).trans hRB
  have hlock : (tr.state y (i + 1)).record.lock ((tr.state y i).fg.σ P.root).h = none ∨
      (tr.state y (i + 1)).record.lock ((tr.state y i).fg.σ P.root).h = some E.root := by
    rcases hl : (tr.state y (i + 1)).record.lock ((tr.state y i).fg.σ P.root).h with _ | r
    · exact Or.inl rfl
    refine Or.inr (congrArg some ?_)
    have hp' := hp.toUpTo tr H (le_max_left a (max (tr.time (i + 1)) (tr.time io)))
    exact hp'.record_entry_eq hy ((le_max_left _ _).trans (le_max_right _ _)) hPh
      (Or.inr (Or.inr hl)) ho ((le_max_right _ _).trans (le_max_right _ _)) hEB hy hE
      (hEh.trans heq.symm) (hETh.trans hEr.symm)
  rcases client_progress_of_lock hrun hy hatt hEnt hCh hlock with
    ⟨att, rfl, hah, haT⟩ | ⟨k', hk', att, hs, hah, haT⟩
  · exact ⟨i + 1, att, ⟨R, hatt⟩, ht.le, hah, haT.trans hTh⟩
  · exact ⟨k', att, hs, hrun.time_mono (Nat.lt_succ_iff.mp hk'), hah, haT.trans hTh⟩

/-- **C2: bounded old-entry crossing.** -/
theorem old_entry_crossing {Gp : Time} {W M cF kF v s : Nat} {p : Fin sp.n} {kP iP : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hp : ResetPremises tr H proposer dg g ΔF a)
    (hpat : PatternPremises tr H proposer dg g ΔF Gp W M cF kF)
    (hreports : ReadyProposalReportSupply tr H proposer dg g ΔF a)
    (hwindow : ∀ u, v ≤ u → u < v + M →
      ∃ (k : Nat) (B : SA.Blk sp.n (List (FG.Att sp.n))),
        ReadyProposal tr H proposer (proposer u) k u B ∧
        ∀ y i, Compose.RunEntry tr H y i B →
          ∃ (w : Fin sp.n) (kw : Nat) (Q : SA.Blk sp.n (List (FG.Att sp.n))),
            ReadyProposal tr H proposer w kw Q.slot Q ∧
            u + cF ≤ Q.slot ∧ Q.slot ≤ u + cF + kF ∧
            ∃ Pr, Q.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) B Pr)
    (hvs : v ≤ s) (hroom : s + oldSlots sp ΔF Gp < v + M)
    (hP : ReadyProposal tr H proposer p kP s P)
    (haccept : tr.AcceptAt p iP P)
    (hhigh : HZ tr H g + 1 ≤ ((tr.post iP).fg.σ P.root).h)
    (hafter : drainTime sp a ≤ sp.ts s) :
    ∃ (q : Fin sp.n) (kU iU : Nat) (U : SA.Blk sp.n (List (FG.Att sp.n))),
      ReadyProposal tr H proposer q kU U.slot U ∧
      Compose.RunEntry tr H q iU U ∧
      Anc (tr.HonestBlocks H) P U ∧
      s < U.slot ∧ U.slot ≤ s + oldSlots sp ΔF Gp ∧
      ((tr.post iU).fg.σ U.root).h = ((tr.post iP).fg.σ P.root).h + 1 := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hU := honest_coherent hp
  have hΔ : (1 : Int) ≤ sp.Δ := sp.toParams.hΔ
  have hΔF : 0 < ΔF := hp.healthy.1.deltaF
  have hold := timeout_add_three_le_oldSlots (sp := sp) hΔF.le (pattern_Gp_nonneg hpat)
  have hδt : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * (sp.toParams.δt : Time) := by
    have h1 := hpat.cF_upper
    have h2 : (cF : Time) ≤ (sp.toParams.δt : Time) := by
      exact_mod_cast (show cF ≤ sp.toParams.δt by have := hpat.timeout; omega)
    nlinarith
  have hδ1 : 1 ≤ sp.toParams.δt := by
    by_contra h
    have : (sp.toParams.δt : Time) = 0 := by exact_mod_cast (show sp.toParams.δt = 0 by omega)
    rw [this] at hδt
    linarith
  have hts {a c : Nat} (h : a ≤ c) : sp.ts a ≤ sp.ts c :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast h)
  have hts_add (c m : Nat) : sp.ts (c + m : Nat) = sp.ts c + 4 * sp.Δ * (m : Time) := by
    simp only [SAParams.ts]; push_cast; ring
  obtain ⟨hpH, -, -, hPprop, hPs, -⟩ := id hP
  -- `P` at its acceptance
  have hpostP : tr.post iP = tr.state p (iP + 1) := (tr.state_succ_of_call haccept).symm
  have hPm : P ∈ (tr.state p (iP + 1)).fg.tree := by
    rw [tr.state_succ_of_call haccept, (Store.tree_grows _ _ _ _
      (Compose.fg_reachable hrun.toLocalRun hpH iP)).1 P _ (hrun.cutLaw p hpH iP _ haccept).2.1]
    exact Set.mem_insert _ _
  have hPH : P ∈ tr.HonestBlocks H := ⟨p, hpH, iP + 1, hPm⟩
  rw [hpostP] at hhigh ⊢
  -- the replay height of `P` at any honest store holding it
  have hPσ : ∀ {w} (_ : w ∈ H) {c}, P ∈ (tr.state w c).fg.tree →
      (tr.state w c).fg.σ P.root = (tr.state p (iP + 1)).fg.σ P.root :=
    fun hw _ hPw => σ_eq_honest hrun hnc hw hpH hPw hPm
  have hgv : gbar g ≤ sp.ts s := by
    have h1 := cutZ_lt_reset hrun hp.healthy hp.reset
    have h2 := lt_cutZ sp g
    have h3 : ¬ sp.ts (sp.slot a + 1 : Nat) ≤ a := fun h => by
      have := (SA.ts_le_iff_le_slot sp (by linarith [gbar_nonneg g]) _).1 h
      push_cast at this; omega
    have h4 := hts (show sp.slot a + 1 ≤ sp.slot a + 2 * sp.k + 5 by omega)
    rw [drainTime_eq] at hafter
    linarith
  -- a report time is before `t_{s+2}`
  have hslot_rep : ∀ {r : Nat}, tr.time r ≤ sp.ts s + 6 * sp.Δ →
      sp.slot (tr.time r) ≤ s + 1 := fun {r} hr => by
    by_contra h
    have := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg r) ((s + 2 : Nat) : Int)).2
      (by push_cast; omega)
    rw [hts_add s 2] at this
    push_cast at this
    linarith
  -- **an actual honest block above `P`, one height higher, of a slot `≤ s + δ_t`**
  have key : ∃ w ∈ H, ∃ c D, D ∈ (tr.state w c).fg.tree ∧ Anc (tr.HonestBlocks H) P D ∧
      ((tr.state w c).fg.σ P.root).h < ((tr.state w c).fg.σ D.root).h ∧
      D.slot ≤ s + sp.toParams.δt := by
    have higher : ∀ z ∈ H, ∀ r ℓ C, SA.ToFGAt tr.projAC z r ℓ C →
        tr.time r ≤ sp.ts s + 6 * sp.Δ → Anc (tr.HonestBlocks H) P C →
        ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h →
        ∃ w ∈ H, ∃ c D, D ∈ (tr.state w c).fg.tree ∧ Anc (tr.HonestBlocks H) P D ∧
          ((tr.state w c).fg.σ P.root).h < ((tr.state w c).fg.σ D.root).h ∧
          D.slot ≤ s + sp.toParams.δt := by
      intro z hz r ℓ C hC hrt hPC hlt
      have hCm := toFG_mem_tree hrun hz hC
      refine ⟨z, hz, r, C, hCm, hPC, hlt, ?_⟩
      have := tree_slot_le hp hz hCm
      have := hslot_rep hrt
      omega
    rcases hreports.report_cover hp hpat.catchPremise p kP s P hP hafter with
      hall | ⟨z, hz, r, ℓ, C, hC, hrt, hPC, hlt⟩
    swap
    · exact higher z hz r ℓ C hC hrt hPC hlt
    by_cases hhi : ∃ z ∈ H, ∃ r ℓ C, SA.ToFGAt tr.projAC z r ℓ C ∧
        tr.time r ≤ sp.ts s + 6 * sp.Δ ∧ Anc (tr.HonestBlocks H) P C ∧
        ((tr.state z r).fg.σ P.root).h < ((tr.state z r).fg.σ C.root).h
    · obtain ⟨z, hz, r, ℓ, C, hC, hrt, hPC, hlt⟩ := hhi
      exact higher z hz r ℓ C hC hrt hPC hlt
    push Not at hhi
    -- every honest validator signed `P`'s row at its report; the proposal of `s + δ_t`
    obtain ⟨kx, X, hXr, -⟩ := hwindow (s + sp.toParams.δt) (by omega) (by omega)
    obtain ⟨hpxH, hpxe, -, hXprop, hXs, -⟩ := hXr
    obtain ⟨-, k, ℓ, d, pay, hc, hcall, hd, htc, hpar, -⟩ :=
      honestProposalRun_of_proposesAt hrun hnc hpxH hpxe hXprop hXs
    have htX : tr.time kx = sp.ts (s + sp.toParams.δt : Nat) := by
      rw [hXprop.2.2, sp.slotTime_eq, hXs]; rfl
    -- its parent is above the high origin of a report above `P`
    obtain ⟨r₀, ℓ₀, C₀, hC₀, hr₀, hPC₀⟩ := hall p hpH
    have hC₀m := toFG_mem_tree hrun hpH hC₀
    have hP₀m := mem_of_honest_anc hrun hnc hpH hPC₀ hC₀m
    have hC₀h : HZ tr H g + 1 ≤ ((tr.state p r₀).fg.σ C₀.root).h := by
      have := h_le_of_store_anc (Compose.fg_reachable hrun.toLocalRun hpH r₀)
        (store_anc_of_honest_anc hrun hnc hpH hPC₀ hC₀m)
      rw [hPσ hpH hP₀m] at this
      omega
    obtain ⟨io, hio, jo, O, ho, hC₀O⟩ := high_report_origin hp hpH hC₀ hC₀h
    have hiot : tr.time io < sp.ts (s + sp.toParams.δt : Nat) := by
      have := hrun.time_mono hio.le
      rw [hts_add]
      linarith
    have hOd := (hp.toUpTo tr H (le_max_left a (tr.time k))).reset_proposal_passes
      hpat.catchPremise hpxH (hafter.trans (hts (by omega))) hc hcall hd htc
      (le_max_right _ _) O ⟨p, io, jo, ho, hiot⟩
    have hPD := (hPC₀.trans hC₀O).trans hOd
    have hrow : ∀ y ∈ H,
        (∃ w ∈ H, ∃ c, P ∈ (tr.state w c).fg.tree ∧ ∃ k att, tr.SignAt y k att ∧
          tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ att.h = ((tr.state w c).fg.σ P.root).h ∧
          att.T = ((tr.state w c).fg.σ P.root).Th) ∨
        ∃ R, Anc (tr.HonestBlocks H) R d.head ∧ ∃ w ∈ H, ∃ c, P ∈ (tr.state w c).fg.tree ∧
          R ∈ (tr.state w c).fg.tree ∧
          ((tr.state w c).fg.σ P.root).h < ((tr.state w c).fg.σ R.root).h := by
      intro y hy
      obtain ⟨r, ℓ', C, hC, hrt, hPC⟩ := hall y hy
      have hPy' := mem_of_honest_anc hrun hnc hy hPC (toFG_mem_tree hrun hy hC)
      obtain ⟨hPy, -, hor⟩ := row_of_high_report hp hy hC hPC (by rw [hPσ hy hPy']; exact hhigh)
      rcases hor with ⟨k', att, hs', hk', hah, haT⟩ | hlt
      · exact Or.inl ⟨y, hy, r, hPy, k', att, hs', hk'.trans hrt, hah, haT⟩
      · exact absurd (hhi y hy r ℓ' C hC hrt hPC) (not_le.2 hlt)
    obtain ⟨-, hXx, hh⟩ := round_cross hrun hnc (ResetService.of_gst (b := tr.time kx) tr H
      hp.healthy.1) hpat.shared.noRestart hp.healthy.2.2 hPH hPD hpar hpxH hXprop
      (v := sp.ts s + 6 * sp.Δ) (by linarith) (by rw [htX, hts_add]; linarith) le_rfl
      (by rw [hPs, hXs]; exact le_rfl) hrow
    have hDH := mem_of_anc_right hPD hPH
    refine ⟨proposer (s + sp.toParams.δt), hpxH, kx + 1, X, hXx,
      hPD.tail ⟨hDH, ⟨_, hpxH, kx + 1, hXx⟩, hpar⟩, by omega, by rw [hXs]⟩
  -- the first crossing on `P ⪯ D` is a stretch proposal and its own entry
  obtain ⟨w, hw, c, D, hDm, hPD, hlt, hDs⟩ := key
  have hrw := Compose.fg_reachable hrun.toLocalRun hw c
  have hsub : (tr.state w c).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨w, hw, c, hX⟩
  have hPw := mem_of_honest_anc hrun hnc hw hPD hDm
  obtain ⟨U, hUm, hPU, hUD, hUh, hUTh⟩ :=
    first_crossing hrw (store_anc_of_honest_anc hrun hnc hw hPD hDm) hlt
  have hne : U ≠ P := fun h => by rw [h] at hUh; omega
  have hsl := Anc.slot_le hU (hPU.mono hsub)
  have hsUD := (Anc.slot_le hU (hUD.mono hsub)).1
  have hslt : s < U.slot := hPs ▸ hsl.2 (Ne.symm hne)
  obtain ⟨kU, B, hBr, -⟩ := hwindow U.slot (by omega) (by omega)
  obtain ⟨hqH, -, -, hBprop, hBs, -⟩ := id hBr
  obtain rfl : U = B := Compose.eq_of_slot hrun hqH hBprop (hsub hUm) hBs.symm
  obtain ⟨hacc, hUq, hpost⟩ := accept_of_proposesAt hrun hnc hqH hBprop
  have hσU := σ_eq_honest hrun hnc hqH hw hUq hUm
  refine ⟨proposer U.slot, kU, kU, U, hBr, ⟨hqH, hacc, ?_⟩, hPU.mono hsub, hslt, by omega, ?_⟩
  · rw [hpost, hσU]; exact hUTh
  · rw [hpost, hσU, hUh, hPσ hw hPw]

end Consensus.Goldilocks.Healing.Recovery

end

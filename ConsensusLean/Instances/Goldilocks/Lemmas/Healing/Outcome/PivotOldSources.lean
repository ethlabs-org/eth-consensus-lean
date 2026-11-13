module
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: old sources at proposals

Prerequisites for the post-reset proposal pivot. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-! ### Old sources -/

/-- **The old sources of slot `u`**: the HR.4 high origins written before `t_u` (the post-reset
counterpart of `Compose.pivot_before`'s old origins; their labels are below `u`). -/
def OldSrc (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (g : Time) (u : Nat)
    (O : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∃ (x : Fin sp.n) (i j : Nat), HighOrigin tr H g x i j O ∧ tr.time i < sp.ts u

/-- An old source is a high origin written before the slot starts. -/
theorem oldSrc_iff {u : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))} :
    OldSrc tr H g u O ↔
      ∃ (x : Fin sp.n) (i j : Nat), HighOrigin tr H g x i j O ∧ tr.time i < sp.ts u := Iff.rfl

/-- The causal cache comparison also permits an origin written after the receiver cut. -/
theorem ResetPremisesUpTo.finalized_compatible_high_origin {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (hcb : ∀ q < c, tr.time q ≤ b)
    {x : Fin sp.n} {i j : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j O) (hib : tr.time i ≤ b) :
    Compatible (tr.HonestBlocks H) (tr.state z c).fg.F O := by
  have hr := Compose.fg_reachable hp.run.toLocalRun hz c
  have hU := hp.honest_coherent
  have hsub : (tr.state z c).fg.tree ⊆ tr.HonestBlocks H := fun _ h => ⟨z, hz, c, h⟩
  by_cases hh : HZ tr H g + 1 ≤ (tr.state z c).fg.hj
  · obtain ⟨_, hJm, hFJ, ⟨C, hC, hCJ, _⟩, _⟩ := Store.cache_invariants _ _ _ _ hr
    obtain ⟨E, hE, hEr, hEC, hcase⟩ := Store.J_entry_of_reachable hr hC
    obtain rfl : E = (tr.state z c).fg.J := hU.1 (hsub hE) (hsub hJm) (hEr.trans hCJ)
    rcases hcase with hg | ⟨hJh, hJT⟩
    · obtain ⟨_, _, _, _, _, _, _, _, _, hO⟩ := hp.highOrigin_mem ho
      exact Or.inl ((hFJ.mono hsub).trans
        (Compose.honest_genesis_root_anc hp.run hU (hsub hJm)
          (congrArg (·.root) hg) ⟨x, ho.1, i, hO⟩))
    · obtain ⟨_, _, _, _, v, _, d, hdc, _, _, r, hrd, m, B, hB, hJB⟩ :=
        hp.left_entry_origin hz hJm hJT (by omega) hEC
          (by have := Store.hj_lt_h hr hC; (clear * - hJh this; omega))
      have hFB := (hFJ.mono hsub).trans hJB
      rcases hp.origins_compatible hB (hcb r (by clear * - hdc hrd; omega)) ho hib with h | h
      · exact Or.inl (hFB.trans h)
      · exact Anc.total hU hFB h
  · exact Or.inl (hp.low_finalized_below_origin hz c (by clear * - hh; omega) ho)

/-- Compare the actual cache and origin within a fixed horizon using only held
chains and prior signed-attestation origins. No later tick is required. -/
theorem finalized_compatible_high_origin_before
    (hp : ResetPremises tr H proposer dg g ΔF a) (Q : Time)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (_hcQ : tr.time c ≤ Q)
    {x : Fin sp.n} {i j : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j O) (_hiQ : tr.time i ≤ Q) :
    Compatible (tr.HonestBlocks H) (tr.state z c).fg.F O :=
  (hp.toUpTo tr H (le_max_left a (max (tr.time c) (tr.time i)))).finalized_compatible_high_origin
    hz (fun _ hq => (hp.run.time_mono hq.le).trans ((le_max_left _ _).trans (le_max_right _ _)))
    ho ((le_max_right _ _).trans (le_max_right _ _))

/-- Whole-run cache comparison permits an origin written after the receiver cut. -/
theorem finalized_compatible_high_origin_at_any_cut
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat}
    {x : Fin sp.n} {i j : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j O) :
    Compatible (tr.HonestBlocks H) (tr.state z c).fg.F O := by
  exact finalized_compatible_high_origin_before hp (max (tr.time c) (tr.time i)) hz
    (le_max_left _ _) ho (le_max_right _ _)

/-- Post-reset specialization retained for callers with an explicit reset cut bound. -/
theorem finalized_compatible_high_origin (hp : ResetPremises tr H proposer dg g ΔF a)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (_hac : a ≤ tr.time c)
    {x : Fin sp.n} {i j : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j O) :
    Compatible (tr.HonestBlocks H) (tr.state z c).fg.F O :=
  finalized_compatible_high_origin_at_any_cut hp hz ho

/-- A post-reset finalized cache lies below an actual bounded high origin. -/
theorem ResetPremisesUpTo.finalized_below_high_origin {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (ha : a ≤ tr.time k)
    (hkb : ∀ q < k, tr.time q ≤ b) :
    ∃ x r l B, HighOrigin tr H g x r l B ∧ tr.time r ≤ tr.time k ∧ tr.time r ≤ b ∧
      Anc (tr.HonestBlocks H) (tr.state y k).fg.F B := by
  have seed : ∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r ≤ a := by
    obtain ⟨⟨v, hv, d, att, hsign, hh, hda⟩, _⟩ := hp.reset
    obtain ⟨r, hrd, l, O, ho, _⟩ := hp.high_row_source hv hsign hh.ge
    exact ⟨v, r, l, O, ho, (hp.run.time_mono hrd.le).trans hda.le⟩
  have hr := Compose.fg_reachable hp.run.toLocalRun hy k
  have hU := hp.honest_coherent
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocks H := fun _ h => ⟨y, hy, k, h⟩
  obtain ⟨hFm, hJm, hFJ, ⟨C, hC, hCJ, hChj⟩, _⟩ := Store.cache_invariants _ _ _ _ hr
  obtain ⟨E, hE, hEr, hEC, hcase⟩ := Store.J_entry_of_reachable hr hC
  obtain rfl : E = (tr.state y k).fg.J := hU.1 (hsub hE) (hsub hJm) (hEr.trans hCJ)
  rcases hcase with hg | ⟨hJh, hJT⟩
  · obtain ⟨v, r, l, B, ho, ht⟩ := seed
    have hFG := (Store.accepted_tree _ _ _ _ hr).2.2.2 _ hFm
    rw [← hg] at hFG
    have he := (hFJ.mono hsub).antisymm hU (hFG.mono hsub)
    obtain ⟨_, _, _, _, _, _, _, _, _, hB⟩ := hp.highOrigin_mem ho
    exact ⟨v, r, l, B, ho, ht.trans ha, ht.trans hp.reset_le,
      Compose.honest_genesis_root_anc hp.run hU (hsub hFm)
        (congrArg (·.root) (he.trans hg)) ⟨v, ho.1, r, hB⟩⟩
  by_cases hh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj
  · obtain ⟨_, _, _, _, v, _, d, hdk, _, _, r, hrd, l, B, ho, hJB⟩ :=
      hp.left_entry_origin hy hJm hJT (by clear * - hChj hJh hh; omega) hEC
        (by have := Store.hj_lt_h hr hC; (clear * - hJh this; omega))
    exact ⟨v, r, l, B, ho, hp.run.time_mono (by clear * - hdk hrd; omega), hkb r (by
        clear * - hdk hrd; omega),
      (hFJ.mono hsub).trans hJB⟩
  obtain ⟨v, r, l, B, ho, ht⟩ := seed
  exact ⟨v, r, l, B, ho, ht.trans ha, ht.trans hp.reset_le,
    hp.low_finalized_below_origin hy k (by clear * - hh; omega) ho⟩

/-- Actual-call relay of a high supporting head to the proposal frame. -/
theorem ResetPremisesUpTo.proposal_relay_high {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) {u i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u)
    {x : Fin sp.n} {r l : Nat} {O B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hOB : Anc (tr.HonestBlocks H) O B)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (hacc : tr.projAC.AcceptAt z c B)
    (hct : tr.time c < sp.ts ((u : Int) - 1) + 2 * sp.Δ)
    (hFB : Anc (tr.HonestBlocks H) ell.frame.F B) :
    B ∈ ell.frame.tree ∧ SA.AcceptedBefore tr.projAC p B (sp.ts ((u : Int) - 1) + 3 * sp.Δ) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  have hgc : g ≤ tr.time c := by
    have := (hp.cutZ_lt_of_anc ho hz (hp.acceptAt_mem hz hacc) hOB).1
    have := lt_cutZ sp g
    have := le_gbar g
    linarith
  have hsi : sp.slot (tr.time i) = u := by
    rw [hti]; simpa using (SA.slot_arithmetic sp u).1 0 (by clear * -; omega)
  have hts : sp.ts (u : Int) = sp.ts ((u : Int) - 1) + 4 * sp.Δ := by
    simp only [SAParams.ts]; ring
  have hrs := Compose.proposal_call_restarts hp.run hp.noColl hpH hci hcall hd
  rw [hsi] at hrs
  have hdl : ∀ k ≤ i, tr.projAC.deadline p k (tr.projAC.time c) ≤
      sp.ts ((u : Int) - 1) + 3 * sp.Δ := fun k hk => by
    have hd := Compose.ac_deadline_le_of_restarts (T := tr.projAC)
      (fun c' hc' hr' => hrs c' (hc'.trans hk) hr') (tr.projAC.time c)
    have := max_le hct.le (show sp.ts ((u : Int) - 1) ≤ sp.ts ((u : Int) - 1) + 2 * sp.Δ by
      linarith only [hΔ])
    change _ ≤ max (tr.time c) (sp.ts ((u : Int) - 1)) + sp.Δ at hd
    linarith only [this, hd]
  obtain ⟨k, hki, hak, hkt⟩ := (hp.sync.syncAC hp.run le_rfl).2 z hz c B hacc hgc le_rfl
    p hpH i ell hci (by
        have := hdl i le_rfl; change _ ≤ tr.time i; linarith only [hti, hΔ, hts, this]) hFB
  exact ⟨SA.mem_tree_of_acceptAt sp hr hpH hak hki hci hFB,
    Or.inr ⟨k, hak, lt_of_lt_of_le hkt (hdl k hki)⟩⟩

/-- The label of an old source is below `u`. -/
theorem label_lt_of_old (hp : ResetPremises tr H proposer dg g ΔF a)
    {u : Nat} {x : Fin sp.n}
    {i j : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j O)
    (ht : tr.time i < sp.ts u) : j < u := by
  obtain ⟨-, D, CV, -, hfl, -⟩ := highOrigin_mem hp ho
  by_contra hcon
  have h1 : sp.ts u ≤ sp.ts j := (SA.ts_le_iff sp).2 (by omega)
  linarith [ts_le_of_fastLock hp hfl]

/-- An earlier high source is held at a bounded actual proposal, or finalized there. -/
theorem ResetPremisesUpTo.proposal_holds_old {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) {u i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {x : Fin sp.n} {r l : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hrt : tr.time r < sp.ts u) :
    O ∈ ell.frame.tree ∨ Anc (tr.HonestBlocks H) O ell.frame.F := by
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun.localRun
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hpH hci
  have hrb : tr.time r ≤ b := hrt.le.trans (hti ▸ hib)
  have hcmp := hp.finalized_compatible_high_origin hpH
    (fun q hqi => (hp.run.time_mono hqi.le).trans hib) ho hrb
  have hfr := Compose.frame_of_projAC hp.run hpH hci
  have hF : ell.frame.F = (tr.state p i).fg.F := by rw [hfr]; rfl
  rw [← hF] at hcmp
  rcases hcmp with hFO | hOF
  · left
    obtain ⟨ellX, D, CV, hcx, hfl, _, _, _, hOD, _⟩ := hp.highOrigin_mem ho
    have hf : 2 * Hᶜ.ncard < sp.n := by have := hp.faults; have := Fin.pos p; omega
    obtain ⟨z, hz, j, e, hv, hes, B, hB, hBr, hDB⟩ :=
      SA.fastLock_honest_vote hrun hf ho.1 hfl hp.stock
    have hOB := (hOD.mono (SA.frameIn_of_callAt hr ho.1 hcx).2).trans hDB
    obtain ⟨ellZ, hcz, he⟩ := hv
    obtain ⟨⟨B', hB't, hB'r, _⟩, hjt⟩ := Compose.cast_head_fcRoot hr hz ⟨hcz, he⟩
    have hEq : B' = B := hr.coherent.1 ((SA.frameIn_of_callAt hr hz hcz).2 hB't) hB
      (hB'r.trans hBr.symm)
    rw [hEq] at hB't
    have htr : sp.ts l ≤ tr.time r := by
      rcases hfl with ⟨ell', C, ⟨_, _, ht, _⟩, _⟩ | ⟨ell', A, _, hsl, _⟩
      · change tr.time r = sp.ts l + 6 * sp.Δ at ht
        linarith only [hΔ, ht]
      · exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg r) l).mpr (by omega)
    have hlu : l < u := by exact_mod_cast (SA.ts_lt_iff sp).mp (htr.trans_lt hrt)
    have hts : sp.ts l ≤ sp.ts ((u : Int) - 1) := (SA.ts_le_iff sp).mpr (by clear * - hlu; omega)
    have hjt' : tr.time j ≤ sp.ts ((u : Int) - 1) + sp.Δ := by
      rw [hes] at hjt
      change tr.time j ≤ sp.ts l + sp.Δ at hjt
      linarith only [hts, hjt]
    rcases Compose.frame_anc_accepted hr hz j ellZ hcz B hB't B .refl with hg | ⟨c, hcj, hacc⟩
    · exact False.elim ((hp.cutZ_lt_of_anc ho hz
        (mem_tree_of_frame hp.run hz hcz hB't) hOB).2 hg)
    have hct : tr.time c < sp.ts ((u : Int) - 1) + 2 * sp.Δ := by
      have := hr.time_mono hcj
      change tr.time c ≤ tr.time j at this
      linarith only [hΔ, hjt', this]
    have hBt := (hp.proposal_relay_high hpH hci hcall hd hti ho hOB hz hacc hct
      (hFO.trans hOB)).1
    exact Compose.mem_between hr.coherent hΦ hΦU hΦ.rooted.1 hBt hFO hOB
  · exact Or.inr hOF

/-- An old source is held by the proposer, or below its finalized cache. Relay starts at an
honest supporting vote head, not at the possibly later write of the origin. -/
theorem proposal_holds_old (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {u i : Nat} (hai : a ≤ tr.time i)
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hO : OldSrc tr H g u O) :
    O ∈ ℓp.frame.tree ∨ Anc (tr.HonestBlocks H) O ℓp.frame.F := by
  obtain ⟨x, r, l, ho, hrt⟩ := hO
  exact (hp.toUpTo tr H hai).proposal_holds_old hpH hci hcall hd hti le_rfl ho hrt

/-- Conditional seed receipt at a proposal, including the finalized-equality case. -/
theorem proposal_holds_high_of_finalized
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {u i : Nat} (hai : a ≤ tr.time i)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) {x : Fin sp.n} {r l : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x r l O)
    (hrt : tr.time r < sp.ts u) (hFO : Anc (tr.HonestBlocks H) ell.frame.F O) :
    O ∈ ell.frame.tree := by
  rcases proposal_holds_old hp hpH hai hci hcall hd hti (oldSrc_iff.2 ⟨x, r, l, ho, hrt⟩)
    with hO | hOF
  · exact hO
  · have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
    obtain ⟨hPhi, -⟩ := SA.frameIn_of_callAt hr hpH hci
    have he := Anc.antisymm hr.coherent hOF hFO
    rw [he]
    exact hPhi.rooted.1

/-- Bounded root comparison uses only an actual proposal and earlier source comparisons. -/
theorem ResetPremisesUpTo.held_target_proposal_root_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r i u : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBx : B ∈ (tr.state x r).fg.tree)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B → B ∈ ell.frame.tree)
    (hseed : ∃ v q m S, HighOrigin tr H g v q m S ∧ tr.time q < sp.ts u ∧
      Compatible (tr.HonestBlocks H) B S)
    (hcompare : ∀ v q m O, q < i → HighOrigin tr H g v q m O →
      Compatible (tr.HonestBlocks H) B O) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B := by
  by_cases hlow : (tr.state p i).fg.hj ≤ HZ tr H g
  · obtain ⟨v, q, m, S, hS, hm, hBS⟩ := hseed
    have hFS := hp.low_finalized_below_origin hpH i hlow hS
    have hFF : ell.frame.F = (tr.state p i).fg.F := by
      rw [Compose.frame_of_projAC hp.run hpH hci]; rfl
    have hSt : S ∈ ell.frame.tree := by
      rcases hp.proposal_holds_old hpH hci hcall hd hti hib hS hm with h | h
      · exact h
      · rw [hFF] at h
        have he := Anc.antisymm hp.honest_coherent h hFS
        rw [he, ← hFF]
        exact (SA.frameIn_of_callAt
          (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
          hpH hci).1.rooted.1
    exact hp.low_root_of_held_seed_at_call hx hBx hpH hS hci
      (mem_tree_of_frame hp.run hpH hci hSt) hlow hBS hheld
  · exact hp.high_J_root_of_held_at_call_before hx hBx hpH hci (by clear * - hlow; omega) hcompare

/-- Root comparison for an actual proposal duty and an arbitrary held target. -/
theorem held_target_proposal_root_before
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r i u : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBx : B ∈ (tr.state x r).fg.tree)
    (hai : a ≤ tr.time i) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B → B ∈ ell.frame.tree)
    (hseed : ∃ v q m S, HighOrigin tr H g v q m S ∧ tr.time q < sp.ts u ∧
      Compatible (tr.HonestBlocks H) B S)
    (hcompare : ∀ v q m O, q < i → HighOrigin tr H g v q m O →
      Compatible (tr.HonestBlocks H) B O) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B :=
  (hp.toUpTo tr H hai).held_target_proposal_root_before hx hpH hBx hci hcall hd hti le_rfl hheld
    hseed hcompare


end Consensus.Goldilocks.Healing

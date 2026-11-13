module
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: proposal and recipient frames

Frame uniqueness, relay and view agreement for the post-reset duty suppliers. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- A bounded clean source is below the head of an actual later-label honest cast.
The cast's agreement with the operational proposal is supplied explicitly. -/
theorem ResetPremisesUpTo.clean_source_below_cast {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {r s i : Nat}
    {B P : SA.Blk sp.n (List (FG.Att sp.n))}
    (horig : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e) (hib : tr.time i ≤ b)
    (hsi : s < e.msg.slot) (hPU : P ∈ tr.HonestBlocks H) (heP : e.msg.head = P.root) :
    Anc (tr.HonestBlocks H) B P := by
  have hext : SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
    rcases horig with ⟨CV, hf⟩ | hslo
    · exact hp.fast_source_votes_before hc hx hf hs hrb i hib y hy ell e hcast hsi
    · exact hp.slow_source_votes_before hc hx hslo hs hrb i hib y hy ell e hcast hsi
  obtain ⟨D, hD, hDr, hBD⟩ := hext
  obtain rfl : D = P := hp.honest_coherent.1 hD hPU (hDr.trans heP)
  exact hBD

/-- Same-label raw sources lie below the unanimous operational head via an actual
honest supporter, not via an assumed later successful update. -/
theorem ResetPremisesUpTo.same_slot_source_below_unanimous {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H) {r u : Nat}
    {B P : SA.Blk sp.n (List (FG.Att sp.n))}
    (horig : (∃ CV, SA.FastLockAt tr.projAC x r u B CV) ∨ SA.SlowLockAt tr.projAC x r u B)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts u)
    (hPU : P ∈ tr.HonestBlocks H)
    (hun : ∀ z ∈ H, ∀ q e, SA.VoteAt tr.projAC z q e → tr.time q ≤ b →
      e.msg.slot = u → e.msg.head = P.root) : Anc (tr.HonestBlocks H) B P := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have below : ∀ z ∈ H, ∀ q ≤ r, ∀ e, SA.VoteAt tr.projAC z q e → e.msg.slot = u →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B → Anc (tr.HonestBlocks H) B P := by
    rintro z hz q hqr e hv hes ⟨D, hD, hDr, hBD⟩
    obtain rfl : D = P := hr.coherent.1 hD hPU
      (hDr.trans (hun z hz q e hv ((hp.run.time_mono hqr).trans hrb) hes))
    exact hBD
  rcases horig with ⟨CV, ⟨ell, C, hupd, hC, hD, _⟩ | hop⟩ | ⟨ell, C, hupd, hC, hD⟩
  · obtain ⟨z, hz, q, hqr, e, hv, _, hes, he⟩ := hp.result_supporter hc hx
      ⟨ell, hupd, hC, rfl⟩ ((SA.deepest_mem hD).1.1.2.2.mono
        (SA.frameIn_of_callAt hr hx hupd.1).2) hrb hts
    exact below z hz q hqr.le e hv hes he
  · obtain ⟨_, z, hz, q, hqr, e, hv, hes, he⟩ := hp.optimistic_supporter hx hop
    exact below z hz q hqr e hv hes he
  · obtain ⟨z, hz, q, hqr, e, hv, _, hes, he⟩ := hp.result_supporter hc hx
      ⟨ell, hupd, hC, rfl⟩ ((SA.deepest_mem hD).1.1.2.2.mono
        (SA.frameIn_of_callAt hr hx hupd.1).2) hrb hts
    exact below z hz q hqr.le e hv hes he

/-- Through the update deadline, normalized live locks compare with the operational
head. Older and same-label source ancestry are derived from actual bounded votes. -/
theorem ResetPremisesUpTo.call_locks_compatible_of_unanimous {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPU : P ∈ tr.HonestBlocks H)
    (hts : cutZ sp.toParams g ≤ sp.ts u)
    (hun : ∀ z ∈ H, ∀ q e, SA.VoteAt tr.projAC z q e → tr.time q ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hvote : ∃ z ∈ H, ∃ q ell e, SA.CastAt tr.projAC z q ell e ∧
      tr.time q ≤ b ∧ e.msg.slot = u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) (hjb : tr.time j ≤ b)
    (hafter : drainTime sp a ≤ tr.time j) (hbefore : tr.time j ≤ sp.ts u + 6 * sp.Δ)
    (hnext : ∀ r < j, ∀ B CV, SA.OptimisticLockAt tr.projAC y r (u + 1) B CV →
      Compatible (tr.HonestBlocks H) B P) :
    ∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state y j).locks ell.frame (tr.time j),
      Compatible (tr.HonestBlocks H) L P := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hcall
  have hDelta := sp.toParams.hΔ
  rintro L ⟨hLt, l', ⟨l, hl, B, hB, hBr, hlive, rfl⟩, hLr⟩
  obtain rfl : L = ell.frame.viableAncestor B := hPhi.coherent.1 hLt
    (SA.viableAncestor_anc hPhi hB).1 hLr.symm
  obtain ⟨r, hrj, D, horig, X, hX, hXr, hXD⟩ : ∃ r < j, ∃ D,
      ((∃ CV, SA.FastLockAt tr.projAC y r l.slot D CV) ∨ SA.SlowLockAt tr.projAC y r l.slot D) ∧
      ∃ X ∈ tr.HonestBlocks H, X.root = l.block ∧ Anc (tr.HonestBlocks H) X D := by
    cases hf : l.fast with
    | false =>
      obtain ⟨r, hrj, D, hs, hX⟩ := SA.slow_lock_provenance hr hy j l hl hf
      exact ⟨r, hrj, D, Or.inr hs, hX⟩
    | true =>
      obtain ⟨r, hrj, D, CV, hf, hX⟩ := SA.fast_lock_provenance hr hy j l hl hf
      exact ⟨r, hrj, D, Or.inl ⟨CV, hf⟩, hX⟩
  have hXB : X = B := hr.coherent.1 hX (hPhiU hB) (hXr.trans hBr.symm)
  rw [hXB] at hXD
  have hLD := ((SA.anc_viableAncestor ell.frame B).mono hPhiU).trans hXD
  have hrb := (hp.run.time_mono hrj.le).trans hjb
  have hrt := (hp.run.time_mono hrj.le).trans hbefore
  have hDP : Compatible (tr.HonestBlocks H) D P := by
    by_cases hlu : l.slot < u
    · have hs := drain_live_locks (SA.locksWF_state hr hy j) hafter _
        ⟨l, hl, B, hB, hBr, hlive, rfl⟩
      obtain ⟨z, hz, q, ellq, e, hcast, hqb, hes⟩ := hvote
      exact Or.inl (hp.clean_source_below_cast hc hy hz horig hs hrb hcast hqb
        (hes ▸ hlu) hPU (hun z hz q e ⟨ellq, hcast⟩ hqb hes))
    by_cases heq : l.slot = u
    · exact Or.inl (hp.same_slot_source_below_unanimous hc hy (heq ▸ horig) hrb hts hPU hun)
    have hgt : u < l.slot := by omega
    rcases horig with ⟨CV, ⟨ellr, C, hupd, _⟩ | hop⟩ | ⟨ellr, C, hupd, _⟩
    · have htr : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
      have hlt := (SA.ts_lt_iff sp).2 (show (u : Int) < l.slot by omega)
      exfalso; linarith only [hrt, htr, hlt]
    · have hsl : sp.slot (tr.time r) = l.slot := hop.choose_spec.choose_spec.2.1
      have hmono := SA.slot_mono sp (hr.time_nonneg r) hrt
      change sp.slot (tr.time r) ≤ sp.slot (sp.ts u + 6 * sp.Δ) at hmono
      have hs : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 :=
        SA.slot_of_mem sp (u + 1) (by simp only [SAParams.ts]; push_cast; linarith only [hDelta])
          (by simp only [SAParams.ts]; push_cast; linarith only [hDelta])
      rw [hsl, hs] at hmono
      exact hnext r hrj D CV (show l.slot = u + 1 by omega ▸ hop)
    · have htr : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
      have hlt := (SA.ts_lt_iff sp).2 (show (u : Int) < l.slot by omega)
      exfalso; linarith only [hrt, htr, hlt]
  rcases hDP with hDP | hPD
  · exact Or.inl (hLD.trans hDP)
  · exact SA.anc_total hr.coherent hLD hPD

/-- A high floor yields an actual earlier report, retaining the signed entry witness
from the finite floor producer. Only causal origin comparisons remain inputs. -/
theorem ResetPremisesUpTo.held_target_high_floor_report_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y v : Fin sp.n} (hy : y ∈ H) {i q m : Nat}
    {P S : SA.Blk sp.n (List (FG.Att sp.n))} (hPy : P ∈ (tr.state y i).fg.tree)
    (hseed : HighOrigin tr H g v q m S) (hSP : Anc (tr.HonestBlocks H) S P)
    (hpair : ∀ x r l B, r < i → HighOrigin tr H g x r l B →
      ∀ x' r' l' B', r' < i → HighOrigin tr H g x' r' l' B' →
        Compatible (tr.HonestBlocks H) B B')
    (hseedcomp : ∀ x r l B, r < i → HighOrigin tr H g x r l B →
      Compatible (tr.HonestBlocks H) S B)
    (hcompare : ∀ x r l B, r < i → HighOrigin tr H g x r l B →
      Compatible (tr.HonestBlocks H) P B)
    (hfloor : ((tr.state y i).fg.σ P.root).h < (tr.state y i).fg.headHeightFloor) :
    ∃ x ∈ H, ∃ r ell C, r < i ∧ SA.ToFGAt tr.projAC x r ell C ∧
      Anc (tr.HonestBlocks H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h := by
  have hSy := hp.mem_tree_of_anc hy hSP hPy
  have hr := Compose.fg_reachable hp.run.toLocalRun hy i
  obtain ⟨-, -, -, -, -, -, -, -, -, hSs⟩ := hp.highOrigin_mem hseed
  have hSh := σ_h_le_of_anc hr (hp.anc_tree_of_anc hy hSP hPy)
  have hSf : ((tr.state v q).fg.σ S.root).h < (tr.state y i).fg.headHeightFloor := by
    rw [hp.σ_eq_run hseed.1 hy hSs hSy]
    omega
  obtain ⟨x, r, l, B, E, hri, ho, -, hE, hEB, -, hEf, d, att, hrd, hdi, hs, hT⟩ :=
    hp.high_floor_signed_source_of_row_bound hseed hy (u := sp.slot (tr.time i) + 1)
      (fun W hW att ha z hz d hd hdi r' l O hrd ho => by
        obtain ⟨-, D, CV, -, hfl, -⟩ := hp.highOrigin_mem ho
        have ht : sp.ts l ≤ tr.time r' := by
          rcases hfl with ⟨ell, C, ⟨-, -, ht, -⟩, -⟩ | ⟨ell, A, -, hsl, -⟩
          · change tr.time r' = sp.ts l + 6 * sp.Δ at ht
            linarith only [ht, sp.toParams.hΔ]
          · change sp.slot (tr.time r') = l at hsl
            exact (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg r') l).2 (by omega)
        have hlabel := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg i) l).1
          (ht.trans (hp.run.time_mono (by omega)))
        omega) hpair hseedcomp hSf
  have hPE : Anc (tr.HonestBlocks H) P E := by
    have hcomp : Compatible (tr.HonestBlocks H) P E := by
      rcases hcompare x r l B hri ho with h | h
      · exact SA.anc_total hp.honest_coherent h hEB
      · exact Or.inr (hEB.trans h)
    rcases hcomp with h | h
    · exact h
    · have := σ_h_le_of_anc hr (hp.anc_tree_of_anc hy h hPy)
      omega
  obtain ⟨j, ell, C, hji, hto, hPC, hh⟩ :=
    hp.higher_report_of_signed_entry hy ho.1 hPy hE hs hdi hT hPE (by omega)
  exact ⟨x, ho.1, j, ell, C, hji, hto, hPC, hh⟩

/-- Held-only finite update selection from actual early-resolved honest pool votes.
The receipt/unanimity and normalized-lock comparison obligations are explicit; neither
full viability nor whole-run health is used. The post-state records the actual raw write. -/
theorem ResetPremisesUpTo.ready_update_selection_of_pool {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hu : SA.UpdateAt tr.projAC y j u ell) (hPt : P ∈ ell.frame.tree)
    (hPg : P.root ≠ sp.genesisRoot)
    (hpool : ∀ v ∈ H, ∃ vote ∈ (tr.projAC.state y j).pool u,
      vote.val = v ∧ vote.head = P.root ∧
      SA.resolutionTime (tr.projAC.state y j) ell.frame vote < SA.ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ vote' ∈ (tr.projAC.state y j).pool u, vote'.val = v → vote' = vote)
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state y j).locks ell.frame (tr.time j),
      Compatible (tr.HonestBlocks H) L P) :
    SA.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P ∧
      ¬ SA.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P ∧
      SA.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P ∧
      tr.projAC.post j = SA.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u ∧
      (tr.projAC.post j).latestConfirmed =
        (SA.updateLatestConfirmed sp (tr.projAC.state y j) ell.frame P).latestConfirmed := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hu.1
  let A := tr.projAC.state y j
  have hHvot : H ⊆ SA.voters {v | v ∈ A.pool u} := fun v hv => by
    obtain ⟨vote, hm, he, -⟩ := hpool v hv
    exact ⟨vote, hm, he⟩
  have hvle : (SA.voters {v | v ∈ A.pool u}).ncard ≤ sp.n := by
    have := Set.ncard_le_ncard (Set.subset_univ (SA.voters {v | v ∈ A.pool u}))
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have hHn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hHle := Set.ncard_le_ncard hHvot
  have hf := hp.faults
  have hn : 0 < sp.n := sp.toParams.hn
  have hscore : H.ncard ≤ SA.confirmationScore sp A ell.frame u P := by
    unfold SA.confirmationScore
    apply Set.ncard_le_ncard (ht := Set.toFinite _)
    intro v hv
    obtain ⟨vote, hm, he, hh, hres, huniq⟩ := hpool v hv
    refine ⟨?_, vote, ⟨hm, hres⟩, he, ?_, P, hPt, hh.symm, .refl⟩
    · rintro ⟨x, hx, z, hz, hne, hxv, hzv⟩
      exact hne ((huniq x hx hxv).trans (huniq z hz hzv).symm)
    · exact_mod_cast SA.state_pool_slot sp hr hy j u vote hm
  have hconf : SA.getConfirmation sp A ell.frame u = some P := by
    unfold SA.getConfirmation
    have hPS : P ∈ {B | B ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.F B ∧
        (SA.voters {v | v ∈ A.pool u}).ncard < 2 * SA.confirmationScore sp A ell.frame u B} :=
      ⟨hPt, hPhi.rooted.2 P hPt, by omega⟩
    have hall : ∀ B ∈ {B | B ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.F B ∧
        (SA.voters {v | v ∈ A.pool u}).ncard < 2 * SA.confirmationScore sp A ell.frame u B},
        ell.frame.Anc B P := by
      rintro B ⟨hBt, -, hmaj⟩
      by_contra hBP
      unfold SA.confirmationScore at hmaj
      dsimp only at hmaj
      refine absurd hmaj (not_lt.2 (le_trans (Nat.mul_le_mul_left 2
        (Set.ncard_le_ncard (t := Hᶜ) ?_)) (by omega)))
      rintro v ⟨-, x, ⟨hx, -⟩, rfl, -, R, hR, hRr, hBR⟩ hv
      obtain ⟨vote, -, -, hh, -, huniq⟩ := hpool _ hv
      obtain rfl := huniq x hx rfl
      obtain rfl : R = P := hPhi.coherent.1 hR hPt (hRr.trans hh)
      exact hBP hBR
    obtain ⟨D, hD⟩ := SA.exists_deepest hPhi (fun B hB => hB.1) ⟨P, hPS⟩
    have hDP := hall D (SA.deepest_mem hD).1
    have hPD := SA.anc_deepest hPhi (fun B hB => hB.1)
      (fun B hB C hC => SA.anc_total hPhi.coherent (hall B hB) (hall C hC)) hD P hPS
    rw [hD, Anc.antisymm hPhi.coherent hDP hPD]
  have hnv : ¬ SA.conflictsWithLock sp A.locks ell.frame (tr.time j) P := by
    rintro ⟨L, hL, hnc⟩
    apply hnc
    rcases hlocks L hL with h | h
    · exact Or.inr (SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hL.1 h hPt)
    · exact Or.inl (SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPt h hL.1)
  have hfast : SA.fastSelect sp A ell.frame u P = some P :=
    SA.fastSelect_eq_result hPhi hPt hPg (by unfold SA.FastTest; rw [hp.stock]; omega)
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hslot : sp.slot (tr.time j) = u + 1 := by
    rw [ht]
    exact SA.slot_of_mem sp (u + 1)
      (by simp only [SAParams.ts]; push_cast; linarith only [sp.toParams.hΔ])
      (by simp only [SAParams.ts]; push_cast; linarith only [sp.toParams.hΔ])
  have hpost : tr.projAC.post j = SA.updateConfirmation sp A ell.frame (tr.time j) u := by
    have he := hr.exec j ell hu.1.2 (hu.1.1 ▸ hy)
    rw [hu.1.1, hu.2.1] at he
    have h1 : tr.projAC.post j = (SA.acOnTick sp y A ell.frame (tr.time j)).1 :=
      (congrArg Prod.fst he).symm
    rw [h1]
    unfold SA.acOnTick
    dsimp only
    have hn1 : ¬ tr.time j = sp.ts (u + 1 : Nat) + sp.Δ := by
      rw [ht]; simp only [SAParams.ts]; push_cast; linarith only [sp.toParams.hΔ]
    have h2 : tr.time j = sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
      rw [ht]; simp only [SAParams.ts]; push_cast; ring
    have hj : SA.joined sp A (tr.time j) := hu.2.2.2
    have hc2 : (tr.time j = sp.ts (u + 1 : Nat) + 2 * sp.Δ ∧ 0 < u + 1) = True :=
      eq_true ⟨h2, Nat.succ_pos u⟩
    rw [hslot]
    simp only [hj, not_true_eq_false, hn1, hc2, ↓reduceIte, Nat.add_sub_cancel]
  refine ⟨hconf, hnv, hfast, hpost, ?_⟩
  rw [hpost]
  unfold SA.updateConfirmation
  simp only [hconf, hnv, ↓reduceIte]
  unfold SA.updateLatestConfirmed
  split <;> rfl

/-- An honest designated actual proposal is the unique block of its positive slot
in every honest frame, without reset or readiness premises. -/
theorem proposal_frame_unique
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hu : 0 < u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) {Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Q ∈ ell.frame.tree) (hQu : Q.slot = u) : Q = P := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hac.localRun
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hPprop, _, ja, _, hacc, _⟩ :=
    honestProposalRun_of_proposesAt hrun hnc hpH hdesignated hactual hPs
  rw [← hdesignated] at hPprop hacc
  obtain ⟨ellp, hcp, hblock⟩ := hacc
  have hPm := (SA.accept_new sp hr hpH ⟨ellp, hcp, hblock⟩).1 ellp hcp
  have hQf : SA.HonestFrameBlock tr.projAC H Q := ⟨y, hy, j, ell, hcall, hQ⟩
  have hroot : Q.root ≠ sp.genesisRoot := by
    intro hg
    have hG := Store.genesis_mem (Compose.fg_reachable hrun.toLocalRun hy j)
    obtain rfl := hr.coherent.1 ((SA.frameIn_of_callAt hr hy hcall).2 hQ)
      ⟨y, hy, j, hG⟩ hg
    simp [Params.genesisBlock] at hQu
    omega
  exact (hac.honest.one_block P Q ⟨p, hpH, ja, ellp, hcp, hPm⟩ hQf (hPprop ▸ hpH)
    (by rw [hPprop, hac.honest.proposer Q hQf hroot, hQu, hdesignated])
    (by rw [hPs, hQu])).symm

/-- Actual honest proposals are unique in honest frames at their positive slot.
This uses no payload-support clause of `ReadyProposal`. -/
theorem reset_proposal_frame_unique
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hu : 0 < u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) {Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Q ∈ ell.frame.tree) (hQu : Q.slot = u) : Q = P :=
  proposal_frame_unique hp.run hp.noColl hP.1 hP.2.1 hP.2.2.2.1 hP.2.2.2.2.1 hu hy hcall
    hQ hQu

/-- Actual proposal uniqueness in a bounded run needs no readiness/support predicate. -/
theorem ResetPremisesUpTo.reset_proposal_frame_unique {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hu : 0 < u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) {Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Q ∈ ell.frame.tree) (hQu : Q.slot = u) : Q = P :=
  proposal_frame_unique hp.run hp.noColl hpH hdesignated hactual hPs hu hy hcall hQ hQu

/-- Finite guarded acceptance transport uses the causal reset restart bound. -/
theorem ResetPremisesUpTo.reset_accept_frame {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {q j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ha : tr.projAC.AcceptAt x q B)
    {ell : ACLabel (goldilocksNode sp ro)} (hcall : tr.projAC.CallAt y j ell)
    (hjb : tr.time j ≤ b) (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocks H) ell.frame.F B) : B ∈ ell.frame.tree := by
  have hS := healthy_base_of_reset_catch_before hp hc
  have hr := hS.run.localRun
  by_cases hnew : SA.gbar g ≤ tr.time q
  · have hd := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := j)
      (fun k hkj hk => restart_le_before hp hy (Compose.projAC_restartAt.mp hk)
        ((hp.run.time_mono hkj).trans hjb)) (tr.time q)
    have hdl : tr.projAC.deadline y j (tr.time q) ≤ tr.time j := by
      apply hd.trans
      change max (tr.time q) (sp.ts (sp.slot (SA.gbar g) + 1 : Nat)) + sp.Δ ≤ tr.time j
      rw [← max_add_add_right]
      exact max_le hq hjoin
    obtain ⟨k, hkj, hak, _⟩ := hS.sync.relay
      x hx q B ha hnew y hy j ell hcall (hdl.trans hjb) hdl hF
    exact SA.mem_tree_of_acceptAt sp hr hy hak hkj hcall hF
  · obtain ⟨k, hkj, hak, _⟩ := hS.catchUp.relay x hx q B ha (not_le.mp hnew)
      y hy j ell hcall hg hjb hF
    exact SA.mem_tree_of_acceptAt sp hr hy hak hkj hcall hF

/-- Finite relay of held blocks retains the receiver's finalization guard. -/
theorem ResetPremisesUpTo.reset_frame_relay {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {q j : Nat}
    {ellx elly : ACLabel (goldilocksNode sp ro)}
    (hcx : tr.projAC.CallAt x q ellx) (hcy : tr.projAC.CallAt y j elly)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ellx.frame.tree)
    (hjb : tr.time j ≤ b) (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocks H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hr := (healthy_base_of_reset_catch_before hp hc).run.localRun
  rcases Compose.frame_anc_accepted hr hx q ellx hcx B hB B .refl with hgen | ⟨k, hk, ha⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy j elly hcy
    obtain rfl : B = G := hr.coherent.1 ((SA.frameIn_of_callAt hr hx hcx).2 hB)
      hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
    · exact he ▸ (SA.frameIn_of_callAt hr hy hcy).1.rooted.1
    · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
  · exact hp.reset_accept_frame hc hx hy ha hcy hjb hg hjoin
      (by have := hp.run.time_mono hk; change tr.time k ≤ tr.time q at this
          linarith only [hq, this]) hF

/-- The actual proposal reaches a voter's frame above its finalization root. -/
theorem reset_proposal_frame
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k j u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hu : 0 < u)
    (hy : y ∈ H) {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocks H) ell.frame.F P) : P ∈ ell.frame.tree := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  by_cases hearly : tr.time j < sp.ts u + sp.Δ
  · obtain ⟨Q, hQ, hQs, -⟩ := SA.cast_ready hr hy hcy (by rw [hes]; exact hearly)
    rw [hes] at hQs
    exact (reset_proposal_frame_unique hp hP hu hy hcy.1 hQ hQs) ▸ hQ
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ja, -, hacc, hta⟩ :=
      honestProposalRun_of_ready hp.run hp.noColl hP
    rw [← hP.2.1] at hacc
    exact reset_accept_frame hp hc hP.1 hy hacc hcy.1 hg
      (by change tr.time ja = sp.ts u at hta; rw [hta]; exact not_lt.mp hearly) hF

/-- Bounded actual casts hold the operational proposal above their finalized root. -/
theorem ResetPremisesUpTo.reset_proposal_frame {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k j u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = u) (hu : 0 < u)
    (hy : y ∈ H) {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u) (hjb : tr.time j ≤ b)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocks H) ell.frame.F P) : P ∈ ell.frame.tree := by
  have hr := (healthy_base_of_reset_catch_before hp hc).run.localRun
  by_cases hearly : tr.time j < sp.ts u + sp.Δ
  · obtain ⟨Q, hQ, hQs, _⟩ := SA.cast_ready hr hy hcy (by rw [hes]; exact hearly)
    rw [hes] at hQs
    exact (hp.reset_proposal_frame_unique hpH hdesignated hactual hPs hu hy hcy.1 hQ hQs) ▸ hQ
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ja, _, hacc, hta⟩ :=
      honestProposalRun_of_proposesAt hp.run hp.noColl hpH hdesignated hactual hPs
    rw [← hdesignated] at hacc
    exact hp.reset_accept_frame hc hpH hy hacc hcy.1 hjb hg hjoin
      (by change tr.time ja = sp.ts u at hta; rw [hta]; exact not_lt.mp hearly) hF

/-- Payload support is transported only above the receiver's `F`. Early votes use their
actual readiness witness; deadline votes use guarded relay, not ready-proposal support. -/
theorem reset_support_frame
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k (s + 1) P)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    {v : SA.Vote sp.n} (hv : v ∈ pay.2) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ ellp.frame.tree) (hBr : B.root = v.head)
    (hF : Anc (tr.HonestBlocks H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  by_cases hearly : tr.time j < sp.ts (s + 1 : Nat) + sp.Δ
  · obtain ⟨Q, hQ, hQs, hsup⟩ := SA.cast_ready hr hy hcy (by rw [hes]; exact hearly)
    rw [hes] at hQs hsup
    obtain rfl := reset_proposal_frame_unique hp hP (by omega) hy hcy.1 hQ hQs
    have hslot : sp.slot (tr.time i) = s + 1 := by
      rw [hti]; exact SA.slot_of_mem sp _ le_rfl ((SA.ts_lt_iff sp).mpr (by omega))
    have hpay' : pay = SA.voteViewList (tr.projAC.state p i) ellp.frame (s : Int) ⊤ := by
      unfold SA.acProposal at hd
      split_ifs at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      rw [← hd.2, hslot]
      congr 1
      push_cast
      ring
    have hvs : v.slot + 1 = s + 1 := by
      rw [hpay'] at hv
      simp only [SA.voteViewList, SA.SAState.poolAt, Int.toNat_natCast, List.filter_filter,
        List.mem_filter, List.mem_ite_nil_left, not_lt, Nat.cast_nonneg, true_and,
        Bool.and_eq_true, decide_eq_true_eq] at hv
      rw [SA.state_pool_slot sp hr hP.1 i s v hv.1]
    obtain ⟨B', hB', hBr', -⟩ := hsup v (by rw [SA.blockSupport, hpay]; exact hv) hvs
    rwa [hr.coherent.1 ((SA.frameIn_of_callAt hr hP.1 hci).2 hB)
      ((SA.frameIn_of_callAt hr hy hcy.1).2 hB') (hBr.trans hBr'.symm)]
  · exact reset_frame_relay hp hc hP.1 hy hci hcy.1 hB hg
      (by rw [hti]; exact not_lt.mp hearly) hF

/-- A pre-freeze voter block reaches the proposal frame under the proposer's `F` guard. -/
theorem reset_frozen_frame
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} (hpH : p ∈ H) (hy : y ∈ H) {i j s : Nat}
    {ellp elly : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hci : tr.projAC.CallAt p i ellp) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hcy : SA.CastAt tr.projAC y j elly e)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ elly.frame.tree)
    (hst : e.readPoint.blockStamp B.root < SA.ETime.of (SA.freeze sp (s + 1)))
    (hF : Anc (tr.HonestBlocks H) ellp.frame.F B) : B ∈ ellp.frame.tree := by
  have hr := (healthy_base_of_reset_catch hp hc).run.localRun
  rw [SA.readPoint_blockStamp_eq hr hy hcy] at hst
  rcases stamp_origin hr hy j elly hcy.1 B hB with hgen | ⟨q, -, ellq, hcq, hBq, hstamp⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hpH i ellp hci
    obtain rfl : B = G := hr.coherent.1 ((SA.frameIn_of_callAt hr hy hcy.1).2 hB)
      hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
    · exact he ▸ (SA.frameIn_of_callAt hr hpH hci).1.rooted.1
    · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
  · rw [hstamp] at hst
    have ht : tr.time q < SA.freeze sp (s + 1) :=
      WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst)
    apply reset_frame_relay hp hc hy hpH hcq hci hBq hg ?_ hF
    rw [hti]
    simp only [SA.freeze, SA.SAParams.ts] at ht ⊢
    push_cast at ht ⊢
    linarith only [ht]

/-- Guarded incidence gives view agreement on common held targets. Proposal heldness at the
voter remains explicit; this lemma does not supply viable-tree membership. -/
theorem reset_views_agree
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k (s + 1) P)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hPy : P ∈ elly.frame.tree) (hg : SA.gbar g ≤ sp.ts s)
    (hgi : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : SA.gbar g + 2 * sp.Δ ≤ tr.time j) :
    SA.equivocators (SA.View.ofLists pay).votes =
        SA.equivocators (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      SA.voters (SA.View.ofLists pay).votes =
        SA.voters (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      ∀ X ∈ ellp.frame.tree, X ∈ elly.frame.tree →
        SA.supporters ellp.frame (SA.View.ofLists pay) s X =
          SA.supporters elly.frame (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s X := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF (sp.ts s) (sp.ts (s + 1 : Nat)) hp.run.toLocalRun
    (syncRun_of_gst hp.healthy.1 ((SA.le_gbar g).trans hg))
  apply SA.view_agree hac hP.1 hy hP.2.1 ⟨hci, hcall, d, hd⟩ hti hcy
    ⟨P, hPy, hP.2.2.2.2.1, hpay⟩ hsync
  · intro B hB _ hstamp hF
    exact reset_frozen_frame hp hc hP.1 hy hci hti hcy hgi hB hstamp hF
  · intro v hv B hB hBr hF
    exact reset_support_frame hp hc hP hci hd hti hpay hy hcy hes hgj hv hB hBr hF

/-- Finite payload support uses early cast readiness or guarded deadline relay. -/
theorem ResetPremisesUpTo.reset_support_frame {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer (s + 1)) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = s + 1)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1) (hjb : tr.time j ≤ b)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    {v : SA.Vote sp.n} (hv : v ∈ pay.2) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ ellp.frame.tree) (hBr : B.root = v.head)
    (hF : Anc (tr.HonestBlocks H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hr := (healthy_base_of_reset_catch_before hp hc).run.localRun
  by_cases hearly : tr.time j < sp.ts (s + 1 : Nat) + sp.Δ
  · obtain ⟨Q, hQ, hQs, hsup⟩ := SA.cast_ready hr hy hcy (by rw [hes]; exact hearly)
    rw [hes] at hQs hsup
    obtain rfl := hp.reset_proposal_frame_unique hpH hdesignated hactual hPs
      (by omega) hy hcy.1 hQ hQs
    have hslot : sp.slot (tr.time i) = s + 1 := by
      rw [hti]; exact SA.slot_of_mem sp _ le_rfl ((SA.ts_lt_iff sp).mpr (by omega))
    have hpay' : pay = SA.voteViewList (tr.projAC.state p i) ellp.frame (s : Int) ⊤ := by
      unfold SA.acProposal at hd
      split_ifs at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      rw [← hd.2, hslot]
      congr 1
      push_cast
      ring
    have hvs : v.slot + 1 = s + 1 := by
      rw [hpay'] at hv
      simp only [SA.voteViewList, SA.SAState.poolAt, Int.toNat_natCast, List.filter_filter,
        List.mem_filter, List.mem_ite_nil_left, not_lt, Nat.cast_nonneg, true_and,
        Bool.and_eq_true, decide_eq_true_eq] at hv
      rw [SA.state_pool_slot sp hr hpH i s v hv.1]
    obtain ⟨B', hB', hBr', _⟩ := hsup v (by rw [SA.blockSupport, hpay]; exact hv) hvs
    rwa [hr.coherent.1 ((SA.frameIn_of_callAt hr hpH hci).2 hB)
      ((SA.frameIn_of_callAt hr hy hcy.1).2 hB') (hBr.trans hBr'.symm)]
  · exact hp.reset_frame_relay hc hpH hy hci hcy.1 hB hjb hg hjoin
      (by rw [hti]; exact not_lt.mp hearly) hF

/-- A bounded pre-freeze competitor reaches the proposal under its finalized guard. -/
theorem ResetPremisesUpTo.reset_frozen_frame {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} (hpH : p ∈ H) (hy : y ∈ H) {i j s : Nat}
    {ellp elly : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hci : tr.projAC.CallAt p i ellp) (hti : tr.time i = sp.ts (s + 1 : Nat))
    (hcy : SA.CastAt tr.projAC y j elly e) (hib : tr.time i ≤ b)
    (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ elly.frame.tree)
    (hst : e.readPoint.blockStamp B.root < SA.ETime.of (SA.freeze sp (s + 1)))
    (hF : Anc (tr.HonestBlocks H) ellp.frame.F B) : B ∈ ellp.frame.tree := by
  have hr := (healthy_base_of_reset_catch_before hp hc).run.localRun
  rw [SA.readPoint_blockStamp_eq hr hy hcy] at hst
  rcases stamp_origin hr hy j elly hcy.1 B hB with hgen | ⟨q, _, ellq, hcq, hBq, hstamp⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hpH i ellp hci
    obtain rfl : B = G := hr.coherent.1 ((SA.frameIn_of_callAt hr hy hcy.1).2 hB)
      hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
    · exact he ▸ (SA.frameIn_of_callAt hr hpH hci).1.rooted.1
    · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
  · rw [hstamp] at hst
    have ht : tr.time q < SA.freeze sp (s + 1) :=
      WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst)
    apply hp.reset_frame_relay hc hy hpH hcq hci hBq hib hg hjoin ?_ hF
    rw [hti]
    simp only [SA.freeze, SA.SAParams.ts] at ht ⊢
    push_cast at ht ⊢
    linarith only [ht]

/-- Finite operational proposal and voter views agree on common held targets. -/
theorem ResetPremisesUpTo.reset_views_agree {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H) (hdesignated : p = proposer (s + 1)) (hactual : tr.ProposesAt p k P)
    (hPs : P.slot = s + 1)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hy : y ∈ H) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b)
    (hPy : P ∈ elly.frame.tree) (hg : SA.gbar g ≤ sp.ts s)
    (hgi : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoi : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    (hjoj : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j) :
    SA.equivocators (SA.View.ofLists pay).votes =
        SA.equivocators (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      SA.voters (SA.View.ofLists pay).votes =
        SA.voters (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      ∀ X ∈ ellp.frame.tree, X ∈ elly.frame.tree →
        SA.supporters ellp.frame (SA.View.ofLists pay) s X =
          SA.supporters elly.frame (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s X := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hsync := hp.sync.syncAC (hi := sp.ts (s + 1 : Nat)) hp.run ((SA.le_gbar g).trans hg)
  apply SA.view_agree hac hpH hy hdesignated ⟨hci, hcall, d, hd⟩ hti hcy
    ⟨P, hPy, hPs, hpay⟩ hsync
  · intro B hB _ hstamp hF
    exact hp.reset_frozen_frame hc hpH hy hci hti hcy hib hgi hjoi hB hstamp hF
  · intro v hv B hB hBr hF
    exact hp.reset_support_frame hc hpH hdesignated hactual hPs hci hd hti hpay hy hcy hes
      hjb hgj hjoj hv hB hBr hF

end Consensus.Goldilocks.Healing

end

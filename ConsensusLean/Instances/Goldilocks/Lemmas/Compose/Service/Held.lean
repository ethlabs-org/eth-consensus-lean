module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Agree
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Strict

public section

/-! # Goldilocks under `Sleepy`: the updater's finalized tip is below the honest proposal

workbench#12 §4, "`F ≤ P` through the update": at an honest node's joined update of slot `s`
(its tick at `t_s + 6Δ`), its `Σ.F` is at or below the honest proposal `P` of slot `s`.

* Every origin of a label at most `s` is below `P` (`origin_anc_proposal`: an honest slot-`s`
  vote is `P` and extends it, by S2 or as its honest supporter), so every honest slot-`(s+1)`
  vote extends `P` (`votes_succ_extend`, the later transfer for the protected block `P`).
* The honest rows the updater holds were signed before `t_s + 6Δ`, with sources below origins of
  labels at most `s + 1`: below `P`, or below an honest slot-`(s+1)` head that extends `P`; so
  every such source is compatible with `P` (`rows_compatible`), and so is `Σ.J`, genesis or the
  entry of one, and `Σ.F ⪯ Σ.J`.
* `Σ.F` is genesis, or strictly below a block `B` of the tree that finalizes it
  (`Store.F_lt_finalizer`, the FG store's strict finalization), of a slot at most `s + 1` (`B` is in
  the frame of the update, `frame_slot_le`); so `Σ.F` has a slot at most `s` and, compatible with
  `P`, is at or below `P`. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time}

/-- The honest proposal is an honest block. -/
private theorem proposal_honest (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt p k P) : P ∈ tr.HonestBlocks H := by
  have h := hrun.toLocalRun
  have hacc := proposal_accepted hrun hnc hp hP
  refine ⟨p, hp, k + 1, ?_⟩
  rw [tr.state_succ_of_call hacc,
    (Store.tree_grows _ _ _ _ (fg_reachable h hp _)).1 P _ (h.cutLaw p hp _ _ hacc).2.1]
  exact Set.mem_insert _ _

/-- **An origin of a label at most `s` is below `P`**: an honest slot-`s` vote, which is `P`,
extends it (S2 for a label below `s`; its honest supporter for the label `s`). -/
private theorem origin_anc_proposal (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat} (hC : Origin tr H C j) (hj : j ≤ s) :
    Anc (tr.HonestBlocks H) C P := by
  have hinv := sleepy_invariant hrun hnc hsl
  have hU := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun.coherent
  have hall := honest_votes_eq_proposal hrun hnc hsl hp hP hPs hpj
  have hPU := proposal_honest hrun hnc hp hP
  rcases hj.lt_or_eq with hlt | rfl
  · obtain ⟨x, hx, k', e, hv, hes⟩ := honest_vote_exists hrun hnc hsl s
    obtain ⟨Hd, hHd, hHdr, hCH⟩ := hinv.vote_extends C j hC x hx k' e hv (by omega)
    rwa [hU.1 hHd hPU (hHdr.trans (hall x hx k' e hv hes))] at hCH
  · obtain ⟨x, hx, k', e, hv, hes, Hd, hHd, hHdr, hCH⟩ := honest_supporter hrun hnc hsl hC
    rwa [hU.1 hHd hPU (hHdr.trans (hall x hx k' e hv hes))] at hCH

/-- **Every honest slot-`(s+1)` vote extends `P`** (the later transfer for the protected block `P`,
by induction on the vote's cut). -/
private theorem votes_succ_extend (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) :
    ∀ x ∈ H, ∀ j e, SA.VoteAt tr.projAC x j e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg P := by
  have hinv := sleepy_invariant hrun hnc hsl
  have hall := honest_votes_eq_proposal hrun hnc hsl hp hP hPs hpj
  have hPU := proposal_honest hrun hnc hp hP
  have hPb : OriginsBelow tr H (s + 1) := originsBelow_iff.2
    fun C j C' j' _ _ hC hC' => hinv.origins_compatible C j C' j' hC hC'
  intro x hx j
  induction j using Nat.strong_induction_on generalizing x with
  | _ j ih =>
    intro e ⟨ℓ, hc, he⟩ hes
    exact later_transfer_step hrun hnc hsl hPb hx ⟨hc, he⟩ hes hPU
      (fun C j hC hj => Or.inr (origin_anc_proposal hrun hnc hsl hp hP hPs hpj hC hj))
      (fun x hx k e' hv hs => ⟨P, hPU, (hall x hx k e' hv hs).symm, .refl⟩)
      (fun z hz j' hj' e' hv hs => ih j' hj' z hz e' hv hs)

/-- **The rows the updater holds have sources compatible with `P`**: signed before `t_s + 6Δ`,
with a source below an origin before the signing, of a label at most `s + 1`. -/
private theorem rows_compatible (hrun : GoldilocksRun dg H tr) (hnc : NoCollRun dg tr)
    (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ : Nat} (ht : tr.time k₀ = sp.ts s + 6 * sp.Δ) :
    HonestRowsSourced tr H (fun D => Compatible (tr.HonestBlocks H) D P) y k₀ := by
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hPU := proposal_honest hrun hnc hp hP
  have hsl₀ : sp.slot (tr.time k₀) = s + 1 := by
    have h6 : sp.ts s + 6 * sp.Δ = sp.ts ((s + 1 : Nat) : Int) + 2 * sp.Δ :=
      (SA.slot_arithmetic sp s).2.2
    rw [ht, h6]
    simpa using (SA.slot_arithmetic sp (s + 1)).1 2 (by omega)
  refine honestRowsSourced_iff.2 fun X hX a ha hav => ?_
  obtain ⟨m, hm, -, ks, hksm, hsg⟩ := honest_row_signed_before hrun hnc hy hX ha hav
  obtain ⟨D, -, hDs, C, l, hCo, hDC⟩ := attestation_source hrun hnc hav hsg
  refine ⟨D, ?_, hDs⟩
  obtain ⟨x, hx, k', hk', CV, hR | hO⟩ := originBefore_iff.1 hCo
  · -- a regular origin, written at `t_l + 6Δ ≤ t_s + 6Δ`
    have hk'₀ : k' < k₀ := by omega
    have htime : tr.time k' ≤ tr.time k₀ := hrun.time_mono hk'₀.le
    obtain ⟨ℓ', ⟨-, -, htk', -⟩, -⟩ := id hR
    have htk'' : tr.time k' = sp.ts l + 6 * sp.Δ := htk'
    have hl : l ≤ s := by
      have : sp.ts (l : Int) ≤ sp.ts (s : Int) := by linarith
      exact_mod_cast (SA.ts_le_iff sp).1 this
    exact Or.inl (hDC.trans
      (origin_anc_proposal hrun hnc hsl hp hP hPs hpj (Origin.of_result hx hR) hl))
  · -- an optimistic origin, of the slot of its time
    have hk'₀ : k' < k₀ := by omega
    have hOo := Origin.of_optimistic hx hO
    obtain ⟨-, -, -, hslk, -⟩ := hO
    have hl : l ≤ s + 1 := by
      have := SA.slot_mono sp (hr.time_nonneg k') (hrun.time_mono hk'₀.le)
      rw [← hslk]
      change sp.slot (tr.time k') ≤ s + 1
      rw [← hsl₀]
      exact this
    rcases Nat.lt_or_ge l (s + 1) with hls | hls
    · exact Or.inl (hDC.trans
        (origin_anc_proposal hrun hnc hsl hp hP hPs hpj hOo (by omega)))
    obtain rfl : l = s + 1 := le_antisymm hl hls
    obtain ⟨z, hz, j, e, hv, hes, Hd, hHd, hHdr, hCH⟩ := honest_supporter hrun hnc hsl hOo
    obtain ⟨Hd', hHd', hHd'r, hPH⟩ :=
      votes_succ_extend hrun hnc hsl hp hP hPs hpj z hz j e hv hes
    obtain rfl : Hd' = Hd := hU.1 hHd' hHd (hHd'r.trans hHdr.symm)
    exact Anc.total hU (hDC.trans hCH) hPH

/-- **The updater's `Σ.F` is at or below `P`** (workbench#12 §4). -/
theorem updater_F_anc_proposal (hrun : GoldilocksRun dg H tr)
    (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF) {p : Fin sp.n} (hp : p ∈ H) {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hP : tr.ProposesAt p k P)
    (hPs : P.slot = s) (hpj : SA.joined sp (tr.state p k).ac (tr.time k)) {y : Fin sp.n}
    (hy : y ∈ H) {k₀ : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) :
    Anc (tr.HonestBlocks H) (tr.state y k₀).fg.F P := by
  have hr := (goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hPU := proposal_honest hrun hnc hp hP
  have hR := fg_reachable hrun.toLocalRun hy k₀
  obtain ⟨hFt, hJt, hFJ, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hcoh := (Store.accepted_tree _ _ _ _ hR).2.1
  have hsU : (tr.state y k₀).fg.tree ⊆ tr.HonestBlocks H := fun Z hZ => ⟨y, hy, k₀, hZ⟩
  have ht : tr.time k₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hsrc := rows_compatible hrun hnc hsl hp hP hPs hpj hy ht
  set R : SA.Blk sp.n (List (FG.Att sp.n)) → Prop := fun D => Compatible (tr.HonestBlocks H) D P
  have hRc : ∀ A B, Anc (tr.HonestBlocks H) A B → R B → R A := by
    rintro A B hAB (hBP | hPB)
    · exact Or.inl (hAB.trans hBP)
    · exact Anc.total hU hAB hPB
  -- `Σ.J`, hence `Σ.F`, is compatible with `P`
  have hJ : (tr.state y k₀).fg.J.root = sp.genesisRoot ∨ R (tr.state y k₀).fg.J := by
    by_cases h0 : (tr.state y k₀).fg.hj = 0
    · left
      rw [justified_genesis hrun h0 hy]
      rfl
    obtain ⟨-, -, D, hD, hDs⟩ := justified_honest_source hrun hnc hsl hy hsrc (by omega)
    obtain ⟨x, hx, k', -, -, hJD, -, -⟩ := honest_source_entry hrun hnc hDs ⟨y, hy, k₀, hJt⟩ rfl
    exact Or.inr (hRc _ _ (Anc.mono (T := tr.HonestBlocks H) (fun Z hZ => ⟨x, hx, k', hZ⟩) hJD) hD)
  have hJR : R (tr.state y k₀).fg.J := by
    rcases hJ with hg | h
    · exact Or.inl (honest_genesis_root_anc hrun hU (hsU hJt) hg hPU)
    · exact h
  have hFR : R (tr.state y k₀).fg.F := hRc _ _ (Anc.mono hsU hFJ) hJR
  -- `Σ.F` is genesis, or of a slot at most `s`
  by_cases hg : (tr.state y k₀).fg.F =
      sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload
  · exact honest_genesis_root_anc hrun hU (hsU hFt) (by rw [hg]; rfl) hPU
  obtain ⟨B, hBt, -, hFB, hne⟩ := Store.F_lt_finalizer hR hg
  have hfr : ℓ.frame = Node.frame (tr.state y k₀) := by
    obtain ⟨hn, hl⟩ := hu.1
    obtain ⟨c, hc, hcl⟩ := Option.bind_eq_some_iff.1 hl
    obtain rfl : c = .ac ℓ := by
      cases c with
      | ac ℓ' => cases hcl; rfl
      | fg _ => cases hcl
    exact (hrun.cutLaw y hy k₀ (.ac ℓ) ⟨hn, hc⟩).1
  have hBf : B ∈ ℓ.frame.tree := by rw [hfr]; exact ⟨hBt, hFB⟩
  have hsl₀ : sp.slot (tr.projAC.time k₀) = s + 1 := by
    have h6 : sp.ts s + 6 * sp.Δ = sp.ts ((s + 1 : Nat) : Int) + 2 * sp.Δ :=
      (SA.slot_arithmetic sp s).2.2
    change sp.slot (tr.time k₀) = s + 1
    rw [ht, h6]
    simpa using (SA.slot_arithmetic sp (s + 1)).1 2 (by omega)
  have hBs : B.slot ≤ s + 1 := hsl₀ ▸ SA.frame_slot_le sp hr hy hu.1 B hBf
  have hFs : (tr.state y k₀).fg.F.slot < B.slot := (Anc.slot_le hcoh hFB).2 hne
  rcases hFR with h | hPF
  · exact h
  by_cases hPFe : P = (tr.state y k₀).fg.F
  · exact hPFe ▸ .refl
  have := (Anc.slot_le hU hPF).2 hPFe
  omega

end Consensus.Goldilocks.Compose

end

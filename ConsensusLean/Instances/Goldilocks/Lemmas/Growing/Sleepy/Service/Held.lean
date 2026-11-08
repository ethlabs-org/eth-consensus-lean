module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Agree
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.TransferLater
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Held
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: the updater's finalized tip is below `P`

The growing-fault form of `Compose/Service/Held`. At the update of slot `s` (at `t_s + 6Δ`) of a
node honest then, its `Σ.F` is at or below the proposal `P` of slot `s` by a proposer honest at
`t_s + Δ`:

* every origin of a label at most `s` is below `P` (an honest slot-`s` vote is `P`, and extends the
  origin by S2 or as its honest supporter), so every honest slot-`(s+1)` vote extends `P`
  (`later_transfer_step_at`);
* the honest attestations the updater holds are classified at the update's cut: the static row and
  source facts on the prefix through the update give each a source below an origin before its
  signing, of a label at most `s + 1`, so compatible with `P` (inside the blocks held while
  honest);
* `Σ.J`, hence `Σ.F`, is compatible with `P` (the static justification geometry on the prefix,
  with `2 f_d < n` at the update), and `Σ.F` has a slot at most `s`. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- The proposal of a proposer honest at its proposal is a block held while honest. -/
theorem proposal_honest_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {p : Fin sp.n} {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} (hp : p ∈ H (tr.time k))
    (hP : tr.ProposesAt p k P) : P ∈ tr.HonestBlocksAt H := by
  have hd := hrun.time_nonneg k
  have hr := hrun.upTo hd
  have hP' : (tr.upTo (tr.time k)).ProposesAt p k P :=
    ⟨(RunTrace.upTo_ownBlockAt tr).2 ⟨le_rfl, hP.1⟩, hP.2.1, hP.2.2⟩
  have hacc := Compose.proposal_accepted hr (hnc.upTo _) hp hP'
  refine upTo_subset hrun hd ⟨p, hp, k + 1, ?_⟩
  rw [Trace.state_succ_of_call _ hacc,
    (Store.tree_grows _ _ _ _ (Compose.fg_reachable hr.toLocalRun hp _)).1 P _
      (hr.cutLaw p hp _ _ hacc).2.1]
  exact Set.mem_insert _ _

/-- Every origin within `b` of a label at most `s` is below `P`, when every honest slot-`s` vote
at a time `≤ b` is `P`. -/
private theorem origin_anc_proposal_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hPU : P ∈ tr.HonestBlocksAt H)
    (hsb : sp.ts s + sp.Δ ≤ b)
    (hall : ∀ x j e, HVoteAt tr H x j e → e.msg.slot = s → tr.time j ≤ b → e.msg.head = P.root)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {j : Nat}
    (hC : OriginWithin tr H C j b) (hj : j ≤ s) : Anc (tr.HonestBlocksAt H) C P := by
  have hU := honestBlocksAt_coherent hrun hnc
  rcases hj.lt_or_eq with hlt | rfl
  · have hcount := hB.slot s (sp.ts s + sp.Δ) (Nat.zero_le _) le_rfl hsb
      (by linarith [sp.toParams.hΔ])
    obtain ⟨x, hx, hw, hjx⟩ := Set.nonempty_of_ncard_ne_zero (Nat.zero_lt_of_lt hcount).ne'
    obtain ⟨k, e, hv, hes, hkt⟩ := vote_of_awake_joined_at hrun hnc hx hw hjx
    have hkb : tr.time k ≤ b := hkt.trans hsb
    obtain ⟨Hd, hHd, hHdr, hCH⟩ := hinv.vote_extends C j hC x k e hv hkb (by omega)
    rwa [hU.1 hHd hPU (hHdr.trans (hall x k e hv hes hkb))] at hCH
  · obtain ⟨x, k, e, hv, hkb, hes, Hd, hHd, hHdr, hCH⟩ := honest_supporter_at hrun hnc hsync hB hC
    rwa [hU.1 hHd hPU (hHdr.trans (hall x k e hv hes hkb))] at hCH

/-- Every honest slot-`(s+1)` vote at a time `≤ b` extends `P` (the later transfer for the
protected block `P`). -/
private theorem votes_succ_extend_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hPU : P ∈ tr.HonestBlocksAt H)
    (hsb : sp.ts s + sp.Δ ≤ b)
    (hall : ∀ x j e, HVoteAt tr H x j e → e.msg.slot = s → e.msg.head = P.root) :
    ∀ x j e, HVoteAt tr H x j e → e.msg.slot = s + 1 → tr.time j ≤ b →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  have hPb : OriginsBelowUpTo tr H (s + 1) b := originsBelowUpTo_iff.2
    fun C j C' j' _ _ hC hC' => hinv.origins_compatible C j C' j' hC hC'
  intro x j
  induction j using Nat.strong_induction_on generalizing x with
  | _ j ih =>
    intro e hv hes hjb
    obtain ⟨hx, ℓ, hc, he⟩ := hVoteAt_iff.1 hv
    exact later_transfer_step_at hrun hnc hb0 hsync hB hPb hx ⟨hc, he⟩ hes hjb hPU
      (fun C j hC hj => Or.inr (origin_anc_proposal_at hrun hnc hsync hB hinv hPU hsb
        (fun x k e hv hs _ => hall x k e hv hs) hC hj))
      (fun x k e' hv hs => ⟨P, hPU, (hall x k e' hv hs).symm, .refl⟩)
      (fun z j' hj' hz e' hv' hs' => ih j' hj' z e' (hVoteAt_iff.2 ⟨hz, hv'⟩) hs'
        ((hrun.time_mono hj'.le).trans hjb))

/-- **The attestations the updater holds have sources compatible with `P`**, classified at the
update's cut `d = t_s + 6Δ`: on the prefix through `d`, each such attestation was signed before the
update by a validator honest then, with a source below an origin before the signing, of a label at
most `s + 1`. -/
private theorem rows_compatible_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hPU : P ∈ tr.HonestBlocksAt H)
    (hall : ∀ x j e, HVoteAt tr H x j e → e.msg.slot = s → e.msg.head = P.root)
    {y : Fin sp.n} {k₀ : Nat} (hy : y ∈ H (tr.time k₀)) (ht : tr.time k₀ = sp.ts s + 6 * sp.Δ)
    (hb : tr.time k₀ ≤ b) :
    HonestRowsSourced (tr.upTo (tr.time k₀)) (H (tr.time k₀))
      (fun D => Compatible (tr.HonestBlocksAt H) D P) y k₀ := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hsb : sp.ts s + sp.Δ ≤ b := by linarith
  have hd := hrun.time_nonneg k₀
  have hr := hrun.upTo hd
  have hnc' := hnc.upTo (tr.time k₀)
  have hsub := upTo_subset hrun hd
  have hsl₀ : sp.slot (tr.time k₀) = s + 1 := by
    have h6 : sp.ts s + 6 * sp.Δ = sp.ts ((s + 1 : Nat) : Int) + 2 * sp.Δ :=
      (SA.slot_arithmetic sp s).2.2
    rw [ht, h6]
    simpa using (SA.slot_arithmetic sp (s + 1)).1 2 (by omega)
  refine honestRowsSourced_iff.2 fun X hX a ha hav => ?_
  obtain ⟨m, hm, -, ks, hksm, hsg⟩ := Compose.honest_row_signed_before hr hnc' hy hX ha hav
  obtain ⟨D, -, hDs, C, l, hCo, hDC⟩ := Compose.attestation_source hr hnc' hav hsg
  refine ⟨D, ?_, hDs⟩
  have hDC' := hDC.mono hsub
  have hks : ∀ k < ks, tr.time k ≤ b := fun k hk =>
    (hrun.time_mono (show k ≤ k₀ by omega)).trans hb
  have hCb : OriginWithin tr H C l b := originWithin_of_upTo hrun (hCo.within hks)
  obtain ⟨x, -, k', hk', CV, hR | hO⟩ := Compose.originBefore_iff.1 hCo
  · -- a regular origin, written at `t_l + 6Δ ≤ t_s + 6Δ`
    obtain ⟨ℓ', ⟨-, -, htk', -⟩, -⟩ := id hR
    have htime : tr.time k' ≤ tr.time k₀ := hrun.time_mono (show k' ≤ k₀ by omega)
    have htk'' : tr.time k' = sp.ts l + 6 * sp.Δ := htk'
    have hl : l ≤ s := by
      have : sp.ts (l : Int) ≤ sp.ts (s : Int) := by linarith
      exact_mod_cast (SA.ts_le_iff sp).1 this
    exact Or.inl (hDC'.trans (origin_anc_proposal_at hrun hnc hsync hB hinv hPU hsb
      (fun x k e hv hs _ => hall x k e hv hs) hCb hl))
  · -- an optimistic origin, of the slot of its time
    obtain ⟨-, -, -, hslk, -⟩ := hO
    have hl : l ≤ s + 1 := by
      have := SA.slot_mono sp (hrun.time_nonneg k') (hrun.time_mono (show k' ≤ k₀ by omega))
      rw [← hslk]
      change sp.slot (tr.time k') ≤ s + 1
      rw [← hsl₀]
      exact this
    rcases Nat.lt_or_ge l (s + 1) with hls | hls
    · exact Or.inl (hDC'.trans (origin_anc_proposal_at hrun hnc hsync hB hinv hPU hsb
        (fun x k e hv hs _ => hall x k e hv hs) hCb (by omega)))
    obtain rfl : l = s + 1 := le_antisymm hl hls
    obtain ⟨z, j, e, hv, hjb, hes, Hd, hHd, hHdr, hCH⟩ := honest_supporter_at hrun hnc hsync hB hCb
    obtain ⟨Hd', hHd', hHd'r, hPH⟩ :=
      votes_succ_extend_at hrun hnc hb0 hsync hB hinv hPU hsb hall z j e hv hes hjb
    obtain rfl : Hd' = Hd := hU.1 hHd' hHd (hHd'r.trans hHdr.symm)
    exact Anc.total hU (hDC'.trans hCH) hPH

/-- **The updater's `Σ.F` is at or below `P`**, from rows sourced compatibly with `P`: the static
justification geometry on the prefix through the update, with `2 f_d < n` at the update. -/
private theorem updater_F_anc_of_rows_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hPU : P ∈ tr.HonestBlocksAt H) (hPs : P.slot = s) {y : Fin sp.n} {k₀ : Nat}
    (hy : y ∈ H (tr.time k₀)) (hf : 2 * (H (tr.time k₀))ᶜ.ncard < sp.n)
    {ℓ : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y k₀ s ℓ)
    (hsrc : HonestRowsSourced (tr.upTo (tr.time k₀)) (H (tr.time k₀))
      (fun D => Compatible (tr.HonestBlocksAt H) D P) y k₀) :
    Anc (tr.HonestBlocksAt H) (tr.state y k₀).fg.F P := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hd := hrun.time_nonneg k₀
  have hr := hrun.upTo hd
  have hnc' := hnc.upTo (tr.time k₀)
  have hsub := upTo_subset hrun hd
  have hst : (tr.upTo (tr.time k₀)).state y k₀ = tr.state y k₀ :=
    Trace.upTo_state tr y fun k hk => hrun.time_mono hk.le
  have hR := Compose.fg_reachable hr.toLocalRun hy k₀
  rw [hst] at hR
  obtain ⟨hFt, hJt, hFJ, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hcoh := (Store.accepted_tree _ _ _ _ hR).2.1
  have hsU : (tr.state y k₀).fg.tree ⊆ tr.HonestBlocksAt H := fun Z hZ =>
    mem_honestBlocksAt hrun hy hZ
  have ht : tr.time k₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  set R : SA.Blk sp.n (List (FG.Att sp.n)) → Prop := fun D => Compatible (tr.HonestBlocksAt H) D P
  have hRc : ∀ A B, Anc (tr.HonestBlocksAt H) A B → R B → R A := by
    rintro A B hAB (hBP | hPB)
    · exact Or.inl (hAB.trans hBP)
    · exact Anc.total hU hAB hPB
  -- `Σ.J`, hence `Σ.F`, is compatible with `P`
  have hJ : (tr.state y k₀).fg.J.root = sp.genesisRoot ∨ R (tr.state y k₀).fg.J := by
    by_cases h0 : (tr.state y k₀).fg.hj = 0
    · left
      rw [← hst] at h0 ⊢
      rw [Compose.justified_genesis hr h0 hy]
      rfl
    have hj1 : 1 ≤ ((tr.upTo (tr.time k₀)).state y k₀).fg.hj := by rw [hst]; omega
    obtain ⟨-, -, D, hD, hDs⟩ := Compose.justified_honest_source_before hr hnc' hf hy hsrc hj1
    have hJt' : ((tr.upTo (tr.time k₀)).state y k₀).fg.J ∈
        (tr.upTo (tr.time k₀)).HonestBlocks (H (tr.time k₀)) := ⟨y, hy, k₀, by rw [hst]; exact hJt⟩
    obtain ⟨x, hx, k', -, -, hJD, -, -⟩ := Compose.honest_source_entry hr hnc' hDs hJt' rfl
    rw [hst] at hJD
    exact Or.inr (hRc _ _ (Anc.mono (fun Z hZ => hsub ⟨x, hx, k', hZ⟩) hJD) hD)
  have hJR : R (tr.state y k₀).fg.J := by
    rcases hJ with hg | h
    · exact Or.inl (honestAt_genesis_root_anc hrun hU (hsU hJt) hg hPU)
    · exact h
  have hFR : R (tr.state y k₀).fg.F := hRc _ _ (Anc.mono hsU hFJ) hJR
  -- `Σ.F` is genesis, or of a slot at most `s`
  by_cases hg : (tr.state y k₀).fg.F =
      sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload
  · exact honestAt_genesis_root_anc hrun hU (hsU hFt) (by rw [hg]; rfl) hPU
  obtain ⟨B, hBt, -, hFB, hne⟩ := Store.F_lt_finalizer hR hg
  have hfr : ℓ.frame = Node.frame (tr.state y k₀) := frame_of_projAC_at hrun hy hu.1
  have hBf : B ∈ ℓ.frame.tree := by rw [hfr]; exact ⟨hBt, hFB⟩
  have hsl₀ : sp.slot (tr.time k₀) = s + 1 := by
    have h6 : sp.ts s + 6 * sp.Δ = sp.ts ((s + 1 : Nat) : Int) + 2 * sp.Δ :=
      (SA.slot_arithmetic sp s).2.2
    rw [ht, h6]
    simpa using (SA.slot_arithmetic sp (s + 1)).1 2 (by omega)
  have hBs : B.slot ≤ s + 1 := hsl₀ ▸ frame_slot_le_at hrun hnc hy hu.1 B hBf
  have hFs : (tr.state y k₀).fg.F.slot < B.slot := (Anc.slot_le hcoh hFB).2 hne
  rcases hFR with h | hPF
  · exact h
  by_cases hPFe : P = (tr.state y k₀).fg.F
  · exact hPFe ▸ .refl
  have := (Anc.slot_le hU hPF).2 hPFe
  omega

/-- **By the update every honest slot-`s` vote is `P`**, for a proposer honest at `t_s + Δ`,
through `b ≥ t_s + 6Δ` (a slot-`s` vote is cast by `t_s + Δ`). -/
theorem honest_votes_eq_proposal_at_update_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) (hsb : sp.ts s + 6 * sp.Δ ≤ b) :
    ∀ x j e, HVoteAt tr H x j e → e.msg.slot = s → e.msg.head = P.root := by
  have hΔ := sp.toParams.hΔ
  intro x j e hv hes
  apply honest_votes_eq_proposal_at hrun hnc hsync hB hinv hp hP hPs (by linarith) x j e hv hes
  obtain ⟨hx, ℓ, hc⟩ := hVoteAt_iff.1 hv
  have h := (cast_head_fcRoot_at hrun hnc hx hc).2
  rw [hes] at h
  linarith

/-- **The updater's `Σ.F` is at or below `P`** at the update of slot `s` of a node honest then,
for the proposal `P` of slot `s` by a proposer honest at `t_s + Δ`, through `b`. -/
theorem updater_F_anc_proposal_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {y : Fin sp.n} {k₀ : Nat}
    (hy : y ∈ H (tr.time k₀)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (hb : tr.time k₀ ≤ b) :
    Anc (tr.HonestBlocksAt H) (tr.state y k₀).fg.F P := by
  have hΔ := sp.toParams.hΔ
  have hk : tr.time k = sp.ts s := by rw [hP.2.2, sp.slotTime_eq, hPs]; rfl
  have hPU := proposal_honest_at hrun hnc (hrun.antitone (by rw [hk]; linarith) hp) hP
  have ht : tr.time k₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hall := honest_votes_eq_proposal_at_update_at hrun hnc hsync hB hinv hp hP hPs (ht ▸ hb)
  exact updater_F_anc_of_rows_at hrun hnc hPU hPs hy
    (hB.two (tr.time k₀) (hrun.time_nonneg k₀) hb) hu
    (rows_compatible_at hrun hnc hb0 hsync hB hinv hPU hall hy ht hb)

end Consensus.Goldilocks.Compose.Growing

end

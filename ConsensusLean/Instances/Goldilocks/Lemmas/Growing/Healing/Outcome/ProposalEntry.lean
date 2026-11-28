module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Floor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LeftEntry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The high left entries of a proposer under growing faults

A high left entry of the store of a proposer honest at its own cut has a crossing attestation
whose high origin was written before the proposal slot, or is covered
(`proposal_entry_below_old_or_covered_at`, `proposal_entry_below_old_or_healed_at`): the
crossing supplier of the proposer's fork-choice root and height floor
(`Healing/Outcome/RootFloor`). -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

/-- A high proposer entry is below a pre-slot high origin, or covered up to the proposal slot.
The bounded cover retains the member's healed floors and its label for later S2 votes. -/
theorem proposal_entry_below_old_or_covered_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts u)
    (hib : tr.time i ≤ b) {E C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hE : E ∈ (tr.state p i).fg.tree) (hET : ((tr.state p i).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state p i).fg.σ E.root).h) (hEC : (tr.state p i).fg.Anc E C)
    (hlt : ((tr.state p i).fg.σ E.root).h < ((tr.state p i).fg.σ C.root).h) :
    (∃ O, (∃ v r l, HighOrigin tr H g v r l O ∧ tr.time r < sp.ts u ∧ tr.time r ≤ b) ∧
      Anc (tr.HonestBlocksAt H) E O) ∨ CoveredUpTo tr H g a b u E := by
  obtain ⟨W, hW, att, ha, v, d, hv, hdi, hs, hT, hsource⟩ :=
    hp.left_entry_origin_or_covered_at (hp.run.time_nonneg i)
      (fun _ hq => hp.run.time_mono hq.le) hpH hib hE hET hEh hEC hlt
  rcases hsource with ⟨r, hrd, l, O, ho, hEO⟩ | ⟨_, hcov⟩
  · have hlu := ProposalSources.origin_label_lt_at_proposal_at hp hpH hci hcall hti hib
      (by omega : r < i) ho
    obtain ⟨_, _, _, _, hfl, _⟩ := ho.2.2.1
    have hrti : tr.time r ≤ tr.time i := hp.run.time_mono (by omega)
    have hrt := Outcome.fastLock_time_lt_at hp.run hfl hlu (by
      rw [hti] at hrti
      linarith [sp.toParams.hΔ])
    exact Or.inl ⟨O, ⟨v, r, l, ho, hrt, hrti.trans hib⟩, hEO⟩
  · have hslot : sp.slot (tr.time i) = u := by
      rw [hti]
      exact AC.slot_of_mem sp u le_rfl ((AC.ts_lt_iff sp).2 (by push_cast; omega))
    exact Or.inr (hslot ▸ hcov)

/-- A member of the healed family at the reset's floors has its label after `c_z`: a lock or
origin member is past the drain, a high origin member is high. -/
private theorem healedOrigin_cutZ_le_ts
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hC : Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a) (healedOriginFloor sp a) C s
      b) : cutZ sp.toParams g ≤ sp.ts s := by
  have hk := sp.two_le_k
  rcases Compose.Growing.healedOrigin_iff.1 hC with ⟨hs, -⟩ | ⟨hs, -⟩ | ⟨x, i, -, ho⟩
  · exact hp.clean_window_timing_at (s := s)
      (by simp only [healedOriginFloor, healedLockFloor] at hs; omega) s (by omega)
  · exact hp.clean_window_timing_at hs s (by omega)
  · exact hp.cutZ_le_ts_of_highOrigin_at ho

/-- A lock write by a node honest at it, before an honest proposal of slot `u`, of a label after
`c_z`, has a label below `u`: a fast update or a slow lock is written at `t_l + 6Δ ≤ t_u`, and a
same-slot optimistic write is excluded by the proposal (`proposal_no_optimistic_of`). -/
private theorem lock_label_lt_at_proposal_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts u)
    (hib : tr.time i ≤ b) {v : Fin sp.n} {r l : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hri : r < i) (hv : v ∈ H (tr.time r)) (hcz : cutZ sp.toParams g ≤ sp.ts l)
    (hlock : (∃ CV, AC.FastLockAt tr.projAC v r l D CV) ∨ AC.SlowLockAt tr.projAC v r l D) :
    l < u := by
  have hrt : tr.time r ≤ sp.ts u := hti ▸ hp.run.time_mono hri.le
  have hΔ := sp.toParams.hΔ
  have hupd : ∀ ℓ, AC.UpdateAt tr.projAC v r l ℓ → l < u := fun ℓ hu => by
    have ht' : tr.time r = sp.ts l + 6 * sp.Δ := hu.2.2.1
    exact_mod_cast (AC.ts_lt_iff sp).mp (show sp.ts l < sp.ts u by linarith only [ht', hrt, hΔ])
  rcases hlock with ⟨CV, ⟨ℓ, C, hu, -⟩ | hop⟩ | ⟨ℓ, C, hu, -, -⟩
  · exact hupd ℓ hu
  · obtain ⟨-, -, -, hsl, -⟩ := id hop
    change sp.slot (tr.time r) = l at hsl
    have hts : sp.ts l ≤ tr.time r :=
      (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg r) l).mpr (by omega)
    have hle : l ≤ u := by
      exact_mod_cast (AC.ts_le_iff sp).mp (hts.trans hrt)
    have hne : l ≠ u := by
      intro he
      rw [he] at hop hts hcz
      have htime : tr.time r = tr.time i := hti.symm ▸ le_antisymm hrt hts
      have hd := hp.run.time_nonneg i
      have hf := hp.committee_cs2_at (s := u) (by have := lt_cutZ sp g; linarith)
        (hti ▸ hib) hd hib
      have hc' : (tr.upTo (tr.time i)).projAC.CallAt p i ell := by
        rw [RunTrace.upTo_projAC]
        exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hci⟩
      have hop' : AC.OptimisticLockAt (tr.upTo (tr.time i)).projAC v r u D CV := by
        rw [RunTrace.upTo_projAC]
        exact (AC.upTo_optimisticLockAt hp.run.time_mono).mpr ⟨htime.le, hop⟩
      exact Compose.proposal_no_optimistic_of (hp.run.upTo hd) (hp.noColl.upTo _)
        (by rw [RunTrace.upTo_projAC]
            exact AC.CommitteePAt.upTo hp.run.time_mono hp.run.antitone hp.committeeFacts.hP _)
        hf hpH hc' hcall hti v (htime ▸ hv) r hri D CV hop'
    omega
  · exact hupd ℓ hu

/-- **A high proposer entry is below a pre-slot high origin, or below a healed member of a label
strictly below the proposal slot, written before the proposal cut.** The member is a lock write by
the entry's signer before the signing (`signed_row_lock_member_before_at`); its label is below `u`
by its write time, or, for a same-slot optimistic write, by the proposal itself. -/
theorem proposal_entry_below_old_or_healed_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {p : Fin sp.n} {i u : Nat} (hpH : p ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal) (hti : tr.time i = sp.ts u)
    (hib : tr.time i ≤ b) {E C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hE : E ∈ (tr.state p i).fg.tree) (hET : ((tr.state p i).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state p i).fg.σ E.root).h) (hEC : (tr.state p i).fg.Anc E C)
    (hlt : ((tr.state p i).fg.σ E.root).h < ((tr.state p i).fg.σ C.root).h) :
    (∃ O, (∃ v r l, HighOrigin tr H g v r l O ∧ tr.time r < sp.ts u ∧ tr.time r ≤ b) ∧
      Anc (tr.HonestBlocksAt H) E O) ∨
    (HighSourceCover tr H g a b ∧ ∃ M s, HealedMemberBefore tr H g a b M s i ∧ s < u ∧
      Anc (tr.HonestBlocksAt H) E M) := by
  have ht := hp.run.time_nonneg i
  have hle : ∀ q < i, tr.time q ≤ tr.time i := fun _ hq => hp.run.time_mono hq.le
  obtain ⟨W, hW, att, ha, v, d, hv, hdi, hs, hT, hsource⟩ :=
    hp.left_entry_origin_or_covered_at ht hle hpH hib hE hET hEh hEC hlt
  rcases hsource with ⟨r, hrd, l, O, ho, hEO⟩ | ⟨hvz, hcov⟩
  · have hlu := ProposalSources.origin_label_lt_at_proposal_at hp hpH hci hcall hti hib
      (by omega : r < i) ho
    obtain ⟨_, _, _, _, hfl, _⟩ := ho.2.2.1
    have hrti : tr.time r ≤ tr.time i := hp.run.time_mono (by omega)
    have hrt := Outcome.fastLock_time_lt_at hp.run hfl hlu (by
      rw [hti] at hrti
      linarith [sp.toParams.hΔ])
    exact Or.inl ⟨O, ⟨v, r, l, ho, hrt, hrti.trans hib⟩, hEO⟩
  obtain ⟨hc, -⟩ := coveredUpTo_iff.1 hcov
  have hdt := hp.run.time_mono hdi.le
  have hvd := hp.run.antitone (hdt.trans (le_max_right _ _)) hvz
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  obtain ⟨E', hE', hEr, hE'h⟩ := Healing.signAt_entry (hp.run.upTo (hp.run.time_nonneg d)) hvd
    ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
  rw [RunTrace.upTo_state_of_le hp.run.time_mono le_rfl] at hE' hE'h
  have hsub : (tr.state p i).fg.tree ⊆ tr.HonestBlocksAt H := fun _ h =>
    ⟨p, i, tr.time i, ht, hle, hpH, h⟩
  have hsub' : (tr.state v d).fg.tree ⊆ tr.HonestBlocksAt H := fun _ h =>
    ⟨v, d, tr.time d, hp.run.time_nonneg d, fun _ hq => hp.run.time_mono hq.le, hvd, h⟩
  obtain rfl : E' = E := hU.1 (hsub' hE') (hsub hE) (hEr.trans hT)
  have hσ := σ_eq_honest_at hp.run hp.noColl (hp.run.time_nonneg d)
    (fun _ hq => hp.run.time_mono hq.le) hvd ht hle hpH hE' hE
  obtain ⟨E₀, hE₀, hE₀r, r, hrd, s, M, D, hM, hEM, -, hvr, hlock⟩ :=
    Outcome.signed_row_lock_member_before_at hp.run hp.noColl
      (hp.run.antitone (max_le_max le_rfl hdt) hvz) hs (by rw [← hE'h, hσ]; exact hEh)
      (hp.snapshot.imp fun _ h => h.1) hc (hdt.trans hib)
  obtain rfl : E₀ = E' := hU.1 hE₀ (hsub hE) (hE₀r.trans hT)
  exact Or.inr ⟨hc, M, s, hM.mono (by omega), lock_label_lt_at_proposal_at hp hpH hci hcall hti hib
    (by omega : r < i) hvr (healedOrigin_cutZ_le_ts hp hM.healedOrigin) hlock, hEM⟩

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

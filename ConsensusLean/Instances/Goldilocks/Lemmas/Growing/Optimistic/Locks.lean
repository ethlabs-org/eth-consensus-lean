module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Later
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.LockVeto

public section

/-! # Optimistic inclusion: no live lock conflicts with the proposal

The proposal `P` of slot `s` by a proposer honest at `t_s + Δ` is an origin of label `s` within
any horizon `b ≥ t_s + 6Δ` (`proposal_originWithin_at`): the update of slot `s` at `t_s + 6Δ` of a
node honest, awake and joined then returns it (the witness of `later_update_adopts_gt_at`). The
horizon `t_s + 6Δ` only places that witness inside the invariant's window; it is not a premise of
the optimistic inclusion statement, whose honesty premises end at `t_p + 2Δ`. At an optimistic
check point no live lock conflicts with `P` (`proposal_not_conflicts_point_at`): stored locks do
not veto an origin (`origin_not_conflicts_at`, shared with `result_not_vetoed_at`), and the read
point's locks lie below stored ones or below the call's own fast lock.

Every step is proved. -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams ReplayOrder Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **The proposal is an origin within `b`**, held while honest, for a horizon `b ≥ t_s + 6Δ`: the
update of slot `s` at `t_s + 6Δ` of a node honest, awake and joined then returns it. -/
theorem proposal_originWithin_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) (hsb : sp.ts s + 6 * sp.Δ ≤ b)
    {K : AC.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K)
    (hBK : CommitteeBoundsFrom tr H K 0 b) :
    OriginWithin tr H P s b ∧ P ∈ tr.HonestBlocksAt H := by
  have hΔ := sp.toParams.hΔ
  have hT : sp.ts (s + 1 : Nat) + 2 * sp.Δ = sp.ts s + 6 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have hf := hB.late (s + 1) (sp.ts (s + 1 : Nat) + 2 * sp.Δ) (Nat.zero_le _) le_rfl
    (by rw [hT]; exact hsb) (by linarith)
  rw [hT] at hf
  obtain ⟨x, hx, hw, hj⟩ := Set.nonempty_of_ncard_ne_zero (Nat.zero_lt_of_lt hf).ne'
  obtain ⟨kx, ℓx, hux⟩ := update_of_awake_joined_at hrun hx hw hj
  have hkx : tr.time kx = sp.ts s + 6 * sp.Δ := hux.2.2.1
  have hxk : x ∈ H (tr.time kx) := hkx ▸ hx
  obtain ⟨hC, -⟩ := adopt_result_at hrun hnc hb0 hsync hB hinv hp hP hPs hxk hux (by linarith)
    hKB hBK
  have hPt : P ∈ ℓx.frame.tree := (AC.deepest_mem hC).1.1
  refine ⟨originWithin_iff.2 ⟨x, kx, _, hxk, by linarith, Or.inl ⟨ℓx, hux, ?_, rfl⟩⟩,
    (frameIn_at hrun hnc hxk hux.1).2 hPt⟩
  rw [projAC_state_at hrun hxk]; exact hC

/-- **No live lock conflicts with the proposal at an optimistic check point** of a node honest then,
at a cut through the horizon `b ≥ t_s + 6Δ` of the proposal's origin, at a positive slot, when
the proposal is in the call's frame and the fast locks written by the call's own earlier checks
are compatible with it (`hbelow`). A receipt's point keeps the stored locks; an own vote's read
point holds locks below stored ones or below the call's own fast lock
(`readPoint_locks_provenance_strict`). -/
theorem proposal_not_conflicts_point_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) (hsb : sp.ts s + 6 * sp.Δ ≤ b)
    {K : AC.CommitteeDict sp.n} (hKB : CommitteeFacts tr H K)
    (hBK : CommitteeBoundsFrom tr H K 0 b)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ℓ : ACLabel (goldilocksNode sp ro)}
    {A : AC.ACState sp.n} (hpt : AC.OptimisticPoint tr.projAC y j ℓ A) (hb : tr.time j ≤ b)
    (hPt : P ∈ ℓ.frame.tree) (hpos : 0 < sp.slot (tr.time j))
    (hbelow : ∀ D CV, AC.OptimisticLockAt tr.projAC y j (sp.slot (tr.time j)) D CV →
      Compatible (tr.HonestBlocksAt H) D P) (t : Time) :
    ¬ AC.conflictsWithLock sp A.locks ℓ.frame t P := by
  have hcoh := honestBlocksAt_coherent hrun hnc
  have hΦ := frameIn_at hrun hnc hy hpt.1
  have hst := stored_lock_compatible hrun hnc hb0 hinv hy hpt.1 hb
    (proposal_originWithin_at hrun hnc hb0 hsync hB hinv hp hP hPs hsb hKB hBK).1 hPt
  rw [← projAC_state_at hrun hy] at hst
  apply not_conflicts_of_compatible hrun hnc hΦ.1 hΦ.2 hPt _ t
  have hc := hpt.1
  obtain ⟨-, ⟨m, -, rfl⟩ | ⟨B, -, rfl⟩ | ⟨e, he, rfl⟩⟩ := hpt
  · rw [AC.admitVote_locks_eq]; exact hst
  · rw [AC.blockReceipt_locks]; exact hst
  rw [AC.admitVote_locks_eq]
  have hd := hrun.time_nonneg j
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time j)) y j ℓ e :=
    ac_castAt_upTo.mpr ⟨le_rfl, hc, he⟩
  intro l' hl' B₀ hB₀ hB₀r
  obtain ⟨B', hB', hB'r, h⟩ :=
    AC.readPoint_locks_provenance_strict (acRun_upTo hrun hnc hd) hy hc' hpos l' hl'
  obtain rfl : B' = B₀ := hΦ.1.coherent.1 hB' hB₀ (hB'r.trans hB₀r.symm)
  -- compatibility with `P` passes to ancestors
  have down : ∀ {X Y}, Anc (tr.HonestBlocksAt H) X Y → Compatible (tr.HonestBlocksAt H) P Y →
      Compatible (tr.HonestBlocksAt H) P X := by
    rintro X Y hXY (h | h)
    · exact AC.anc_total hcoh h hXY
    · exact Or.inr (hXY.trans h)
  rcases h with ⟨l, hl, B, hB, hBr, hA⟩ | ⟨B, CV, ho, -, hA⟩
  · rw [projAC_upTo_state hrun le_rfl] at hl
    exact down (hA.mono hΦ.2) (hst l hl B hB hBr)
  · obtain ⟨-, ho⟩ := (AC.upTo_optimisticLockAt hrun.time_mono).mp ho
    exact down (hA.mono hΦ.2) (hbelow B CV ho).symm

end Consensus.Goldilocks.Compose.Growing

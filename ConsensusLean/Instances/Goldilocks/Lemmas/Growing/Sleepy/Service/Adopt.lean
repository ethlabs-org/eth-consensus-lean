module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Held
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Batch
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Adopt
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Confirmation
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Timing
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy` with growing faults: the proposal is adopted by its slot's update

The growing-fault form of `Compose/Service/Adopt`, for the proposal `P` of slot `s` by a proposer
honest at `t_s + Δ` and the update of slot `s` (at `d = t_s + 6Δ`) of a node honest then:

* `proposal_held_at_update_at`: `P` is in the update's frame, above its `Σ.F` (the proposer's
  acceptance is relayed to the updater, honest at its call, by `t_s + Δ`);
* `proposal_majority_at_update_at`, **the double-count channel** (TL §1.5), charged at `d`: the
  slot-`s` voters still honest at `d` (`VotersAt s d`) support `P` (their votes are `P`, in the
  pool and resolved), the pool's voters are among them or compromised by `d`, and
  `(H d)ᶜ < |VotersAt s d|` (`faults_lt_voters`, the slot count at `d`);
* `result_not_vetoed_at`, `adopt_result_at`, `update_adopts_at`: the update returns `P`, not
  vetoed, and the record moves to `P` or keeps a deeper block. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **`P` is in the updater's frame, above its `Σ.F`**, under the service from `a ≤ t_s`, when the
updater's `Σ.F` is below `P`: the acceptance relay brings `P`, accepted at `t_s` by its proposer
honest then, to the updater (restarts at or before `t_s`) before `t_s + Δ`. -/
theorem proposal_held_at_update_from (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b)
    {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) (ha : a ≤ sp.ts s) {y : Fin sp.n} {k₀ : Nat}
    (hy : y ∈ H (tr.time k₀)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (hb : tr.time k₀ ≤ b)
    (hFP : Anc (tr.HonestBlocksAt H) (tr.state y k₀).fg.F P) :
    P ∈ ℓ.frame.tree ∧ ℓ.frame.Anc ℓ.frame.F P := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hU := honestBlocksAt_coherent hrun hnc
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hu.1
  have hF : Anc (tr.HonestBlocksAt H) ℓ.frame.F P := by
    rw [frame_of_projAC_at hrun hy hu.1]
    exact hFP
  -- `P` is accepted by its proposer at `t_s`, and the AC cut of that block follows
  have htk : tr.time k = sp.ts s := by rw [hP.2.2, sp.slotTime_eq, hPs]; rfl
  have hpk : p ∈ H (tr.time k) := hrun.antitone (by rw [htk]; linarith) hp
  have hdk := hrun.time_nonneg k
  have hr := hrun.upTo hdk
  have hP' : (tr.upTo (tr.time k)).ProposesAt p k P :=
    ⟨(RunTrace.upTo_ownBlockAt tr).2 ⟨le_rfl, hP.1⟩, hP.2.1, hP.2.2⟩
  have hacc := Compose.proposal_accepted hr (hnc.upTo _) hpk hP'
  obtain ⟨ℓ', hc', hcall', ht'⟩ := Compose.accept_next hr.toLocalRun hpk hacc
  have hc'' : tr.CallAt p (k + 1) (.ac ℓ') := ((Trace.upTo_callAt _).1 hc').2
  have hk1 : tr.time (k + 1) = sp.ts s := ht'.trans htk
  have hpk1 : p ∈ H (tr.time (k + 1)) := hk1 ▸ (htk ▸ hpk)
  -- the updater's restarts are at or before `t_s`, so its deadline for `t_s` is `t_s + Δ`
  have hrs := update_restarts_at hrun hnc hy hu
  have htk₀ : tr.time k₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hdl : tr.projAC.deadline y k₀ (tr.time (k + 1)) ≤ tr.time k₀ := by
    have h := ac_deadline_le_of_restarts (T := tr.projAC) hrs (tr.time (k + 1))
    change tr.projAC.deadline y k₀ (tr.time (k + 1)) ≤ max (tr.time (k + 1)) (sp.ts s) + sp.Δ
      at h
    rw [hk1, max_self] at h
    rw [htk₀, hk1]
    linarith
  obtain ⟨k', hk', hAz, -⟩ := hsync.acRelay p (k + 1) P hpk1 ⟨ℓ', projAC_callAt.2 hc'', hcall'⟩
    (hk1 ▸ ha) y k₀ ℓ hy hu.1 (hdl.trans hb) hdl hF
  have hPt := mem_tree_of_acceptAt_at hrun hnc hy hAz hk' hu.1 hF
  exact ⟨hPt, SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.rooted.1 hF hPt⟩

/-- **`P` is in the updater's frame, above its `Σ.F`**: `Σ.F ⪯ P`
(`updater_F_anc_proposal_at`), so the acceptance relay brings `P`, accepted at `t_s` by its
proposer honest then, to the updater (restarts at or before `t_s`) before `t_s + Δ`. -/
theorem proposal_held_at_update_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {y : Fin sp.n} {k₀ : Nat}
    (hy : y ∈ H (tr.time k₀)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (hb : tr.time k₀ ≤ b) :
    P ∈ ℓ.frame.tree ∧ ℓ.frame.Anc ℓ.frame.F P := by
  exact proposal_held_at_update_from hrun hnc (hsync.toFrom hrun) hp hP hPs (ts_natCast_nonneg _)
    hy hu hb (updater_F_anc_proposal_at hrun hnc hb0 hsync hB hinv hp hP hPs hy hu hb)

/-- **`P` has a strict majority at the update's test**, under the service from `a ≤ t_s` with its
catch-up before `a + κ ≤ t_s + 2Δ` and the counts from `σ₀ ≤ s`, for `P` held at the update and
every honest slot-`s` vote `P`: the double-count channel charged at the update's cut
`d = t_s + 6Δ`, as in `proposal_majority_at_update_at`. -/
theorem proposal_majority_at_update_from (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {a κ b : Time} (hsync : SleepyServiceFrom tr H ΔF a κ b) {σ₀ : Nat}
    (hB : SleepyBoundsFrom tr H σ₀ b) {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat}
    (hσ₀ : σ₀ ≤ s) (ha : a ≤ sp.ts s) (hκ : a + κ ≤ sp.ts s + 2 * sp.Δ) {y : Fin sp.n}
    {k₀ : Nat} (hy : y ∈ H (tr.time k₀)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (hb : tr.time k₀ ≤ b) (hPt : P ∈ ℓ.frame.tree)
    (hall : ∀ x j e, HVoteAt tr H x j e → e.msg.slot = s → e.msg.head = P.root) :
    (SA.voters {v | v ∈ (tr.state y k₀).ac.pool s}).ncard <
      2 * SA.confirmationScore sp (tr.state y k₀).ac ℓ.frame s P := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have ht : tr.time k₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hbatch := honest_batch_at_update_from hrun hnc hsync hy hu hb ha hκ hPt hall
  rw [← projAC_state_at hrun hy]
  set d := tr.time k₀
  set A := tr.projAC.state y k₀
  set Hv := VotersAt tr H s d
  have hcount : (H d)ᶜ.ncard < Hv.ncard :=
    faults_lt_voters hrun (fun _ _ => rfl) hnc hB hσ₀ (by rw [ht]; linarith) hb (by rw [ht])
  -- a validator honest at `d` has one slot-`s` vote in the pool: its vote
  have hone : ∀ x j e, HVoteAt tr H x j e → x ∈ H d → e.msg.slot = s →
      ∀ v ∈ A.pool s, v.val = x → v = e.msg := by
    intro x j e hv hxd hs v hvp hvx
    obtain ⟨j', -, e', hv', rfl⟩ := pool_vote_at hrun hnc hy hvp (hvx ▸ hxd)
    have hs' := state_pool_slot_at hrun hnc hy s _ hvp
    rw [hvx] at hv'
    exact congrArg (fun e : SA.Em sp (List (FG.Att sp.n)) => e.msg)
      (one_vote_per_slot_at hrun hnc hv' hv (hs'.trans hs.symm)).2
  have hsupp : Hv ⊆ SA.supporters ℓ.frame ⟨{v | v ∈ A.pool s}, {v | v ∈ A.pool s ∧
      SA.resolutionTime A ℓ.frame v < SA.ETime.of (sp.ts s + 2 * sp.Δ)}⟩ s P := by
    intro x hxv
    obtain ⟨hxd, j, e, hv, hs⟩ := votersAt_iff.1 hxv
    obtain ⟨hvp, hres⟩ := hbatch x j e hv hxd hs
    obtain ⟨hx, ℓx, hcx, hex⟩ := hVoteAt_iff.1 hv
    have hval := (castAt_spec_at hrun hnc hx ⟨hcx, hex⟩).1
    refine ⟨?_, e.msg, ⟨hvp, hres⟩, hval, by exact_mod_cast hs, P, hPt,
      (hall x j e hv hs).symm, Relation.ReflTransGen.refl⟩
    rintro ⟨v, hv₁, v', hv', hne, hvx, hv'x⟩
    exact hne ((hone x j e hv hxd hs v hv₁ hvx).trans (hone x j e hv hxd hs v' hv' hv'x).symm)
  have hvot : SA.voters {v | v ∈ A.pool s} ⊆ Hv ∪ (H d)ᶜ := by
    rintro w ⟨v, hv, rfl⟩
    by_cases hw : v.val ∈ H d
    · obtain ⟨j, -, e, he, rfl⟩ := pool_vote_at hrun hnc hy hv hw
      exact Or.inl (votersAt_iff.2 ⟨hw, j, e, he, state_pool_slot_at hrun hnc hy s _ hv⟩)
    · exact Or.inr hw
  have h1 := Set.ncard_le_ncard hvot (Set.toFinite _)
  have h2 := Set.ncard_union_le Hv (H d)ᶜ
  have h3 := Set.ncard_le_ncard hsupp (Set.toFinite _)
  change _ < 2 * (SA.supporters ℓ.frame _ s P).ncard
  omega

/-- **`P` has a strict majority at the update's test**, the double-count channel charged at the
update's cut `d = t_s + 6Δ`: the slot-`s` voters still honest at `d` have one slot-`s` vote each,
which is `P`, in the pool and resolved before `t_s + 2Δ`; every other voter of the pool is
compromised by `d`; and `(H d)ᶜ < |VotersAt s d|`. -/
theorem proposal_majority_at_update_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {y : Fin sp.n} {k₀ : Nat}
    (hy : y ∈ H (tr.time k₀)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (hb : tr.time k₀ ≤ b) :
    (SA.voters {v | v ∈ (tr.state y k₀).ac.pool s}).ncard <
      2 * SA.confirmationScore sp (tr.state y k₀).ac ℓ.frame s P := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have ht : tr.time k₀ = sp.ts s + 6 * sp.Δ := hu.2.2.1
  exact proposal_majority_at_update_from hrun hnc (hsync.toFrom hrun) hB (Nat.zero_le _)
    (ts_natCast_nonneg _) (by rw [zero_add]; exact add_nonneg (ts_natCast_nonneg _) (by linarith))
    hy hu hb (proposal_held_at_update_at hrun hnc hb0 hsync hB hinv hp hP hPs hy hu hb).1
    (honest_votes_eq_proposal_at_update_at hrun hnc hsync hB hinv hp hP hPs (ht ▸ hb))

/-- **No result of an update of a node honest then is vetoed**: a live lock block is an ancestor
of a stored lock block, on the origin chain (S1); the result is an origin; blocks on the origin
chain are compatible. -/
theorem result_not_vetoed_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hinv : SleepyInvariantUpTo tr H b)
    {y : Fin sp.n} {k₀ s : Nat} (hy : y ∈ H (tr.time k₀)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (hb : tr.time k₀ ≤ b)
    {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hC : SA.getConfirmation sp (tr.state y k₀).ac ℓ.frame s = some C) :
    ¬ SA.conflictsWithLock sp (tr.state y k₀).ac.locks ℓ.frame (tr.time k₀) C := by
  have hcoh := honestBlocksAt_coherent hrun hnc
  obtain ⟨hΦ, hHB⟩ := frameIn_at hrun hnc hy hu.1
  have hfr := frame_of_projAC_at hrun hy hu.1
  have hCt : C ∈ ℓ.frame.tree := (SA.deepest_mem hC).1.1
  have hCo : OriginWithin tr H C s b := originWithin_iff.2
    ⟨y, k₀, _, hy, hb, Or.inl ⟨ℓ, hu, by rw [projAC_state_at hrun hy]; exact hC, rfl⟩⟩
  rintro ⟨V, hV, hconf⟩
  obtain ⟨l, hl, B₀, hB₀, hB₀r, -, rfl⟩ := SA.mem_liveLockBlocks hΦ hV
  obtain ⟨L, hL, hLr, hch⟩ := hinv.locks_at_cut hrun hb0 hy
    (fun k hk => (hrun.time_mono hk.le).trans hb) l hl
  obtain rfl : L = B₀ := hcoh.1 (mem_honestBlocksAt hrun hy hL) (hHB hB₀) (hLr.trans hB₀r.symm)
  have hcomp := OnOriginChainWithin.compatible hrun hnc hinv.origins_compatible
    (hHB hCt) (hHB hB₀)
    (onOriginChainWithin_iff.2 (Or.inr ⟨C, s, hCo, Relation.ReflTransGen.refl⟩)) hch
  obtain ⟨hVt, hVB⟩ := SA.viableAncestor_anc hΦ hB₀
  have hVB' := hVB.mono hHB
  have hCV : Compatible (tr.HonestBlocksAt H) C (ℓ.frame.viableAncestor L) := by
    rcases hcomp with h | h
    · exact SA.anc_total hcoh h hVB'
    · exact Or.inr (hVB'.trans h)
  apply hconf
  rcases hCV with h | h
  · exact Or.inl (SA.anc_tree_of_anc_U hcoh hΦ hHB hCt h hVt)
  · exact Or.inr (SA.anc_tree_of_anc_U hcoh hΦ hHB hVt h hCt)

/-- **The update of slot `s` returns exactly `P`** when `P` is held above `Σ.F` with a strict
majority at the update's test: every block with a strict majority is on one chain with it, and no
block above it has a resolved slot-`s` supporter. -/
theorem adopt_result_of (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hPs : P.slot = s) {y : Fin sp.n} {k₀ : Nat}
    (hy : y ∈ H (tr.time k₀)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (hPt : P ∈ ℓ.frame.tree)
    (hFP : ℓ.frame.Anc ℓ.frame.F P)
    (hmaj : (SA.voters {v | v ∈ (tr.state y k₀).ac.pool s}).ncard <
      2 * SA.confirmationScore sp (tr.state y k₀).ac ℓ.frame s P) :
    SA.getConfirmation sp (tr.state y k₀).ac ℓ.frame s = some P := by
  exact getConfirmation_eq_of_majority (frameIn_at hrun hnc hy hu.1).1 hPs hPt hFP hmaj

/-- **The update of slot `s` returns exactly `P`, not vetoed**: `P` is held above `Σ.F` with a
strict majority, every block with a strict majority is on one chain with it, and no block above
it has a resolved slot-`s` supporter. -/
theorem adopt_result_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {y : Fin sp.n} {k₀ : Nat}
    (hy : y ∈ H (tr.time k₀)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (hb : tr.time k₀ ≤ b) :
    SA.getConfirmation sp (tr.state y k₀).ac ℓ.frame s = some P ∧
      ¬ SA.conflictsWithLock sp (tr.state y k₀).ac.locks ℓ.frame (tr.time k₀) P := by
  have hres := adopt_result_of hrun hnc hPs hy hu
    (proposal_held_at_update_at hrun hnc hb0 hsync hB hinv hp hP hPs hy hu hb).1
    (proposal_held_at_update_at hrun hnc hb0 hsync hB hinv hp hP hPs hy hu hb).2
    (proposal_majority_at_update_at hrun hnc hb0 hsync hB hinv hp hP hPs hy hu hb)
  exact ⟨hres, result_not_vetoed_at hrun hnc hb0 hinv hy hu hb hres⟩

/-- **An update whose result is `P`, not vetoed, adopts `P`**: after it, the record of the
updater names a block of the update's frame that extends `P` (the record moves to `P` or keeps a
deeper block). -/
theorem update_adopts_of (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {y : Fin sp.n} {k₀ : Nat}
    (hy : y ∈ H (tr.time k₀)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ)
    (hC : SA.getConfirmation sp (tr.state y k₀).ac ℓ.frame s = some P)
    (hv : ¬ SA.conflictsWithLock sp (tr.state y k₀).ac.locks ℓ.frame (tr.time k₀) P) :
    ∃ E ∈ ℓ.frame.tree, E.root = (tr.state y (k₀ + 1)).ac.latestConfirmed ∧
      Anc (tr.HonestBlocksAt H) P E := by
  have hHB := (frameIn_at hrun hnc hy hu.1).2
  obtain ⟨⟨hn, hl⟩, hcall, ht, hj⟩ := hu
  rw [projAC_state_at hrun hy] at hj
  -- the cut `k₀` is the run's AC cut `ℓ`
  obtain ⟨c, hc, hcl⟩ := Option.bind_eq_some_iff.1 hl
  obtain rfl : c = .ac ℓ := by
    cases c with
    | ac ℓ' => cases hcl; rfl
    | fg _ => cases hcl
  obtain ⟨-, hstep, -, -⟩ := hrun.cutLaw y k₀ (.ac ℓ) ⟨hn, hc⟩ hy
  have hpost : tr.state y (k₀ + 1) = tr.post k₀ := by
    rw [Trace.state, ite_eq_left ⟨hn, by rw [hc]; exact Option.some_ne_none _⟩]
  classical
  have hrec : (tr.state y (k₀ + 1)).ac.latestConfirmed =
      if SA.AncR ℓ.frame P (tr.state y k₀).ac.latestConfirmed then
        (tr.state y k₀).ac.latestConfirmed else P.root := by
    rw [hpost, show (tr.post k₀).ac = _ from (congrArg Prod.fst hstep).symm, hcall]
    exact Compose.acOnTick_update_record y ht hj hC hv
  have hPt : P ∈ ℓ.frame.tree := (SA.deepest_mem hC).1.1
  split_ifs at hrec with hA
  · obtain ⟨R, hR, hRr, hPR⟩ := hA
    exact ⟨R, hR, hRr.trans hrec.symm, hPR.mono hHB⟩
  · exact ⟨P, hPt, hrec.symm, Relation.ReflTransGen.refl⟩

/-- **The update of slot `s` adopts `P`**: after the update of slot `s` of a node honest then,
through `b`, its record names a block held while honest that extends `P`. -/
theorem update_adopts_at (hrun : Growing.GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {b : Time} (hb0 : 0 ≤ b) (hsync : SleepyServiceBefore tr H ΔF b)
    (hB : SleepyBoundsFrom tr H 0 b) (hinv : SleepyInvariantUpTo tr H b) {p : Fin sp.n} {k : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hp : p ∈ H (sp.ts s + sp.Δ))
    (hP : tr.ProposesAt p k P) (hPs : P.slot = s) {y : Fin sp.n} {k₀ : Nat}
    (hy : y ∈ H (tr.time k₀)) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k₀ s ℓ) (hb : tr.time k₀ ≤ b) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = (tr.state y (k₀ + 1)).ac.latestConfirmed ∧
      Anc (tr.HonestBlocksAt H) P E := by
  obtain ⟨hC, hv⟩ := adopt_result_at hrun hnc hb0 hsync hB hinv hp hP hPs hy hu hb
  obtain ⟨E, hE, hEr, hPE⟩ := update_adopts_of hrun hnc hy hu hC hv
  exact ⟨E, (frameIn_at hrun hnc hy hu.1).2 hE, hEr, hPE⟩

end Consensus.Goldilocks.Compose.Growing

end

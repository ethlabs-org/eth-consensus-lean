module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SourceCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LowFinalized
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.LocalSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.LeftEntry
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The finalized-chain root at a call compares with held blocks, under growing faults

The growing forms of `ResetPremisesUpTo.high_J_root_of_held_at_call_before` and
`low_root_of_held_seed_at_call` (`Healing/Retention/Boot`). The caller is honest at its call `≤ b`,
and every other node is read at its own cut. A high justified height places the call after `c_z`
(`cutZ_le_of_high_hj_at`), and the high-root law reads honesty at the later of each cut and `c_z`,
the charge of a high origin's writer.

* `high_J_root_of_held_at_call_before_covered_at`: with a high justified height, `Σ.J` (hence
  `Σ.F` and `fc_root`) is compatible with a held block `B` compatible with every earlier high
  origin. A row
  in the caller's tree naming a high entry incompatible with `B`, by a signer honest at the call
  (after `c_z`), was signed at an earlier cut, from a high origin (`high_row_source_at`) earlier
  than the call, so compatible with `B`: such rows have no signer honest at the call, and fewer
  than `q` are faulty there (`J_compatible_of_rows`).
* `low_root_of_held_seed_at_call_at`: with a low justified height, `Σ.F` is below the held high
  seed `S` (`low_finalized_below_origin_at`), so `fc_root` compares with every block compatible
  with `S`; in the active case a block above `S` held by the caller is a high block above `Σ.F`,
  hence above `Σ.J`. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams Payload)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-- **A high justified height is read after the snapshot**: at a state of a reader honest at
`t`, every earlier cut at a time `≤ t`, a justified height `≥ H_z + 1` gives `c_z ≤ t`. Otherwise
the replay quorum at `c_z` has an attester of height `H_z + 1` honest at `c_z`, which signed
before `t < c_z`, against the reset's minimality and `c_z < a`. -/
theorem cutZ_le_of_high_hj_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj) :
    cutZ sp.toParams g ≤ t := by
  by_contra hlt
  have htZ : t ≤ cutZ sp.toParams g := (not_le.mp hlt).le
  obtain ⟨j₀, hj₀, hj₀b⟩ := hp.snapshot
  have hq : (H (cutZ sp.toParams g))ᶜ.ncard < sp.toParams.fg.q := by
    have h3 := hp.faults _ (ht.trans htZ) (hj₀.2.le.trans hj₀b)
    have hn := sp.toParams.hn
    change 3 * (H (cutZ sp.toParams g))ᶜ.ncard ≤ sp.toParams.n - 1 at h3
    change (H (cutZ sp.toParams g))ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    clear * - hn h3; omega
  have hreach := fg_reachable_at hp.run ht hle hy
  obtain ⟨-, -, -, ⟨X, hX, -, hXj⟩, -⟩ := Store.cache_invariants _ _ _ _ hreach
  obtain ⟨c, -, -, -, hc⟩ := Store.chain_state_of_chain _ _ _ _ hreach X hX
  obtain ⟨-, -, hjh, -⟩ := FG.chain_invariants _ _ _ hc
  obtain ⟨Y, hYX, att, hatt, hattH, hatth⟩ :=
    Store.exists_honest_att_of_lt hreach hq hX (HZ tr H g + 1) (by clear * -; omega) (by
      clear * - hjh hXj hhigh; omega)
  have hY : Y ∈ (tr.state y k).fg.tree := by
    by_cases he : Y = X
    · exact he ▸ hX
    · exact (Anc.mem hYX he).1
  have hY' : Y ∈ ((tr.upTo t).state y k).fg.tree := by rwa [Trace.upTo_state tr y hle]
  rcases Compose.tree_cases (hp.run.upTo ht).toLocalRun hy hY' with rfl | ⟨i', hi', hA⟩
  · cases hatt
  obtain ⟨d, hdi, hs⟩ := hp.run.toLocalRun.att_unforgeable y i' att
    (hp.run.antitone (hle i' hi') hy) (Or.inr ⟨Y, ⟨true, ((RunTrace.upTo_acceptAt tr).mp hA).2⟩,
      hatt⟩) (hp.run.antitone ((hle i' hi').trans htZ) hattH)
  have hdt : tr.time d ≤ t := (hp.run.time_mono hdi.le).trans (hle i' hi')
  have hdZ : max (cutZ sp.toParams g) (tr.time d) = cutZ sp.toParams g :=
    max_eq_left (hdt.trans htZ)
  have ha := hp.reset.2 att.val d att (by rw [hdZ]; exact hattH) hs hatth
  have := hp.cutZ_lt_reset_at
  linarith

/-- **A held block compatible with the earlier origins.** `B` is compatible with every high origin
written before the cut `k`, and, under the high-source cover, with every member of the healed
family of label at most `m` written before `k`. -/
def CompatibleWithOrigins (tr : GoldilocksTrace sp) (H : Time → Set (Fin sp.n)) (g a b : Time)
    (k m : Nat) (B : AC.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  (∀ v r l O, r < k → HighOrigin tr H g v r l O → Compatible (tr.HonestBlocksAt H) B O) ∧
  (HighSourceCover tr H g a b → ∀ C s, HealedMemberBefore tr H g a b C s k →
      s ≤ m → Compatible (tr.HonestBlocksAt H) B C)

theorem compatibleWithOrigins_iff {tr : GoldilocksTrace sp} {H : Time → Set (Fin sp.n)}
    {g a b : Time} {k m : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))} :
    CompatibleWithOrigins tr H g a b k m B ↔
      ((∀ v r l O, r < k → HighOrigin tr H g v r l O → Compatible (tr.HonestBlocksAt H) B O) ∧
      (HighSourceCover tr H g a b → ∀ C s, HealedMemberBefore tr H g a b C s k →
          s ≤ m → Compatible (tr.HonestBlocksAt H) B C)) :=
  Iff.rfl

/-- The justified block itself compares with a held target during quarantine, independently
of which root the frame uses for fork choice. -/
theorem high_J_root_J_compatible_quarantine_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hBy : B ∈ (tr.state y k).fg.tree)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
    (hpre : ∀ D, sp.deepDepth = some D → t ≤ cutZ sp.toParams g + 4 * D * sp.Δ)
    (hcompare : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocksAt H) B O) :
    Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.J B := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hreach := fg_reachable_at hrun ht hle hy
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => ⟨y, k, t, ht, hle, hy, hX⟩
  have hgB := ((Store.accepted_tree _ _ _ _ hreach).2.2.2 B hBy).mono hsub
  have hcz := hp.cutZ_le_of_high_hj_at ht hle hy hhigh
  have hrow : ∀ E ∈ (tr.state y k).fg.tree,
      HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h →
      ((tr.state y k).fg.σ E.root).Th = E.root → ¬ Compatible (tr.HonestBlocksAt H) E B →
      ∀ W ∈ (tr.state y k).fg.tree, ∀ att ∈ W.fgPayload, att.T = E.root →
        att.val ∉ H t := by
    intro E hE hEh _ hncE W hW att ha haT haH
    have he := Trace.upTo_state tr y hle
    have hW' : W ∈ ((tr.upTo t).state y k).fg.tree := by rwa [he]
    rcases Compose.tree_cases (hrun.upTo ht).toLocalRun hy hW' with rfl | ⟨i', hi', hA⟩
    · cases ha
    have hA' := ((RunTrace.upTo_acceptAt tr).mp hA).2
    obtain ⟨d, hdi, hs⟩ := hrun.toLocalRun.att_unforgeable y i' att
      (hrun.antitone (hle i' hi') hy) (Or.inr ⟨W, ⟨true, hA'⟩, ha⟩)
      (hrun.antitone (hle i' hi') haH)
    have hdk : d < k := hdi.trans hi'
    have hv := hrun.antitone (hle d hdk) haH
    obtain ⟨E', hE', hE'r, hE'h⟩ := Healing.signAt_entry
      (hrun.upTo (hrun.time_nonneg d)) hv ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
    have he' := Trace.upTo_state tr att.val (fun q (hq : q < d) => hrun.time_mono hq.le)
    rw [he'] at hE' hE'h
    have hsub' : (tr.state att.val d).fg.tree ⊆ tr.HonestBlocksAt H :=
      fun _ h => ⟨att.val, d, tr.time d, hrun.time_nonneg d,
        fun q hq => hrun.time_mono hq.le, hv, h⟩
    obtain rfl : E' = E := hU.1 (hsub' hE') (hsub hE) (hE'r.trans haT)
    have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg d)
      (fun q hq => hrun.time_mono hq.le) hv ht hle hy hE' hE
    obtain ⟨r, hrd, l, O, ho, E₀, hE₀, hE₀O, hE₀r, -⟩ :=
      Outcome.high_row_source_at hrun hnc (hrun.antitone (max_le hcz (hle d hdk)) haH) hs
        (by rw [← hE'h, hσ]; exact hEh) (hp.snapshot.imp fun _ h => h.1)
        fun D hD => (hle d hdk).trans (hpre D hD)
    have hsub₀ : (tr.state att.val r).fg.tree ⊆ tr.HonestBlocksAt H :=
      fun _ h => ⟨att.val, r, tr.time r, hrun.time_nonneg r,
        fun q hq => hrun.time_mono hq.le, hrun.antitone (le_max_right _ _) ho.1, h⟩
    obtain rfl : E₀ = E' := hU.1 (hsub₀ hE₀) (hsub' hE') (hE₀r.trans hE'r.symm)
    have hEO : Anc (tr.HonestBlocksAt H) E₀ O := hE₀O.mono hsub₀
    rcases hcompare _ r l O (by omega) ho with hBO | hOB
    · exact hncE (AC.anc_total hU hEO hBO)
    · exact hncE (Or.inl (hEO.trans hOB))
  have hq : (H t)ᶜ.ncard < sp.toParams.fg.q := by
    have hf := hp.faults t ht htb
    have hn := sp.toParams.hn
    change 3 * (H t)ᶜ.ncard ≤ sp.toParams.n - 1 at hf
    change (H t)ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    clear * - hn hf; omega
  exact Store.J_compatible_of_rows hreach hq hU hsub hgB hrow hhigh

/-- Under the source cover, expose the justified-block comparison rather than only the
fork-choice-root comparison. -/
theorem high_J_root_J_compatible_cover_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hBy : B ∈ (tr.state y k).fg.tree)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj) (hc : HighSourceCover tr H g a b)
    (hcompare : ∀ C s, HealedMemberBefore tr H g a b C s k →
      s ≤ sp.slot t → Compatible (tr.HonestBlocksAt H) B C) :
    Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.J B := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hreach := fg_reachable_at hrun ht hle hy
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => ⟨y, k, t, ht, hle, hy, hX⟩
  have hgB := ((Store.accepted_tree _ _ _ _ hreach).2.2.2 B hBy).mono hsub
  have hcz := hp.cutZ_le_of_high_hj_at ht hle hy hhigh
  have hrow : ∀ E ∈ (tr.state y k).fg.tree,
      HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h →
      ((tr.state y k).fg.σ E.root).Th = E.root → ¬ Compatible (tr.HonestBlocksAt H) E B →
      ∀ W ∈ (tr.state y k).fg.tree, ∀ att ∈ W.fgPayload, att.T = E.root →
        att.val ∉ H t := by
    intro E hE hEh _ hncE W hW att ha haT haH
    have he := Trace.upTo_state tr y hle
    have hW' : W ∈ ((tr.upTo t).state y k).fg.tree := by rwa [he]
    rcases Compose.tree_cases (hrun.upTo ht).toLocalRun hy hW' with rfl | ⟨i', hi', hA⟩
    · cases ha
    have hA' := ((RunTrace.upTo_acceptAt tr).mp hA).2
    obtain ⟨d, hdi, hs⟩ := hrun.toLocalRun.att_unforgeable y i' att
      (hrun.antitone (hle i' hi') hy) (Or.inr ⟨W, ⟨true, hA'⟩, ha⟩)
      (hrun.antitone (hle i' hi') haH)
    have hdk : d < k := hdi.trans hi'
    have hv := hrun.antitone (hle d hdk) haH
    obtain ⟨E', hE', hE'r, hE'h⟩ := Healing.signAt_entry
      (hrun.upTo (hrun.time_nonneg d)) hv ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
    have he' := Trace.upTo_state tr att.val (fun q (hq : q < d) => hrun.time_mono hq.le)
    rw [he'] at hE' hE'h
    have hsub' : (tr.state att.val d).fg.tree ⊆ tr.HonestBlocksAt H :=
      fun _ h => ⟨att.val, d, tr.time d, hrun.time_nonneg d,
        fun q hq => hrun.time_mono hq.le, hv, h⟩
    obtain rfl : E' = E := hU.1 (hsub' hE') (hsub hE) (hE'r.trans haT)
    have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg d)
      (fun q hq => hrun.time_mono hq.le) hv ht hle hy hE' hE
    obtain ⟨E₁, hE₁H, hE₁r, hcov⟩ := Outcome.signed_row_covered_before_at hrun hnc
      (hrun.antitone (max_le hcz (hle d hdk)) haH) hs (by rw [← hE'h, hσ]; exact hEh)
      (hp.snapshot.imp fun _ h => h.1) hc ((hle d hdk).trans htb)
    obtain rfl : E₁ = E' := hU.1 hE₁H (hsub' hE') (hE₁r.trans haT)
    obtain ⟨-, C, s, hC, hs', hEC⟩ := coveredBefore_iff.1 hcov
    rcases hcompare C s (hC.mono hdk.le)
        (hs'.trans (AC.slot_mono sp (hrun.time_nonneg d) (hle d hdk))) with hBC | hCB
    · exact hncE (AC.anc_total hU hEC hBC)
    · exact hncE (Or.inl (hEC.trans hCB))
  have hq : (H t)ᶜ.ncard < sp.toParams.fg.q := by
    have hf := hp.faults t ht htb
    have hn := sp.toParams.hn
    change 3 * (H t)ᶜ.ncard ≤ sp.toParams.n - 1 at hf
    change (H t)ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    clear * - hn hf; omega
  exact Store.J_compatible_of_rows hreach hq hU hsub hgB hrow hhigh

/-- A high justified block compares with a held target compatible with the bounded origins,
whether the reset is still quarantined or has source cover. -/
theorem high_J_root_J_compatible_covered_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hBy : B ∈ (tr.state y k).fg.tree)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
    (hcompare : CompatibleWithOrigins tr H g a b k (sp.slot t) B) :
    Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.J B := by
  rcases hp.quarantine_or_cover_at htb with hpre | hc
  · exact hp.high_J_root_J_compatible_quarantine_at ht hle hy htb hBy hhigh hpre
      (compatibleWithOrigins_iff.1 hcompare).1
  · exact hp.high_J_root_J_compatible_cover_at ht hle hy htb hBy hhigh hc
      ((compatibleWithOrigins_iff.1 hcompare).2 hc)

/-- **The finalized-chain root of a reader under the high-source cover**: with a high justified
height, a reader honest at `t ≤ b` has the root of its store compatible with every held block
compatible with the healed members of label at most the slot of `t` written before `k`. A row
naming a high entry incompatible with `B` has a signer honest at `t` only if the entry is below
such a member (`signed_row_covered_before_at`), and fewer than `q` are faulty at `t`. -/
theorem high_J_root_of_held_cover_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i k : Nat} {t t' : Time} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ht : 0 ≤ t) (hle : ∀ q < k, tr.time q ≤ t) (hy : y ∈ H t) (htb : t ≤ b)
    (ht' : 0 ≤ t') (hle' : ∀ q < i, tr.time q ≤ t') (hx : x ∈ H t')
    (hBx : B ∈ (tr.state x i).fg.tree)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj) (hc : HighSourceCover tr H g a b)
    (hcompare : ∀ C s, HealedMemberBefore tr H g a b C s k →
        s ≤ sp.slot t → Compatible (tr.HonestBlocksAt H) B C) :
    Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F B := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hreach := fg_reachable_at hrun ht hle hy
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => ⟨y, k, t, ht, hle, hy, hX⟩
  have hgB := ((Store.accepted_tree _ _ _ _ (fg_reachable_at hrun ht' hle' hx)).2.2.2 B hBx).mono
    (fun X hX => (⟨x, i, t', ht', hle', hx, hX⟩ : X ∈ tr.HonestBlocksAt H))
  have hcz := hp.cutZ_le_of_high_hj_at ht hle hy hhigh
  have hrow : ∀ E ∈ (tr.state y k).fg.tree,
      HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h →
      ((tr.state y k).fg.σ E.root).Th = E.root → ¬ Compatible (tr.HonestBlocksAt H) E B →
      ∀ W ∈ (tr.state y k).fg.tree, ∀ att ∈ W.fgPayload, att.T = E.root →
        att.val ∉ H t := by
    intro E hE hEh _ hncE W hW att ha haT haH
    have he := Trace.upTo_state tr y hle
    have hW' : W ∈ ((tr.upTo t).state y k).fg.tree := by rwa [he]
    rcases Compose.tree_cases (hrun.upTo ht).toLocalRun hy hW' with rfl | ⟨i', hi', hA⟩
    · cases ha
    have hA' := ((RunTrace.upTo_acceptAt tr).mp hA).2
    obtain ⟨d, hdi, hs⟩ := hrun.toLocalRun.att_unforgeable y i' att
      (hrun.antitone (hle i' hi') hy) (Or.inr ⟨W, ⟨true, hA'⟩, ha⟩)
      (hrun.antitone (hle i' hi') haH)
    have hdk : d < k := hdi.trans hi'
    have hv := hrun.antitone (hle d hdk) haH
    obtain ⟨E', hE', hE'r, hE'h⟩ := Healing.signAt_entry
      (hrun.upTo (hrun.time_nonneg d)) hv ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
    have he' := Trace.upTo_state tr att.val (fun q (hq : q < d) => hrun.time_mono hq.le)
    rw [he'] at hE' hE'h
    have hsub' : (tr.state att.val d).fg.tree ⊆ tr.HonestBlocksAt H :=
      fun _ h => ⟨att.val, d, tr.time d, hrun.time_nonneg d,
        fun q hq => hrun.time_mono hq.le, hv, h⟩
    obtain rfl : E' = E := hU.1 (hsub' hE') (hsub hE) (hE'r.trans haT)
    have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg d)
      (fun q hq => hrun.time_mono hq.le) hv ht hle hy hE' hE
    obtain ⟨E₁, hE₁H, hE₁r, hcov⟩ := Outcome.signed_row_covered_before_at hrun hnc
      (hrun.antitone (max_le hcz (hle d hdk)) haH) hs (by rw [← hE'h, hσ]; exact hEh)
      (hp.snapshot.imp fun _ h => h.1) hc ((hle d hdk).trans htb)
    obtain rfl : E₁ = E' := hU.1 hE₁H (hsub' hE') (hE₁r.trans haT)
    obtain ⟨-, C, s, hC, hs', hEC⟩ := coveredBefore_iff.1 hcov
    rcases hcompare C s (hC.mono hdk.le)
        (hs'.trans (AC.slot_mono sp (hrun.time_nonneg d) (hle d hdk))) with
      hBC | hCB
    · exact hncE (AC.anc_total hU hEC hBC)
    · exact hncE (Or.inl (hEC.trans hCB))
  have hq : (H t)ᶜ.ncard < sp.toParams.fg.q := by
    have hf := hp.faults t ht htb
    have hn := sp.toParams.hn
    change 3 * (H t)ᶜ.ncard ≤ sp.toParams.n - 1 at hf
    change (H t)ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    clear * - hn hf; omega
  have hJ := Store.J_compatible_of_rows hreach hq hU hsub hgB hrow hhigh
  have hF : Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F B := by
    obtain ⟨-, -, hFJ, -⟩ := Store.cache_invariants _ _ _ _ hreach
    rcases hJ with hJB | hBJ
    · exact Or.inl ((hFJ.mono hsub).trans hJB)
    · exact AC.anc_total hU (hFJ.mono hsub) hBJ
  exact hF

/-- A cut of a node honest at it, with a high justified height, has its store's finalized-chain
root compatible with every held block compatible with the earlier high origins, when the cut is
inside the deep quarantine. The cut is after `c_z` (`cutZ_le_of_high_hj_at`). -/
theorem high_J_root_of_held_before_quarantine_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i k : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (hBx : B ∈ (tr.state x i).fg.tree) (hy : y ∈ H (tr.time k))
    (hkb : tr.time k ≤ b)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
    (hpre : ∀ D, sp.deepDepth = some D → tr.time k ≤ cutZ sp.toParams g + 4 * D * sp.Δ)
    (hcompare : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocksAt H) B O) :
    Compatible (tr.HonestBlocksAt H) (Node.frame (tr.state y k)).F B := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hk0 := hrun.time_nonneg k
  have hlek : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => hrun.time_mono hq.le
  have hcz := hp.cutZ_le_of_high_hj_at hk0 hlek hy hhigh
  have hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time k)) := by rwa [max_eq_right hcz]
  have hi0 := hrun.time_nonneg i
  have hlei : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have hreach := fg_reachable_at hrun hk0 hlek hy
  have hgB := ((Store.accepted_tree _ _ _ _ (fg_reachable_at hrun hi0 hlei hx)).2.2.2 B hBx).mono
    (fun X hX => (⟨x, i, tr.time i, hi0, hlei, hx, hX⟩ : X ∈ tr.HonestBlocksAt H))
  have hq : (H (max (cutZ sp.toParams g) (tr.time k)))ᶜ.ncard < sp.toParams.fg.q := by
    have hf := hp.faults (tr.time k) hk0 hkb
    have hn := sp.toParams.hn
    rw [max_eq_right hcz]
    change 3 * (H (tr.time k))ᶜ.ncard ≤ sp.toParams.n - 1 at hf
    change (H (tr.time k))ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    clear * - hn hf; omega
  exact (LocalSources.high_roots_before (goldilocksNode sp).genesisPayload
    (fun v i => (tr.state v i).fg) tr.time (fun t => H (max (cutZ sp.toParams g) t)) tr.SignAt
    (HighOrigin tr H g) tr.JoinedAt (tr.HonestBlocksAt H) (HZ tr H g) (tr.time k) hU
    hrun.time_mono
    (fun v i hv _ X hX => ⟨v, i, tr.time i, hrun.time_nonneg i,
      fun q hq => hrun.time_mono hq.le, hrun.antitone (le_max_right _ _) hv, hX⟩)
    (Outcome.local_observations hrun hnc _ _ (tr.time k))
    (Outcome.local_sources hrun hnc g (tr.time k) (hp.snapshot.imp fun _ h => h.1) hpre)
    y k B hyz le_rfl hreach hgB hq hhigh
    (fun v r l O hrk _ ho => hcompare v r l O hrk ho)).2

/-- A cut of a node honest at it, with a high justified height, has its store's finalized-chain
root compatible with every held block compatible with the earlier origins: the high origins, and
under the high-source cover the healed members up to the slot of the cut. -/
theorem high_J_root_of_held_before_covered_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i k : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (hBx : B ∈ (tr.state x i).fg.tree) (hy : y ∈ H (tr.time k))
    (hkb : tr.time k ≤ b)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
    (hcompare : CompatibleWithOrigins tr H g a b k (sp.slot (tr.time k)) B) :
    Compatible (tr.HonestBlocksAt H) (Node.frame (tr.state y k)).F B := by
  rcases hp.quarantine_or_cover_at hkb with hpre | hc
  · exact hp.high_J_root_of_held_before_quarantine_at hx hBx hy hkb hhigh hpre
      (compatibleWithOrigins_iff.1 hcompare).1
  · exact hp.high_J_root_of_held_cover_at (hp.run.time_nonneg k)
      (fun _ hq => hp.run.time_mono hq.le) hy hkb (hp.run.time_nonneg i)
      (fun _ hq => hp.run.time_mono hq.le) hx hBx hhigh hc
      ((compatibleWithOrigins_iff.1 hcompare).2 hc)

/-- `high_J_root_of_held_before_quarantine_at` at an AC call, whose frame is the store's. -/
theorem high_J_root_of_held_at_call_before_quarantine_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i k : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (hBx : B ∈ (tr.state x i).fg.tree) (hy : y ∈ H (tr.time k))
    (hkb : tr.time k ≤ b) {ell : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y k ell)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
    (hpre : ∀ D, sp.deepDepth = some D → tr.time k ≤ cutZ sp.toParams g + 4 * D * sp.Δ)
    (hcompare : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocksAt H) B O) :
    Compatible (tr.HonestBlocksAt H) ell.frame.F B := by
  rw [Outcome.frame_of_call hp.run hy hc]
  exact hp.high_J_root_of_held_before_quarantine_at hx hBx hy hkb hhigh hpre hcompare

/-- `high_J_root_of_held_before_covered_at` at an AC call. -/
theorem high_J_root_of_held_at_call_before_covered_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i k : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (hBx : B ∈ (tr.state x i).fg.tree) (hy : y ∈ H (tr.time k))
    (hkb : tr.time k ≤ b) {ell : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y k ell)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
    (hcompare : CompatibleWithOrigins tr H g a b k (sp.slot (tr.time k)) B) :
    Compatible (tr.HonestBlocksAt H) ell.frame.F B := by
  rw [Outcome.frame_of_call hp.run hy hc]
  exact hp.high_J_root_of_held_before_covered_at hx hBx hy hkb hhigh hcompare

/-- A cut of a node honest at it, with a low justified height and a held high seed, has its
finalized-chain root compatible with every held block compatible with the seed. -/
theorem low_root_of_held_seed_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} {B S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hib : tr.time i ≤ b)
    (hS : HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b)
    (_hSy : S ∈ (tr.state y i).fg.tree)
    (hlow : (tr.state y i).fg.hj ≤ HZ tr H g)
    (hBS : Compatible (tr.HonestBlocksAt H) B S)
    (_hheld : Anc (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).F B →
      B ∈ (Node.frame (tr.state y i)).tree) :
    Compatible (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).F B := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hi0 := hrun.time_nonneg i
  have hlei : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have hFS := hp.low_finalized_below_origin_at hi0 hlei hy hib hlow hS hqb
  change Compatible _ (tr.state y i).fg.F B
  rcases hBS with hBS | hSB
  · exact AC.anc_total hU hFS hBS
  · exact Or.inl (hFS.trans hSB)

/-- `low_root_of_held_seed_at` at an AC call, whose frame is the store's. -/
theorem low_root_of_held_seed_at_call_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y v : Fin sp.n} {r i q m : Nat} {B S : AC.Blk sp.n (List (FG.Att sp.n))}
    (_hx : x ∈ H (tr.time r)) (_hBx : B ∈ (tr.state x r).fg.tree) (_hrb : tr.time r ≤ b)
    (hy : y ∈ H (tr.time i)) (hib : tr.time i ≤ b)
    (hS : HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b)
    {ell : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y i ell) (hSy : S ∈ (tr.state y i).fg.tree)
    (hlow : (tr.state y i).fg.hj ≤ HZ tr H g)
    (hBS : Compatible (tr.HonestBlocksAt H) B S)
    (hheld : Anc (tr.HonestBlocksAt H) ell.frame.F B → B ∈ ell.frame.tree) :
    Compatible (tr.HonestBlocksAt H) ell.frame.F B := by
  rw [Outcome.frame_of_call hp.run hy hc] at hheld ⊢
  exact hp.low_root_of_held_seed_at hy hib hS hqb hSy hlow hBS hheld

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

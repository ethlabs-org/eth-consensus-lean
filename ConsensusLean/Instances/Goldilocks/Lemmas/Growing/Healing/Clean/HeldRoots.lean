module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LowFinalized
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.LocalSources
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

* `high_J_root_of_held_at_call_before_at`: with a high justified height, `Σ.J` (hence `Σ.F` and
  `fc_root`) is compatible with a held block `B` compatible with every earlier high origin. A row
  in the caller's tree naming a high entry incompatible with `B`, by a signer honest at the call
  (after `c_z`), was signed at an earlier cut, from a high origin (`high_row_source_at`) earlier
  than the call, so compatible with `B`: such rows have no signer honest at the call, and fewer
  than `q` are faulty there (`J_compatible_of_rows`).
* `low_root_of_held_seed_at_call_at`: with a low justified height, `Σ.F` is below the held high
  seed `S` (`low_finalized_below_origin_at`), so `fc_root` compares with every block compatible
  with `S`; in the active case a block above `S` held by the caller is a high block above `Σ.F`,
  hence above `Σ.J`. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
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
  rcases Healing.tree_accepted (hp.run.upTo ht).toLocalRun hy hY' with rfl | ⟨i', hi', hA⟩
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

/-- A cut of a node honest at it, with a high justified height, has its store's finalized-chain
root compatible with every held block compatible with the earlier high origins. The cut is after
`c_z` (`cutZ_le_of_high_hj_at`). -/
theorem high_J_root_of_held_before_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i k : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (hBx : B ∈ (tr.state x i).fg.tree) (hy : y ∈ H (tr.time k))
    (hkb : tr.time k ≤ b)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
    (hcompare : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocksAt H) B O) :
    Compatible (tr.HonestBlocksAt H) (Node.frame (tr.state y k)).fcRoot B := by
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
  exact LocalSources.high_frame_root_before (goldilocksNode sp ro).genesisPayload
    (fun v i => (tr.state v i).fg) tr.time (fun t => H (max (cutZ sp.toParams g) t)) tr.SignAt
    (HighOrigin tr H g) tr.JoinedAt (tr.HonestBlocksAt H) (HZ tr H g) b hU hrun.time_mono
    (fun v i hv _ X hX => ⟨v, i, tr.time i, hrun.time_nonneg i,
      fun q hq => hrun.time_mono hq.le, hrun.antitone (le_max_right _ _) hv, hX⟩)
    (Outcome.local_observations hrun hnc _ _ b) (Outcome.local_sources hrun hnc g b)
    y k B (Node.frame (tr.state y k)) hyz hkb hreach hgB hq hhigh
    (fun v r l O hrk _ ho => hcompare v r l O hrk ho) rfl

/-- `high_J_root_of_held_before_at` at an AC call, whose frame is the store's. -/
theorem high_J_root_of_held_at_call_before_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i k : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (hBx : B ∈ (tr.state x i).fg.tree) (hy : y ∈ H (tr.time k))
    (hkb : tr.time k ≤ b) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ell)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
    (hcompare : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocksAt H) B O) :
    Compatible (tr.HonestBlocksAt H) ell.frame.fcRoot B := by
  rw [Outcome.frame_of_call hp.run hy hc]
  exact hp.high_J_root_of_held_before_at hx hBx hy hkb hhigh hcompare

/-- A cut of a node honest at it, with a low justified height and a held high seed, has its
finalized-chain root compatible with every held block compatible with the seed. -/
theorem low_root_of_held_seed_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y v : Fin sp.n} {i q m : Nat} {B S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hy : y ∈ H (tr.time i)) (hib : tr.time i ≤ b)
    (hS : HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b)
    (hSy : S ∈ (tr.state y i).fg.tree)
    (hlow : (tr.state y i).fg.hj ≤ HZ tr H g)
    (hBS : Compatible (tr.HonestBlocksAt H) B S)
    (hheld : Anc (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).F B →
      B ∈ (Node.frame (tr.state y i)).tree) :
    Compatible (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).fcRoot B := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hi0 := hrun.time_nonneg i
  have hlei : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have hreach := fg_reachable_at hrun hi0 hlei hy
  have hFS := hp.low_finalized_below_origin_at hi0 hlei hy hib hlow hS hqb
  have hSh := Outcome.high_of_anc_at hrun hnc hS hi0 hlei hy hSy .refl
  have hJ : ∀ D ∈ (tr.state y i).fg.tree,
      (tr.state y i).fg.Anc (tr.state y i).fg.F D →
      HZ tr H g + 1 ≤ ((tr.state y i).fg.σ D.root).h →
      (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 →
      ¬ (tr.state y i).fg.Contest → Anc (tr.HonestBlocksAt H) (tr.state y i).fg.J D := by
    intro D hD hFD hDh he hn
    have hle := (Store.cache_invariants _ _ _ _ hreach).2.2.2.2.1 D hD
    have hJD : (tr.state y i).fg.Anc (tr.state y i).fg.J D := by
      by_contra h
      exact hn ⟨he, D, hD, hFD, by clear * - hlow hDh he hle; omega, h⟩
    exact hJD.mono fun X hX => ⟨y, i, tr.time i, hi0, hlei, hy, hX⟩
  change Compatible _ (tr.state y i).fg.fcRoot B
  unfold Store.fcRoot
  split_ifs with hactive
  · rcases hBS with hBS | hSB
    · exact AC.anc_total hU
        (hJ S hSy (store_anc_of_honest_anc_at hrun hnc hi0 hlei hy hFS hSy) hSh
          hactive.1 hactive.2) hBS
    · have hFB := hFS.trans hSB
      have hBy := (hheld hFB).1
      have hBhy := Outcome.high_of_anc_at hrun hnc hS hi0 hlei hy hBy hSB
      exact Or.inl (hJ B hBy (store_anc_of_honest_anc_at hrun hnc hi0 hlei hy hFB hBy) hBhy
        hactive.1 hactive.2)
  · rcases hBS with hBS | hSB
    · exact AC.anc_total hU hFS hBS
    · exact Or.inl (hFS.trans hSB)

/-- `low_root_of_held_seed_at` at an AC call, whose frame is the store's. -/
theorem low_root_of_held_seed_at_call_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y v : Fin sp.n} {r i q m : Nat} {B S : AC.Blk sp.n (List (FG.Att sp.n))}
    (_hx : x ∈ H (tr.time r)) (_hBx : B ∈ (tr.state x r).fg.tree) (_hrb : tr.time r ≤ b)
    (hy : y ∈ H (tr.time i)) (hib : tr.time i ≤ b)
    (hS : HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ell) (hSy : S ∈ (tr.state y i).fg.tree)
    (hlow : (tr.state y i).fg.hj ≤ HZ tr H g)
    (hBS : Compatible (tr.HonestBlocksAt H) B S)
    (hheld : Anc (tr.HonestBlocksAt H) ell.frame.F B → B ∈ ell.frame.tree) :
    Compatible (tr.HonestBlocksAt H) ell.frame.fcRoot B := by
  rw [Outcome.frame_of_call hp.run hy hc] at hheld ⊢
  exact hp.low_root_of_held_seed_at hy hib hS hqb hSy hlow hBS hheld

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

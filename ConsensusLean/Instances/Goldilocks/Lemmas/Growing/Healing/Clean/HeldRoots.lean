module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LowFinalized
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot

public section

/-! # The finalized-chain root at a call compares with held blocks, under growing faults

The growing forms of `high_J_root_of_held_at_call_before` and `low_root_of_held_seed_at_call`
(`Healing/Retention/Boot`). The caller is honest at its call `≤ b`, and every other node is read
at its own cut.

* `high_J_root_of_held_at_call_before_at`: with a high justified height, `Σ.J` (hence `Σ.F` and
  `fc_root`) is compatible with a held block `B` compatible with every earlier high origin. A row
  in the caller's tree naming a high entry incompatible with `B`, by a signer honest at the call,
  was signed at an earlier cut, from a high origin (`high_row_source_at`) earlier than the call,
  so compatible with `B`: such rows have no signer honest at the call, and fewer than `q` are
  faulty there (`J_compatible_of_rows`).
* `low_root_of_held_seed_at_call_at`: with a low justified height, `Σ.F` is below the held high
  seed `S` (`low_finalized_below_origin_at`), so `fc_root` compares with every block compatible
  with `S`; in the active case a block above `S` held by the caller is a high block above `Σ.F`,
  hence above `Σ.J`. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A call of a node honest at it, with a high justified height, has its finalized-chain root
compatible with every held block compatible with the earlier high origins. -/
theorem high_J_root_of_held_at_call_before_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time i)) (hBx : B ∈ (tr.state x i).fg.tree) (hy : y ∈ H (tr.time k))
    (hkb : tr.time k ≤ b) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ell)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
    (hcompare : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocksAt H) B O) :
    Compatible (tr.HonestBlocksAt H) ell.frame.fcRoot B := by
  have hrun := hp.run
  have hnc := hp.noColl
  rw [Outcome.frame_of_call hrun hy hc]
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hk0 := hrun.time_nonneg k
  have hlek : ∀ q < k, tr.time q ≤ tr.time k := fun q hq => hrun.time_mono hq.le
  have hi0 := hrun.time_nonneg i
  have hlei : ∀ q < i, tr.time q ≤ tr.time i := fun q hq => hrun.time_mono hq.le
  have hreach := fg_reachable_at hrun hk0 hlek hy
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocksAt H :=
    fun X hX => ⟨y, k, tr.time k, hk0, hlek, hy, hX⟩
  have hgB := ((Store.accepted_tree _ _ _ _ (fg_reachable_at hrun hi0 hlei hx)).2.2.2 B hBx).mono
    (fun X hX => (⟨x, i, tr.time i, hi0, hlei, hx, hX⟩ : X ∈ tr.HonestBlocksAt H))
  have hrow : ∀ E ∈ (tr.state y k).fg.tree,
      HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h →
      ((tr.state y k).fg.σ E.root).Th = E.root → ¬ Compatible (tr.HonestBlocksAt H) E B →
      ∀ W ∈ (tr.state y k).fg.tree, ∀ att ∈ W.fgPayload, att.T = E.root →
        att.val ∉ H (tr.time k) := by
    intro E hE hEh _ hncE W hW att ha haT haH
    have he := Trace.upTo_state tr y hlek
    have hW' : W ∈ ((tr.upTo (tr.time k)).state y k).fg.tree := by rwa [he]
    rcases Healing.tree_accepted (hrun.upTo hk0).toLocalRun hy hW' with rfl | ⟨i', hi', hA⟩
    · cases ha
    have hA' := ((RunTrace.upTo_acceptAt tr).mp hA).2
    obtain ⟨d, hdi, hs⟩ := hrun.toLocalRun.att_unforgeable y i' att
      (hrun.antitone (hlek i' hi') hy) (Or.inr ⟨W, ⟨true, hA'⟩, ha⟩)
      (hrun.antitone (hlek i' hi') haH)
    have hdk : d < k := hdi.trans hi'
    have hv := hrun.antitone (hlek d hdk) haH
    obtain ⟨E', hE', hE'r, hE'h⟩ := Healing.signAt_entry
      (hrun.upTo (hrun.time_nonneg d)) hv ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
    have he' := Trace.upTo_state tr att.val (fun q (hq : q < d) => hrun.time_mono hq.le)
    rw [he'] at hE' hE'h
    have hsub' : (tr.state att.val d).fg.tree ⊆ tr.HonestBlocksAt H :=
      fun _ h => ⟨att.val, d, tr.time d, hrun.time_nonneg d,
        fun q hq => hrun.time_mono hq.le, hv, h⟩
    obtain rfl : E' = E := hU.1 (hsub' hE') (hsub hE) (hE'r.trans haT)
    have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg d)
      (fun q hq => hrun.time_mono hq.le) hv hk0 hlek hy hE' hE
    obtain ⟨r, hrd, l, O, ho, E₀, hE₀, hE₀O, hE₀r, -⟩ :=
      Outcome.high_row_source_at hrun hnc hv hs (by rw [← hE'h, hσ]; exact hEh)
    have hsub₀ : (tr.state att.val r).fg.tree ⊆ tr.HonestBlocksAt H :=
      fun _ h => ⟨att.val, r, tr.time r, hrun.time_nonneg r,
        fun q hq => hrun.time_mono hq.le, ho.1, h⟩
    obtain rfl : E₀ = E' := hU.1 (hsub₀ hE₀) (hsub' hE') (hE₀r.trans hE'r.symm)
    have hEO : Anc (tr.HonestBlocksAt H) E₀ O := hE₀O.mono hsub₀
    rcases hcompare _ r l O (by clear * - hi' hrd hdi; omega) ho with hBO | hOB
    · exact hncE (SA.anc_total hU hEO hBO)
    · exact hncE (Or.inl (hEO.trans hOB))
  have hq : (H (tr.time k))ᶜ.ncard < sp.toParams.fg.q := by
    have hf := hp.faults (tr.time k) hk0 hkb
    have hn := sp.toParams.hn
    change 3 * (H (tr.time k))ᶜ.ncard ≤ sp.toParams.n - 1 at hf
    change (H (tr.time k))ᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    clear * - hn hf; omega
  have hJ := Store.J_compatible_of_rows hreach hq hU hsub hgB hrow hhigh
  have hF : Compatible (tr.HonestBlocksAt H) (tr.state y k).fg.F B := by
    obtain ⟨-, -, hFJ, -⟩ := Store.cache_invariants _ _ _ _ hreach
    rcases hJ with hJB | hBJ
    · exact Or.inl ((hFJ.mono hsub).trans hJB)
    · exact SA.anc_total hU (hFJ.mono hsub) hBJ
  change Compatible _ (tr.state y k).fg.fcRoot B
  unfold Store.fcRoot
  split_ifs <;> assumption

/-- A call of a node honest at it, with a low justified height and a held high seed, has its
finalized-chain root compatible with every held block compatible with the seed. -/
theorem low_root_of_held_seed_at_call_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y v : Fin sp.n} {r i q m : Nat} {B S : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hx : x ∈ H (tr.time r)) (_hBx : B ∈ (tr.state x r).fg.tree) (_hrb : tr.time r ≤ b)
    (hy : y ∈ H (tr.time i)) (hib : tr.time i ≤ b)
    (hS : HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ell) (hSy : S ∈ (tr.state y i).fg.tree)
    (hlow : (tr.state y i).fg.hj ≤ HZ tr H g)
    (hBS : Compatible (tr.HonestBlocksAt H) B S)
    (hheld : Anc (tr.HonestBlocksAt H) ell.frame.F B → B ∈ ell.frame.tree) :
    Compatible (tr.HonestBlocksAt H) ell.frame.fcRoot B := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hfr := Outcome.frame_of_call hrun hy hc
  rw [hfr] at hheld ⊢
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
    · exact SA.anc_total hU
        (hJ S hSy (store_anc_of_honest_anc_at hrun hnc hi0 hlei hy hFS hSy) hSh
          hactive.1 hactive.2) hBS
    · have hFB := hFS.trans hSB
      have hBy := (hheld hFB).1
      have hBhy := Outcome.high_of_anc_at hrun hnc hS hi0 hlei hy hBy hSB
      exact Or.inl (hJ B hBy (store_anc_of_honest_anc_at hrun hnc hi0 hlei hy hFB hBy) hBhy
        hactive.1 hactive.2)
  · rcases hBS with hBS | hSB
    · exact SA.anc_total hU hFS hBS
    · exact Or.inl (hFS.trans hSB)

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

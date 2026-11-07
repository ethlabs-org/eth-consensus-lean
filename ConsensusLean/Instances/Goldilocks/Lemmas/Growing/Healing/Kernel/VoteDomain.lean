module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.VoteRoots
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.VoteFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High

public section

/-! # Finite vote-domain assembly with the causal row bound explicit

This helper does not replace the frozen no-extra-premise endpoint. Its one
additional input isolates the remaining vote-row exclusion proof.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- The finite domain reduction once the vote-row labels are strictly earlier. -/
theorem held_target_vote_domain_of_row_bound_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y v : Fin sp.n} {r i q m : Nat} {B S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    (hBx : B ∈ (tr.state x r).fg.tree) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e) (hib : tr.time i ≤ b)
    (hheld : Anc (tr.HonestBlocksAt H) ell.frame.F B →
      B ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hS : HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b) (hm : m < e.msg.slot)
    (hBS : Compatible (tr.HonestBlocksAt H) B S)
    (hcompare : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      Compatible (tr.HonestBlocksAt H) B O)
    (hseedCompare : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      Compatible (tr.HonestBlocksAt H) S O)
    (hpair : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      ∀ z' d' n' O', d' < i → HighOrigin tr H g z' d' n' O' →
      Compatible (tr.HonestBlocksAt H) O O')
    (hrow : ∀ W ∈ (tr.state y i).fg.tree, ∀ att ∈ W.fgPayload,
      ∀ z d, z ∈ H (tr.time d) → tr.SignAt z d att → d < i → ∀ c l O,
        c < d → HighOrigin tr H g z c l O → l < e.msg.slot) :
    Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  have ht := hp.run.time_nonneg i
  have hle : ∀ c < i, tr.time c ≤ tr.time i := fun _ hc => hp.run.time_mono hc.le
  have hroot : Compatible (tr.HonestBlocksAt H) ell.frame.fcRoot B := by
    by_cases hlow : (tr.state y i).fg.hj ≤ HZ tr H g
    · exact low_root_of_seed_before_at hp hx hBx hrb hy hib hS hqb hcast hm hlow hBS hheld
    · exact hp.high_J_root_of_held_at_call_before_at hx hBx hy hib hcast.1
        (by omega) hcompare
  by_cases hcovered : Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot
  · exact Or.inl hcovered
  have hkeep : ∃ W ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Anc (tr.HonestBlocksAt H) B W ∧ (tr.state y i).fg.IsViable W := by
    obtain ⟨hPhi, -⟩ := frame_tree_subset_at hp.run hp.noColl hy hcast.1
    have hPhiU := Outcome.frame_tree_subset hp.run hy hcast.1
    have hFB := (Anc.mono hPhiU hPhi.F_anc_fcRoot).trans (hroot.resolve_right hcovered)
    have hBt := hheld hFB
    have hBy := (frame_tree_subset_at hp.run hp.noColl hy hcast.1).2 hBt.1
    have hreach := fg_reachable_at hp.run ht hle hy
    by_cases hfloor : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h
    · exact ⟨B, hBt, .refl, hfloor⟩
    have hBfloor := lt_of_not_ge hfloor
    have hSsrc := Outcome.high_origin_mem_at hp.run hp.noColl hS
    by_cases hSf : (tr.state y i).fg.headHeightFloor ≤ ((tr.state v q).fg.σ S.root).h
    · have hBS' : Anc (tr.HonestBlocksAt H) B S := by
        rcases hBS with h | h
        · exact h
        · have hSy := mem_of_honest_anc_at hp.run hp.noColl ht hle hy h hBy
          have hh := Healing.h_le_of_store_anc hreach
            (store_anc_of_honest_anc_at hp.run hp.noColl ht hle hy h hBy)
          rw [← σ_eq_honest_at hp.run hp.noColl (hp.run.time_nonneg q)
            (fun _ hc => hp.run.time_mono hc.le) hS.1 ht hle hy hSsrc hSy] at hh
          omega
      have hSy := high_origin_held_at_vote_at hp hS hqb hy hcast hm (hFB.trans hBS')
      have hSf' : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ S.root).h := by
        rw [← σ_eq_honest_at hp.run hp.noColl (hp.run.time_nonneg q)
          (fun _ hc => hp.run.time_mono hc.le) hS.1 ht hle hy hSsrc hSy]
        exact hSf
      exact raw_target_frozen_witness_at hp hS hqb hy hcast hm hFB hBS' hSy .refl hSf'
    · obtain ⟨z, d, n, O, E, hd, ho, hn, hE, hEO, _, hEf⟩ :=
        high_floor_source_core_of_row_bound_at hp hS hy hib hrow hpair hseedCompare
          (lt_of_not_ge hSf)
      have hBO : Anc (tr.HonestBlocksAt H) B O := by
        rcases hcompare z d n O hd ho with h | h
        · exact h
        · have hh := Healing.h_le_of_store_anc hreach
            (store_anc_of_honest_anc_at hp.run hp.noColl ht hle hy (hEO.trans h) hBy)
          omega
      exact raw_target_frozen_witness_at hp ho
        ((hp.run.time_mono hd.le).trans hib) hy hcast hn hFB hBO hE hEO hEf
  exact (vote_viable_of_root_at hp hy hcast hroot (Or.inl hkeep)).symm

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

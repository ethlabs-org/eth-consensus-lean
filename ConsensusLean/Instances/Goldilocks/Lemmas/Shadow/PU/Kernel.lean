module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.VoteDomain
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts

public section

/-! # P-U shadow kernel: the retained-vote induction and R1

The stock healing kernel's R1 chain over the shadow run, read off the reset core
(`ResetPremisesUpTo'.toCore`):

* `ResetPremisesUpTo'.high_origin_held_at_vote_at'` and
  `KernelProof.high_origin_votes_of_domain_before_at'` (HighInduction, the vote domain an
  explicit input): the core versions of the stock lemmas.
* `ResetPremisesUpTo'.high_origin_votes_before_at'` (ResetFacts, R2): the deep quarantine arm
  plugs in the P-U vote domain (`held_target_vote_domain_before_of_quarantine_at'`); the cover
  arm is S2 of the high-source cover; stock proof.
* `ResetPremisesUpTo'.origins_compatible_at'` (ResetFacts, R1, through
  `ResetRunCore.origins_compatible_of_votes_at`) and
  `ProposalImpl.finalized_compatible_high_origin_at'` (Pivot/OldSources); stock proofs. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload)
open Consensus.Goldilocks.Store

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}
  {hold : Time} {cm : Time → Finset (Fin sp.n)} {βK : ℚ}

/-- A high origin above a later honest cast's finalized tip is in its voter block tree
(`ResetPremisesUpTo.high_origin_held_at_vote_at`, `Outcome/VoteReceipt`): the voter block
tree is closed under ancestors and holds the origin's frozen head. -/
theorem ResetPremisesUpTo.high_origin_held_at_vote_at'
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {i j k : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) (_hkb : tr.time k ≤ b)
    (hj : j < e.msg.slot) (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    B ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot :=
  hp.toCore.high_origin_held_at_vote_at ho hib hy hc _hkb hj hF

/-- **The retained-vote induction**, given the finite held-target domain
(`KernelProof.high_origin_votes_of_domain_before_at`). -/
theorem KernelProof.high_origin_votes_of_domain_before_at'
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    (hdomain : ∀ {x y v : Fin sp.n} {r i q m : Nat}
      {B S : AC.Blk sp.n (List (FG.Att sp.n))},
      x ∈ H (tr.time r) → y ∈ H (tr.time i) →
      B ∈ (tr.state x r).fg.tree → tr.time r ≤ b →
      ∀ {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))},
      AC.CastAt tr.projAC y i ell e → tr.time i ≤ b →
      (Anc (tr.HonestBlocksAt H) ell.frame.F B →
        B ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot) →
      HighOrigin tr H g v q m S → tr.time q ≤ b → m < e.msg.slot →
      Compatible (tr.HonestBlocksAt H) B S →
      (∀ z d n O, d < i → HighOrigin tr H g z d n O →
        Compatible (tr.HonestBlocksAt H) B O) →
      (∀ z d n O, d < i → HighOrigin tr H g z d n O →
        Compatible (tr.HonestBlocksAt H) S O) →
      (∀ z d n O, d < i → HighOrigin tr H g z d n O →
        ∀ z' d' n' O', d' < i → HighOrigin tr H g z' d' n' O' →
          Compatible (tr.HonestBlocksAt H) O O') →
      Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
        B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot)) :
    ∀ k, tr.time k ≤ b → ∀ x i j B, HighOrigin tr H g x i j B → tr.time i ≤ b →
      ∀ y ell e, y ∈ H (tr.time k) → AC.CastAt tr.projAC y k ell e → j < e.msg.slot →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg B :=
  hp.toCore.high_origin_votes_of_domain_before_at hdomain

/-- **R2 over the shadow run** (`ResetPremisesUpTo.high_origin_votes_before_at`): every
later-label honest cast extends each high origin within the finite horizon. -/
theorem ResetPremisesUpTo.high_origin_votes_before_at'
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) :
    ∀ k, tr.time k ≤ b → ∀ x i j B, HighOrigin tr H g x i j B → tr.time i ≤ b →
      ∀ y ell e, y ∈ H (tr.time k) → AC.CastAt tr.projAC y k ell e → j < e.msg.slot →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hcase : (∀ D, sp.deepDepth = some D → b ≤ cutZ sp.toParams g + 4 * D * sp.Δ) ∨
      HighSourceCover tr H g a b := by
    cases hdd : sp.deepDepth with
    | none => exact Or.inl fun D hD => by cases hD
    | some D =>
      rcases hp.deepCover D hdd with hb | hc
      · exact Or.inl fun D' hD' => by cases hD'; exact hb
      · exact Or.inr hc
  rcases hcase with hpre | hc
  · exact KernelProof.high_origin_votes_of_domain_before_at' hp
      (fun hx hy hBx hrb _ _ hcast hib hheld hS hqb hm hBS hcompare hseedCompare hpair =>
        KernelProof.held_target_vote_domain_before_of_quarantine_at' hp hx hy hBx hrb hcast hib
          hheld hS hqb hm hBS hcompare hseedCompare hpair hpre)
  · intro k hkb x i j B ho hib y ell e hy hc' hj
    exact hc.s2 B j (Compose.Growing.HealedOrigin.of_high hib ho) y k e
      (Compose.Growing.hVoteAt_iff.2 ⟨hy, ell, hc'⟩) hkb hj

/-- **R1 over the shadow run** (`ResetPremisesUpTo.origins_compatible_at`): high origins within
the horizon are comparable. -/
theorem ResetPremisesUpTo.origins_compatible_at'
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x z : Fin sp.n} {i j r l : Nat} {B O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hO : HighOrigin tr H g z r l O) (hrb : tr.time r ≤ b) :
    Compatible (tr.HonestBlocksAt H) B O :=
  hp.toCore.origins_compatible_of_votes_at hp.high_origin_votes_before_at' ho hib hO hrb

/-- A held block with the genesis root is below every held block (`genesis_root_anc_at`). -/
private theorem genesis_root_anc_at {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {G B : AC.Blk sp.n (List (FG.Att sp.n))} (hG : G ∈ tr.HonestBlocksAt H)
    (hg : G.root = sp.toParams.genesisRoot) (hB : B ∈ tr.HonestBlocksAt H) :
    Anc (tr.HonestBlocksAt H) G B := by
  obtain ⟨y, k, t, ht, hle, hy, hBt⟩ := hB
  have hfs := finalitySpec_updateFinality (P := sp.toParams) (ACP := Payload sp.n)
  have hr := (Compose.Growing.reachable_at' hrun ht hy hle).reachableWith
  have hh := (accepted_tree_with hfs hr).2.2.2 B hBt
  have hsub := Compose.Growing.tree_held_at' ht hy hle
  have he : G = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
    (Coherence.honestBlocksAt_coherent hrun hnc).1 hG (hsub (genesis_mem_with hfs hr)) hg
  rw [he]
  exact hh.mono hsub

/-- **The finalized cache compares with a high origin** at independently honest cuts
(`ProposalImpl.finalized_compatible_high_origin_at`). -/
theorem ProposalImpl.finalized_compatible_high_origin_at'
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c)) (hcb : tr.time c ≤ b)
    {x : Fin sp.n} {i j : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j O) (hib : tr.time i ≤ b) :
    Compatible (tr.HonestBlocksAt H) (tr.state z c).fg.F O := by
  have ht := hp.run.time_nonneg c
  have hle : ∀ q < c, tr.time q ≤ tr.time c := fun _ hq => hp.run.time_mono hq.le
  have hfs := finalitySpec_updateFinality (P := sp.toParams) (ACP := Payload sp.n)
  have hr := (Compose.Growing.reachable_at' hp.run ht hz hle).reachableWith
  have hU := Coherence.honestBlocksAt_coherent hp.run hp.noColl
  have hsub := Compose.Growing.tree_held_at' ht hz hle
  by_cases hh : HZ tr H g + 1 ≤ (tr.state z c).fg.hj
  · obtain ⟨_, hJm, hFJ, ⟨C, hC, hCJ, _⟩, _⟩ := cache_invariants_with hfs hr
    obtain ⟨E, hE, hEr, hEC, hcase⟩ := J_entry_with hfs hr hC
    obtain rfl : E = (tr.state z c).fg.J := hU.1 (hsub hE) (hsub hJm) (hEr.trans hCJ)
    rcases hcase with hg | ⟨hJh, hJT⟩
    · exact Or.inl ((hFJ.mono hsub).trans (genesis_root_anc_at hp.run hp.noColl
        (hsub hJm) (congrArg (·.root) hg)
        ⟨x, i, tr.time i, hp.run.time_nonneg i, fun _ hq => hp.run.time_mono hq.le,
          hp.run.antitone (le_max_right _ _) ho.1,
          Outcome.high_origin_mem_at' hp.run hp.noColl ho⟩))
    · obtain ⟨_, _, _, _, v, d, _, hdc, _, _, hor⟩ :=
        hp.left_entry_origin_or_covered_at ht hle hz hcb hJm hJT (by omega) hEC
          (by have := hj_lt_h_with hfs hr hC; omega)
      rcases hor with ⟨r, hrd, m, B, hB, hJB⟩ | ⟨-, hcov⟩
      · have hFB := (hFJ.mono hsub).trans hJB
        rcases hp.origins_compatible_at' hB
            ((hp.run.time_mono (show r ≤ c by omega)).trans hcb) ho hib with h | h
        · exact Or.inl (hFB.trans h)
        · exact Anc.total hU hFB h
      · exact (hcov.of_anc (hFJ.mono hsub)).compatible_highOrigin' hp.run hp.noColl hib ho
  · exact Or.inl (hp.low_finalized_below_origin_at ht hle hz hcb (by omega) ho hib)

end Consensus.Goldilocks.Healing.Growing

end

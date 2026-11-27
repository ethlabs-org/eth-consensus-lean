module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Boundaries
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResultPrefix
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginCompare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighInduction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.VoteDomain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.TargetCompare
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.CoreStock

public section

/-! # Reset-source boundary for downstream kernel consumers

The finite reset lower bound and seed are supplied by ResetSource and Seed.
The remaining induction boundaries read every writer, cast and vote at its own cut.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}

/-- Step 6 finite result induction, consumed by the latest-votes wrapper.
The explicit domain and stored-lock inputs are unchanged from the static boundary. -/
theorem ResetPremisesUpTo.late_result_prefix_votes_before_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {r s : Nat}
    (hx : x ∈ H (tr.time r))
    {B C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : AC.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s)
    (hdomain : ∀ y i ell e, y ∈ H (tr.time i) → AC.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → s < e.msg.slot →
      (∀ z q e', q < i → Compose.Growing.HVoteAt tr H z q e' →
        s < e'.msg.slot → AC.VoteExtends (tr.HonestBlocksAt H) e'.msg B) →
      Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
        B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
    (hstored : ∀ y i ell e, y ∈ H (tr.time i) → AC.CastAt tr.projAC y i ell e →
      tr.time i ≤ b → e.msg.slot = s + 1 → ∀ l ∈ (tr.projAC.state y i).locks,
        sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
        ∀ Y ∈ tr.HonestBlocksAt H, Y.root = l.block → Compatible (tr.HonestBlocksAt H) Y B) :
    ∀ i, tr.time i ≤ b → ∀ y, y ∈ H (tr.time i) → ∀ ell e,
      AC.CastAt tr.projAC y i ell e → s < e.msg.slot →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  exact KernelProof.late_result_prefix_votes_before_at hp hx hres hBC hrb hts hdomain hstored

/-- The healed-frontier arm of the finite result-prefix boundary. -/
theorem ResetPremisesUpTo.late_result_prefix_votes_of_healed_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (_hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {rL rO s : Nat} {B C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hC : Compose.Growing.HealedOrigin tr H g rL rO C s b)
    (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hV : ∀ m, Compose.Growing.HealedVotesBelow tr H g rL rO m b) :
    ∀ i, tr.time i ≤ b → ∀ y, y ∈ H (tr.time i) → ∀ ell e,
      AC.CastAt tr.projAC y i ell e → s < e.msg.slot →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  exact KernelProof.late_result_prefix_votes_of_healed_at hC hBC hV

/-- R2: every later-label honest cast extends each high origin within the finite horizon.
The origin write need not precede the cast; its writer's honesty is carried by HighOrigin. Inside
the deep quarantine by the domain induction; under the high-source cover by S2. -/
theorem ResetPremisesUpTo.high_origin_votes_before_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
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
  · -- inside the deep quarantine: the domain induction
    exact KernelProof.high_origin_votes_of_domain_before_at hp
      (fun hx hy hBx hrb _ _ hcast hib hheld hS hqb hm hBS hcompare hseedCompare hpair =>
        KernelProof.held_target_vote_domain_before_of_quarantine_at hp hx hy hBx hrb hcast hib
          hheld hS hqb hm hBS hcompare hseedCompare hpair hpre)
  · -- under the high-source cover: S2, a high origin being a member of the healed family
    intro k hkb x i j B ho hib y ell e hy hc' hj
    exact hc.s2 B j (Compose.Growing.HealedOrigin.of_high hib ho) y k e
      (Compose.Growing.hVoteAt_iff.2 ⟨hy, ell, hc'⟩) hkb hj

/-- R1 over the reset core, from the retained high-origin votes (R2): high origins within the
horizon are comparable, with each writer honest at its write. -/
theorem ResetRunCore.origins_compatible_of_votes_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetRunCore tr H u frameOf proposer dg g ΔF a b cm βK hold)
    (hvotes : ∀ k, tr.time k ≤ b → ∀ x i j B, HighOrigin tr H g x i j B → tr.time i ≤ b →
      ∀ y ell e, y ∈ H (tr.time k) → AC.CastAt tr.projAC y k ell e → j < e.msg.slot →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg B)
    {x z : Fin sp.n} {i j r l : Nat} {B O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hO : HighOrigin tr H g z r l O) (hrb : tr.time r ≤ b) :
    Compatible (tr.HonestBlocksAt H) B O := by
  apply hp.origins_compatible_before_at (k := max i r + 1) ?_
    ho hib (Or.inl (by omega)) hO hrb (by omega)
  intro x₀ i₀ j₀ B₀ ho₀ hi₀ y c e _ hy hcb hv hj
  obtain ⟨ell, hc⟩ := hv
  exact hvotes c hcb x₀ i₀ j₀ B₀ ho₀ hi₀ y ell e hy hc hj

/-- R1: high origins within the horizon are comparable, with each writer honest at its write. -/
theorem ResetPremisesUpTo.origins_compatible_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x z : Fin sp.n} {i j r l : Nat} {B O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (hO : HighOrigin tr H g z r l O) (hrb : tr.time r ≤ b) :
    Compatible (tr.HonestBlocksAt H) B O :=
  hp.toCore.origins_compatible_of_votes_at hp.high_origin_votes_before_at ho hib hO hrb

/-- Finite domain reduction with independently honest source and cast observations,
inside the deep quarantine (`hpre`). -/
theorem ResetPremisesUpTo.held_target_vote_domain_before_of_quarantine_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y v : Fin sp.n} {r i q m : Nat} {B S : AC.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    (hBx : B ∈ (tr.state x r).fg.tree) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hcast : AC.CastAt tr.projAC y i ell e) (hib : tr.time i ≤ b)
    (hheld : Anc (tr.HonestBlocksAt H) ell.frame.F B →
      B ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hS : HighOrigin tr H g v q m S) (hqb : tr.time q ≤ b) (hm : m < e.msg.slot)
    (hBS : Compatible (tr.HonestBlocksAt H) B S)
    (hcompare : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      Compatible (tr.HonestBlocksAt H) B O)
    (hseedCompare : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      Compatible (tr.HonestBlocksAt H) S O)
    (hpair : ∀ z d n O, d < i → HighOrigin tr H g z d n O →
      ∀ z' d' n' O', d' < i → HighOrigin tr H g z' d' n' O' →
      Compatible (tr.HonestBlocksAt H) O O')
    (hpre : ∀ D, sp.deepDepth = some D → b ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    Anc (tr.HonestBlocksAt H) B ell.frame.fcRoot ∨
      B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot) := by
  exact KernelProof.held_target_vote_domain_before_of_quarantine_at hp hx hy hBx hrb hcast hib
    hheld hS hqb hm hBS hcompare hseedCompare hpair hpre

/-- An actual bounded supporter compares its target with an older bounded high origin. -/
theorem ResetPremisesUpTo.target_compatible_older_origin_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x z : Fin sp.n} {r m q l : Nat} {B O : AC.Blk sp.n (List (FG.Att sp.n))}
    {e : AC.Em sp (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r m O) (hrb : tr.time r ≤ b)
    (hz : z ∈ H (tr.time q)) (hv : AC.VoteAt tr.projAC z q e) (hqb : tr.time q ≤ b)
    (hs : e.msg.slot = l) (hml : m < l)
    (hB : AC.VoteExtends (tr.HonestBlocksAt H) e.msg B) :
    Compatible (tr.HonestBlocksAt H) B O := by
  obtain ⟨ell, hc⟩ := hv
  obtain ⟨HO, hHO, hOr, hOO⟩ :=
    hp.high_origin_votes_before_at q hqb x r m O ho hrb z ell e hz hc (by omega)
  obtain ⟨HB, hHB, hBr, hBB⟩ := hB
  have hcoh := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  obtain rfl : HO = HB := hcoh.1 hHO hHB (hOr.trans hBr.symm)
  exact AC.anc_total hcoh hBB hOO

/-- Prior honest head support compares a target with a later bounded controlling origin. -/
theorem ResetPremisesUpTo.target_compatible_later_origin_before_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {r m i l : Nat} {B O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r m O) (hri : r < i) (hrb : tr.time r ≤ b) (hlm : l < m)
    (hsupport : ∀ z q e, q < i → Compose.Growing.HVoteAt tr H z q e →
      l < e.msg.slot → AC.VoteExtends (tr.HonestBlocksAt H) e.msg B) :
    Compatible (tr.HonestBlocksAt H) B O := by
  exact KernelProof.target_compatible_later_origin_before_at hp ho hri hrb hlm hsupport

end Consensus.Goldilocks.Healing.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighVote
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginCompare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.VoteReceipt

public section

/-! # Strong induction for retained high-origin votes

The finite domain reduction is an explicit input, so this induction stays below
the public ResetFacts wrappers. Comparisons consume only strictly earlier votes.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- The retained-vote induction, given the independent finite held-target domain. -/
theorem high_origin_votes_of_domain_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hdomain : ∀ {x y v : Fin sp.n} {r i q m : Nat}
      {B S : SA.Blk sp.n (List (FG.Att sp.n))},
      x ∈ H (tr.time r) → y ∈ H (tr.time i) →
      B ∈ (tr.state x r).fg.tree → tr.time r ≤ b →
      ∀ {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))},
      SA.CastAt tr.projAC y i ell e → tr.time i ≤ b →
      (Anc (tr.HonestBlocksAt H) ell.frame.F B →
        B ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) →
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
        B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot)) :
    ∀ k, tr.time k ≤ b → ∀ x i j B, HighOrigin tr H g x i j B → tr.time i ≤ b →
      ∀ y ell e, y ∈ H (tr.time k) → SA.CastAt tr.projAC y k ell e → j < e.msg.slot →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkb x i j B ho hib y ell e hy hc hj
    have prior : ∀ x₀ i₀ j₀ B₀, HighOrigin tr H g x₀ i₀ j₀ B₀ → tr.time i₀ ≤ b →
        ∀ z c e', c < k → z ∈ H (tr.time c) → tr.time c ≤ b →
          SA.VoteAt tr.projAC z c e' → j₀ < e'.msg.slot →
            SA.VoteExtends (tr.HonestBlocksAt H) e'.msg B₀ := by
      rintro x₀ i₀ j₀ B₀ ho₀ hi₀ z c e' hck hz hcb ⟨ell', hc'⟩ hj'
      exact ih c hck hcb x₀ i₀ j₀ B₀ ho₀ hi₀ z ell' e' hz hc' hj'
    have hslot := (Compose.Growing.castAt_spec_at hp.run hp.noColl hy hc).2.1
    have hts : sp.ts e.msg.slot ≤ tr.time k :=
      (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg k) _).mpr (by rw [hslot])
    have hact : sp.ts (j + 1 : Nat) ≤ tr.time k :=
      ((SA.ts_le_iff sp).mpr (by omega)).trans hts
    have compare : ∀ z d n O, d < k → HighOrigin tr H g z d n O →
        Compatible (tr.HonestBlocksAt H) B O := by
      intro z d n O hd hO
      exact origins_compatible_before_at hp prior ho hib
        (Or.inr fun c hct => not_le.mp fun hkc =>
          (not_lt_of_ge (hact.trans (hp.run.time_mono hkc))) hct)
        hO ((hp.run.time_mono hd.le).trans hkb) hd
    have pair : ∀ z d n O, d < k → HighOrigin tr H g z d n O →
        ∀ z' d' n' O', d' < k → HighOrigin tr H g z' d' n' O' →
          Compatible (tr.HonestBlocksAt H) O O' := by
      intro z d n O hd hO z' d' n' O' hd' hO'
      exact origins_compatible_before_at hp prior hO ((hp.run.time_mono hd.le).trans hkb)
        (Or.inl hd) hO' ((hp.run.time_mono hd'.le).trans hkb) hd'
    have hvi := hdomain ho.1 hy (highOrigin_mem_at hp.run hp.noColl ho) hib hc hkb
      (hp.high_origin_held_at_vote_at ho hib hy hc hkb hj) ho hib hj
      (Or.inl .refl) compare compare pair
    exact high_vote_extends_of_domain_at hp ho hib hy hc hkb hj hvi
      (fun z q e' hq hv hs => prior x i j B ho hib z q e' hq
        (Compose.Growing.hVoteAt_iff.1 hv).1 ((hp.run.time_mono hq.le).trans hkb)
        (Compose.Growing.hVoteAt_iff.1 hv).2 hs)

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

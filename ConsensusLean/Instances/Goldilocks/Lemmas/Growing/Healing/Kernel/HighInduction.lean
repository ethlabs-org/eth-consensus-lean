module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighVote
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginCompare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.VoteReceipt
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift

public section

/-! # Strong induction for retained high-origin votes

The finite domain reduction is an explicit input, so this induction stays below
the public ResetFacts wrappers. Comparisons consume only strictly earlier votes.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

/-- The retained-vote induction, given the independent finite held-target domain. -/
theorem KernelProof.high_origin_votes_of_domain_before_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    (hdomain : ∀ {x y v : Fin sp.n} {r i q m : Nat}
      {B S : AC.Blk sp.n (List (FG.Att sp.n))},
      x ∈ H (tr.time r) → y ∈ H (tr.time i) →
      B ∈ (tr.state x r).fg.tree → tr.time r ≤ b →
      ∀ {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))},
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
      Anc (tr.HonestBlocksAt H) B ell.frame.F ∨
        B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot)) :
    ∀ k, tr.time k ≤ b → ∀ x i j B, HighOrigin tr H g x i j B → tr.time i ≤ b →
      ∀ y ell e, y ∈ H (tr.time k) → AC.CastAt tr.projAC y k ell e → j < e.msg.slot →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  have hrun := hp.run
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkb x i j B ho hib y ell e hy hc hj
    have prior : ∀ x₀ i₀ j₀ B₀, HighOrigin tr H g x₀ i₀ j₀ B₀ → tr.time i₀ ≤ b →
        ∀ z c e', c < k → z ∈ H (tr.time c) → tr.time c ≤ b →
          AC.VoteAt tr.projAC z c e' → j₀ < e'.msg.slot →
            AC.VoteExtends (tr.HonestBlocksAt H) e'.msg B₀ := by
      rintro x₀ i₀ j₀ B₀ ho₀ hi₀ z c e' hck hz hcb ⟨ell', hc'⟩ hj'
      exact ih c hck hcb x₀ i₀ j₀ B₀ ho₀ hi₀ z ell' e' hz hc' hj'
    have hslot := (Compose.Growing.castAt_spec_at hrun hp.noColl hy hc).2.1
    have hts : sp.ts e.msg.slot ≤ tr.time k :=
      (AC.ts_le_iff_le_slot sp (hrun.time_nonneg k) _).mpr (by rw [hslot])
    have hact : sp.ts (j + 1 : Nat) ≤ tr.time k :=
      ((AC.ts_le_iff sp).mpr (by omega)).trans hts
    have compare : ∀ z d n O, d < k → HighOrigin tr H g z d n O →
        Compatible (tr.HonestBlocksAt H) B O := by
      intro z d n O hd hO
      exact KernelProof.origins_compatible_before_at hp prior ho hib
        (Or.inr fun c hct => not_le.mp fun hkc =>
          (not_lt_of_ge (hact.trans (hrun.time_mono hkc))) hct)
        hO ((hrun.time_mono hd.le).trans hkb) hd
    have pair : ∀ z d n O, d < k → HighOrigin tr H g z d n O →
        ∀ z' d' n' O', d' < k → HighOrigin tr H g z' d' n' O' →
          Compatible (tr.HonestBlocksAt H) O O' := by
      intro z d n O hd hO z' d' n' O' hd' hO'
      exact KernelProof.origins_compatible_before_at hp prior hO ((hrun.time_mono hd.le).trans hkb)
        (Or.inl hd) hO' ((hrun.time_mono hd'.le).trans hkb) hd'
    have hvi := hdomain (hrun.antitone (le_max_right _ _) ho.1) hy
      (highOrigin_mem_at hrun hp.noColl ho) hib hc hkb
      (hp.high_origin_held_at_vote_at ho hib hy hc hkb hj) ho hib hj
      (Or.inl .refl) compare compare pair
    exact KernelProof.high_vote_extends_of_domain_at hp ho hy hc hkb hj hvi
      (fun z q e' hq hv hs => prior x i j B ho hib z q e' hq
        (Compose.Growing.hVoteAt_iff.1 hv).1 ((hrun.time_mono hq.le).trans hkb)
        (Compose.Growing.hVoteAt_iff.1 hv).2 hs)

end Consensus.Goldilocks.Healing.Growing

end

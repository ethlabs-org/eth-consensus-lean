module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed

public section

/-! # Goldilocks Healing: H.2 (ii), persistent inclusion after a unanimous honest proposal

workbench `h2-open-items.md` §7: the unanimous batch of slot `p` propagates to every later honest
vote (§7.1: `(P, p)` is protected by P3, so `h2_votes_continue`); every surviving lock image
compares with `P` (§7.2, `h2_locks_compare`, open); the record read by `ac_confirmed` extends `P`
(§§7.3–7.4, `h2_record_extends`, open), and so does the head (§7.5, `h2_head_extends`, open);
`ac_confirmed` is their deepest common ancestor (`anc_acConfirmed`, from the frame lemma
`anc_acConfirmed_of_frame` of `AC/Confirmed`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g t₀ : Time}

/-- The reads of H.2 (ii): calls of honest nodes from `t_p + 6Δ` on (at `t_p + 6Δ` itself,
from the node's tick there on). -/
def LateRead (tr : SATrace sp FGP ro) (p : Nat) (y : Fin sp.n) (j : Nat)
    (ℓ : ACLabel (goldilocksSA sp FGP ro)) : Prop :=
  tr.CallAt y j ℓ ∧ sp.ts p + 6 * sp.Δ ≤ tr.time j ∧
    (tr.time j = sp.ts p + 6 * sp.Δ →
      ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j)

/-- **§7.2, all surviving lock images compare with `P`**: at every honest cut from `t_p` on,
every stored lock is on a block compatible with `P` (a label `< p` through its clean raw origin
and §6.1; label `p` through an honest supporter of `P`; a later label through an honest
supporter of a vote extending `P`, §7.1). -/
theorem h2_locks_compare (hI : InclusionRun tr H U g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : sp.toParams.proposer p ∈ H) (hP : HonestProposal tr (sp.toParams.proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ))
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P) :
    ∀ y ∈ H, ∀ i, sp.ts p ≤ tr.time i → ∀ l ∈ (tr.state y i).locks, ∀ L ∈ U, L.root = l.block →
      Compatible U L P := by
  sorry

/-- **§§7.3–7.4, the record**: at every late read, the record that `ac_confirmed` reads (the
latest confirmed block in the frame, else `Φ.F`) extends `P` (the first test at `t_p + 6Δ`
leaves a record extending `P` or `P ⪯ Φ.F`; every later receipt, tick and record write keeps
it). -/
theorem h2_record_extends (hI : InclusionRun tr H U g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : sp.toParams.proposer p ∈ H) (hP : HonestProposal tr (sp.toParams.proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    (hlocks : ∀ y ∈ H, ∀ i, sp.ts p ≤ tr.time i → ∀ l ∈ (tr.state y i).locks, ∀ L ∈ U,
      L.root = l.block → Compatible U L P) :
    ∀ y ∈ H, ∀ j ℓ, LateRead tr p y j ℓ →
      Anc U P ((lookup ℓ.frame (tr.post j).latestConfirmed).getD ℓ.frame.F) := by
  sorry

/-- **§7.5, full heads**: at every late read, the head extends `P` (`P ⪯ fc_root`, or the
anchor compares with `P` by §7.2 and the latest view's honest votes, all extending `P`, give
every child toward `P` a strict majority). -/
theorem h2_head_extends (hI : InclusionRun tr H U g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : sp.toParams.proposer p ∈ H) (hP : HonestProposal tr (sp.toParams.proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P)
    (hlocks : ∀ y ∈ H, ∀ i, sp.ts p ≤ tr.time i → ∀ l ∈ (tr.state y i).locks, ∀ L ∈ U,
      L.root = l.block → Compatible U L P) :
    ∀ y ∈ H, ∀ j ℓ, LateRead tr p y j ℓ → Anc U P (acHead sp (tr.post j) ℓ.frame (tr.time j)) := by
  sorry

/-- **The confirmed tip extends a block both of its inputs extend** (`ac_confirmed` is the
deepest common ancestor of the record and the head in the frame's tree). -/
theorem anc_acConfirmed (hI : InclusionRun tr H U g t₀) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ℓ) {P : Blk sp.n FGP}
    (hC : Anc U P ((lookup ℓ.frame (tr.post j).latestConfirmed).getD ℓ.frame.F))
    (hH : Anc U P (acHead sp (tr.post j) ℓ.frame (tr.time j))) :
    Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)) := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hI.run.localRun hy hc
  exact anc_acConfirmed_of_frame hI.run.localRun.coherent hΦ hΦU hC hH

/-- **H.2 (ii), §7**: for an honest proposal `P` of slot `p` at `t_p ≥ t₀ + 2Θ + 8Δ` with the
locks settled from `t_{p−1}`, if every honest vote of slot `p` is `P`, then at every call of an
honest node from `t_p + 6Δ` on (at `t_p + 6Δ` itself, from its tick there on),
`P ⪯ ac_confirmed` after the call. -/
theorem h2_proposal_confirmed (hI : InclusionRun tr H U g t₀) {p : Nat} {P : Blk sp.n FGP}
    (hpH : sp.toParams.proposer p ∈ H) (hP : HonestProposal tr (sp.toParams.proposer p) p P)
    (hp : t₀ + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ))
    (hunan : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root) :
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
      (tr.time j = sp.ts p + 6 * sp.Δ →
        ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)) := by
  have hΔ := sp.toParams.hΔ
  have hΘ := Θ_nonneg sp
  -- `P` is a frame block, protected by P3; §7.1 propagates the unanimous batch
  have hPU : P ∈ U := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, j, -, ⟨ℓ, hc, hcall⟩, -⟩ := hP
    exact (frameIn_of_callAt hI.run.localRun hpH hc).2
      ((accept_new sp hI.run.localRun hpH ⟨ℓ, hc, hcall⟩).1 ℓ hc)
  have hself : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → VoteExtends U e.msg P :=
    fun x hx j e hv hs => ⟨P, hPU, (hunan x hx j e hv hs).symm, Relation.ReflTransGen.refl⟩
  have hcont := h2_votes_continue hI (Or.inr (Or.inr ⟨hpH, hP, hp, hunan⟩)) le_rfl
    (by linarith) hself
  have hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P := by
    intro x hx j e hv hle
    rcases Nat.eq_or_lt_of_le hle with h | h
    · exact hself x hx j e hv h.symm
    · exact votesExtendAfter_iff.1 hcont x hx j e hv h
  have hlocks := h2_locks_compare hI hpH hP hp hset hvotes
  intro y hy j ℓ hc ht htick
  have hr : LateRead tr p y j ℓ := ⟨hc, ht, htick⟩
  exact anc_acConfirmed hI hy hc (h2_record_extends hI hpH hP hp hvotes hlocks y hy j ℓ hr)
    (h2_head_extends hI hpH hP hp hvotes hlocks y hy j ℓ hr)

end Consensus.Goldilocks.SA

end

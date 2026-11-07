module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Confirmed
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the steps of H.1

H.1 decomposed into the steps of its paper proof (claims H.1, proof shape) over a
`StandaloneRun` (H.1's premises), with `r = r_AC(ḡ)`: a slot `j` is `≥ r` exactly when
`ḡ + 4Δ ≤ t_j`. The steps live in sibling modules:

* `Setting.lean`: the premises and the steps' vocabulary;
* `SlowLock.lean`: slow lock provenance (the fast case is `fast_lock_provenance`);
* `Compat.lean`: results of one slot `≥ r` are compatible;
* `Trivial.lean`: viability and `Carry` under trivial frames, the honest batch, and the fast
  origin's transfer to the votes (`votes_continue`, `fast_origin_transfer_votes`);
* `Transfer.lean`: the transfer at proposals, the transfer of slow origins, and unanimity.

This module has the rest: `good_origin_transfer`; the drain (`drain_tight`: a lock live at a
slot `σ` with `t_σ ≥ ḡ + 8kΔ` sits below a good origin) and settled locks from a slot start
(`locks_settled_slot`), with `drain` and `locks_settled` at `ḡ + 2Θ` as corollaries;
`proposal_confirmed_core` (the confirmed tip); and the assembly: H.1's conclusions for one
honest proposal from settled locks and `t_p ≥ ḡ + 8Δ` (`ac_healing_standalone_of_settled`),
at `t_p ≥ ḡ + (8k + 4)Δ` (`ac_healing_standalone_of_parent_tight`, settled from
`t_{p−1} ≥ ḡ + 8kΔ`) and at `t_p ≥ ḡ + 2Θ + 8Δ` (`ac_healing_standalone_of_parent`). The
unanimity and confirmation steps need of the slot only `t_p ≥ ḡ + 8Δ` (their `_core` forms). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {proposer : Nat → Fin sp.n}

/-! ## A slow origin whose window is `≥ r` transfers -/

/-- **Transfer of a good origin**: a good origin is carried by every honest vote and proposal head
of a later slot. -/
theorem good_origin_transfer (hS : StandaloneRun tr H U proposer g) {B : Blk sp.n FGP} {j : Nat}
    (hB : GoodOrigin tr H g B j) :
    VotesExtendAfter tr H U j B ∧ ProposalsExtendAfter tr H U j B := by
  refine ⟨?_, origin_transfer_proposals hS hB⟩
  rcases goodOrigin_iff.1 hB with ⟨x, hx, i, CV, hfl, hs⟩ | ⟨x, hx, i, hsl, hs⟩
  · exact fast_origin_transfer_votes hS hx hfl hs
  · exact slow_origin_transfer_votes hS hx hsl hs

/-! ## Drain -/

/-- **Drain, from `ḡ + 8kΔ`.** A lock that an honest node stores, live at a slot `σ` with
`t_σ ≥ ḡ + 8kΔ` (`σ ≤ j + k` for its label `j`), sits below a good origin of its label: its
label is at least `σ − k`, so a fast one has `t_j ≥ ḡ + 4kΔ` and a slow one has
`t_{j−k+1} ≥ ḡ + 4Δ`. -/
theorem drain_tight (hS : StandaloneRun tr H U proposer g)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {l : Lock}
    (hl : l ∈ (tr.state y i).locks) {σ : Nat} (hσ : σ ≤ l.slot + sp.k)
    (hT : gbar g + 8 * (sp.k : Time) * sp.Δ ≤ sp.ts σ) :
    ∃ B, (∃ L ∈ U, L.root = l.block ∧ Anc U L B) ∧ GoodOrigin tr H g B l.slot := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  simp only [SAParams.ts] at hT
  have hlk := mul_nonneg hΔ.le (show (0 : Int) ≤ l.slot + sp.k - σ by omega)
  cases hf : l.fast
  · obtain ⟨j, -, B, hsl, hLB⟩ := slow_lock_provenance hr hy i l hl hf
    refine ⟨B, hLB, goodOrigin_iff.2 (Or.inr ⟨y, hy, j, hsl, ?_⟩)⟩
    simp only [SAParams.ts]
    linarith
  · obtain ⟨j, -, B, CV, hfl, hLB⟩ := fast_lock_provenance hr hy i l hl hf
    refine ⟨B, hLB, goodOrigin_iff.2 (Or.inl ⟨y, hy, j, CV, hfl, ?_⟩)⟩
    have := mul_nonneg hΔ.le (show (0 : Int) ≤ sp.k - 1 by omega)
    simp only [SAParams.ts]
    linarith

/-- **Drain.** A lock that an honest node stores, live at a slot `σ` with
`t_σ ≥ ḡ + 2Θ` (`σ ≤ j + k` for its label `j`), sits below a good origin of its label
(`drain_tight`: `2Θ ≥ 8kΔ`). -/
theorem drain (hS : StandaloneRun tr H U proposer g)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {l : Lock}
    (hl : l ∈ (tr.state y i).locks) {σ : Nat} (hσ : σ ≤ l.slot + sp.k)
    (hT : gbar g + 2 * Θ sp ≤ sp.ts σ) :
    ∃ B, (∃ L ∈ U, L.root = l.block ∧ Anc U L B) ∧ GoodOrigin tr H g B l.slot :=
  drain_tight hS hy hl hσ (by have := sp.toParams.hΔ; unfold Θ at hT; linarith)

/-- **Settled locks from a slot start**: from `t_{σ₀} ≥ ḡ + 8kΔ` on, every lock live at an
honest node is carried by every later honest duty (a call at `t ≥ t_{σ₀}` is of a slot
`≥ σ₀`, so `drain_tight` applies at its slot). -/
theorem locks_settled_slot (hS : StandaloneRun tr H U proposer g) {σ₀ : Nat}
    (h : gbar g + 8 * (sp.k : Time) * sp.Δ ≤ sp.ts σ₀) : LocksSettled tr H U (sp.ts σ₀) := by
  have hr := hS.run.localRun
  rw [locksSettled_iff]
  intro y hy i hi l hl hlive L hL hLr
  have hσ : gbar g + 8 * (sp.k : Time) * sp.Δ ≤ sp.ts (sp.slot (tr.time i)) :=
    h.trans ((ts_le_iff sp).2 ((ts_le_iff_le_slot sp (hr.time_nonneg i) _).1 hi))
  obtain ⟨B, ⟨L', hL', hL'r, hLB⟩, hgood⟩ := drain_tight hS hy hl hlive hσ
  obtain rfl : L' = L := hr.coherent.1 hL' hL (hL'r.trans hLr.symm)
  obtain ⟨hv, hp⟩ := good_origin_transfer hS hgood
  refine ⟨votesExtendAfter_iff.2 fun x hx j e he hs => ?_, proposalsExtendAfter_iff.2
    fun x hx j ℓ m d pay hc hcall ht hm hd =>
      hLB.trans (proposalsExtendAfter_iff.1 hp x hx j ℓ m d pay hc hcall ht hm hd)⟩
  obtain ⟨Hd, hHd, hHdr, hBHd⟩ := votesExtendAfter_iff.1 hv x hx j e he hs
  exact ⟨Hd, hHd, hHdr, hLB.trans hBHd⟩

/-- **Settled locks**: from `ḡ + 2Θ + 4Δ` on, every lock live at an honest node is
carried by every later honest duty (`locks_settled_slot` at the slot of `ḡ + 2Θ + 4Δ`, which
starts after `ḡ + 2Θ ≥ ḡ + 8kΔ`). -/
theorem locks_settled (hS : StandaloneRun tr H U proposer g) :
    LocksSettled tr H U (gbar g + 2 * Θ sp + 4 * sp.Δ) := by
  have hΔ := sp.toParams.hΔ
  have hX : 0 ≤ gbar g + 2 * Θ sp + 4 * sp.Δ := by linarith [gbar_nonneg g, Θ_nonneg sp]
  have h1 : ¬ sp.ts ((sp.slot (gbar g + 2 * Θ sp + 4 * sp.Δ) : Nat) + 1 : Int) ≤
      gbar g + 2 * Θ sp + 4 * sp.Δ := by
    rw [ts_le_iff_le_slot sp hX]; omega
  have h2 : sp.ts ((sp.slot (gbar g + 2 * Θ sp + 4 * sp.Δ) : Nat) + 1 : Int) =
      sp.ts (sp.slot (gbar g + 2 * Θ sp + 4 * sp.Δ)) + 4 * sp.Δ := by
    simp only [SAParams.ts]; ring
  have hΘ : 2 * Θ sp = 8 * (sp.k : Time) * sp.Δ + 8 * sp.Δ := by unfold Θ; ring
  exact (locks_settled_slot hS (by linarith [not_le.1 h1])).mono
    ((ts_le_iff_le_slot sp hX _).2 le_rfl)

/-! ## The honest proposal -/

/-- **The confirmed tip**, from `t_p ≥ ḡ + 8Δ`: when every honest vote of slot `p` and later
extends the honest proposal `P` and the locks are settled, `P ⪯ ac_confirmed` at every honest
call from `t_p + 6Δ` on (at `t_p + 6Δ`, from the tick there): the slot-`p` result is exactly
`P` and is not vetoed (labels `p − 1`, `p`, `p + 1` as in the claims' proof shape), afterwards
the record is replaced only by a block extending it or compatible with `P`, and the head
extends `P`. -/
theorem proposal_confirmed_core (hS : StandaloneRun tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposal tr (proposer p) p P)
    (hp : gbar g + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ))
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P) :
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
      (tr.time j = sp.ts p + 6 * sp.Δ →
        ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)) := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hΘ := Θ_nonneg sp
  have hg0 := gbar_nonneg g
  have hexact := proposal_votes_core hS hpH hP hp hset
  have hPU : P ∈ U := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, j, -, ⟨ℓ, hc, hcall⟩, -⟩ := hP
    exact (frameIn_of_callAt hr hpH hc).2 ((accept_new sp hr hpH ⟨ℓ, hc, hcall⟩).1 ℓ hc)
  intro y hy j ℓ hc ht htick
  -- the node's tick at `t_p + 6Δ`, at or before the call
  obtain ⟨k, hkj, ℓk, hck, hcallk, htk⟩ : ∃ k ≤ j, ∃ ℓk : ACLabel (goldilocksSA sp FGP ro),
      tr.CallAt y k ℓk ∧ ℓk.call = .tick ∧ tr.time k = sp.ts p + 6 * sp.Δ := by
    rcases eq_or_lt_of_le ht with heq | hlt
    · obtain ⟨k, hkj, ℓk, hck, hcall, htk⟩ := htick heq.symm
      exact ⟨k, hkj, ℓk, hck, hcall, htk.trans heq.symm⟩
    · obtain ⟨k, ℓk, hck, hcall, htk⟩ := hS.driven.tick y hy (sp.ts p + 6 * sp.Δ)
        (by linarith) ⟨4 * (p : Int) + 6, by simp only [SAParams.ts]; ring⟩
        (hS.awake hy (by linarith))
      refine ⟨k, ?_, ℓk, hck, hcall, htk⟩
      by_contra h
      have := hr.time_mono (le_of_lt (not_le.1 h))
      linarith
  obtain ⟨R, hR, hRr, hPR⟩ :=
    record_extends_core hS hpH hP (by linarith) hset hexact hvotes hy hck hcallk htk j ℓ hc hkj
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
  have hPt := (proposal_mem_tree hS hpH hP (by linarith) hy hc (by linarith)).1
  have hlocks :=
    liveLock_compatible_core hS (by linarith) hset hexact hvotes hPU hy hc ht (Or.inr rfl)
  rw [show tr.state y (j + 1) = tr.post j by simp [Trace.state, hc.1, hc.2]] at hlocks
  exact anc_acConfirmed_of_record hr.coherent hΦ hΦU hR hRr hPR
    (head_extends hS (by linarith) hvotes hy hc ht hPt hlocks)

/-- **The confirmed tip** from `t_p ≥ ḡ + 2Θ + 8Δ` (`proposal_confirmed_core`). -/
theorem proposal_confirmed (hS : StandaloneRun tr H U proposer g) {p : Nat} {P : Blk sp.n FGP}
    (hpH : proposer p ∈ H) (hP : HonestProposal tr (proposer p) p P)
    (hp : gbar g + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ))
    (hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P) :
    ∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
      (tr.time j = sp.ts p + 6 * sp.Δ →
        ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j)) :=
  proposal_confirmed_core hS hpH hP (by linarith [Θ_nonneg sp]) hset hvotes

/-! ## Assembly -/

/-- **H.1 from settled locks** (claims H.1, proof shape): H.1's conclusions (i) and (ii) for an
honest proposal `P` of slot `p` with `t_p ≥ ḡ + 8Δ` once the locks are settled from `t_{p−1}`.
The threshold of H.1 is where the drain settles the locks (`ac_healing_standalone_of_parent`,
`ac_healing_standalone_of_parent_tight`). -/
theorem ac_healing_standalone_of_settled (hS : StandaloneRun tr H U proposer g) {p : Nat}
    {P : Blk sp.n FGP} (hpH : proposer p ∈ H)
    (hP : HonestProposal tr (proposer p) p P)
    (hp : gbar g + 8 * sp.Δ ≤ sp.ts p)
    (hset : LocksSettled tr H U (sp.ts p - 4 * sp.Δ)) :
    (∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root) ∧
    (∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
      (tr.time j = sp.ts p + 6 * sp.Δ →
        ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j))) := by
  have hΔ := sp.toParams.hΔ
  have hi := proposal_votes_core hS hpH hP hp hset
  have hPU : P ∈ U := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, j, -, ⟨ℓ, hc, hcall⟩, -⟩ := hP
    exact (frameIn_of_callAt hS.run.localRun hpH hc).2
      ((accept_new sp hS.run.localRun hpH ⟨ℓ, hc, hcall⟩).1 ℓ hc)
  have hself : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → VoteExtends U e.msg P :=
    fun x hx j e hv hs => ⟨P, hPU, (hi x hx j e hv hs).symm, Relation.ReflTransGen.refl⟩
  have hcont := votes_continue hS (m := p) (by linarith) hself
  have hvotes : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → p ≤ e.msg.slot → VoteExtends U e.msg P := by
    intro x hx j e hv hle
    rcases Nat.eq_or_lt_of_le hle with h | h
    · exact hself x hx j e hv h.symm
    · exact votesExtendAfter_iff.1 hcont x hx j e hv h
  exact ⟨hi, proposal_confirmed_core hS hpH hP hp hset hvotes⟩

/-- **H.1 for an honest proposal with its parent, at `t_p ≥ ḡ + (8k + 4)Δ`**: the locks are
settled from the slot start `t_{p−1} = t_p − 4Δ ≥ ḡ + 8kΔ` (`locks_settled_slot`). -/
theorem ac_healing_standalone_of_parent_tight (hS : StandaloneRun tr H U proposer g) {p : Nat}
    {P : Blk sp.n FGP} (hpH : proposer p ∈ H)
    (hP : HonestProposal tr (proposer p) p P)
    (hp : gbar g + (8 * (sp.k : Time) + 4) * sp.Δ ≤ sp.ts p) :
    (∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root) ∧
    (∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
      (tr.time j = sp.ts p + 6 * sp.Δ →
        ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j))) := by
  have hΔ := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  have hk : (2 : Time) ≤ sp.k := by exact_mod_cast sp.two_le_k
  have hkΔ := mul_le_mul_of_nonneg_right hk hΔ.le
  have hp1 : 1 ≤ p := by
    have h0 : sp.ts 0 = 0 := by simp [SAParams.ts]
    have : (0 : Int) < p := (ts_lt_iff sp).1 (by rw [h0]; linarith)
    omega
  have hts : sp.ts ((p - 1 : Nat) : Int) = sp.ts p - 4 * sp.Δ := by
    rw [show ((p - 1 : Nat) : Int) = (p : Int) - 1 by omega, ts_sub_one]
  have hset := locks_settled_slot hS (σ₀ := p - 1) (by rw [hts]; linarith)
  rw [hts] at hset
  exact ac_healing_standalone_of_settled hS hpH hP (by linarith) hset

/-- **H.1 for an honest proposal with its parent** (claims H.1, proof shape): H.1's conclusions (i)
and (ii) for an honest proposal whose parent is the head of its `ac_proposal`. -/
theorem ac_healing_standalone_of_parent (hS : StandaloneRun tr H U proposer g) {p : Nat}
    {P : Blk sp.n FGP} (hpH : proposer p ∈ H)
    (hP : HonestProposal tr (proposer p) p P)
    (hp : gbar g + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p) :
    (∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root) ∧
    (∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
      (tr.time j = sp.ts p + 6 * sp.Δ →
        ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j))) := by
  have hΘ := Θ_nonneg sp
  exact ac_healing_standalone_of_settled hS hpH hP (by linarith)
    ((locks_settled hS).mono (by linarith))

end Consensus.Goldilocks.SA

end

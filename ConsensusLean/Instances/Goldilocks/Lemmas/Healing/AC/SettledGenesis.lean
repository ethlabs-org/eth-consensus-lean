module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlotZero
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Steps
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalCore
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: settled locks from genesis

On a run synchronous from the start (`g ≤ 0`, so `ḡ = 0`) with trivial frames, every lock an
honest node stores is on genesis or below a good origin of its label
(`stored_lock_genesis_or_good_originU`):

* a fast or optimistic lock of a label `j ≥ 1`, and a slow lock of a label `j ≥ k`, have a good
  origin (`t_j ≥ 4Δ`, resp. `t_{j−k+1} ≥ 4Δ`);
* a fast or optimistic lock of label `0` is extended by an honest slot-0 vote, which heads genesis
  (`slot_zero_vote_headU`), so it is on genesis;
* a slow lock of a label below `k` is never written: its block is on the confirmation path of the
  update's result, which excludes genesis, and is below the slot-0 result (label `0`) or the saved
  slot-0 result (labels `1, …, k − 1`), which are genesis (`slot_zero_result_genesisU`,
  `slot_zero_saved_genesisU`).

So the locks are settled at every time (`locks_settled_of_sync_startU`), without the drain, and
H.1's conclusions hold for every honest proposal of a slot `p ≥ 2` (`ac_healing_of_sync_startU`),
the floor-`p` seam's own bound `ḡ + 8Δ ≤ t_p`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {proposer : Nat → Fin sp.n}

/-- **Every stored lock is genesis or below a good origin**, on a run synchronous from the
start. -/
theorem stored_lock_genesis_or_good_originU {m : WriteMode} (hw : m.width = sp.k)
    {u : Nat → Set Lock} (hS : StandaloneRunU m u tr H U proposer g) (hg : g ≤ 0)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {l : Lock} (hl : l ∈ (tr.state y i).locks) :
    l.block = sp.genesisRoot ∨
      ∃ B, (∃ L ∈ U, L.root = l.block ∧ Anc U L B) ∧ GoodOriginW m.width tr H g B l.slot := by
  simp only [hw, goodOriginW_k]
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hg0 : gbar g = 0 := max_eq_right hg
  cases hf : l.fast
  · obtain ⟨j, -, B, hsl, hLB⟩ := slow_lock_provenanceM hr hy i l hl hf
    rw [hw, slowLockAtW_k] at hsl
    by_cases hk : sp.k ≤ l.slot
    · refine Or.inr ⟨B, hLB, goodOrigin_iff.2 (Or.inr ⟨y, hy, j, hsl, ?_⟩)⟩
      rw [hg0]
      simp only [SAParams.ts]
      have := mul_nonneg hΔ.le (show (0 : Int) ≤ (l.slot : Int) - sp.k by omega)
      linarith
    · exfalso
      obtain ⟨ℓ, C, hupd, hconf, hdeep⟩ := hsl
      obtain ⟨⟨hBt, hBg, hBC⟩, -, hwin⟩ := (deepest_mem hdeep).1
      obtain ⟨-, hΦU⟩ := frameIn_of_callAtU hr hy hupd.1
      have ht : 2 * sp.Δ ≤ tr.time j := by
        rw [hupd.2.2.1]; simp only [SAParams.ts]
        have := mul_nonneg hΔ.le (show (0 : Int) ≤ l.slot by omega)
        linarith
      rcases Nat.eq_zero_or_pos l.slot with h0 | hpos
      · rw [h0] at hconf
        have hCg := slot_zero_result_genesisU hS hg hy hupd.1 ht hconf
        have hCt := (deepest_mem hconf).1.1
        exact hBg (by
          rw [eq_of_anc_genesisU hr hy hupd.1 (hΦU hCt) hCg (Anc.mono hΦU hBC)]
          exact hCg)
      · obtain ⟨S, hSt, hSr, hBS⟩ := hwin 0 (by omega) (by exact_mod_cast hpos)
        have hSg := slot_zero_saved_genesisU hS hg hy hSr
        exact hBg (by
          rw [eq_of_anc_genesisU hr hy hupd.1 (hΦU hSt) hSg (Anc.mono hΦU hBS)]
          exact hSg)
  · obtain ⟨j, -, B, CV, hfl, L, hL, hLr, hLB⟩ := fast_lock_provenanceU hr hy i l hl hf
    rcases Nat.eq_zero_or_pos l.slot with h0 | hpos
    · left
      obtain ⟨z, hz, j', e, hv, hes, Hd, hHd, hHdr, hBHd⟩ :=
        fastLock_honest_voteU hS.run hS.two_faulty_lt hy hfl
      rw [h0] at hes
      have hHdg : Hd.root = sp.genesisRoot := hHdr.trans (slot_zero_vote_headU hS hz hv hes)
      obtain ⟨ℓv, hcv, -⟩ := hv
      rw [← hLr, eq_of_anc_genesisU hr hz hcv hHd hHdg (hLB.trans hBHd), hHdg]
    · refine Or.inr ⟨B, ⟨L, hL, hLr, hLB⟩, goodOrigin_iff.2 (Or.inl ⟨y, hy, j, CV, hfl, ?_⟩)⟩
      rw [hg0]
      simp only [SAParams.ts]
      have := mul_nonneg hΔ.le (show (0 : Int) ≤ (l.slot : Int) - 1 by omega)
      linarith

/-- **Settled from genesis**: on a run synchronous from the start, the locks are settled at
every time. -/
theorem locks_settled_of_sync_startU {m : WriteMode} (hw : m.width = sp.k)
    {u : Nat → Set Lock} (hS : StandaloneRunU m u tr H U proposer g) (hg : g ≤ 0) :
    LocksSettledU u tr H U 0 := by
  have hr := hS.run.localRun
  rw [locksSettledU_iff]
  intro y hy i _ l hl _ L hL hLr
  rcases stored_lock_genesis_or_good_originU hw hS hg hy hl with
    hgen | ⟨B, ⟨L', hL', hL'r, hL'B⟩, hB⟩
  · have hLg : L.root = sp.genesisRoot := hLr.trans hgen
    -- every block of an honest frame is above `L`, the frames' genesis
    have key : ∀ x ∈ H, ∀ k (ℓ : ACLabel (goldilocksSA sp FGP ro)), tr.CallAt x k ℓ →
        ∀ X ∈ ℓ.frame.tree, Anc U L X := by
      intro x hx k ℓ hc X hX
      obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hx hc
      have hFL : ℓ.frame.F = L :=
        hr.coherent.1 (hΦU hΦ.rooted.1) hL ((hS.trivial x hx k ℓ hc).1.trans hLg.symm)
      rw [← hFL]
      exact Anc.mono hΦU (hΦ.rooted.2 X hX)
    refine ⟨votesExtendAfter_iff.2 fun x hx k e hv _ => ?_,
      proposalsExtendAfterU_iff.2 fun x hx k ℓ m d pay hc _ _ _ hprop => ?_⟩
    · obtain ⟨ℓ, hc, he⟩ := hv
      obtain ⟨Hd, hHd, hHdr, -⟩ := honest_head_frameU hr hx ⟨hc, he⟩
      exact ⟨Hd, (frameIn_of_callAtU hr hx hc).2 hHd, hHdr, key x hx k ℓ hc Hd hHd⟩
    · obtain ⟨-, hd⟩ := acProposal_headWith hprop
      obtain ⟨hΦ, -⟩ := frameIn_of_callAtU hr hx hc
      rw [hd]
      exact key x hx k ℓ hc _ (getHead_mem hΦ (fun _ hB => hB.1) _ _ _ _)
  · obtain rfl : L' = L := hr.coherent.1 hL' hL (hL'r.trans hLr.symm)
    obtain ⟨hv, hp⟩ := good_origin_transferU hS (goodOriginW_k.1 (hw ▸ hB))
    refine ⟨votesExtendAfter_iff.2 fun x hx k e he hs => ?_,
      proposalsExtendAfterU_iff.2 fun x hx k ℓ m d pay hc hcall ht hm hprop =>
        hL'B.trans (proposalsExtendAfterU_iff.1 hp x hx k ℓ m d pay hc hcall ht hm hprop)⟩
    obtain ⟨Hd, hHd, hHdr, hBHd⟩ := votesExtendAfter_iff.1 hv x hx k e he hs
    exact ⟨Hd, hHd, hHdr, hL'B.trans hBHd⟩

/-- **Inclusion from a synchronous start** (H.1's conclusions at `p ≥ 2`): on a run
synchronous from the start, every honest proposal of a slot `p ≥ 2` is voted by every honest node
of its slot, and is in the confirmed tip after every honest call from `t_p + 6Δ` on (at
`t_p + 6Δ` itself, from that node's tick there on). -/
theorem ac_healing_of_sync_startU {m : WriteMode} (hw : m.width = sp.k)
    {u : Nat → Set Lock} (hS : StandaloneRunU m u tr H U proposer g) (hg : g ≤ 0) {p : Nat}
    (hp : 2 ≤ p) {P : Blk sp.n FGP} (hpH : proposer p ∈ H)
    (hP : HonestProposalU u tr (proposer p) p P) :
    (∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root) ∧
    (∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
      (tr.time j = sp.ts p + 6 * sp.Δ →
        ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j))) := by
  have hΔ := sp.toParams.hΔ
  have hg0 : gbar g = 0 := max_eq_right hg
  have hp4 := mul_nonneg hΔ.le (show (0 : Int) ≤ (p : Int) - 2 by omega)
  refine ac_healing_standalone_of_settled_fromU hS hw hpH hP ?_
    (((locks_settled_of_sync_startU hw hS hg).toFrom p).mono ?_)
  · rw [hg0]; simp only [SAParams.ts]; linarith
  · simp only [SAParams.ts]; linarith

/-- **Inclusion from a synchronous start** (H.1's conclusions), for the parent's unlock. -/
theorem ac_healing_of_sync_start (hS : StandaloneRun tr H U proposer g) (hg : g ≤ 0) {p : Nat}
    (hp : 2 ≤ p) {P : Blk sp.n FGP} (hpH : proposer p ∈ H)
    (hP : HonestProposal tr (proposer p) p P) :
    (∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root) ∧
    (∀ y ∈ H, ∀ j ℓ, tr.CallAt y j ℓ → sp.ts p + 6 * sp.Δ ≤ tr.time j →
      (tr.time j = sp.ts p + 6 * sp.Δ →
        ∃ k ≤ j, ∃ ℓ', tr.CallAt y k ℓ' ∧ ℓ'.call = .tick ∧ tr.time k = tr.time j) →
      Anc U P (acConfirmed sp (tr.post j) ℓ.frame (tr.time j))) :=
  ac_healing_of_sync_startU rfl hS.toU hg hp hpH hP.toU

end Consensus.Goldilocks.SA

end

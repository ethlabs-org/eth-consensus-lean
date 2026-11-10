module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the post-drain slot and the voter's walk to the proposal

Two run-free steps of every post-drain unanimity argument:

* `post_drain_slot`: a slot `u` with `t_u ≥ R` after a reset `a > c_z` is `s + 1` with
  `ḡ ≤ t_s`, `ḡ + 2Δ ≤ t_{s+1}` and `t_{slot(ḡ)+1} + Δ ≤ t_{s+1}`;
* `voter_head_eq_proposal`: the proposer's walk from its start reaches the duty head `Q`, the
  parent of the proposal `P`, through a pivot `D`. A voter whose walk passes from its anchor
  through a block `X` that is `P` or on the pivot path, which sees `P` as the only eligible child
  of `Q` with no best child of its own, and to which every best child of the proposer on the path
  from `X` to `Q` stays best, ends its walk at `P`.

The run supplies the premises: the pivot, the voter's passage through `X`, the stop at the
parent and the transport of best children. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams Payload)

variable {sp : SAParams}

/-- **The post-drain slot**: a slot at or after the drain time of a reset after `c_z` is a
successor slot whose start is past the healing time and the join of the slot after `ḡ`. -/
theorem post_drain_slot {g a : Time} {u : Nat} (hca : cutZ sp.toParams g < a)
    (hR : drainTime sp a ≤ sp.ts u) :
    ∃ s, u = s + 1 ∧ sp.slot a + 2 * sp.k + 5 ≤ s + 1 ∧ SA.gbar g ≤ sp.ts s ∧
      SA.gbar g + 2 * sp.Δ ≤ sp.ts (s + 1 : Nat) ∧
      sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ sp.ts (s + 1 : Nat) := by
  have hDelta := sp.toParams.hΔ
  have hcut := lt_cutZ (sp := sp) g
  have hga0 := SA.gbar_nonneg g
  have ha0 : 0 ≤ a := by linarith
  have hu : sp.slot a + 2 * sp.k + 5 ≤ u := by
    rw [drainTime_eq] at hR
    exact_mod_cast (SA.ts_le_iff sp).1 hR
  obtain ⟨s, rfl⟩ : ∃ s, u = s + 1 := ⟨u - 1, by omega⟩
  have hs1 : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hg : SA.gbar g ≤ sp.ts s := by
    have hle : sp.ts (sp.slot a) + 4 * sp.Δ ≤ sp.ts s := by
      have hs : sp.ts ((sp.slot a : Int) + 1) ≤ sp.ts s :=
        (SA.ts_le_iff sp).2 (by omega)
      simpa only [SAParams.ts, mul_add, mul_one] using hs
    have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    have he : sp.ts ((sp.slot a : Int) + 1) = sp.ts (sp.slot a) + 4 * sp.Δ := by
      simp only [SAParams.ts]; ring
    rw [he] at ha'
    linarith
  refine ⟨s, rfl, hu, hg, by linarith, ?_⟩
  rw [cutZ_eq] at hca
  have hqa := (SA.ts_le_iff_le_slot sp ha0 _).1 hca.le
  have hqs : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts s :=
    (SA.ts_le_iff sp).2 (by push_cast at hqa ⊢; omega)
  linarith

/-- **The voter's walk ends at the proposal.** The proposer's walk of the full viable tree of `Φ`
from `d.start` reaches the duty head `d.head`, the parent of `P`, through the pivot `D`. A voter
of slot `s + 1` with frame `Ψ` and read point `R` whose walk passes from its anchor through `X`,
where `X` is `P` or lies between `D` and `d.head`, ends its walk at `P` when `P` is viable for it
and

* `hstep`, `hP`: `P` is its only eligible child of `d.head` and has no best child;
* `hbest`: every best child of the proposer at a block between `X` and `d.head` (exclusive), on
  the pivot path, is best for it too. -/
theorem voter_head_eq_proposal {Φ Ψ : SA.Frm sp.n (List (FG.Att sp.n))} (hΦ : FrameOK Φ)
    (hΨ : FrameOK Ψ) {A R : SA.SAState sp.n} {ti tj : Time} {s : Nat}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp A Φ ti).2 = some (d, pay)) (hslot : sp.slot ti = s + 1)
    {D X P : SA.Blk sp.n (List (FG.Att sp.n))} (hsD : Φ.Anc d.start D)
    (hXc : X = P ∨ (Φ.Anc D X ∧ Φ.Anc X d.head))
    (haX : Ψ.Anc (SA.getAnchor sp R Ψ tj) X)
    (hXend : Ψ.Anc X (SA.getHead sp R Ψ tj (Ψ.viableTree (SA.voteDomain sp R Ψ (s + 1)))
      (SA.mergedVoteView sp R Ψ (s + 1)) (((s + 1 : Nat) : Int) - 1)))
    (hPv : P ∈ Ψ.viableTree (SA.voterBlockTree sp R Ψ (s + 1)))
    (hstep : P ∈ {B | B ∈ Ψ.viableTree (SA.voterBlockTree sp R Ψ (s + 1)) ∧
        B.parent = some d.head.root ∧
        SA.goldfishEligible sp Ψ tj (SA.mergedVoteView sp R Ψ (s + 1)) s B} ∧
      ∀ B ∈ {B | B ∈ Ψ.viableTree (SA.voterBlockTree sp R Ψ (s + 1)) ∧
        B.parent = some d.head.root ∧
        SA.goldfishEligible sp Ψ tj (SA.mergedVoteView sp R Ψ (s + 1)) s B}, B = P)
    (hP : ¬ ∃ C, SA.IsBest sp (SA.goldfishScore sp Ψ (SA.mergedVoteView sp R Ψ (s + 1)) s)
      {B | B ∈ Ψ.viableTree (SA.voterBlockTree sp R Ψ (s + 1)) ∧ B.parent = some P.root ∧
        SA.goldfishEligible sp Ψ tj (SA.mergedVoteView sp R Ψ (s + 1)) s B} C)
    (hbest : ∀ B C, Φ.Anc X B → Φ.Anc D B → Φ.Anc B d.head → B ≠ d.head → Φ.Anc C d.head →
      SA.IsBest sp (SA.goldfishScore sp Φ (SA.View.ofLists pay) s)
        {B' | B' ∈ Φ.viableTree Φ.tree ∧ B'.parent = some B.root ∧
          SA.goldfishEligible sp Φ ti (SA.View.ofLists pay) s B'} C →
      SA.IsBest sp (SA.goldfishScore sp Ψ (SA.mergedVoteView sp R Ψ (s + 1)) s)
        {B' | B' ∈ Ψ.viableTree (SA.voterBlockTree sp R Ψ (s + 1)) ∧ B'.parent = some B.root ∧
          SA.goldfishEligible sp Ψ tj (SA.mergedVoteView sp R Ψ (s + 1)) s B'} C) :
    SA.getHead sp R Ψ tj (Ψ.viableTree (SA.voterBlockTree sp R Ψ (s + 1)))
      (SA.mergedVoteView sp R Ψ (s + 1)) (((s + 1 : Nat) : Int) - 1) = P := by
  have hcast : ((s + 1 : Nat) : Int) - 1 = s := by omega
  set W₁ := SA.ghost sp (Φ.viableTree Φ.tree) (SA.goldfishScore sp Φ (SA.View.ofLists pay) s)
    (SA.goldfishEligible sp Φ ti (SA.View.ofLists pay) s) with hW₁
  have hTp : Φ.viableTree Φ.tree ⊆ Φ.tree := fun _ h => h.1
  have hQ : d.head = W₁ Φ.tree.ncard d.start := by
    rw [hW₁]
    unfold SA.acProposal at hd
    split_ifs at hd
    simp only [Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp only [hslot, hcast]
    rfl
  have hstop₀ := SA.ghost_stopped hΦ.coherent hTp (hΦ.finite.subset hTp)
    (sc := SA.goldfishScore sp Φ (SA.View.ofLists pay) s)
    (el := SA.goldfishEligible sp Φ ti (SA.View.ofLists pay) s)
    (Set.ncard_le_ncard hTp hΦ.finite) d.start
  rw [← hW₁] at hstop₀
  have hstop₁ := hstop₀
  rw [← hQ] at hstop₁
  have hW₁add : ∀ a b x, W₁ (a + b) x = W₁ b (W₁ a x) := fun a b x => by
    rw [hW₁]; exact SA.ghost_add a b x
  have hstopQ : ∀ m, W₁ m d.head = d.head := fun m => by
    have h0 : W₁ 0 d.head = d.head := rfl
    rw [hW₁] at h0 ⊢
    exact (SA.ghost_fuel_stable (f := 0) (Nat.zero_le m)
      (by rw [h0]; exact hstop₁)).trans h0
  have hXQend : ∀ {X}, Φ.Anc D X → Φ.Anc X d.head → W₁ Φ.tree.ncard X = d.head := by
    intro X hDX hXQ
    obtain ⟨kx, -, hkx⟩ := SA.ghost_visits hΦ.coherent hTp _ (hsD.trans hDX) (hQ ▸ hXQ)
    rw [← hW₁] at hkx
    have hadd := hW₁add kx Φ.tree.ncard d.start
    rw [hkx] at hadd
    rw [← hadd, add_comm, hW₁add, ← hQ, hstopQ]
  rw [hcast] at hXend ⊢
  rw [SA.viableTree_voteDomain_eq_of_viable ⟨P, hPv⟩] at hXend
  set W₂ := SA.ghost sp (Ψ.viableTree (SA.voterBlockTree sp R Ψ (s + 1)))
    (SA.goldfishScore sp Ψ (SA.mergedVoteView sp R Ψ (s + 1)) s)
    (SA.goldfishEligible sp Ψ tj (SA.mergedVoteView sp R Ψ (s + 1)) s) with hW₂
  have hTy : Ψ.viableTree (SA.voterBlockTree sp R Ψ (s + 1)) ⊆ Ψ.tree := fun _ h => h.1.1
  have hXP : ∃ fX, W₂ fX X = P := by
    rcases hXc with rfl | ⟨hDX, hXQ⟩
    · exact ⟨0, rfl⟩
    refine ⟨Φ.tree.ncard + 1, SA.ghost_follow _ X (hXQend hDX hXQ) hstop₁ ?_ hstep hP⟩
    intro m hm hne C hC
    by_cases hXe : X = d.head
    · exact absurd (by rw [hXe]; exact hstopQ m) hne
    have hXt := (Anc.mem hXQ hXe).1
    have hXm : Φ.Anc X (W₁ m X) := SA.anc_ghost hTp m hXt
    have hmem : W₁ m X ∈ Φ.tree := by
      rcases eq_or_ne (W₁ m X) X with he | he
      · rw [he]; exact hXt
      · exact (Anc.mem hXm (Ne.symm he)).2
    have hend : W₁ (Φ.tree.ncard - m) (W₁ m X) = d.head := by
      rw [← hW₁add, Nat.add_sub_cancel' hm.le]
      exact hXQend hDX hXQ
    have hQm : Φ.Anc (W₁ m X) d.head := hend ▸ SA.anc_ghost hTp _ hmem
    have hCQ : Φ.Anc C d.head := by
      have hw := SA.walkEnd_ghost
        (sc := SA.goldfishScore sp Φ (SA.View.ofLists pay) s)
        (el := SA.goldfishEligible sp Φ ti (SA.View.ofLists pay) s)
        hΦ.coherent hTp (hΦ.finite.subset hTp) (Set.ncard_le_ncard hTp hΦ.finite) d.start
      rw [← hW₁, ← hQ] at hw
      obtain ⟨f, hf, -⟩ := SA.walkEnd_iff.1
        (hw.of_anc hΦ.coherent hTp (hsD.trans (hDX.trans hXm)) hQm)
      cases f with
      | zero => exact absurd hf hne
      | succ f =>
        have h1 : W₁ 1 (W₁ m X) = C := SA.ghost_succ_of_best 0 _ hC
        rw [hW₁] at h1
        rw [show f + 1 = 1 + f by omega, SA.ghost_add, h1] at hf
        exact hf ▸ SA.anc_ghost hTp f (hTp hC.1.1)
    exact hbest _ C hXm (hDX.trans hXm) hQm hne hCQ hC
  obtain ⟨fX, hfX⟩ := hXP
  change W₂ Ψ.tree.ncard (SA.getAnchor sp R Ψ tj) = P
  obtain ⟨ky, -, hky⟩ := SA.ghost_visits hΨ.coherent hTy _ haX hXend
  have hP₂ : W₂ (ky + fX) (SA.getAnchor sp R Ψ tj) = P := by
    rw [hW₂, SA.ghost_add, ← hW₂]
    rw [← hW₂] at hky
    rw [hky]; exact hfX
  have hstop₂ := SA.ghost_stopped hΨ.coherent hTy (hΨ.finite.subset hTy)
    (sc := SA.goldfishScore sp Ψ (SA.mergedVoteView sp R Ψ (s + 1)) s)
    (el := SA.goldfishEligible sp Ψ tj (SA.mergedVoteView sp R Ψ (s + 1)) s)
    (Set.ncard_le_ncard hTy hΨ.finite) (SA.getAnchor sp R Ψ tj)
  rw [← hW₂] at hstop₂
  have hmax₁ := SA.ghost_fuel_stable (le_max_left Ψ.tree.ncard (ky + fX)) hstop₂
  have hmax₂ := SA.ghost_fuel_stable (le_max_right Ψ.tree.ncard (ky + fX)) (hP₂ ▸ hP)
  rw [← hW₂] at hmax₁ hmax₂
  rw [← hmax₁, hmax₂, hP₂]

end Consensus.Goldilocks.Healing

end

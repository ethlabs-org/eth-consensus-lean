module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk

public section

/-! # Goldilocks: a voter's walk that passes the proposal path ends at the proposal

The walk comparison behind "every honest slot-`s` vote is the proposal `P`". The proposal walk
(`ac_proposal`: the full viable tree, the payload's view `pay`, from the unlocked anchor
`d.start`) ends at the duty head `Q = d.head`. A voter's walk (any tree `T` of its frame, any
score and eligibility) that passes a block `X` of the path from a block `D` of the proposal walk
through `Q` to `P`, agrees with the proposal walk's best children strictly between `D` and `Q`,
has `P` as its only eligible child at `Q` and no best child at `P`, ends at `P`
(`voter_walk_eq_proposal`). It reads the two frames and walks only; the pass, the agreement and
the stop are its users' (`Service/Agree` for constant faults, its growing-fault form, and HS.3 of
`Healing/AgreeVotes`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams Payload)

variable {sp : SAParams} {FGP : Type}

/-- The duty head of a proposal is the walk of the full viable tree from its start, with the
payload's view of the previous slot's votes. -/
private theorem acProposal_head {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP}
    {t : Time} {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (h : (SA.acProposal sp A Φ t).2 = some (d, pay)) :
    d.head = SA.ghost sp (Φ.viableTree Φ.tree)
      (SA.goldfishScore sp Φ (SA.View.ofLists pay) ((sp.slot t : Int) - 1))
      (SA.goldfishEligible sp Φ t (SA.View.ofLists pay) ((sp.slot t : Int) - 1))
      Φ.tree.ncard d.start := by
  unfold SA.acProposal at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- **A voter's walk that passes the proposal path ends at the proposal.** Let the proposal call
in the well-formed frame `Φp` at `t` (slot `s`) return `(d, pay)`, and let `D` be on the proposal
walk's path from `d.start` to `d.head`. Let a walk over `T ⊆ Φy.tree` (`Φy` well formed, both
frames inside `U`) from `a` reach a block `X` that is `P` or between `D` and `d.head` in `Φp`,
with `X` on its path (`hXend`). If its best child agrees with the proposal walk's at every block
between `D` and `d.head` (other than `d.head`) above `a` in `U` (`hsuf`), its only eligible child
at `d.head` is `P` (`hstep`) and it has no best child at `P` (`hstop`), then with one step per
block of `Φy.tree` it ends at `P`. -/
theorem voter_walk_eq_proposal {U : Set (SA.Blk sp.n FGP)} {A : SA.SAState sp.n}
    {Φp Φy : SA.Frm sp.n FGP} {t : Time} {s : Nat} {d : DutyHead sp.n FGP (Payload sp.n)}
    {pay : Payload sp.n} (hd : (SA.acProposal sp A Φp t).2 = some (d, pay))
    (hts : sp.slot t = s) (hΦp : FrameOK Φp) (hΦpU : Φp.tree ⊆ U) (hΦy : FrameOK Φy)
    (hΦyU : Φy.tree ⊆ U) {D : SA.Blk sp.n FGP} (hsD : Φp.Anc d.start D)
    (hDQ : Φp.Anc D d.head) {T : Set (SA.Blk sp.n FGP)} (hT : T ⊆ Φy.tree)
    {sc : SA.Blk sp.n FGP → Nat} {el : SA.Blk sp.n FGP → Prop} {P a X : SA.Blk sp.n FGP}
    (hXc : X = P ∨ (Φp.Anc D X ∧ Φp.Anc X d.head)) (haX : Φy.Anc a X)
    (hXend : Φy.Anc X (SA.ghost sp T sc el Φy.tree.ncard a))
    (hstep : P ∈ {B | B ∈ T ∧ B.parent = some d.head.root ∧ el B} ∧
      ∀ B ∈ {B | B ∈ T ∧ B.parent = some d.head.root ∧ el B}, B = P)
    (hstop : ¬ ∃ C, SA.IsBest sp sc {B | B ∈ T ∧ B.parent = some P.root ∧ el B} C)
    (hsuf : ∀ X, Φp.Anc D X → Φp.Anc X d.head → Anc U a X → X ≠ d.head →
      ∀ C, SA.IsBest sp (SA.goldfishScore sp Φp (SA.View.ofLists pay) ((s : Int) - 1))
          {B | B ∈ Φp.viableTree Φp.tree ∧ B.parent = some X.root ∧
            SA.goldfishEligible sp Φp t (SA.View.ofLists pay) ((s : Int) - 1) B} C →
        SA.IsBest sp sc {B | B ∈ T ∧ B.parent = some X.root ∧ el B} C) :
    SA.ghost sp T sc el Φy.tree.ncard a = P := by
  -- the proposal walk: from its start, through `D`, to `Q`, where it stops
  set W₁ := SA.ghost sp (Φp.viableTree Φp.tree)
    (SA.goldfishScore sp Φp (SA.View.ofLists pay) ((s : Int) - 1))
    (SA.goldfishEligible sp Φp t (SA.View.ofLists pay) ((s : Int) - 1)) with hW₁
  have hTp : Φp.viableTree Φp.tree ⊆ Φp.tree := fun _ h => h.1
  have hQ : d.head = W₁ Φp.tree.ncard d.start := by
    rw [acProposal_head hd, hts]
  have hstop₀ := SA.ghost_stopped hΦp.coherent hTp (hΦp.finite.subset hTp)
    (sc := SA.goldfishScore sp Φp (SA.View.ofLists pay) ((s : Int) - 1))
    (el := SA.goldfishEligible sp Φp t (SA.View.ofLists pay) ((s : Int) - 1))
    (Set.ncard_le_ncard hTp hΦp.finite) d.start
  rw [← hW₁] at hstop₀
  have hstop₁ := hstop₀
  rw [← hQ] at hstop₁
  obtain ⟨kp, -, hkp⟩ := SA.ghost_visits hΦp.coherent hTp _ hsD (hQ ▸ hDQ)
  rw [← hW₁] at hkp
  have h₁ : W₁ Φp.tree.ncard D = d.head := by
    have hadd := SA.ghost_add (T := Φp.viableTree Φp.tree)
      (sc := SA.goldfishScore sp Φp (SA.View.ofLists pay) ((s : Int) - 1))
      (el := SA.goldfishEligible sp Φp t (SA.View.ofLists pay) ((s : Int) - 1))
      kp Φp.tree.ncard d.start
    rw [← hW₁, hkp] at hadd
    rw [← hadd, hQ]
    exact SA.ghost_fuel_stable (by omega) hstop₀
  have hW₁add : ∀ a b x, W₁ (a + b) x = W₁ b (W₁ a x) := fun a b x => by
    rw [hW₁]; exact SA.ghost_add a b x
  have hstopQ : ∀ m, W₁ m d.head = d.head := fun m => by
    have h0 : W₁ 0 d.head = d.head := by rw [hW₁]; rfl
    rw [hW₁] at h0 ⊢
    exact (SA.ghost_fuel_stable (f := 0) (Nat.zero_le m) (by rw [h0]; exact hstop₁)).trans h0
  -- the proposal walk from a block `X` of its path from `D` ends at `Q`
  have hXQend : ∀ {X}, Φp.Anc D X → Φp.Anc X d.head → W₁ Φp.tree.ncard X = d.head := by
    intro X hDX hXQ
    obtain ⟨kx, -, hkx⟩ := SA.ghost_visits hΦp.coherent hTp _ hDX (h₁ ▸ hXQ)
    rw [← hW₁] at hkx
    rw [← hkx, ← hW₁add, add_comm, hW₁add, h₁, hstopQ]
  set W₂ := SA.ghost sp T sc el with hW₂
  -- from `X`, the voter's walk ends at `P`
  have hXP : ∃ fX, W₂ fX X = P := by
    rcases hXc with rfl | ⟨hDX, hXQ⟩
    · exact ⟨0, rfl⟩
    refine ⟨Φp.tree.ncard + 1, SA.ghost_follow _ X ?_ hstop₁ ?_ hstep hstop⟩
    · exact hXQend hDX hXQ
    · intro m hm hne
      by_cases hXQ' : X = d.head
      · exact absurd (by rw [hXQ']; exact hstopQ m) hne
      have hXt : X ∈ Φp.tree := (Anc.mem hXQ hXQ').1
      -- the position `W₁ m X` is between `D` and `Q`
      have hXm : Φp.Anc X (W₁ m X) := by rw [hW₁]; exact SA.anc_ghost hTp m hXt
      have hQm : Φp.Anc (W₁ m X) d.head := by
        have hmem : W₁ m X ∈ Φp.tree := by
          rcases eq_or_ne (W₁ m X) X with h | h
          · rw [h]; exact hXt
          · exact (Anc.mem hXm (Ne.symm h)).2
        have hend : W₁ (Φp.tree.ncard - m) (W₁ m X) = d.head := by
          rw [← hW₁add, Nat.add_sub_cancel' hm.le]
          exact hXQend hDX hXQ
        rw [← hend, hW₁]
        exact SA.anc_ghost hTp _ hmem
      exact hsuf _ (hDX.trans hXm) hQm ((haX.mono hΦyU).trans (hXm.mono hΦpU)) hne
  -- the voter's walk passes `X`, so reaches `P`, where it has stopped
  obtain ⟨fX, hfX⟩ := hXP
  obtain ⟨ky, -, hky⟩ := SA.ghost_visits hΦy.coherent hT _ haX hXend
  have hP₂ : W₂ (ky + fX) a = P := by
    rw [hW₂, SA.ghost_add, ← hW₂]
    rw [← hW₂] at hky
    rw [hky]; exact hfX
  have hstop₂ := SA.ghost_stopped hΦy.coherent hT (hΦy.finite.subset hT) (sc := sc) (el := el)
    (Set.ncard_le_ncard hT hΦy.finite) a
  rw [← hW₂] at hstop₂
  have hmax₁ := SA.ghost_fuel_stable (le_max_left (Φy.tree.ncard) (ky + fX)) hstop₂
  have hmax₂ := SA.ghost_fuel_stable (le_max_right (Φy.tree.ncard) (ky + fX)) (hP₂ ▸ hstop)
  rw [← hW₂] at hmax₁ hmax₂
  rw [← hmax₁, hmax₂, hP₂]

end Consensus.Goldilocks.Compose

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Views

public section

/-! # Goldilocks Healing: H.2's shared suffix

Only the winning child must transfer between frames, not the entire eligible-child set.
-/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time}

/-- Above both roots, a winning child on the proposal's parent path wins at the reader. -/
theorem h2_suffix_best (hS : HealthyBase tr H U proposer g) {p k : Nat} (hp : 0 < p)
    (hpH : proposer p ∈ H) {P Q : Blk sp.n FGP}
    (hP : HonestProposal tr (proposer p) p P)
    {ℓp : ACLabel (goldilocksSA sp FGP ro)} (hck : tr.CallAt (proposer p) k ℓp)
    (hcall : ℓp.call = .proposal) (htk : tr.time k = sp.ts p)
    (hlate : gbar g + 2 * sp.Δ ≤ sp.ts p) (hgeo : Geo proposer tr H p P)
    (hPnot : P ∉ ℓp.frame.tree) (hPs : P.slot = p)
    (hQP : P.parent = some Q.root) (hQv : Q ∈ ℓp.frame.viableTree ℓp.frame.tree)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) (hes : e.msg.slot = p)
    {Vp : View sp.n}
    (hvot : voters Vp.votes = voters (mergedVoteView sp e.readPoint ℓ.frame p).votes)
    (hsc : ∀ B ∈ ℓp.frame.tree, B ∈ ℓ.frame.tree →
      goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame p) ((p : Int) - 1) B =
        goldfishScore sp ℓp.frame Vp ((p : Int) - 1) B)
    {X C : Blk sp.n FGP} (hfX : Anc U ℓp.frame.fcRoot X)
    (hyX : Anc U ℓ.frame.fcRoot X) (hXQ : Anc U X Q) (hne : X ≠ Q)
    (hCQ : Anc U C Q)
    (hC : IsBest sp (goldfishScore sp ℓp.frame Vp ((p : Int) - 1))
      (eligibleChildren (ℓp.frame.viableTree ℓp.frame.tree)
        (goldfishEligible sp ℓp.frame (tr.time k) Vp ((p : Int) - 1)) X) C) :
    IsBest sp (goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame p) ((p : Int) - 1))
      (eligibleChildren (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame p))
        (goldfishEligible sp ℓ.frame (tr.time i) (mergedVoteView sp e.readPoint ℓ.frame p)
          ((p : Int) - 1)) X) C := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  obtain ⟨hΦp, hΦpU⟩ := frameIn_of_callAt hr hpH hck
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc.1
  have hPv := (hgeo k ℓp hck hcall htk y hy i ℓ e hc hes).1
  have hPt := hΦ.viableHeads_subset hPv
  have hQU := hΦpU hQv.1
  have hQP' : Anc U Q P := .single ⟨hQU, hΦU hPt, hQP⟩
  have hXP := hXQ.trans hQP'
  have hXt := frame_mem_of_between sp hU hΦp hΦpU hQv.1 hXQ
    ((hΦp.F_anc_fcRoot.mono hΦpU).trans hfX)
  have hXy := frame_mem_of_between sp hU hΦ hΦU hPt hXP
    ((hΦ.F_anc_fcRoot.mono hΦU).trans hyX)
  have hXP' := anc_tree_of_anc_U hU hΦ hΦU hXy hXP hPt
  have hXdom : X ∈ voterBlockTree sp e.readPoint ℓ.frame p :=
    ⟨hXy, Or.inr ⟨P, hPt, hPs, hXP'⟩⟩
  have hCP := hCQ.trans hQP'
  have hXC : Anc U X C := .single ⟨hΦpU hXt, hΦpU hC.1.1.1, hC.1.2.1⟩
  have hfC := hyX.trans hXC
  have hCy := frame_mem_of_between sp hU hΦ hΦU hPt hCP
    ((hΦ.F_anc_fcRoot.mono hΦU).trans hfC)
  have hCP' := anc_tree_of_anc_U hU hΦ hΦU hCy hCP hPt
  have hCv : C ∈ ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame p) :=
    ⟨⟨hCy, Or.inr ⟨P, hPt, hPs, hCP'⟩⟩,
      anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfC hCy,
      P, ⟨hPt, Or.inr ⟨P, hPt, hPs, .refl⟩⟩, hPv, hCP'⟩
  have hrefl : ∀ B ∈ ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame p),
      B.parent = some X.root → B ∈ ℓp.frame.viableTree ℓp.frame.tree := by
    intro B hB hBX
    have hfB := hfX.tail ⟨hΦpU hXt, hΦU hB.1.1, hBX⟩
    rcases h2_competitor_reflect hS hp hpH hP hck hcall htk hlate hgeo hPnot hQP hQv
      hy hc hes hB hfB with he | h
    · subst B
      exact False.elim (hne (hU.1 (hΦpU hXt) hQU (Option.some.inj (hBX.symm.trans hQP))))
    · exact h
  by_cases hXv : X ∈ ℓp.frame.viableHeads
  · have hCs : C.slot ≠ sp.slot (tr.time k) := by
      have := (Anc.slot_le hU hCQ).1
      have := hU.2 Q hQU P (hΦU hPt) hQP
      have hsl : sp.slot (tr.time k) = p := by
        rw [htk]; exact slot_of_mem sp p le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))
      omega
    exact isBest_transfer hXv hCs hvot hsc (fun _ h => h.1) (fun _ h => h.1.1) hCv hrefl hC
  · have hXvy : X ∉ ℓ.frame.viableHeads := fun h => hXv
      ((hgeo k ℓp hck hcall htk y hy i ℓ e hc hes).2 X hXdom
        (fun he => hPnot (he ▸ hXt)) |>.1 h)
    refine isBest_transfer_low (fun W hW he => hXv ?_) (fun W hW he => hXvy ?_)
      hsc (fun _ h => h.1) (fun _ h => h.1.1) hCv hrefl hC
    · exact (hΦp.coherent.1 (hΦp.viableHeads_subset hW) hXt he) ▸ hW
    · exact (hΦ.coherent.1 (hΦ.viableHeads_subset hW) hXy he) ▸ hW

/-- Once the reader reaches the proposal's parent, its next and final block is the proposal.
The parent's viability aligns eligibility; any competing eligible child contradicts the
proposer's stopping condition. -/
theorem h2_suffix_end (hS : HealthyBase tr H U proposer g) {p k : Nat} (hp : 0 < p)
    (hpH : proposer p ∈ H) {P Q : Blk sp.n FGP}
    (hP : HonestProposal tr (proposer p) p P)
    {ℓp : ACLabel (goldilocksSA sp FGP ro)} (hck : tr.CallAt (proposer p) k ℓp)
    (hcall : ℓp.call = .proposal) (htk : tr.time k = sp.ts p)
    (hlate : gbar g + 2 * sp.Δ ≤ sp.ts p) (hgeo : Geo proposer tr H p P)
    (hPnot : P ∉ ℓp.frame.tree) (hPs : P.slot = p)
    (hQP : P.parent = some Q.root) (hQv : Q ∈ ℓp.frame.viableTree ℓp.frame.tree)
    (hQhead : Q ∈ ℓp.frame.viableHeads)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) (hes : e.msg.slot = p)
    (hyQ : Anc U ℓ.frame.fcRoot Q) {Vp : View sp.n}
    (hvot : voters Vp.votes = voters (mergedVoteView sp e.readPoint ℓ.frame p).votes)
    (hsc : ∀ B ∈ ℓp.frame.tree, B ∈ ℓ.frame.tree →
      goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame p) ((p : Int) - 1) B =
        goldfishScore sp ℓp.frame Vp ((p : Int) - 1) B)
    (hstop : ¬ ∃ C, IsBest sp (goldfishScore sp ℓp.frame Vp ((p : Int) - 1))
      (eligibleChildren (ℓp.frame.viableTree ℓp.frame.tree)
        (goldfishEligible sp ℓp.frame (tr.time k) Vp ((p : Int) - 1)) Q) C) :
    WalkEnd (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame p))
      (goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame p) ((p : Int) - 1))
      (goldfishEligible sp ℓ.frame (tr.time i) (mergedVoteView sp e.readPoint ℓ.frame p)
        ((p : Int) - 1)) Q P := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  obtain ⟨hΦp, hΦpU⟩ := frameIn_of_callAt hr hpH hck
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc.1
  have hPv := (hgeo k ℓp hck hcall htk y hy i ℓ e hc hes).1
  have hPt := hΦ.viableHeads_subset hPv
  have hQP' : Anc U Q P := .single ⟨hΦpU hQv.1, hΦU hPt, hQP⟩
  have hQt := frame_mem_of_between sp hU hΦ hΦU hPt hQP'
    ((hΦ.F_anc_fcRoot.mono hΦU).trans hyQ)
  have hQPy := anc_tree_of_anc_U hU hΦ hΦU hQt hQP' hPt
  have hQdom : Q ∈ voterBlockTree sp e.readPoint ℓ.frame p :=
    ⟨hQt, Or.inr ⟨P, hPt, hPs, hQPy⟩⟩
  have hQvy := (hgeo k ℓp hck hcall htk y hy i ℓ e hc hes).2 Q hQdom
    (fun he => hPnot (he ▸ hQv.1)) |>.2 hQhead
  have hsl : sp.slot (tr.time i) = p := (castAt_spec hr hy hc).2.1.symm.trans hes
  have hPvt : P ∈ ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame p) :=
    ⟨⟨hPt, Or.inr ⟨P, hPt, hPs, .refl⟩⟩, hΦ.fcRoot_anc_viableHeads P hPv,
      P, ⟨hPt, Or.inr ⟨P, hPt, hPs, .refl⟩⟩, hPv, .refl⟩
  refine WalkEnd.step (C := P)
    ⟨⟨hPvt, hQP, Or.inr (Or.inl (hPs.trans hsl.symm))⟩, ?_⟩ (walkEnd_self ?_)
  · intro B hB hne
    have hBp := h2_competitor_reflect hS hp hpH hP hck hcall htk hlate hgeo hPnot hQP hQv
      hy hc hes hB.1 ((hQv.2.1.mono hΦpU).tail ⟨hΦpU hQv.1, hΦU hB.1.1.1, hB.2.1⟩)
    have hBp' := hBp.resolve_left hne
    have hel : goldfishEligible sp ℓp.frame (tr.time k) Vp ((p : Int) - 1) B := by
      rcases hB.2.2 with h | h | h
      · exact False.elim (h ⟨Q, hQvy, hB.2.1⟩)
      · exact False.elim (hne (h2_frame_slot_eq hS hp hpH hP hy hc.1 hB.1.1.1
          (h.trans hsl)))
      · exact Or.inr (Or.inr (by rw [hvot, ← hsc B hBp'.1 hB.1.1.1]; exact h))
    apply False.elim
    apply hstop
    exact exists_isBest hΦp (S := eligibleChildren (ℓp.frame.viableTree ℓp.frame.tree)
      (goldfishEligible sp ℓp.frame (tr.time k) Vp ((p : Int) - 1)) Q)
      (fun _ h => h.1.1) ⟨B, hBp', hB.2.1, hel⟩ _
  · rintro ⟨B, hB, -⟩
    have hlt := hU.2 P (hΦU hPt) B (hΦU hB.1.1.1) hB.2.1
    have hle := frame_slot_le sp hr hy hc.1 B hB.1.1.1
    omega

/-- Transfer the proposal walk from any shared suffix start through its final new block. -/
theorem h2_suffix_walk (hS : HealthyBase tr H U proposer g) {p k : Nat} (hp : 0 < p)
    (hpH : proposer p ∈ H) {P : Blk sp.n FGP}
    (hP : HonestProposal tr (proposer p) p P)
    {ℓp : ACLabel (goldilocksSA sp FGP ro)} (hck : tr.CallAt (proposer p) k ℓp)
    (hcall : ℓp.call = .proposal) (htk : tr.time k = sp.ts p)
    (hlate : gbar g + 2 * sp.Δ ≤ sp.ts p) (hgeo : Geo proposer tr H p P)
    (hPnot : P ∉ ℓp.frame.tree) (hPs : P.slot = p)
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (hpay : (acProposal sp (tr.state (proposer p) k) ℓp.frame (tr.time k)).2 =
      some (d, pay)) (hQP : P.parent = some d.head.root)
    (hQv : d.head ∈ ℓp.frame.viableTree ℓp.frame.tree)
    (hQhead : d.head ∈ ℓp.frame.viableHeads)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) (hes : e.msg.slot = p)
    (hvot : voters (View.ofLists pay).votes =
      voters (mergedVoteView sp e.readPoint ℓ.frame p).votes)
    (hsc : ∀ B ∈ ℓp.frame.tree, B ∈ ℓ.frame.tree →
      goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame p) ((p : Int) - 1) B =
        goldfishScore sp ℓp.frame (View.ofLists pay) ((p : Int) - 1) B)
    {D : Blk sp.n FGP} (hsD : Anc U d.start D) (hDQ : Anc U D d.head)
    (hyD : Anc U ℓ.frame.fcRoot D) :
    WalkEnd (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame p))
      (goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame p) ((p : Int) - 1))
      (goldfishEligible sp ℓ.frame (tr.time i) (mergedVoteView sp e.readPoint ℓ.frame p)
        ((p : Int) - 1)) D P := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  obtain ⟨hΦp, hΦpU⟩ := frameIn_of_callAt hr hpH hck
  obtain ⟨hst, hfs, hw⟩ := h2_parent_walkEnd hΦp hpay
  have hsl : sp.slot (tr.time k) = p := by
    rw [htk]; exact slot_of_mem sp p le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))
  rw [hsl] at hw
  have hT : ℓp.frame.viableTree ℓp.frame.tree ⊆ U := fun _ h => hΦpU h.1
  have hDU : D ∈ U := by
    rcases eq_or_ne d.start D with he | he
    · exact he ▸ hΦpU hst
    · exact (Anc.mem hsD he).2
  have hwd := hw.of_anc hU hT hsD hDQ
  refine h2_walk_transfer hT hDU hwd (fun X hDX hXQ hne C hC => ?_)
    (h2_suffix_end hS hp hpH hP hck hcall htk hlate hgeo hPnot hPs hQP hQv hQhead
      hy hc hes (hyD.trans hDQ) hvot hsc (walkEnd_iff.1 hw).choose_spec.2)
  have hCQ : Anc U C d.head := by
    obtain ⟨f, hf, -⟩ := walkEnd_iff.1 (hwd.of_anc hU hT hDX hXQ)
    cases f with
    | zero => exact False.elim (hne hf)
    | succ f =>
      rw [show f + 1 = 1 + f by omega, ghost_add, ghost_succ_of_best 0 X hC] at hf
      exact hf ▸ anc_ghost hT f (hT hC.1.1)
  exact h2_suffix_best hS hp hpH hP hck hcall htk hlate hgeo hPnot hPs hQP hQv
    hy hc hes hvot hsc (((hfs.mono hΦpU).trans hsD).trans hDX)
    (hyD.trans hDX) hXQ hne hCQ hC

end Consensus.Goldilocks.SA

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Suffix

public section

/-! # Goldilocks Healing: compare a reader with the proposal walk -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time}

/-- A reader extending the proposer anchor follows their shared suffix to the proposal. -/
theorem h2_compare_reader (hS : HealthyBase tr H U proposer g) {p k : Nat} (hp : 0 < p)
    (hpH : proposer p ∈ H) {P : Blk sp.n FGP}
    (hP : HonestProposal tr (proposer p) p P)
    {ℓp : ACLabel (goldilocksSA sp FGP ro)} (hck : tr.CallAt (proposer p) k ℓp)
    (hcall : ℓp.call = .proposal) (htk : tr.time k = sp.ts p)
    (hlate : gbar g + 2 * sp.Δ ≤ sp.ts p) (hgeo : Geo proposer tr H p P)
    (hPnot : P ∉ ℓp.frame.tree) (hPs : P.slot = p)
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (hpay : (acProposal sp (tr.state (proposer p) k) ℓp.frame (tr.time k)).2 =
      some (d, pay)) (hQP : P.parent = some d.head.root)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) (hes : e.msg.slot = p)
    (hvot : voters (View.ofLists pay).votes =
      voters (mergedVoteView sp e.readPoint ℓ.frame p).votes)
    (hsc : ∀ B ∈ ℓp.frame.tree, B ∈ ℓ.frame.tree →
      goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame p) ((p : Int) - 1) B =
        goldfishScore sp ℓp.frame (View.ofLists pay) ((p : Int) - 1) B)
    (haP : Anc U (getAnchor sp e.readPoint ℓ.frame (tr.time i)) P)
    (hsHd : Anc U d.start (getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame p))
      (mergedVoteView sp e.readPoint ℓ.frame p) ((p : Int) - 1))) : e.msg.head = P.root := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  obtain ⟨hΦp, hΦpU⟩ := frameIn_of_callAt hr hpH hck
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc.1
  have hPv := (hgeo k ℓp hck hcall htk y hy i ℓ e hc hes).1
  have hPt := hΦ.viableHeads_subset hPv
  have hPU := hΦU hPt
  obtain ⟨hst, hfs, hwp⟩ := h2_parent_walkEnd hΦp hpay
  have hslp : sp.slot (tr.time k) = p := by
    rw [htk]; exact slot_of_mem sp p le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))
  rw [hslp] at hwp
  have hTp : ℓp.frame.viableTree ℓp.frame.tree ⊆ U := fun _ h => hΦpU h.1
  have hsQ := hwp.anc hTp (hΦpU hst)
  have hQt : d.head ∈ ℓp.frame.tree := by
    rcases eq_or_ne d.start d.head with he | he
    · exact he ▸ hst
    · exact (Anc.mem (hwp.anc (fun _ h => h.1) hst) he).2
  have hQP' : Anc U d.head P := .single ⟨hΦpU hQt, hPU, hQP⟩
  have hsP := hsQ.trans hQP'
  let a := getAnchor sp e.readPoint ℓ.frame (tr.time i)
  let Ty := ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame p)
  let sc := goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame p) ((p : Int) - 1)
  let el := goldfishEligible sp ℓ.frame (tr.time i)
    (mergedVoteView sp e.readPoint ℓ.frame p) ((p : Int) - 1)
  let Hd := ghost sp Ty sc el ℓ.frame.tree.ncard a
  have hTy : Ty ⊆ ℓ.frame.tree := fun _ h => h.1.1
  have hTyU := hTy.trans hΦU
  have hfa := fcRoot_anc_getAnchor hΦ e.readPoint (tr.time i)
  have hat : a ∈ ℓ.frame.tree := by
    rcases Relation.ReflTransGen.cases_tail hfa with he | ⟨_, _, he⟩
    · change getAnchor sp e.readPoint ℓ.frame (tr.time i) ∈ ℓ.frame.tree
      rw [he]; exact hΦ.fcRoot_mem
    · exact he.2.1
  have hwy : WalkEnd Ty sc el a Hd := walkEnd_ghost hU hTyU (hΦ.finite.subset hTy)
    (Set.ncard_le_ncard hTy hΦ.finite) a
  have haHd := hwy.anc hTyU (hΦU hat)
  have hsl : sp.slot (tr.time i) = p := (castAt_spec hr hy hc).2.1.symm.trans hes
  have hstopP : WalkEnd Ty sc el P P := walkEnd_self (by
    rintro ⟨B, hB, -⟩
    have := hU.2 P hPU B (hTyU hB.1) hB.2.1
    have := frame_slot_le sp hr hy hc.1 B (hTy hB.1)
    omega)
  have hHdP : Hd = P := by
    by_cases hfc : ℓp.frame.fcRoot ∈ ℓp.frame.viableTree ℓp.frame.tree
    · have hQhead := Healing.proposal_head_viable hr hpH hck hcall (σ := p)
        (by rw [sp.slotTime_eq, htk]; rfl) hpay hfc
      have hQv : d.head ∈ ℓp.frame.viableTree ℓp.frame.tree :=
        ⟨hQt, (hfs.trans (hwp.anc (fun _ h => h.1) hst)),
          d.head, hQt, hQhead, .refl⟩
      have hsuffix := fun {D} (hsD : Anc U d.start D) (hDQ : Anc U D d.head)
          (hyD : Anc U ℓ.frame.fcRoot D) =>
        h2_suffix_walk hS hp hpH hP hck hcall htk hlate hgeo hPnot hPs hpay hQP hQv
          hQhead hy hc hes hvot hsc hsD hDQ hyD
      rcases anc_total hU haP hsP with has | hsa
      · have hyS := (hfa.mono hΦU).trans has
        exact (hwy.of_anc hU hTyU has hsHd).unique (hsuffix .refl hsQ hyS)
      · by_cases he : a = P
        · exact hwy.unique (he ▸ hstopP)
        have haQ : Anc U a d.head := by
          rcases Relation.ReflTransGen.cases_tail haP with he' | ⟨B, haB, hBP⟩
          · exact False.elim (he he'.symm)
          · obtain rfl : B = d.head := hU.1 hBP.1 (hΦpU hQt)
              (Option.some.inj (hBP.2.2.symm.trans hQP))
            exact haB
        exact hwy.unique (hsuffix hsa haQ (hfa.mono hΦU))
    · have hnov : ∀ W, W ∈ ℓp.frame.viableHeads → False := by
        intro W hW
        exact hfc ⟨hΦp.fcRoot_mem, .refl, W, hΦp.viableHeads_subset hW, hW,
          hΦp.fcRoot_anc_viableHeads W hW⟩
      have hwitness : ∀ W ∈ voterBlockTree sp e.readPoint ℓ.frame p,
          W ∈ ℓ.frame.viableHeads → ℓ.frame.Anc P W := by
        intro W hW hWv
        by_cases he : W = P
        · exact he ▸ .refl
        · exact False.elim (hnov W
            ((hgeo k ℓp hck hcall htk y hy i ℓ e hc hes).2 W hW he |>.1 hWv))
      have hPvt : P ∈ Ty := ⟨⟨hPt, Or.inr ⟨P, hPt, hPs, .refl⟩⟩,
        hΦ.fcRoot_anc_viableHeads P hPv, P, ⟨hPt, Or.inr ⟨P, hPt, hPs, .refl⟩⟩, hPv, .refl⟩
      have hclosed := voterBlockTree_anc hr hy hc
      rw [hes] at hclosed
      have hPHd : Anc U P Hd := Anc.mono hΦU
        (h2_walk_reaches_root hΦ (fun _ h => h.1)
          (fun B hB X hXB _ => hclosed B hB X hXB) hPvt
          (anc_tree_of_anc_U hU hΦ hΦU hat haP hPt) hfa hwitness _ _ _)
      exact (hwy.of_anc hU hTyU haP hPHd).unique hstopP
  have hh := castAt_head_of_viable hr hy hc
    (hes ▸ ⟨P, proposal_mem_viableTree_voterBlockTree hΦ hPt hPs hPv⟩)
  rw [hes] at hh
  exact hh.trans (congrArg Block.root hHdP)

end Consensus.Goldilocks.SA

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Unanimity.Agree
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Unanimity.Anchor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Unanimity.Proposer

public section

/-! # Goldilocks Healing: T1 §6, unanimity of the honest slot-`p` votes

Every honest walk of slot `p` is the canonical walk from its anchor (`vote_children_eq`), so
the head of an honest slot-`p` vote is where the canonical walk from its anchor ends. Take the
earliest honest slot-`p` vote, with anchor `a₀` and head `E₀`: its anchor is not extended by an
earlier honest slot-`p` vote, so every honest slot-`p` vote and the proposal head extend `a₀`
(`vote_anchor_cases`). By induction on cuts, every honest slot-`p` vote has head `E₀`: its
walk passes `a₀` when its anchor is below `a₀`; otherwise its anchor is between `a₀` and `E₀`
(extended by the vote of `a₀`, or by an earlier vote, of head `E₀`), so its walk is the rest
of the walk from `a₀`. The same argument places the proposal's anchor `d.start` on the walk
from `a₀` or below `a₀` (`proposal_anchor_cases`), and the canonical walk from `d.start` ends
at `P` (`proposal_walkEnd`): so `E₀ = P`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {p : Nat} {P : Blk sp.n FGP}
  {k : Nat} {ℓp : ACLabel (goldilocksSA sp FGP ro)} {d : DutyHead sp.n FGP (Payload sp.n)}
  {pay : Payload sp.n}

/-- **The head of an honest slot-`p` vote ends the canonical walk from its anchor.** -/
private theorem vote_walkEnd (hs : UnanimitySetting tr H U g p P k ℓp d pay) {x : Fin sp.n}
    (hx : x ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr x j ℓ e) (hes : e.msg.slot = p) :
    ∃ Hd ∈ U, Hd.root = e.msg.head ∧
      WalkEnd (insert P (ℓp.frame.viableTree ℓp.frame.tree))
        (goldfishScore sp ℓp.frame (View.ofLists pay) ((p : Int) - 1))
        (goldfishEligible sp ℓp.frame (sp.ts p) (View.ofLists pay) ((p : Int) - 1))
        (getAnchor sp e.readPoint ℓ.frame (tr.time j)) Hd := by
  have hr := hs.standalone.run.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc.1
  obtain ⟨-, -, -, hhead⟩ := castAt_spec hr hx hc
  rw [hes] at hhead
  have ha := (vote_anchor_cases hs hx hc hes).1
  set T := ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame p)
  have hT : T ⊆ ℓ.frame.tree := fun B hB => hB.1.1
  have hfin : T.Finite := hΦ.finite.subset hT
  have hw := walkEnd_ghost (sp := sp) (sc := goldfishScore sp ℓ.frame
      (mergedVoteView sp e.readPoint ℓ.frame p) ((p : Int) - 1))
    (el := goldfishEligible sp ℓ.frame (tr.time j) (mergedVoteView sp e.readPoint ℓ.frame p)
      ((p : Int) - 1)) hU (hT.trans hΦU) hfin (Set.ncard_le_ncard hT hΦ.finite)
    (getAnchor sp e.readPoint ℓ.frame (tr.time j))
  set Hd := ghost sp T (goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame p)
      ((p : Int) - 1)) (goldfishEligible sp ℓ.frame (tr.time j)
      (mergedVoteView sp e.readPoint ℓ.frame p) ((p : Int) - 1)) ℓ.frame.tree.ncard
    (getAnchor sp e.readPoint ℓ.frame (tr.time j))
  have hHd : Hd ∈ U := by
    by_cases he : getAnchor sp e.readPoint ℓ.frame (tr.time j) = Hd
    · exact he ▸ ha
    · exact (Anc.mem (hw.anc (hT.trans hΦU) ha) he).2
  refine ⟨Hd, hHd, hhead.symm, ?_⟩
  have hag := fun X => vote_children_eq hs hx hc hes X
  refine hw.congr hU (hT.trans hΦU) ha hHd (fun X _ => hag X) ?_
  obtain ⟨-, -, hstop⟩ := walkEnd_iff.1 hw
  refine walkEnd_self fun ⟨C, hC⟩ => hstop ⟨C, ?_⟩
  exact (IsBest.congr (hag Hd).1 (hag Hd).2).2 hC

/-- **T1 §6, unanimity**, in its setting. -/
theorem proposal_votes_of_setting (hs : UnanimitySetting tr H U g p P k ℓp d pay) :
    ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = p → e.msg.head = P.root := by
  have hU : Coherent U := hs.standalone.run.localRun.coherent
  -- the canonical walk
  set T := insert P (ℓp.frame.viableTree ℓp.frame.tree)
  set sc := goldfishScore sp ℓp.frame (View.ofLists pay) ((p : Int) - 1)
  set el := goldfishEligible sp ℓp.frame (sp.ts p) (View.ofLists pay) ((p : Int) - 1)
  obtain ⟨hpw, hPU, hΦpU, hsd, hdP⟩ := proposal_walkEnd hs
  have hTU : T ⊆ U := Set.insert_subset hPU fun B hB => hΦpU hB.1
  -- a vote extending a block: its head block extends it
  have hext : ∀ {e : Em sp FGP} {Hd B}, Hd ∈ U → Hd.root = e.msg.head →
      VoteExtends U e.msg B → Anc U B Hd := by
    intro e Hd B hHd hr ⟨Hd', hHd', hr', hB⟩
    obtain rfl : Hd' = Hd := hU.1 hHd' hHd (hr'.trans hr.symm)
    exact hB
  intro x₁ hx₁ j₁ e₁ hv₁ hes₁
  -- the earliest honest slot-`p` vote
  have hex : ∃ c, ∃ x ∈ H, ∃ ℓ e, CastAt tr x c ℓ e ∧ e.msg.slot = p := by
    obtain ⟨ℓ, hc, he⟩ := hv₁
    exact ⟨j₁, x₁, hx₁, ℓ, e₁, ⟨hc, he⟩, hes₁⟩
  classical
  obtain ⟨x₀, hx₀, ℓ₀, e₀, hc₀, hes₀⟩ := Nat.find_spec hex
  have hmin : ∀ c < Nat.find hex, ∀ x ∈ H, ∀ e, VoteAt tr x c e → e.msg.slot ≠ p :=
    fun c hc x hx e ⟨ℓ, h, he⟩ hes => Nat.find_min hex hc ⟨x, hx, ℓ, e, ⟨h, he⟩, hes⟩
  set a₀ := getAnchor sp e₀.readPoint ℓ₀.frame (tr.time (Nat.find hex))
  obtain ⟨E₀, hE₀, hE₀r, hw₀⟩ := vote_walkEnd hs hx₀ hc₀ hes₀
  obtain ⟨ha₀, ⟨ha₀d, hall₀⟩ | ⟨z, hz, j', hj', e', hv', hs', -⟩⟩ :=
    vote_anchor_cases hs hx₀ hc₀ hes₀
  swap
  · exact absurd hs' (hmin j' hj' z hz e' hv')
  -- every honest slot-`p` vote has head `E₀`
  have hA : ∀ c, ∀ x ∈ H, ∀ ℓ e, CastAt tr x c ℓ e → e.msg.slot = p →
      ∀ Hd ∈ U, Hd.root = e.msg.head → Hd = E₀ := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih =>
    intro x hx ℓ e hc hes Hd hHd hHdr
    obtain ⟨Hw, hHw, hHwr, hw⟩ := vote_walkEnd hs hx hc hes
    obtain rfl : Hw = Hd := hU.1 hHw hHd (hHwr.trans hHdr.symm)
    obtain ⟨ha, hcases⟩ := vote_anchor_cases hs hx hc hes
    have ha₀H : Anc U a₀ Hw := hext hHw hHwr (hall₀ x hx c e ⟨ℓ, hc⟩ hes)
    rcases anc_total hU (hw.anc hTU ha) ha₀H with h | h
    · exact hw.of_anc hU hTU h ha₀H |>.unique hw₀
    · have haE : Anc U (getAnchor sp e.readPoint ℓ.frame (tr.time c)) E₀ := by
        rcases hcases with ⟨-, hall⟩ | ⟨z, hz, j', hj', e', hv', hs', hext'⟩
        · exact hext hE₀ hE₀r (hall x₀ hx₀ _ e₀ ⟨ℓ₀, hc₀⟩ hes₀)
        · obtain ⟨ℓ', hc', he'⟩ := hv'
          obtain ⟨Hz, hHz, hHzr⟩ := honest_head hs.standalone.run hz ⟨ℓ', hc', he'⟩
          have := ih j' hj' z hz ℓ' e' ⟨hc', he'⟩ hs' Hz hHz hHzr.1
          exact this ▸ hext hHz hHzr.1 hext'
      exact hw.unique (hw₀.of_anc hU hTU h haE)
  -- the canonical walk from `a₀` ends at `P`
  have hB : E₀ = P := by
    obtain ⟨hsU, hscases⟩ := proposal_anchor_cases hs
    have ha₀P : Anc U a₀ P := ha₀d.trans hdP
    rcases anc_total hU (hsd.trans hdP) ha₀P with h | h
    · exact hw₀.unique (hpw.of_anc hU hTU h ha₀P)
    · have hsE : Anc U d.start E₀ := by
        rcases hscases with hall | ⟨z, hz, j', e', hv', hs', hext'⟩
        · exact hext hE₀ hE₀r (hall x₀ hx₀ _ e₀ ⟨ℓ₀, hc₀⟩ hes₀)
        · obtain ⟨ℓ', hc', he'⟩ := hv'
          obtain ⟨Hz, hHz, hHzr⟩ := honest_head hs.standalone.run hz ⟨ℓ', hc', he'⟩
          have := hA j' z hz ℓ' e' ⟨hc', he'⟩ hs' Hz hHz hHzr.1
          exact this ▸ hext hHz hHzr.1 hext'
      exact (hw₀.of_anc hU hTU h hsE).unique hpw
  obtain ⟨ℓ₁, hc₁, he₁⟩ := hv₁
  obtain ⟨H₁, hH₁, hH₁r, -⟩ := honest_head hs.standalone.run hx₁ ⟨ℓ₁, hc₁, he₁⟩
  rw [← hH₁r, hA j₁ x₁ hx₁ ℓ₁ e₁ ⟨hc₁, he₁⟩ hes₁ H₁ hH₁ hH₁r, hB]

end Consensus.Goldilocks.SA

end

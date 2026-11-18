module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: the later-batch walk

`vote_extends_of_counted_batch`, over an SA trace: when a selected honest slot-`s` batch extends a
block `B`, is carried at the read point and outnumbers half of a set covering all merged voters,
and every live lock is viable and compatible with `B`, the successor vote extends `B`
(`SA.isBest_of_majority`, `SA.anc_getHead`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

/-! ### Over an SA trace -/

section SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (SA.Blk sp.n FGP)} {tr : SA.SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- The later-batch walk for a selected honest slot-`s` batch: its votes extend `B`, are
carried at the read point, and outnumber half of a set covering all merged voters.
Viability and compatibility of all live locks then make the successor vote extend `B`. -/
theorem vote_extends_of_counted_batch {ini} (hrun : SA.ACRun proposer tr H U ini)
    {s : Nat} {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (SA.goldilocksSA sp FGP ro)} {e : SA.Em sp FGP}
    (hc : SA.CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) {B : SA.Blk sp.n FGP}
    (hviab : SA.ViableAtVote ℓ e (s + 1) B)
    {SX W : Set (Fin sp.n)} (hSXH : SX ⊆ H)
    (hSXv : ∀ x ∈ SX, ∃ j e', SA.VoteAt tr x j e' ∧ e'.msg.slot = s)
    (hall : ∀ x ∈ SX, ∀ j e', SA.VoteAt tr x j e' → e'.msg.slot = s → SA.VoteExtends U e'.msg B)
    (hW : SA.voters (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes ⊆ W)
    (hcount : W.ncard < 2 * SX.ncard)
    (hcarry : SA.CarryAt tr U y i e s
      {v | ∃ x ∈ SX, ∃ j e', SA.VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s})
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L B) :
    SA.VoteExtends U e.msg B := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨-, -, -, hhead⟩ := SA.castAt_spec hr hy hc
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  have hσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := SA.voteDomain_anc hr hrun.vstart hy hc
  rw [hs] at hdomA
  have hBt : B ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact SA.mem_of_anc h hΦ.fcRoot_mem
  -- The selected honest batch supplies supporters of `B` at `y`.
  have hsupp : SX ⊆
      SA.supporters ℓ.frame (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s B := by
    intro w hwSX
    have hw := hSXH hwSX
    obtain ⟨j, e', hv, hvs⟩ := hSXv w hwSX
    obtain ⟨ℓw, hcw⟩ := id hv
    have hvw : e'.msg.val = w := (SA.castAt_spec hr hw hcw).1
    have hmem : e'.msg ∈ {v | ∃ x ∈ SX, ∃ j e', SA.VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s} :=
      ⟨w, hwSX, j, e', hv, rfl, hvs⟩
    -- `y` holds `e'.msg` itself (an honest validator has one slot-`s` vote)
    have hheld : SA.HeldBefore e.readPoint e'.msg (sp.ts s + 3 * sp.Δ) := by
      rcases hcarry.holds _ hmem with h | ⟨v₁, v₂, h12, h1, h2, hv₁, hv₂, hs₁, hs₂, hh₁, hh₂⟩
      · exact h
      · exfalso
        have hm : ∀ u, u.slot = s → SA.HeldBefore e.readPoint u (sp.ts s + 3 * sp.Δ) →
            u ∈ (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes := by
          intro u hus hu
          refine Or.inl (List.mem_filter.2 ⟨?_, ?_⟩)
          · simp only [SA.SAState.poolAt, show ¬ (((s + 1 : Nat) : Int) - 1 < 0) by omega,
              ite_false]
            simpa [hus] using hu.1
          · simpa [SA.freeze] using hu.2
        obtain ⟨j₁, -, e₁, hv₁', he₁⟩ :=
          SA.honest_merged_vote hrun hy hc (hm v₁ hs₁ hh₁) (hv₁.trans hvw ▸ hw)
        have := (SA.one_vote_per_slotU sp) FGP ro H U tr hr.toU w hw j₁ j e₁ e'
          (hv₁.trans hvw ▸ hv₁') hv (by rw [he₁, hs₁, hvs])
        exact h1 (he₁ ▸ this.2 ▸ rfl)
    obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads _ hmem
    obtain ⟨Hd, hHd, hHdr, hHds⟩ := SA.honest_head hrun hw hv
    obtain ⟨Hd', hHd', hHd'r, hBHd'⟩ := hall w hwSX j e' hv hvs
    have h1 : Hd = Hv := hU.1 hHd hHv (hHdr.trans hHvr.symm)
    have h2 : Hd' = Hv := hU.1 hHd' hHv (hHd'r.trans hHvr.symm)
    have := SA.carried_supporter hrun hy hc hs hBt hvs hheld
      ⟨Hv, hHv, hHvr, h1 ▸ hvs ▸ hHds, h2 ▸ hBHd', hacc Hv Relation.ReflTransGen.refl⟩
      (SA.honest_not_equivocator hrun hy hc (hvw ▸ hw))
    exact hvw ▸ this
  have hcore := SA.anc_getHead hU hΦ hΦU e.readPoint (tr.time i)
    (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int) (fun B hB =>
        SA.voteDomain_subset_tree hB) hdomA hviab.voteDomain
    hlocks fun X' Cx hCx hp hCxC =>
      SA.isBest_of_majority hΦ (SA.merged_support_subset hr hy hc (s + 1)) (fun B hB =>
          (SA.voteDomain_subset_tree hB.1))
        hsupp hW hcount hCx hp hCxC
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : B = SA.getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (SA.voteDomain sp e.readPoint ℓ.frame (s + 1)))
      (SA.mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
  · exact he ▸ hBt
  · exact (Anc.mem hcore he).2

end SA

/-! ### Over a run -/

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

variable {b : Time} {s₀ : Nat}

end Consensus.Goldilocks.Compose

end

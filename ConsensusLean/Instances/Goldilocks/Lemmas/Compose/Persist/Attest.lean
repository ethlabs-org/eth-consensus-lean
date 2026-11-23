module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Inv
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Persist, part 2: the honest attestations after the cut name no excluded entry

C1.1's attestation step (claims C1.1, "Proof shape"): an honest attestation signed at a time in
`(t_{s+1} + Δ, t_m + Δ]` has a source compatible with `B` (A1.9 at the node's `ac_to_fg` call
right before it), so its target names an ancestor of the source
(G0.2 (c), `entry_state_of_source`), which is compatible with `B`: not an excluded entry. -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder goldilocksAC Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {tr : GoldilocksTrace sp ro}
  {H : Set (Fin sp.n)} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {proposer : Nat → Fin sp.n}

/-- An honest signing is at a public time (it is a cut of a tick, C0.5 (c)). -/
theorem sign_public {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {a : FG.Att sp.n}
    (hc : tr.CallAt y j (.fg (.attest C (some a)))) : sp.toParams.IsPublic (tr.time j) := by
  obtain ⟨j₀, e, k, hg, -, hk⟩ := call_in_group hrun.toLocalRun hy hc
  have hm : Cut.fg (.attest C (some a)) ∈
      (Node.exec proposer dg y (tr.state y j₀) (tr.time j) e).2 :=
    List.mem_of_getElem? hk
  obtain ⟨xt, he⟩ := @signed_only_in_ticks sp.toParams (goldilocksNode sp ro) proposer dg y
    (tr.state y j₀) (tr.time j) e C a hm
  subst he
  exact hrun.tick_public y hy j₀ (tr.time j) ⟨xt, hg⟩

variable {ΔF : Time} {x : Fin sp.n} {i₀ s m : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
  {CV : Set (Vote sp.n)}

/-- At `t = t_{slot(t)} + Δ`, `ac_on_tick` of a joined node that has not voted in the slot
casts a vote. -/
theorem acOnTick_votes {FGP : Type} {ro' : ReplayOrder sp FGP} (self : Fin sp.n)
    (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP) {t : Time} (hj : AC.joined sp A t)
    (hv : A.votedSlot ≠ sp.slot t) (hm : A.mayVote (sp.slot t) = true)
    (ht : t = sp.ts (sp.slot t) + sp.Δ) :
    ((goldilocksAC sp FGP ro').step self A Φ t .tick).2 ≠ [] := by
  change (AC.acOnTick sp self A Φ t).2 ≠ []
  unfold AC.acOnTick
  dsimp only
  have hc : (t = sp.ts (sp.slot t) + sp.Δ) = True := eq_true ht
  simp only [hj, not_true_eq_false, hc, ↓reduceIte]
  unfold AC.tryVote
  dsimp only
  simp only [hm, ↓reduceIte]
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  split_ifs with h₁ h₂
  · rcases h₁ with h | h | h
    · exact absurd hj h
    · exact absurd h hv
    · linarith
  · linarith [h₂.1]
  all_goals simp

end Consensus.Goldilocks.Compose

end

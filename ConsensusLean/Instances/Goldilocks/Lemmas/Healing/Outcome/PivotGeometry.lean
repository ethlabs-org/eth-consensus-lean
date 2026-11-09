module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views

public section

/-! # Goldilocks Healing: the geometry of a proposal pivot

The block-tree part of the post-reset pivot, stated over an ambient coherent block set `U`, a set
`old` of old sources and an eligibility predicate on casts. Run facts enter only as premises, so
the constant-honesty and growing-fault pivots instantiate the same proofs: their readers may be
honest at different cuts and their old sources need not have honest writers any more.

* `proposal_suffix_viable_of_floor`: the proposal walk above a block `D` consists of viable
  heads once every held block above `D` reaches the reader's height floor.
* `proposal_pivot_of_supports`: the deepest of the walk's start and the old sources on the walk
  is a viable pivot that every eligible cast's anchor-to-head walk meets, either at `P` or on the
  walk below `P`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- **Viable proposal suffix from the height floor.** On a realized proposal frame, the walk from
a block `D` above the walk's start to the duty head consists of viable heads, provided every held
block above `D` reaches the reader's height floor. -/
theorem proposal_suffix_viable_of_floor {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    {st : NodeState (goldilocksNode sp ro)} {Φ : SA.Frm sp.n (List (FG.Att sp.n))}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) (hfr : Φ = Node.frame st)
    {A : SA.SAState sp.n} {t : Time} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hd : (SA.acProposal sp A Φ t).2 = some (d, pay))
    {D : SA.Blk sp.n (List (FG.Att sp.n))} (hDt : D ∈ Φ.tree) (hsD : Φ.Anc d.start D)
    -- The floor supplier: a held block above `D` reaches the reader's height floor.
    (hfloor : ∀ X ∈ st.fg.tree, Anc U D X →
      st.fg.headHeightFloor ≤ (st.fg.σ X.root).h) :
    ∀ X, Φ.Anc D X → Φ.Anc X d.head → X ∈ Φ.viableHeads := by
  intro X hDX _
  have hXt : X ∈ Φ.tree := Compose.mem_of_anc_left hDX hDt
  obtain ⟨A, _, hstart, _⟩ := Compose.acProposal_walk hd
  have hfX : Φ.Anc Φ.fcRoot X := by
    rw [hstart] at hsD
    exact ((SA.fcRoot_anc_getAnchor hΦ A t).trans hsD).trans hDX
  have hDXU := hDX.mono hΦU
  subst hfr
  obtain ⟨hXs, hFX⟩ := hXt
  exact ⟨hXs, hFX, hfX.mono (fun _ h => h.1), hfloor X hXs hDXU⟩

/-- **The proposal pivot from its suppliers.** On a realized proposal frame `Φ` inside a
coherent `U`, with `P` the child of the duty head, let `D` be the deepest of the walk's start and
the old sources on the walk. Then `D` is a viable pivot on the walk, and every eligible cast's
walk from its anchor to its ghost head passes through `P` or through the walk between `D` and the
duty head. -/
theorem proposal_pivot_of_supports {tr : GoldilocksTrace sp ro}
    {U : Set (SA.Blk sp.n (List (FG.Att sp.n)))} (hU : Coherent U)
    {Φ : SA.Frm sp.n (List (FG.Att sp.n))} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    {A : SA.SAState sp.n} {t : Time} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hd : (SA.acProposal sp A Φ t).2 = some (d, pay))
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPQ : P.parent = some d.head.root)
    (old : Set (SA.Blk sp.n (List (FG.Att sp.n)))) {u : Nat}
    (Elig : Fin sp.n → Nat → ACLabel (goldilocksNode sp ro) → SA.Em sp (List (FG.Att sp.n)) →
      Prop)
    -- Old sources pass: every old source is below the duty head.
    (hpass : ∀ O ∈ old, Anc U O d.head)
    -- Suffix viability: the walk above a block on it that extends every old source is viable.
    (hviable : ∀ D ∈ Φ.tree, Φ.Anc d.start D → (∀ O ∈ old, Anc U O D) →
      ∀ X, Φ.Anc D X → Φ.Anc X d.head → X ∈ Φ.viableHeads)
    -- Cast frames: an eligible cast reads a well-formed frame inside `U`.
    (hframe : ∀ y j ell e, Elig y j ell e → FrameOK ell.frame ∧ ell.frame.tree ⊆ U)
    -- Cast heads: an eligible cast votes for the root of its ghost head.
    (hhead : ∀ y j ell e, Elig y j ell e →
      e.msg.head = (SA.getHead sp e.readPoint ell.frame (tr.time j)
        (ell.frame.viableTree (SA.voteDomain sp e.readPoint ell.frame u))
        (SA.mergedVoteView sp e.readPoint ell.frame u) ((u : Int) - 1)).root)
    -- Start support: an eligible cast's ghost head extends the walk's start.
    (hstart : ∀ y j ell e, Elig y j ell e →
      Anc U d.start (SA.getHead sp e.readPoint ell.frame (tr.time j)
        (ell.frame.viableTree (SA.voteDomain sp e.readPoint ell.frame u))
        (SA.mergedVoteView sp e.readPoint ell.frame u) ((u : Int) - 1)))
    -- Old-source support: an eligible cast's vote extends every old source.
    (hold : ∀ O ∈ old, ∀ y j ell e, Elig y j ell e → SA.VoteExtends U e.msg O)
    -- Anchor dichotomy: for a block `D` of `U` below the duty head and above every old source,
    -- an eligible cast's anchor is below `D`, or above `D` and below `P`.
    (hanchor : ∀ D ∈ U, d.head ∈ U → Anc U D d.head → (∀ O ∈ old, Anc U O D) →
      ∀ y j ell e, Elig y j ell e →
        Anc U (SA.getAnchor sp e.readPoint ell.frame (tr.time j)) D ∨
          (Anc U D (SA.getAnchor sp e.readPoint ell.frame (tr.time j)) ∧
            Anc U (SA.getAnchor sp e.readPoint ell.frame (tr.time j)) P)) :
    ∃ D, Φ.Anc d.start D ∧ Φ.Anc D d.head ∧
      (∀ X, Φ.Anc D X → Φ.Anc X d.head → X ∈ Φ.viableHeads) ∧
      ∀ y j ell e, Elig y j ell e →
        ∃ X, (X = P ∨ (Φ.Anc D X ∧ Φ.Anc X d.head)) ∧
          ell.frame.Anc (SA.getAnchor sp e.readPoint ell.frame (tr.time j)) X ∧
          ell.frame.Anc X (SA.getHead sp e.readPoint ell.frame (tr.time j)
            (ell.frame.viableTree (SA.voteDomain sp e.readPoint ell.frame u))
            (SA.mergedVoteView sp e.readPoint ell.frame u) ((u : Int) - 1)) := by
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hΦ hd
  have hQt : d.head ∈ Φ.tree := Compose.mem_of_anc_left hsQ hst
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦ (S := {X | X ∈ Φ.tree ∧
      Φ.Anc d.start X ∧ Φ.Anc X d.head ∧ (X = d.start ∨ X ∈ old)})
    (fun X hX => hX.1) ⟨d.start, hst, .refl, hsQ, Or.inl rfl⟩
  obtain ⟨hDt, hsD, hDQ, hDk⟩ := (SA.deepest_mem hD).1
  have hmax := SA.anc_deepest hΦ (fun X hX => hX.1)
    (fun X hX Y hY => Anc.total hΦ.coherent hX.2.2.1 hY.2.2.1) hD
  have hDold : ∀ O ∈ old, Anc U O D := by
    intro O hO
    have hOQ := hpass O hO
    rcases Anc.total hU hOQ (Anc.mono hΦU hsQ) with h | h
    · exact h.trans (Anc.mono hΦU hsD)
    have hOt := Compose.mem_between hU hΦ hΦU hst hQt h hOQ
    exact Anc.mono hΦU (hmax O ⟨hOt, SA.anc_tree_of_anc_U hU hΦ hΦU hst h hOt,
      SA.anc_tree_of_anc_U hU hΦ hΦU hOt hOQ hQt, Or.inr hO⟩)
  refine ⟨D, hsD, hDQ, hviable D hDt hsD hDold, fun y j ell e hel => ?_⟩
  obtain ⟨hΨ, hΨU⟩ := hframe y j ell e hel
  have hat := Compose.anchor_tree hΨ e.readPoint (tr.time j)
  have hah : ell.frame.Anc (SA.getAnchor sp e.readPoint ell.frame (tr.time j))
      (SA.getHead sp e.readPoint ell.frame (tr.time j)
        (ell.frame.viableTree (SA.voteDomain sp e.readPoint ell.frame u))
        (SA.mergedVoteView sp e.readPoint ell.frame u) ((u : Int) - 1)) :=
    SA.anc_ghost (fun B hB => SA.voteDomain_subset_tree hB.1) _ hat
  have hht := Compose.mem_of_anc_left hah hat
  have hDh : Anc U D (SA.getHead sp e.readPoint ell.frame (tr.time j)
      (ell.frame.viableTree (SA.voteDomain sp e.readPoint ell.frame u))
      (SA.mergedVoteView sp e.readPoint ell.frame u) ((u : Int) - 1)) := by
    rcases hDk with rfl | hDo
    · exact hstart y j ell e hel
    obtain ⟨W, hW, hWr, hDW⟩ := hold D hDo y j ell e hel
    rwa [hU.1 hW (hΨU hht) (hWr.trans (hhead y j ell e hel))] at hDW
  rcases hanchor D (hΦU hDt) (hΦU hQt) (Anc.mono hΦU hDQ) hDold y j ell e hel with
    haD | ⟨hDa, haP⟩
  · have hDt' := Compose.mem_between hU hΨ hΨU hat hht haD hDh
    exact ⟨D, Or.inr ⟨.refl, hDQ⟩, SA.anc_tree_of_anc_U hU hΨ hΨU hat haD hDt',
      SA.anc_tree_of_anc_U hU hΨ hΨU hDt' hDh hht⟩
  by_cases haPe : SA.getAnchor sp e.readPoint ell.frame (tr.time j) = P
  · exact ⟨P, Or.inl rfl, haPe ▸ .refl, haPe ▸ hah⟩
  have haQ := Compose.anc_parent hU haP haPe hPQ (hΦU hQt)
  have hat' := Compose.mem_between hU hΦ hΦU hDt hQt hDa haQ
  exact ⟨_, Or.inr ⟨SA.anc_tree_of_anc_U hU hΦ hΦU hDt hDa hat',
    SA.anc_tree_of_anc_U hU hΦ hΦU hat' haQ hQt⟩, .refl, hah⟩

end Consensus.Goldilocks.Healing

end

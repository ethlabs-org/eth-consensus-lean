module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree

public section

/-! # Goldilocks Compose/AnyAC: the interface at any AC

The frame-level consequences of requirements 1–5 at a reachable state, whose frame is well
formed (`FrameIn`, from the call law): a block above `fc_root` is in the tree and extends `Φ.F`,
since `Φ.F ⪯ fc_root ∈ Φ.tree` and the tree is rooted at `Φ.F`. -/

namespace Consensus.Goldilocks.Compose

variable {P : Params} {FGP : Type} {A : ACInterface P FGP}

/-- The frame of a reachable state is well formed and inside `U`. -/
theorem frameIn_of_reachableAt {self : Fin P.n} {U : Set A.Blk} {s : A.State} {Φ : A.Frm}
    {t : Time} (h : A.ReachableAt self U s Φ t) : A.FrameIn U Φ := by
  cases h with
  | init _ _ hin => exact hin
  | step _ _ _ hok => exact hok.1

/-- A descendant of a block of a set, inside the set, is in the set. -/
private theorem mem_of_anc_mem {S : Set A.Blk} {X Y : A.Blk} (h : Anc S X Y) (hX : X ∈ S) :
    Y ∈ S := by
  by_cases he : X = Y
  · exact he ▸ hX
  · exact (Anc.mem h he).2

/-- A block above `fc_root` in a well-formed frame is in the tree and extends `Φ.F`. -/
theorem held_of_fcRoot_anc {Φ : A.Frm} (hΦ : FrameOK Φ) {X : A.Blk} (h : Φ.Anc Φ.fcRoot X) :
    X ∈ Φ.tree ∧ Φ.Anc Φ.F X :=
  ⟨mem_of_anc_mem h hΦ.fcRoot_mem, hΦ.F_anc_fcRoot.trans h⟩

variable (A)

/-- **The tips are nested.** -/
theorem tips_nested : TipsNested A := by
  intro hreq self U hU s Φ t₀ hr t ht
  have hΦ := (frameIn_of_reachableAt hr).1
  obtain ⟨hfh, hFc, hch⟩ := hreq.outputs self U hU s Φ t₀ hr t ht
  exact ⟨mem_of_anc_mem hFc hΦ.rooted.1, (held_of_fcRoot_anc hΦ hfh).1, hFc, hch⟩

/-- **The parent of a proposal is held.** -/
theorem proposal_parent_held : ProposalParentHeld A := by
  intro hreq self U hU s Φ t₀ hr σ hσ d p hp
  exact held_of_fcRoot_anc (frameIn_of_reachableAt hr).1
    ((hreq.heads self U hU s Φ t₀ hr).1 σ hσ d p hp).1

/-- **The source is held.** -/
theorem source_held : SourceHeld A := by
  intro hreq self U hU s Φ t₀ hr t ht C hC
  have hΦ := (frameIn_of_reachableAt hr).1
  obtain ⟨hCt, hfC, -⟩ := hreq.source self U hU s Φ t₀ hr t ht C hC
  exact ⟨hCt, hΦ.F_anc_fcRoot.trans hfC⟩

/-- **Duty heads are held.** -/
theorem duty_heads_held : DutyHeadsHeld A := by
  intro hreq self U hU s Φ t₀ hr t c Φ' ht hok e he d hd
  exact held_of_fcRoot_anc hok.1.1
    ((hreq.heads self U hU s Φ t₀ hr).2 t c Φ' ht hok e he d hd).1

end Consensus.Goldilocks.Compose

end

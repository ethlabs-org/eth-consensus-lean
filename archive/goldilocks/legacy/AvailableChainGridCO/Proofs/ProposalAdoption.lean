module
public import AvailableChainGridCO.Proofs.WalkTransport
public import AvailableChainGridCO.Proofs.Preservation

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- The local proposal merge obligations. The target tree has no new
block except the honest proposal. The merged pool has the source seat
count and gives the same scores to common old blocks. These are receipt
and authentication obligations, not assumptions about the HEAD result. -/
structure ProposalViewTransport (p : Params) {n : Nat}
    (source reader : State n) (s : Slot) (B : Block) : Prop where
  tree : ∀ C ∈ voterTree p reader s, C = B ∨ C ∈ source.blocks
  count : voterCount (voterView p reader s) = voterCount (proposerView source s)
  score : ∀ C ∈ source.blocks, C ∈ voterTree p reader s →
    goldfishScore reader.blocks (voterView p reader s) (voterSupportView p reader s) C =
      goldfishScore source.blocks (proposerView source s) (proposerSupportView source s) C

/-- Proposal adoption also permits extra ineligible paths in the target
tree. Only eligible candidates must reflect to the source or be the fresh
proposal. The target anchor can be any prefix of the ordinary parent. -/
theorem ghost_adopts_of_rooted_proposal_transport (p : Params) {n : Nat}
    (source reader : State n) (s : Slot) (B parent : Block)
    (tree : List Block) (sourceAnchor anchor : Block) (htree : tree ⊆ reader.blocks)
    (hsourceRoot : RootInjectiveBelow source.blocks)
    (hreaderRoot : RootInjectiveBelow reader.blocks)
    (hsourceClosed : StoredPrefixClosed source)
    (hsource : ghost sourceAnchor source.blocks
      (goldfishScore source.blocks (proposerView source s) (proposerSupportView source s))
      (goldfishEligible source.blocks (proposerView source s) (proposerSupportView source s) s)
        = parent)
    (hanchor : Block.Preceq sourceAnchor anchor ∧ Block.Preceq anchor parent)
    (hparent : B.parent? = some parent) (hslot : B.slot = s)
    (hpath : ∀ C, C ≠ .genesis → Block.Preceq C B → C ∈ tree)
    (hreflect : ∀ C ∈ tree, goldfishEligible reader.blocks (voterView p reader s)
      (voterSupportView p reader s) s C = true → C = B ∨ C ∈ source.blocks)
    (hcount : voterCount (voterView p reader s) = voterCount (proposerView source s))
    (hscore : ∀ C ∈ source.blocks, C ∈ tree →
      goldfishScore reader.blocks (voterView p reader s) (voterSupportView p reader s) C =
        goldfishScore source.blocks (proposerView source s) (proposerSupportView source s) C) :
    Block.Preceq B (ghost anchor tree
      (goldfishScore reader.blocks (voterView p reader s) (voterSupportView p reader s))
      (goldfishEligible reader.blocks (voterView p reader s) (voterSupportView p reader s) s)) := by
  let srcScore := goldfishScore source.blocks (proposerView source s) (proposerSupportView source s)
  let dstScore := goldfishScore reader.blocks (voterView p reader s) (voterSupportView p reader s)
  let srcEligible := goldfishEligible source.blocks (proposerView source s)
    (proposerSupportView source s) s
  let dstEligible := goldfishEligible reader.blocks (voterView p reader s)
    (voterSupportView p reader s) s
  have hroot : RootInjectiveBelow tree := by
    intro A C hA hC he
    obtain ⟨D, hd, hAD⟩ := hA
    obtain ⟨F, hf, hCF⟩ := hC
    exact hreaderRoot A C ⟨D, htree hd, hAD⟩
      ⟨F, htree hf, hCF⟩ he
  have helig : ∀ C ∈ source.blocks, C ∈ tree →
      dstEligible C = srcEligible C := by
    intro C hc ht
    dsimp [dstEligible, srcEligible, goldfishEligible]
    rw [hcount, hscore C hc ht]
  have hBne : B ≠ .genesis := by intro he; simp [he, Block.parent?] at hparent
  have hB := hpath B hBne (block_preceq_self B)
  apply ghost_adopts_fresh_child source.blocks tree srcScore dstScore
    srcEligible dstEligible sourceAnchor anchor parent B hsourceRoot hroot hsource
    hanchor hparent hpath hB
  · simp [dstEligible, goldfishEligible, hslot]
  · intro D hd hp he
    rcases hreflect D hd he with heq | hsourceD
    · exact heq
    · have hstop := ghost_result_no_eligible_child source.blocks srcScore srcEligible sourceAnchor
        hsourceRoot hsourceClosed D hsourceD (by rwa [hsource])
      rw [← helig D hsourceD hd, he] at hstop
      contradiction
  · intro X C _ _ _ hs hCP
    have hc := ghostStep_child source.blocks srcScore srcEligible X C hs
    have hn : C ≠ .genesis := by intro he; simp [he, Block.parent?] at hc
    have hPB : Block.Preceq parent B := by
      cases B with
      | genesis => contradiction
      | node P slot r_slot root =>
          have he : P = parent := by simpa [Block.parent?] using hparent
          subst P
          exact Bool.or_eq_true_iff.mpr (Or.inr (block_preceq_self parent))
    have ht := hpath C hn (prefix_trans C parent B hCP hPB)
    exact ⟨ht, (helig C hc.1 ht).trans hc.2.2⟩
  · intro X D _ _ hne hd hp he
    rcases hreflect D hd he with hDB | hD
    · subst D
      have hXP : X = parent := Option.some.inj (hp.symm.trans hparent)
      exact (hne hXP).elim
    · exact ⟨hD, (helig D hD hd).symm.trans he⟩
  · exact hscore

/-- The original ordinary-walk interface is retained. -/
theorem ghost_adopts_of_eligible_proposal_transport (p : Params) {n : Nat}
    (source reader : State n) (s : Slot) (B parent : Block)
    (tree : List Block) (anchor : Block) (htree : tree ⊆ reader.blocks)
    (hsourceRoot : RootInjectiveBelow source.blocks)
    (hreaderRoot : RootInjectiveBelow reader.blocks)
    (hsourceClosed : StoredPrefixClosed source)
    (hsource : ghost .genesis source.blocks
      (goldfishScore source.blocks (proposerView source s) (proposerSupportView source s))
      (goldfishEligible source.blocks (proposerView source s) (proposerSupportView source s) s)
        = parent)
    (hanchor : Block.Preceq anchor parent)
    (hparent : B.parent? = some parent) (hslot : B.slot = s)
    (hpath : ∀ C, C ≠ .genesis → Block.Preceq C B → C ∈ tree)
    (hreflect : ∀ C ∈ tree, goldfishEligible reader.blocks (voterView p reader s)
      (voterSupportView p reader s) s C = true → C = B ∨ C ∈ source.blocks)
    (hcount : voterCount (voterView p reader s) = voterCount (proposerView source s))
    (hscore : ∀ C ∈ source.blocks, C ∈ tree →
      goldfishScore reader.blocks (voterView p reader s) (voterSupportView p reader s) C =
        goldfishScore source.blocks (proposerView source s) (proposerSupportView source s) C) :
    Block.Preceq B (ghost anchor tree
      (goldfishScore reader.blocks (voterView p reader s) (voterSupportView p reader s))
      (goldfishEligible reader.blocks (voterView p reader s) (voterSupportView p reader s) s)) :=
  ghost_adopts_of_rooted_proposal_transport p source reader s B parent tree .genesis anchor
    htree hsourceRoot hreaderRoot hsourceClosed hsource ⟨genesis_prefix _, hanchor⟩
    hparent hslot hpath hreflect hcount hscore

/-- Honest proposal adoption from an ordinary source walk that starts at
genesis. This walk remains available when release removes a constraint.
The target root is checked after release, and the view-transport premises
are separate from the source walk and the delivered proposal path. -/
theorem forkChoice_adopts_of_proposal_transport (p : Params) {n : Nat}
    (source reader : State n) (s : Slot) (B parent : Block)
    (hsourceRoot : RootInjectiveBelow source.blocks)
    (hreaderRoot : RootInjectiveBelow reader.blocks)
    (hsourceClosed : StoredPrefixClosed source)
    (hsource : ghost .genesis source.blocks
      (goldfishScore source.blocks (proposerView source s) (proposerSupportView source s))
      (goldfishEligible source.blocks (proposerView source s) (proposerSupportView source s) s)
        = parent)
    (hanchor : Block.Preceq (liveRoot reader) parent)
    (hparent : B.parent? = some parent) (hslot : B.slot = s)
    (hpath : ∀ C, C ≠ .genesis → Block.Preceq C B → C ∈ voterTree p reader s)
    (hviews : ProposalViewTransport p source reader s B) :
    Block.Preceq B (forkChoice reader (voterTree p reader s)
      (voterView p reader s) (voterSupportView p reader s) s) :=
  ghost_adopts_of_eligible_proposal_transport p source reader s B parent
    (voterTree p reader s) (liveRoot reader) (fun _ h => (List.mem_filter.mp h).1)
    hsourceRoot hreaderRoot hsourceClosed hsource hanchor hparent hslot hpath
    (fun C hc _ => hviews.tree C hc) hviews.count hviews.score

/-- A stored proposal and reachable prefix closure supply the complete
path used by local proposal adoption. No separate path premise remains. -/
theorem forkChoice_adopts_stored_proposal (p : Params) {n : Nat}
    (source reader : State n) (s : Slot) (B parent : Block)
    (o : Wire n) (raw support : List (HeadWire n))
    (ho : o ∈ reader.proposals) (hp : o.payload = .proposal B raw support)
    (hB : B ∈ reader.blocks) (hslot : B.slot = s)
    (hsourceRoot : RootInjectiveBelow source.blocks)
    (hreaderRoot : RootInjectiveBelow reader.blocks)
    (hsourceClosed : StoredPrefixClosed source) (hreaderClosed : StoredPrefixClosed reader)
    (hsource : ghost .genesis source.blocks
      (goldfishScore source.blocks (proposerView source s) (proposerSupportView source s))
      (goldfishEligible source.blocks (proposerView source s) (proposerSupportView source s) s)
        = parent)
    (hanchor : Block.Preceq (liveRoot reader) parent)
    (hparent : B.parent? = some parent)
    (hviews : ProposalViewTransport p source reader s B) :
    Block.Preceq B (forkChoice reader (voterTree p reader s)
      (voterView p reader s) (voterSupportView p reader s) s) :=
  forkChoice_adopts_of_proposal_transport p source reader s B parent hsourceRoot hreaderRoot
    hsourceClosed hsource hanchor hparent hslot
    (fun C hn hCB => proposal_path_mem_voterTree p reader s o B C raw support
      ho hp hslot hreaderClosed hB hn hCB) hviews

end AvailableChain.GridCO
end

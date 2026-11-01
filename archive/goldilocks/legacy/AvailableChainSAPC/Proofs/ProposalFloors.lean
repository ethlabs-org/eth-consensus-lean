module
public import AvailableChainSAPC.Proofs.ProposalTransport

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

private theorem floor_prefix_of_score_transport (p : Params) {n : Nat}
    (source target : State n) (sourceTree targetTree : List Block)
    (sourceRaw targetRaw sourceSupport targetSupport : List (GridCO.Wire n)) (r : Slot)
    (hsourceRoot : GridCO.RootInjectiveBelow sourceTree)
    (htargetRoot : GridCO.RootInjectiveBelow targetTree)
    (htarget : targetTree ⊆ target.base.blocks)
    (hcount : GridCO.voterCount sourceRaw = GridCO.voterCount targetRaw)
    (hscore : ∀ c, GridCO.goldfishScore source.base.blocks sourceRaw sourceSupport c =
      GridCO.goldfishScore target.base.blocks targetRaw targetSupport c)
    (hpath : ∀ c, c ≠ .genesis →
      pcFaultCap p < GridCO.goldfishScore source.base.blocks sourceRaw sourceSupport c →
      c ∈ targetTree)
    (hreflect : ∀ c ∈ targetTree, c ≠ .genesis →
      pcFaultCap p < GridCO.goldfishScore target.base.blocks targetRaw targetSupport c →
      c ∈ sourceTree) :
    Block.Preceq (floor p source sourceTree sourceRaw sourceSupport r)
      (floor p target targetTree targetRaw targetSupport r) := by
  let b := floor p source sourceTree sourceRaw sourceSupport r
  change Block.Preceq b (floor p target targetTree targetRaw targetSupport r)
  by_cases hg : b = .genesis
  · simpa only [hg] using GridCO.genesis_prefix
      (floor p target targetTree targetRaw targetSupport r)
  have hf := floor_properties p source sourceTree sourceRaw sourceSupport r hg
  have high (c : Block) (hc : Block.Preceq c b) :
      pcFaultCap p < GridCO.goldfishScore source.base.blocks sourceRaw sourceSupport c :=
    hf.2.2.trans_le (GridCO.goldfishScore_prefix_mono _ _ _ c b hc)
  apply floor_covers p target targetTree targetRaw targetSupport r b
    (htarget (hpath b hg hf.2.2)) hg
  · apply GridCO.ghost_prefix_of_score_transport sourceTree targetTree _ _ _ _
      (pcFaultCap p) b hsourceRoot htargetRoot hf.2.1
      (fun c hn hc => hpath c hn (high c hc)) (fun c _ hc => high c hc)
      (fun c => (hscore c).symm)
    · intro c
      simp only [GridCO.goldfishEligible, hcount, hscore]
    · exact hreflect
  · exact hscore b ▸ hf.2.2

/-- Full merge gives the same F4 floor at an active HEAD and at the
honest proposer. This holds above the cap and for any selected PC.
Extra private paths are bounded by detected equivocation, not by the
actual fault count. -/
theorem honest_proposal_floor_eq {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hroot : RootInjective E (sapcInterface p).toInterface rho)
    (hnet : PartialSynchrony (sapc p) E rho)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ freezeTime p r) (hh : voteTime p (r + 1) ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest)
    (hactive : capBroken p (headState p rho (r + 1) reader) = false)
    (cert : Option (PC p.n)) :
    let source := proposalState p rho (r + 1)
    let target := headState p rho (r + 1) reader
    floor p source source.base.blocks (GridCO.proposerView source.base (r + 1))
        (GridCO.proposerSupportView source.base (r + 1)) (r + 1) =
      floor p target (activeVoterTree p target (r + 1) cert)
        (GridCO.voterView p.engine target.base (r + 1))
        (GridCO.voterSupportView p.engine target.base (r + 1)) (r + 1) := by
  set_option backward.isDefEq.respectTransparency false in
  let source := proposalState p rho (r + 1)
  let target := headState p rho (r + 1) reader
  let tree := activeVoterTree p target (r + 1) cert
  let srcRaw := GridCO.proposerView source.base (r + 1)
  let srcSupport := GridCO.proposerSupportView source.base (r + 1)
  let dstRaw := GridCO.voterView p.engine target.base (r + 1)
  let dstSupport := GridCO.voterSupportView p.engine target.base (r + 1)
  let a := floor p source source.base.blocks srcRaw srcSupport (r + 1)
  let c := floor p target tree dstRaw dstSupport (r + 1)
  have counts := honest_proposal_counts p E rho hx hΔ hnet hrelay r hsync hh b hb reader hr
  have sourceRoot : GridCO.RootInjectiveBelow source.base.blocks := by
    simpa only [source, proposalState, clock_blocks] using!
      time_input_rootInjectiveBelow p E rho hx.toScheduleWellFormed hroot
        (proposalTime p (r + 1)) (rho.proposerOf (r + 1))
  have targetRoot : GridCO.RootInjectiveBelow target.base.blocks := by
    simpa only [target, headState, clock_blocks] using!
      time_input_rootInjectiveBelow p E rho hx.toScheduleWellFormed hroot
        (voteTime p (r + 1)) reader
  have treeRoot : GridCO.RootInjectiveBelow tree := by
    intro x y hx hy he
    obtain ⟨d, hd, hxd⟩ := hx
    obtain ⟨e, he', hye⟩ := hy
    exact targetRoot x y ⟨d, activeVoterTree_subset p target (r + 1) cert hd, hxd⟩
      ⟨e, activeVoterTree_subset p target (r + 1) cert he', hye⟩ he
  have sourcePath (d : Block)
      (hd : pcFaultCap p < GridCO.goldfishScore target.base.blocks dstRaw dstSupport d) :
      d ∈ source.base.blocks :=
    honest_proposal_active_score_path p E rho hx hΔ hnet hrelay r hsync hh b hb reader hr
      hactive d hd
  have targetPath (d : Block) (hn : d ≠ .genesis)
      (hd : pcFaultCap p < GridCO.goldfishScore source.base.blocks srcRaw srcSupport d) :
      d ∈ tree := by
    let events := rho.events.filter (fun e => decide (e.time < voteTime p (r + 1))) ++
      [.tick reader (voteTime p (r + 1))]
    have he : (events.foldl World.step World.init) reader = target := by
      simp only [events, List.foldl_append, List.foldl_cons, List.foldl_nil,
        World.step, Function.update_self]
      rfl
    have hd' : pcFaultCap p < GridCO.goldfishScore target.base.blocks dstRaw dstSupport d :=
      counts.2.2 d ▸ hd
    have h := active_voter_score_path p events reader (r + 1) cert d hn
      (by simpa only [he] using hactive) (by simpa only [he] using hd')
    simpa only [he] using h
  have hac : Block.Preceq a c := floor_prefix_of_score_transport p source target
    source.base.blocks tree srcRaw dstRaw srcSupport dstSupport (r + 1) sourceRoot treeRoot
    (activeVoterTree_subset p target (r + 1) cert) counts.1 counts.2.2 targetPath
    (fun d _ _ hd => sourcePath d hd)
  have hca : Block.Preceq c a := floor_prefix_of_score_transport p target source
    tree source.base.blocks dstRaw srcRaw dstSupport srcSupport (r + 1) treeRoot sourceRoot
    (List.Subset.refl _) counts.1.symm (fun d => (counts.2.2 d).symm)
    (fun d _ hd => sourcePath d hd) (fun d _ hn hd => targetPath d hn hd)
  have ordered (d : Block) (hd : d ∈ source.base.blocks) : GridCO.SlotOrdered d := by
    simp only [source, proposalState, clock_blocks] at hd
    exact (paths_at_fold p _ (rho.proposerOf (r + 1))).2.2 d hd
  have amem : a ∈ source.base.blocks := by
    by_cases hg : a = .genesis
    · simpa only [hg] using (proposalState_paths p rho (r + 1)).2
    · exact (floor_properties p source source.base.blocks srcRaw srcSupport (r + 1) hg).1
  have cmem : c ∈ source.base.blocks := by
    by_cases hg : c = .genesis
    · simpa only [hg] using (proposalState_paths p rho (r + 1)).2
    · exact sourcePath c (floor_properties p target tree dstRaw dstSupport (r + 1) hg).2.2
  exact GridCO.prefix_eq_of_slot_ge a c (ordered c cmem) hac
    (GridCO.slot_le_of_prefix c a (ordered a amem) hca)

end AvailableChain.SAPC
end

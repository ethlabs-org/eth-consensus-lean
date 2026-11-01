module
public import AvailableChainSAPC.Proofs.Proposals

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A proposal cannot be a member of a HEAD or PC container. -/
theorem handles_proposal_direct (p : Params) {n : Nat} (st : State n)
    (outer o : Wire n) (b : Block) (raw support : List (HeadWire n)) (c : Option (PC n))
    (hp : o.payload = .proposal b raw support c) (hh : handles p st outer o) : outer = o := by
  rcases hh with he | hh
  · exact he
  · have hnot (xs : List (HeadWire n)) : o ∉ xs.map fromHead := by
      intro hm
      obtain ⟨head, _, he⟩ := List.mem_map.mp hm
      have hpay := congrArg Signed.payload he
      simp only [fromHead] at hpay
      rw [hp] at hpay
      contradiction
    split at hh
    · exact (hnot _ hh.2).elim
    · exact (hnot _ hh.2).elim
    · contradiction

/-- The required public tick puts the delivery clock in the proposal
slot. This also applies to sleeping readers. -/
theorem proposal_delivery_current_label {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    {index : Nat} {reader : V} {o : Wire p.n} {s : Slot} {t : Time}
    (hi : rho.events[index]? = some (.deliver reader o t))
    (hlo : proposalTime p s ≤ t) (hhi : t < voteTime p s) :
    ((Run.stateBefore (sapc p) rho index reader).base.now / (4 * p.Δ)).toNat = s := by
  have hpub : PublicTime E (proposalTime p s) := by
    refine ⟨4 * s, ?_⟩
    change 4 * p.Δ * (s : Time) = (4 * s : Nat) * E.Δ
    rw [hΔ]
    push_cast
    ring
  have hn : 0 ≤ proposalTime p s := by
    change 0 ≤ 4 * p.Δ * (s : Time)
    exact mul_nonneg (by linarith [p.deltaPos]) (Int.natCast_nonneg s)
  have hl := delivery_now_ge_public p E rho hs hi hpub hn hlo
  have hh := (stateBefore_now_le_event p E rho hs hi reader).trans_lt hhi
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have hdiv : (Run.stateBefore (sapc p) rho index reader).base.now / (4 * p.Δ) =
      (s : Int) := by
    apply (Int.ediv_eq_iff_of_pos hd).mpr
    change 4 * p.Δ * (s : Time) ≤ _ at hl
    change _ < 4 * p.Δ * (s : Time) + p.Δ at hh
    constructor <;> nlinarith [p.deltaPos]
  rw [hdiv]
  simp

theorem collectPCs_proposals (p : Params) {n : Nat} (st : State n) :
    (collectPCs p st).proposals = st.proposals :=
  collectPCs_field p State.proposals (by intros; rfl) st

theorem receiveHead_proposals (p : Params) {n : Nat} (st : State n) (head : HeadWire n) :
    (receiveHead p st head).proposals = st.proposals := by
  unfold receiveHead
  split
  · dsimp only
    split <;> (try split_ifs) <;> rfl
  · rfl

theorem receiveHeads_proposals (p : Params) {n : Nat} (st : State n)
    (heads : List (HeadWire n)) :
    (heads.foldl (receiveHead p) st).proposals = st.proposals :=
  fold_field State.proposals _ (receiveHead_proposals p) heads st

/-- Admission stores the original envelope and the shared base envelope
before processing carried signatures. The carried PC cannot remove them. -/
theorem process_proposal_stored (p : Params) {n : Nat} (st : State n)
    (s : Slot) (b : Block) (raw support : List (HeadWire n)) (c : Option (PC n))
    (hslot : b.slot = s) (hcurrent : s ≤ (st.base.now / (4 * p.Δ)).toNat)
    (hparent : b.parent ∈ st.base.blocks) (horder : b.parent.slot < s)
    (hfresh : b ∉ st.base.blocks) :
    let o : Wire n := ⟨.proposer s, .proposal b raw support c⟩
    b ∈ (process p st o).base.blocks ∧
      baseProposal o b raw support ∈ (process p st o).base.proposals ∧
      o ∈ (process p st o).proposals := by
  dsimp only
  have hbase : proposalBase p st ⟨.proposer s, .proposal b raw support c⟩ b raw support =
      { st.base with
        blocks := st.base.blocks ++ [b],
        blockStamp := st.base.blockStamp ++ [(b, st.base.now)],
        proposals := st.base.proposals ++
          [baseProposal ⟨.proposer s, .proposal b raw support c⟩ b raw support] } := by
    simp [proposalBase, GridCO.admitProposal, baseProposal, SA.Params.engine,
      hslot, not_lt.mpr hcurrent, GridCO.blockKnown, hparent, horder, hfresh]
  have henter : proposalEnters p st ⟨.proposer s, .proposal b raw support c⟩
      b raw support = true := by
    simp [proposalEnters, hbase, GridCO.blockKnown, hfresh]
  simp only [process, admitProposal, henter, ↓reduceIte, collectPCs_base,
    receiveHeads_blocks, receiveHeads_base_proposals, hbase]
  refine ⟨by simp, by simp, ?_⟩
  simp only [collectPCs_proposals, receiveHeads_proposals]
  simp

/-- A valid in-window delivery is an actual acceptance and stores both
views. The execution supplies the parent and freshness guards. -/
theorem delivered_proposal_accepted {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (index : Nat) (reader : V) (s : Slot) (b : Block)
    (raw support : List (HeadWire p.n)) (c : Option (PC p.n)) (t : Time)
    (hlo : proposalTime p s ≤ t) (hhi : t < voteTime p s)
    (hi : rho.events[index]? = some (.deliver reader
      ⟨.proposer s, .proposal b raw support c⟩ t)) :
    let o : Wire p.n := ⟨.proposer s, .proposal b raw support c⟩
    Run.acceptsAt (sapc p) rho index reader o t ∧
      baseProposal o b raw support ∈
        (Run.stateBefore (sapc p) rho (index + 1) reader).base.proposals ∧
      o ∈ (Run.stateBefore (sapc p) rho (index + 1) reader).proposals := by
  have hw := hx.wire index reader _ t hi
  have hd := hx.deps index reader _ t hi
  have hf := hx.fresh index reader _ t hi
  change wellFormed p (⟨.proposer s, .proposal b raw support c⟩ : Wire p.n) = true at hw
  simp only [wellFormed, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  have hslot : b.slot = s := hw.1.1.1.1.1.symm
  have hparent : b.parent ∈ (Run.stateBefore (sapc p) rho index reader).base.blocks := by
    simpa [sapc, depsPresent, GridCO.blockKnown] using hd
  have hfresh : b ∉ (Run.stateBefore (sapc p) rho index reader).base.blocks := by
    simpa [sapc, processed, GridCO.blockKnown] using hf
  have hcurrent := proposal_delivery_current_label p E rho hx.toScheduleWellFormed hΔ hi hlo hhi
  have hstored := process_proposal_stored p (Run.stateBefore (sapc p) rho index reader)
    s b raw support c hslot (le_of_eq hcurrent.symm) hparent hw.1.1.1.2 hfresh
  dsimp only at hstored ⊢
  refine ⟨⟨⟨_, hi, Or.inl rfl⟩, hf, ?_⟩, ?_, ?_⟩
  all_goals rw [stateBefore_succ_event hi]
  · simpa [World.step, sapc, processed, GridCO.blockKnown] using hstored.1
  · simpa [World.step, sapc] using hstored.2.1
  · simpa [World.step, sapc] using hstored.2.2

/-- Post-GST broadcast supplies direct proposal acceptance before HEAD.
This needs no clean-choice invariant and no fault cap. -/
theorem synchronous_proposal_accepted {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hnet : PartialSynchrony (sapc p) E rho)
    (s : Slot) (hsync : E.t_GST ≤ proposalTime p s) (hh : voteTime p s ≤ rho.horizon)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (b : Block) (raw support : List (HeadWire p.n)) (c : Option (PC p.n))
    (hem : Run.emits (sapc p) E rho source
      ⟨.proposer s, .proposal b raw support c⟩ (proposalTime p s)) :
    ∃ index t, proposalTime p s ≤ t ∧ t < voteTime p s ∧
      Run.acceptsAt (sapc p) rho index reader ⟨.proposer s, .proposal b raw support c⟩ t := by
  have hdeadline : max (proposalTime p s) E.t_GST + E.Δ = voteTime p s := by
    rw [max_eq_left hsync, hΔ]
    rfl
  obtain ⟨t, hlo, hhi, index, outer, hi, hhandles⟩ :=
    hnet.broadcast source hs _ _ hem reader hr (by rwa [hdeadline]) rfl
  have he := handles_proposal_direct p _ outer _ b raw support c rfl hhandles
  subst outer
  rw [hdeadline] at hhi
  exact ⟨index, t, hlo, hhi,
    (delivered_proposal_accepted p E rho hx hΔ index reader s b raw support c t hlo hhi hi).1⟩

/-- The same acceptance holds on a healthy outage prefix. -/
theorem healthy_proposal_accepted {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ) (cut : Time)
    (hnet : HealthyPrefixDelivery (sapc p) E rho cut)
    (s : Slot) (hh : voteTime p s ≤ cut)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (b : Block) (raw support : List (HeadWire p.n)) (c : Option (PC p.n))
    (hem : Run.emits (sapc p) E rho source
      ⟨.proposer s, .proposal b raw support c⟩ (proposalTime p s)) :
    ∃ index t, proposalTime p s ≤ t ∧ t < voteTime p s ∧
      Run.acceptsAt (sapc p) rho index reader ⟨.proposer s, .proposal b raw support c⟩ t := by
  have hdeadline : proposalTime p s + E.Δ = voteTime p s := by rw [hΔ]; rfl
  obtain ⟨t, hlo, hhi, index, outer, hi, hhandles⟩ :=
    hnet.broadcast source hs _ _ hem reader hr (by rwa [hdeadline]) rfl
  have he := handles_proposal_direct p _ outer _ b raw support c rfl hhandles
  subst outer
  rw [hdeadline] at hhi
  exact ⟨index, t, hlo, hhi,
    (delivered_proposal_accepted p E rho hx hΔ index reader s b raw support c t hlo hhi hi).1⟩

/-- Actual honest proposal paths are admitted before HEAD and keep their
first stamps at every later input. This discharges the path delivery
obligation used by the timely-save quorum lemma. -/
theorem honest_proposal_path_before_head {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hnet : PartialSynchrony (sapc p) E rho) (s : Slot) (b : Block)
    (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b)
    (hsync : E.t_GST ≤ proposalTime p s) (hh : voteTime p s ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) (cut : Time) (hcut : voteTime p s ≤ cut) :
    pathBefore (Run.stateBeforeTime (sapc p) rho cut reader) (voteTime p s) b = true := by
  obtain ⟨_, _, hem⟩ := honest_proposal_views p E rho hx.toScheduleWellFormed s b hb
  obtain ⟨index, t, _, hhi, ha⟩ := synchronous_proposal_accepted p E rho hx hΔ hnet
    s hsync hh (rho.proposerOf s) reader hb.1 hr b _ _ _ hem
  exact accepted_path_before_cut p E rho hx.toScheduleWellFormed index reader _ b _ _ _
    rfl t _ cut ha hhi hcut

end AvailableChain.SAPC
end

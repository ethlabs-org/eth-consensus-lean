module
public import AvailableChainFGSARun.Proofs.NamedHistory
public import AvailableChainFGSARun.Proofs.EmissionWellFormed

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private def proposal_raw_check (N : NamedProposal p.n) : Bool :=
  N.raw.all (fun v => match v.decode? with
    | some (slot, _, _) => slot + 1 == N.erase.slot
    | none => false)

private theorem proposal_checked_slot (r : Slot) (N : NamedProposal p.n)
    (h : FGSA.wellFormed p ⟨.proposer r, .proposal N⟩ = true) : r = N.erase.slot := by
  change (N.erase != .genesis && r == N.erase.slot &&
    decide (N.erase.parent.slot < N.erase.slot) &&
    proposal_raw_check N &&
    N.support.all (fun v => decide (v ∈ N.raw)) &&
    N.rows.all RowWire.valid && contentOk p N.erase N.raw N.support N.rows) = true at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨_, hs⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := h
  exact beq_iff_eq.mp hs

/-- A scoped emitted proposal has no earlier processing. Scoped root injectivity
must cover the emitted body; it does not follow from an emission alone under P2. -/
theorem fgsa_emitted_proposal_no_prior_processed (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hV : V2.D.ExecutionValid E rho)
    (hRoots : NamedRootCollisionFree p c E rho) {idx : Nat} {v : V} {t : Time}
    (hi : rho.events[idx]? = some (.tick v t)) (s : Slot) (N : NamedProposal p.n)
    (ho : ofWire p ⟨.proposer s, .proposal N⟩ ∈ V2.D.Run.emitsAt E rho idx)
    (hN : NamedProposalInRun p c E rho N) :
    ∀ k, k ≤ idx → ∀ x,
      (fgsa p c).processed (V2.D.Run.stateBefore E rho k x)
        (ofWire p ⟨.proposer s, .proposal N⟩) = false := by
  have hem := ho
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at hem
  have hcurrent := (fgsa_emits_proposal E rho _ v t s (.proposal N)).mp hem
  have hv : v ∈ rho.honest := hV.honest_only _ (List.mem_of_getElem? hi)
  have hwf := honest_emit_wellFormed E rho hV.toDeliveryWellFormed hV.toScheduleWellFormed
    idx v t hi hv hcurrent.1 (ofWire p ⟨.proposer s, .proposal N⟩) ho
  change FGSA.wellFormed p (toWire p (ofWire p ⟨.proposer s, .proposal N⟩)) = true at hwf
  rw [toWire_ofWire] at hwf
  have hs := proposal_checked_slot s N hwf
  have hng : N ≠ .genesis := by
    intro hg
    subst N
    change false = true at hwf
    cases hwf
  have hgen : NamedProposalInRun p c E rho .genesis :=
    namedScope_held E rho hv 0 ((mem_namedBodies _ _).mpr (Or.inl rfl))
  intro k hki x
  change decide (∃ Y ∈ (V2.D.Run.stateBefore E rho k x).st.fg.TF, Y.root = N.root) = false
  apply decide_eq_false_iff_not.mpr
  rintro ⟨Y, hY, hroot⟩
  by_cases hg : Y = .genesis
  · subst Y
    have he : (NamedProposal.genesis : NamedProposal p.n).root = N.root := hroot
    exact hng (namedProposal_eq E rho hRoots hgen hN he).symm
  obtain ⟨wire, ⟨hwire, hblock⟩, _⟩ := (metaInv_stateBefore E rho k x).treeWire Y hY hg
  obtain ⟨r, M, hw, _, _, _, _⟩ := (metaInv_stateBefore E rho k x).wireTree wire hwire
  have hM : NamedProposalInRun p c E rho M :=
    namedScope_stored_proposal E rho k x (by rw [← hw]; exact hwire)
  have herase : M.erase = eraseFG Y := by
    rw [hw] at hblock
    exact Option.some.inj hblock
  have hMN : M = N := by
    apply namedProposal_eq E rho hRoots hM hN
    have hr := congrArg Block.root herase
    rw [named_erase_root, eraseFG_root] at hr
    exact hr.trans hroot
  subst M
  obtain ⟨j, parent, time, hj, hd, hp, _, _⟩ := stored_proposal_delivered E rho k x wire hwire
  have hparent : parent = ofWire p ⟨.proposer r, .proposal N⟩ := by
    apply toWire_injective
    rw [hp, hw, toWire_ofWire]
  have hcheck := hV.wire j x parent time hd
  change FGSA.wellFormed p (toWire p parent) = true at hcheck
  rw [hp, hw] at hcheck
  have hr : r = s := (proposal_checked_slot r N hcheck).trans hs.symm
  subst r
  have hhold : V2.D.Run.holder rho parent.auth = some v := by
    rw [hparent]
    exact congrArg some hcurrent.2.2.1
  obtain ⟨u, hut, q, hq, hemit⟩ := hV.unforgeable x parent time ⟨j, hd⟩ v hv hhold
  rw [hparent, (V2.D.Run.step_tick_eq E rho hq).2] at hemit
  have htime := ((fgsa_emits_proposal E rho _ v u s (.proposal N)).mp hemit).2.1
  have htlim : t ≤ time := by rw [← hcurrent.2.1, htime]; exact hut
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hd
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hk := List.pairwise_iff_getElem.mp hV.sorted j idx hjl hil (by omega)
  rw [hje, hie] at hk
  change toLex (time, 2) ≤ toLex (t, 1) at hk
  rcases Prod.Lex.toLex_le_toLex.mp hk with hlt | ⟨_, hphase⟩
  · exact (not_lt.mpr htlim) hlt
  · omega

end AvailableChain.FGSA.Run
end

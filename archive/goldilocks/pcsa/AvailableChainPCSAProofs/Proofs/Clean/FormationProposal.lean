module
public import AvailableChainPCSAProofs.Proofs.Shared.FormationWindow
public import AvailableChainPCSAProofs.Proofs.Clean.FormationWalk
public import AvailableChainPCSAProofs.Proofs.Shared.Proposal
public import AvailableChainPCSAProofs.Proofs.Clean.FormationFrame

public section

/-! Exact honest proposer geometry for Formation (pcsa34-r4.3b §5.3). -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
variable [Fintype V]

/-- Corrected F4 puts the common base root below the emitted proposal parent. -/
theorem pcsa_formation_base_below_parent (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) :
    ∃ nd : Node p, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some nd ∧
      N.erase.slot = s ∧
      N.pc = proposerPC p nd.st ∧
      Block.Preceq ((N.pc.map PC.target).getD (eraseFG (controls p nd.st).Z))
        N.erase.parent := by
  obtain ⟨nd, hr, hslot, hp, hpc⟩ :=
    pcsa_honest_proposal_state E rho h.base s N h.proposal
  have hb := pcsa_formation_proposer_base_walk E rho s N ΔF h nd hr
  refine ⟨nd, hr, hslot, hpc, ?_⟩
  rw [hpc, hp, ← hb]
  exact @GridCO.ghost_extends GridCO.slowLeasePolicy _ _ _ _

/-- The two corrected F4 clauses bound the actual post-release voter root. -/
theorem pcsa_formation_voter_root_below_parent (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF) (y : V) (nd : Node p)
    (hy : y ∈ rho.honest) (haw : E.awake y (SA.voteTime p.toParams s) = true)
    (hr : pcsa_postClock E rho y (SA.voteTime p.toParams s) = some nd) :
    Block.Preceq (liveRoot p nd.st (voterPC p nd.st s)) N.erase.parent := by
  obtain ⟨src, hs, _, _, hb⟩ := pcsa_formation_base_below_parent E rho s N ΔF h
  have hfSrc := pcsa_formation_frame_read E rho h.frame _ _ src h.proposal.1 hs
  have hfDst := pcsa_formation_frame_read E rho h.frame y _ nd hy hr
  have hv := h.commonView y hy haw
  rw [pcsa_viewAt_def, hr] at hv
  change some ((voterPC p nd.st s).map PC.target) = some (N.pc.map PC.target) at hv
  have ht := Option.some.inj hv
  have he : walkBase p nd.st (voterPC p nd.st s) =
      (N.pc.map PC.target).getD (eraseFG (controls p nd.st).Z) := by
    cases hc : voterPC p nd.st s with
    | none =>
      rw [hc] at ht
      rw [← ht]
      rfl
    | some C =>
      have hm : C ∈ ((pcSnapshotAt nd.st (s - 1) ++ carriedPCs nd.st s).filter
          (frameActive p nd.st)) := bestPC_mem _ C hc
      have ha := (List.mem_filter.mp hm).2
      rw [hc] at ht
      rw [← ht]
      change (if frameActive p nd.st C then C.target else _) = C.target
      rw [ite_eq_left ha]
  apply pcsa_formation_root_below_parent p nd.st (voterPC p nd.st s) N.erase
  · rw [he, hfDst.2.1]
    rw [hfSrc.2.1] at hb
    exact hb
  · intro B hl hc hd
    rw [he] at hc hd
    exact h.leases y hy haw nd hr B hl hc hd

end AvailableChain.PCSA.Run
end

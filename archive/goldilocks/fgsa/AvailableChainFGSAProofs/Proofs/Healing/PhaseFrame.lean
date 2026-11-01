module
public import AvailableChainFGSAClaims.Statements.ComposeStmt
public import AvailableChainFGSARun.Proofs.Reachable -- shake: keep (reach API)

public import AvailableChainFGCompose.Proofs.Healing.PhaseFrame

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private def p0d1PhaseFrameCore (p : Params) {In : Type} (c : AppCodec In) :
  FGCompose.FGCoreReads (fgsa p c) p.n (GridCO.State p.n .root) (Wire p.n) (RowWire p.n) :=
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := eraseFG
    source := fun nd => FGSA.fgSource p nd.st
    headVote := fun nd s => FGSA.headVote p nd.st s
    finalityHead := fun nd => FGSA.fgBlockOf nd.st (FGSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) => (parentFG nd.st N.erase).map (fun P => fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | none => none }

private def p0d1PhaseFrameReads (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d1PhaseFrameCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem p0d1PhaseFrameLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationLaws (p0d1PhaseFrameCore p c) (p0d1PhaseFrameReads p c) where
  controls_eq _ := rfl
  viable_eq _ _ := rfl

/-- Blueprint 21:1193–1209; plan S20, H-PHASE/P4. DC: SAME cache height bound. -/
theorem healing_phase_height_le {i : Nat} {x : V} {W : FGBlock (Fin p.n)}
    (hW : W ∈ (storeAt p c E rho i x).fg.TF) :
    (heightView p W).h ≤ (storeAt p c E rho i x).fg.h_max := by
  exact FGCompose.healing_phase_height_le
    (R := p0d1PhaseFrameCore p c)
    (E := E)
    (rho := rho)
    (O := p0d1PhaseFrameReads p c)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    hW


/-- Blueprint 21:1193–1209; plan S20, H-PHASE/P4. DC: SAME strict cache bound. -/
theorem healing_phase_justified_lt (i : Nat) (x : V) :
    (storeAt p c E rho i x).fg.h_j < (storeAt p c E rho i x).fg.h_max := by
  exact FGCompose.healing_phase_justified_lt
    (R := p0d1PhaseFrameCore p c)
    (E := E)
    (rho := rho)
    (O := p0d1PhaseFrameReads p c)
    (Ef := p.E) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    i x


/-- Blueprint 21:1222–1235; plan S20, H-PHASE/P4.
DC: INTENTIONAL the bound reads the accepted W certificate, not the block F. -/
theorem healing_phase_finality_le {i : Nat} {x : V} {K : FGBlock (Fin p.n)}
    (hK : K ∈ (storeAt p c E rho i x).fg.TF)
    (hF : (finalityView p K).F = (storeAt p c E rho i x).fg.F) :
    (finalityView p K).h_F ≤ (storeAt p c E rho i x).fg.h_j := by
  exact FGCompose.healing_phase_finality_le
    (R := p0d1PhaseFrameCore p c)
    (E := E)
    (rho := rho)
    (O := p0d1PhaseFrameReads p c)
    (Ef := p.E) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    hK hF


/-- Blueprint 21:1193–1209; plan S20, H-PHASE/P4.
DC: SAME a nonempty cumulative store attains its frontier, including height one. -/
theorem healing_phase_frontier_witness (i : Nat) (x : V) :
    ∃ W ∈ (storeAt p c E rho i x).fg.TF,
      (heightView p W).h = (storeAt p c E rho i x).fg.h_max := by
  exact FGCompose.healing_phase_frontier_witness
    (R := p0d1PhaseFrameCore p c)
    (E := E)
    (rho := rho)
    (O := p0d1PhaseFrameReads p c)
    (Ef := p.E) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    i x


/-- Blueprint 21:1153–1171, 1200–1209; plan S20, H-PHASE/P5.
DC: INTENTIONAL live controls and accepted W finality carrier.
Assembly supplies RXing from the foundation final-lock producer. -/
theorem healing_phase_frontier_root (crossing : RXing p c E rho)
    {i : Nat} {x : V} {B : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hB : B ∈ (storeAt p c E rho i x).fg.TF)
    (hh : (heightView p B).h = (R_at p c E rho i x).H) :
    FGBlock.Preceq (storeAt p c E rho i x).fg.F B ∧
      FGBlock.Preceq (R_at p c E rho i x).Z B := by
  exact FGCompose.healing_phase_frontier_root
    (R := p0d1PhaseFrameCore p c)
    (E := E)
    (rho := rho)
    (O := p0d1PhaseFrameReads p c)
    (obs := p0d1PhaseFrameLaws p c)
    (Ef := p.E) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    crossing hx hB hh


/-- Blueprint 21:1153–1171, 1200–1209; plan S20, H-PHASE/P5.
DC: INTENTIONAL membership uses the supplied view and the live controls.
This proves the fifth frozen RPhase clause; its path premise is not needed. -/
theorem healing_frontier_mem (crossing : RXing p c E rho)
    (i : Nat) (x : V) (m : Nat) (X : Finset (FGBlock (Fin p.n))) (B : FGBlock (Fin p.n))
    (hx : x ∈ rho.honest) (_hi : i ≤ rho.events.length) (_hm : 1 ≤ m)
    (hH : (R_at p c E rho i x).H = m) (hX : X ⊆ (storeAt p c E rho i x).fg.TF)
    (hB : B ∈ X) (_hpath : ∀ A, FGBlock.Preceq A B → A ∈ X)
    (hh : (heightView p B).h = m) :
    FGBlock.Preceq (R_at p c E rho i x).Z B ∧ B ∈ D_at p c E rho i x X := by
  exact FGCompose.healing_frontier_mem
    (R := p0d1PhaseFrameCore p c)
    (E := E)
    (rho := rho)
    (O := p0d1PhaseFrameReads p c)
    (obs := p0d1PhaseFrameLaws p c)
    (Ef := p.E) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    crossing i x m X B hx _hi _hm hH hX hB _hpath hh


/-- Blueprint 21:1193–1235; plan S20, H-PHASE/P4.
DC: INTENTIONAL the frame includes a W certificate below its floor.
This local form does not require a settlement time or a height-two bootstrap. -/
theorem healing_phase_frame (crossing : RXing p c E rho)
    {i : Nat} {x : V} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hx : x ∈ rho.honest) (hm : 1 ≤ m)
    (hH : (R_at p c E rho i x).H = m)
    (hc : (R_at p c E rho i x).contest = contested)
    (hr : match J with
      | some B => (R_at p c E rho i x).rootIsJ = true ∧ (R_at p c E rho i x).J = B
      | none => (R_at p c E rho i x).rootIsJ = false) :
    SettledPhaseFrame p (storeAt p c E rho i x) m J contested := by
  have result := FGCompose.healing_phase_frame
    (R := p0d1PhaseFrameCore p c)
    (E := E)
    (rho := rho)
    (O := p0d1PhaseFrameReads p c)
    (obs := p0d1PhaseFrameLaws p c)
    (Ef := p.E) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (J := J) (contested := contested) crossing hx hm hH hc
      (by cases J <;> exact hr)
  cases J <;> exact result


/-- Blueprint 21:1193–1235; plan S20, H-PHASE/P4.
DC: INTENTIONAL live settled frame with an accepted finality carrier.
This is the fourth frozen RPhase clause. Assembly supplies RXing. -/
theorem healing_settled_frame (crossing : RXing p c E rho)
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (_hgst : E.t_GST ≤ u) (hp : PhaseInterval p c E rho u v m J contested)
    (i : Nat) (x : V) (hui : timeIdx rho u ≤ i) (hiv : i ≤ timeIdx rho v)
    (hx : x ∈ rho.honest) :
    SettledPhaseFrame p (storeAt p c E rho i x) m J contested := by
  have result := FGCompose.healing_settled_frame
    (R := p0d1PhaseFrameCore p c)
    (E := E)
    (rho := rho)
    (O := p0d1PhaseFrameReads p c)
    (obs := p0d1PhaseFrameLaws p c)
    (Ef := p.E) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    crossing u v m J contested _hgst
      (by cases J <;> exact hp) i x hui hiv hx
  cases J <;> exact result


/-- The fourth RPhase clause uses the joined healing phase domain. -/
theorem healing_settled_frame_ready (crossing : RXing p c E rho)
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (_hready : recoveryStart p E ≤ u) (hp : PhaseInterval p c E rho u v m J contested)
    (i : Nat) (x : V) (hui : timeIdx rho u ≤ i) (hiv : i ≤ timeIdx rho v)
    (hx : x ∈ rho.honest) :
    SettledPhaseFrame p (storeAt p c E rho i x) m J contested := by
  have result := FGCompose.healing_settled_frame_ready
    (R := p0d1PhaseFrameCore p c)
    (E := E)
    (rho := rho)
    (O := p0d1PhaseFrameReads p c)
    (obs := p0d1PhaseFrameLaws p c)
    (Ef := p.E) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (Jst := recoveryStart p E)
    crossing u v m J contested _hready
      (by cases J <;> exact hp) i x hui hiv hx
  cases J <;> exact result


end AvailableChain.FGSA.Run
end

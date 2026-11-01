module
-- Phase.lean uses the native height and frontier theorems through this import.
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseFrame -- shake: keep (Phase API)
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun

public import AvailableChainFGCompose.Proofs.Healing.PhaseOrder

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private def p0d1PhaseOrderCore (p : Params) {In : Type} (c : AppCodec In) :
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

private def p0d1PhaseOrderReads (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationReads (p0d1PhaseOrderCore p c) where
  height := heightView p
  finality := finalityView p
  controls nd := FGSA.controls p nd.st
  viable nd X := domainR p nd.st X

private theorem p0d1PhaseOrderLaws (p : Params) {In : Type} (c : AppCodec In) :
    FGCompose.FGObservationLaws (p0d1PhaseOrderCore p c) (p0d1PhaseOrderReads p c) where
  controls_eq _ := rfl
  viable_eq _ _ := rfl

/-- Blueprint 21:1193–1209; plan S20, H-PHASE/P1. DC: SAME global cache bound. -/
theorem healing_phase_local_le_frontier {i : Nat} {x : V} (hx : x ∈ rho.honest) :
    (storeAt p c E rho i x).fg.h_max ≤ frontierAtIdx p c E rho i := by
  exact FGCompose.healing_phase_local_le_frontier
    (R := p0d1PhaseOrderCore p c)
    (E := E)
    (rho := rho)
    hx


/-- Blueprint 21:1193–1209; plan S20, H-PHASE/P1.
DC: SAME a top cache persists below a fixed global cap. Assembly supplies RMono. -/
theorem healing_phase_top_persist_all (mono : RMonoAll p c E rho)
    {i j m : Nat} {x : V} (hx : x ∈ rho.honest) (hij : i ≤ j)
    (hcap : frontierAtIdx p c E rho j = m)
    (htop : (storeAt p c E rho i x).fg.h_j + 1 = m) :
    (storeAt p c E rho j x).fg.h_j + 1 = m ∧
      (storeAt p c E rho j x).fg.h_max = m := by
  exact FGCompose.healing_phase_top_persist_all
    (R := p0d1PhaseOrderCore p c)
    (E := E)
    (rho := rho)
    (O := p0d1PhaseOrderReads p c)
    (Ef := p.E) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    ⟨mono⟩ hx hij hcap htop


theorem healing_phase_top_persist (mono : RMono p c E rho) (hnr : V2.D.NoRestart rho)
    {i j m : Nat} {x : V} (hx : x ∈ rho.honest) (hij : i ≤ j)
    (hcap : frontierAtIdx p c E rho j = m)
    (htop : (storeAt p c E rho i x).fg.h_j + 1 = m) :
    (storeAt p c E rho j x).fg.h_j + 1 = m ∧
      (storeAt p c E rho j x).fg.h_max = m := by
  exact FGCompose.healing_phase_top_persist
    (R := p0d1PhaseOrderCore p c)
    (E := E)
    (rho := rho)
    (O := p0d1PhaseOrderReads p c)
    (Ef := p.E) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (fun h => ⟨mono h⟩) hnr hx hij hcap htop


/-- Blueprint 21:1105–1113, 1193–1209; plan S20, H-PHASE/P1.
DC: SAME two equal-height entries on one path are equal.
At justified height zero both entries are genesis (B21, m = 1). -/
theorem healing_phase_entries_eq {C D W : FGBlock (Fin p.n)}
    (hh : (heightView p C).h_j = (heightView p D).h_j)
    (hC : FGBlock.Preceq (heightView p C).J W)
    (hD : FGBlock.Preceq (heightView p D).J W) :
    (heightView p C).J = (heightView p D).J := by
  exact FGCompose.healing_phase_entries_eq (Ef := p.E) (heightView p) (finalityView p)
    (fgCertificateLaws p) (fgJustificationLaws p) hh hC hD


/-- Blueprint 21:1105–1113, 1193–1209; plan S20, H-PHASE/P1.
DC: INTENTIONAL a contest uses cumulative live evidence.
If the cached J changes, its old carrier supplies the off-J witness. -/
theorem healing_phase_contest_persist_of_crossing_all (crossing : RXing p c E rho)
    (mono : RMonoAll p c E rho)
    {i j m : Nat} {x : V}
    (hx : x ∈ rho.honest) (hij : i ≤ j)
    (hcap : frontierAtIdx p c E rho j = m)
    (hH : (R_at p c E rho i x).H = m)
    (hcontest : (R_at p c E rho i x).contest = true) :
    (R_at p c E rho j x).H = m ∧ (R_at p c E rho j x).contest = true := by
  exact FGCompose.healing_phase_contest_persist_of_crossing_all
    (R := p0d1PhaseOrderCore p c)
    (E := E)
    (rho := rho)
    (O := p0d1PhaseOrderReads p c)
    (obs := p0d1PhaseOrderLaws p c)
    (Ef := p.E) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    crossing ⟨mono⟩ hx hij hcap hH hcontest


theorem healing_phase_contest_persist_of_crossing (crossing : RXing p c E rho)
    (mono : RMono p c E rho)
    (hnr : V2.D.NoRestart rho) {i j m : Nat} {x : V}
    (hx : x ∈ rho.honest) (hij : i ≤ j)
    (hcap : frontierAtIdx p c E rho j = m)
    (hH : (R_at p c E rho i x).H = m)
    (hcontest : (R_at p c E rho i x).contest = true) :
    (R_at p c E rho j x).H = m ∧ (R_at p c E rho j x).contest = true := by
  exact FGCompose.healing_phase_contest_persist_of_crossing
    (R := p0d1PhaseOrderCore p c)
    (E := E)
    (rho := rho)
    (O := p0d1PhaseOrderReads p c)
    (obs := p0d1PhaseOrderLaws p c)
    (Ef := p.E) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    crossing (fun h => ⟨mono h⟩) hnr hx hij hcap hH hcontest


/-- Blueprint 21:1091–1113, 1193–1209; plan S20, H-PHASE/P1.
DC: INTENTIONAL gap, top J, contest are the live cumulative phase bits.
This is the first frozen RPhase clause. Assembly supplies RMono. -/
theorem healing_phase_order_of_crossing_all (crossing : RXing p c E rho)
    (mono : RMonoAll p c E rho)
    (a b m : Nat) (_hab : a ≤ b) (_hb : b ≤ rho.events.length) (_hm : 1 ≤ m)
    (hfixed : ∀ i, a ≤ i → i ≤ b → frontierAtIdx p c E rho i = m) :
    (∀ i j, a ≤ i → i ≤ j → j ≤ b →
      (TopEvidence p c E rho i m → TopEvidence p c E rho j m) ∧
      (ContestEvidence p c E rho i m → ContestEvidence p c E rho j m)) ∧
    (∀ i, a ≤ i → i ≤ b → ContestEvidence p c E rho i m → TopEvidence p c E rho i m) := by
  exact FGCompose.healing_phase_order_of_crossing_all
    (R := p0d1PhaseOrderCore p c)
    (E := E)
    (rho := rho)
    (O := p0d1PhaseOrderReads p c)
    (obs := p0d1PhaseOrderLaws p c)
    (Ef := p.E) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    crossing ⟨mono⟩ a b m _hab _hb _hm hfixed


theorem healing_phase_order_of_crossing (crossing : RXing p c E rho)
    (mono : RMono p c E rho) (hnr : V2.D.NoRestart rho)
    (a b m : Nat) (_hab : a ≤ b) (_hb : b ≤ rho.events.length) (_hm : 1 ≤ m)
    (hfixed : ∀ i, a ≤ i → i ≤ b → frontierAtIdx p c E rho i = m) :
    (∀ i j, a ≤ i → i ≤ j → j ≤ b →
      (TopEvidence p c E rho i m → TopEvidence p c E rho j m) ∧
      (ContestEvidence p c E rho i m → ContestEvidence p c E rho j m)) ∧
    (∀ i, a ≤ i → i ≤ b → ContestEvidence p c E rho i m → TopEvidence p c E rho i m) := by
  exact FGCompose.healing_phase_order_of_crossing
    (R := p0d1PhaseOrderCore p c)
    (E := E)
    (rho := rho)
    (O := p0d1PhaseOrderReads p c)
    (obs := p0d1PhaseOrderLaws p c)
    (Ef := p.E) (cert := fgCertificateLaws p)
    (inv := fun i x => (storeBundle_stateBefore E rho i x).cstore.fg)
    (justif := fgJustificationLaws p)
    (keep := fun _ _ hij x => (fgsa_store_durable p c E rho hij x).1)
    crossing (fun h => ⟨mono h⟩) hnr a b m _hab _hb _hm hfixed


end AvailableChain.FGSA.Run
end

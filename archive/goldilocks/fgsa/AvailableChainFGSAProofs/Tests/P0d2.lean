module
public import AvailableChainFGSAProofs.Proofs.Foundations.RowPermission

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run.Tests.P0d2
open AvailableChain.SimplexFG AvailableChain.KitFG

private abbrev d2a_p : Params :=
  { Δ := 1, n := 1, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 4, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

private abbrev d2a_row : Row (Fin 1) := ⟨0, .vote 1 genesisRoot false, none⟩
private abbrev d2a_record : RecordOnce := record_row_once RecordOnce.initial d2a_row
private abbrev d2a_nd : Node d2a_p := ⟨FGSA.initial d2a_p.n, d2a_record⟩

-- Inhabited client inputs. The selected source is a pure client input here;
-- the production wrapper below derives its source from the old hypotheses.
private theorem d2a_current_send :
    (createRowOnce d2a_p.E d2a_p.cfg RecordOnce.initial 0 (some .genesis)
      ⟨0, genesisRoot, 0⟩).1 = some d2a_row := by
  decide +kernel

-- The actual protocol own-record operation writes the full emitted content.
private theorem d2a_current_record :
    ((fgsa d2a_p unitCodec).recordOwn (fgsa d2a_p unitCodec).init
      (ofRow d2a_p ⟨.seat .fg 0, .vote (RowBody.ofRow d2a_row)⟩)).record =
        d2a_record := by
  rfl

-- The real client producer supplies all five record operations and actual tick rows.
private theorem d2a_client :
    FGCompose.FGSafetyClientLaws (fgsaSafetyReads d2a_p unitCodec) d2a_p.E d2a_p.cfg :=
  fgsaSafetyClientLaws d2a_p unitCodec

-- Restart preserves the full sent key and the old matching row.
private theorem d2a_restart_record :
    (fgsaSafetyReads d2a_p unitCodec).record
        ((fgsa d2a_p unitCodec).restore ((fgsa d2a_p unitCodec).durable d2a_nd) 7) =
      d2a_record :=
  by simpa only [fgsaSafetyReads_def] using d2a_client.restart_record d2a_nd 7

private theorem d2a_restart_suppressed :
    let Λ := (fgsaSafetyReads d2a_p unitCodec).record
      ((fgsa d2a_p unitCodec).restore ((fgsa d2a_p unitCodec).durable d2a_nd) 7)
    (createRowOnce d2a_p.E d2a_p.cfg Λ 0 (some .genesis) ⟨0, genesisRoot, 0⟩).1 = none ∧
      (.vote 1 genesisRoot false, none) ∈ Λ.sent := by
  dsimp only
  rw [d2a_restart_record]
  decide +kernel

-- Exact wrapper use under its original public hypotheses, including rSent ≤ r.
private theorem d2a_closed_wrapper {In V : Type} [DecidableEq V] [Fintype V]
    {p : Params} {c : AppCodec In} (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hb : Base₂ p c E rho) (hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
    (x : V) (hx : x ∈ rho.honest) (r : Nat) (nd : Node p)
    (hnd : postClock E rho x (p.actionTime r) = some nd) (C : FGBlock (Fin p.n))
    (hsource : actionSourceFG p c E rho x r = some (some C))
    (hC : C ∈ FGSA.fullTree p nd.st) (hband : (FGSA.controls p nd.st).lo ≤ (heightView p C).h)
    (hawake : E.awake x (p.actionTime r) = true) :
    ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
      namedEntry a.payload.height_pair = some ((heightView p C).h, (heightView p C).T_h.root) :=
  rowPermission_covered E rho hb hf x hx r nd hnd C hsource hC hband hawake

#print axioms d2a_current_send
#print axioms d2a_current_record
#print axioms d2a_client
#print axioms d2a_restart_record
#print axioms d2a_restart_suppressed
#print axioms d2a_closed_wrapper
#print axioms AvailableChain.FGSA.Run.rowPermission_pair
#print axioms AvailableChain.FGSA.Run.rowPermission_covered
#print axioms AvailableChain.FGSA.Run.rowPermission_at

end AvailableChain.FGSA.Run.Tests.P0d2
end

module
public import AvailableChainFGCompose.Proofs.ExecutionAcceptance
public import AvailableChainFGCompose.Proofs.ExecutionObs

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
variable (H : FGHistoricalReads P.State Body) (Wr : FGDependencyWireReads P Body Wire)
variable (Ef : Electorate (Fin n)) (cfg : FGConfig) (K : Nat)

/-- Equality at an ordinary delivery's post-leaf cut. This is an ordinary-fold fact,
not an assertion that a dependency-driver delivery equals `P.process`. -/
theorem ordinary_acceptance_cut_eq {j : Nat} {x : V} {o : P.Object} {t : Time}
    (he : rho.events[j]? = some (.deliver x o t)) :
    (ordinaryFGExecutionObs E rho).cutState x (3 * j + 1) =
      V2.D.Run.stateBefore E rho (j + 1) x := by
  change ordinaryCutState E rho x (3 * j + 1) = _
  rw [ordinaryCutState_def, ite_eq_right (by omega), ite_eq_left (by omega),
    show (3 * j + 1) / 3 = j by omega, ordinaryEntry_def, he]
  rw [V2.D.Run.stateBefore_succ E rho he]
  simp only [Option.map_some, Option.getD_some, ordinaryEntryStep_def,
    V2.D.World.step, Function.update_self, ite_true]

/-- One-way constructor: a SUCCESSFUL ordinary delivery with its original authenticated
body yields a selected acceptance. Mere ordinary `accepts` or prior coverage is insufficient. -/
def ordinary_selectedAcceptance {j : Nat} {x : V} {o : P.Object} {t d : Time}
    {b : Body} {W : FGBlock (Fin n)}
    (hx : x ∈ rho.honest) (he : rho.events[j]? = some (.deliver x o t))
    (origin : FGReceiptOrigin E rho H Wr x b (fgEventToken rho x j o t))
    (herase : R.erase W = H.erase b) (hrows : W.rows = (Wr.bodyRows b).filterMap S.decode)
    (ht : t < d)
    (effect : (R.core (V2.D.Run.stateBefore E rho (j + 1) x)).fg =
      SimplexFG.Window.update_finality Ef cfg K
        { (R.core (V2.D.Run.stateBefore E rho j x)).fg with
          TF := insert W (R.core (V2.D.Run.stateBefore E rho j x)).fg.TF } W) :
    FGSelectedAcceptance R S E rho H Wr (ordinaryFGExecutionObs E rho)
      (SimplexFG.Window.update_finality Ef cfg K) x W d where
  step := 3 * j
  eventIndex := j
  token := fgEventToken rho x j o t
  body := b
  honest := hx
  accepts := ⟨j, o, t, he, rfl, rfl⟩
  origin := origin
  erase_eq := herase
  rows_eq := hrows
  segment := ⟨le_rfl, by change 3 * j < 3 * j + 2; omega⟩
  event_some := ⟨_, he⟩
  before_deadline := by
    change ((rho.events[3 * j / 3]?).map V2.Event.time).getD 0 < d
    rw [show 3 * j / 3 = j by omega, he]
    exact ht
  effect := by
    rw [ordinary_acceptance_cut_eq E rho he]
    have hc := (ordinaryFGExecutionObs_laws E rho).start_state j _ x he
    change (ordinaryFGExecutionObs E rho).cutState x (3 * j) = _ at hc
    rw [hc]
    exact effect

/-- Equality bridge for the constructor's chosen cut and immutable original token. -/
theorem ordinary_selectedAcceptance_fields {j : Nat} {x : V} {o : P.Object} {t d : Time}
    {b : Body} {W : FGBlock (Fin n)}
    (hx : x ∈ rho.honest) (he : rho.events[j]? = some (.deliver x o t))
    (origin : FGReceiptOrigin E rho H Wr x b (fgEventToken rho x j o t))
    (herase : R.erase W = H.erase b) (hrows : W.rows = (Wr.bodyRows b).filterMap S.decode)
    (ht : t < d)
    (effect : (R.core (V2.D.Run.stateBefore E rho (j + 1) x)).fg =
      SimplexFG.Window.update_finality Ef cfg K
        { (R.core (V2.D.Run.stateBefore E rho j x)).fg with
          TF := insert W (R.core (V2.D.Run.stateBefore E rho j x)).fg.TF } W) :
    let A := ordinary_selectedAcceptance R S E rho H Wr Ef cfg K
      hx he origin herase hrows ht effect
    A.step = 3 * j ∧ A.eventIndex = j ∧ A.token = fgEventToken rho x j o t ∧ A.body = b :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Iff: once the successful delivery is selected explicitly, its local effect law is
exactly carrier-finality membership and global observed retention. The effect equation
itself is already carried by the selected witness. -/
theorem ordinary_acceptanceEffect_iff {x : V} {W : FGBlock (Fin n)} {d : Time}
    (A : FGSelectedAcceptance R S E rho H Wr (ordinaryFGExecutionObs E rho)
      (SimplexFG.Window.update_finality Ef cfg K) x W d) :
    FGAcceptanceEffectLaws R S E rho H Wr (ordinaryFGExecutionObs E rho) Ef cfg K x W d A ↔
      (SimplexFG.Window.derive Ef cfg K W).F ∈
        insert W (R.core ((ordinaryFGExecutionObs E rho).cutState x A.step)).fg.TF ∧
      FGObservedFinalityLaws R rho (ordinaryFGExecutionObs E rho) := by
  exact ⟨fun L => ⟨L.leaf.2, L.finality⟩, fun h => ⟨⟨A.effect, h.1⟩, h.2⟩⟩

/-- One-way ordinary conclusion bridge from an explicitly selected successful delivery.
It does not turn the prior-coverage branch of `AcceptPrem_W` into a receipt. -/
theorem acceptBefore_ordinary (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (hs : V2.D.ScheduleWellFormed E rho) (x : V) (W U : FGBlock (Fin n)) (d : Time)
    (A : FGSelectedAcceptance R S E rho H Wr (ordinaryFGExecutionObs E rho)
      (SimplexFG.Window.update_finality Ef cfg K) x W d)
    (EL : FGAcceptanceEffectLaws R S E rho H Wr (ordinaryFGExecutionObs E rho)
      Ef cfg K x W d A) (hhor : d ≤ rho.horizon)
    (hfinal : FGBlock.Preceq U (SimplexFG.Window.derive Ef cfg K W).F)
    (G : FGAcceptanceGuards R (ordinaryFGExecutionObs E rho) Ef cfg K x A.step W U) :
    A.token.receiptTime < d ∧ AcceptsFinalBefore R E rho x U d := by
  have h := acceptBefore_driver R S E rho H Wr (ordinaryFGExecutionObs E rho) Ef cfg K
    hne hK (ordinaryFGExecutionObs_laws E rho) hs x W U d A EL hhor hfinal G
  exact ⟨h.1, (ordinary_acceptsFinalBefore_iff R E rho hs x U d).mp h.2.2.1⟩

/-- One-way pending-fold bridge, using the identical selected successful delivery. -/
theorem finalizePending_ordinary (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (hs : V2.D.ScheduleWellFormed E rho) (x : V) (y : Nat) (U X : FGBlock (Fin n))
    (d : Time) (A : FGSelectedAcceptance R S E rho H Wr (ordinaryFGExecutionObs E rho)
      (SimplexFG.Window.update_finality Ef cfg K) x X d)
    (EL : FGAcceptanceEffectLaws R S E rho H Wr (ordinaryFGExecutionObs E rho)
      Ef cfg K x X d A) (hhor : d ≤ rho.horizon) (fold : PendingFold_W Ef cfg K y U X)
    (G : FGAcceptanceGuards R (ordinaryFGExecutionObs E rho) Ef cfg K x A.step X U) :
    A.token.receiptTime < d ∧ AcceptsFinalBefore R E rho x U d := by
  have h := finalizePending_driver R S E rho H Wr (ordinaryFGExecutionObs E rho) Ef cfg K
    hne hK (ordinaryFGExecutionObs_laws E rho) hs x y U X d A EL hhor fold G
  exact ⟨h.1, (ordinary_acceptsFinalBefore_iff R E rho hs x U d).mp h.2.2.1⟩

end AvailableChain.FGCompose
end

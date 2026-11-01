module
public import AvailableChainFGCompose.Proofs.Finality.MiddleSupport

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable {R : FGCoreReads P n Base Proposal Wire} {S : FGSafetyReads P n Wire}
variable {O : FGObservationReads R} {T : FGTiming}
variable {E : Generic.Env V} {rho : V2.D.Run V P} {I : V2.D.Interface P}
variable {D : FGHistoryWireReads S} {Ef : Electorate (Fin n)}

/-- Event times at the exact action rounds imply the earlier-row height cap. -/
theorem rowsPrem_earlier_height_core (L : FGTimingLaws T) (q y : Nat)
    (hcut : ∀ j x r a h t, HonestRowAt S E rho T j x r a →
      historyRowHeight S D a = some h → y ≤ h → eventTime rho j = some t →
      T.action q ≤ t) :
    ∀ j x r a h, r < q → HonestRowAt S E rho T j x r a →
      historyRowHeight S D a = some h → h < y := by
  intro j x r a h hr ha hh
  by_contra hn
  have late := hcut j x r a h (T.action r) ha hh (Nat.le_of_not_gt hn)
    (kmid_event_time S T E rho ha)
  exact not_le_of_gt ((kmid_action_strictMono T L) hr) late

end AvailableChain.FGCompose
end

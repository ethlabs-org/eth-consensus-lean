module
public import AvailableChainKitFG.ClientOnce
public import AvailableChainKitFG.RecordHighDef

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-- A send-once step keeps the high record guards. Every released height
pair at or above the cut names the high entry and has no timeout.
DC: additive (no DC counterpart); reason: the send-once guard and finality
filter change the client write. Reuse the inclusive `HighRecord` guard.
INTENTIONAL: retain both input premises of `RecordHighStatement`, including
the provisional finality pair. Only released rows have an output guard. -/
def RecordHighOnceStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig) (h0 : Height)
    (entry : Height → BlockId) (Λ : RecordOnce) (signer : V)
    (src : Option (FGBlock V)) (hd : HeadFields),
    HighRecord h0 entry Λ.toRecord →
    (∀ h T,
      src.map (fun C => ((derive E cfg C).h, (derive E cfg C).T_h.root)) = some (h, T) →
      h0 ≤ h → T = entry h) →
    (∀ fp, finality_pair Λ.toRecord hd = some fp →
      h0 ≤ fp.height → fp.target = entry fp.height) →
    let step := createRowOnce E cfg Λ signer src hd
    HighRecord h0 entry step.2.toRecord ∧
    (∀ a, step.1 = some a →
      ∀ h T timeout, a.height_pair = .vote h T timeout →
      h0 ≤ h → T = entry h ∧ timeout = false)

/-- The send-once high-record statement with both input premises.
DC: additive (no DC counterpart); reason: expose the statement for the
send-once client without changing the old statement. -/
theorem RecordHighOnceStatement_def :
    RecordHighOnceStatement =
      (∀ {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
        (E : Electorate V) (cfg : FGConfig) (h0 : Height)
        (entry : Height → BlockId) (Λ : RecordOnce) (signer : V)
        (src : Option (FGBlock V)) (hd : HeadFields),
        HighRecord h0 entry Λ.toRecord →
        (∀ h T,
          src.map (fun C => ((derive E cfg C).h, (derive E cfg C).T_h.root)) = some (h, T) →
          h0 ≤ h → T = entry h) →
        (∀ fp, finality_pair Λ.toRecord hd = some fp →
          h0 ≤ fp.height → fp.target = entry fp.height) →
        let step := createRowOnce E cfg Λ signer src hd
        HighRecord h0 entry step.2.toRecord ∧
        (∀ a, step.1 = some a →
          ∀ h T timeout, a.height_pair = .vote h T timeout →
          h0 ≤ h → T = entry h ∧ timeout = false)) := by rfl

/- `NoHighContestStatement` already takes arbitrary `Row V` values and the
same high height-pair guard. It does not depend on a record or row builder.
The released-row conclusion above supplies that guard without a new port. -/

end AvailableChain.KitFG
end

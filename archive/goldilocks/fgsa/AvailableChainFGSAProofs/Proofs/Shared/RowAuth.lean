module
public import AvailableChainFGSA.Model.ProposalContent

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
DC counterpart: none (row decoding helper).
A decoded row has the FG seat authentication of its signer. -/
theorem row_auth_of_toRow {n : Nat} (a : RowWire n) (u : Row (Fin n))
    (hau : a.toRow? = some u) : a.auth = .seat .fg u.signer := by
  rcases a with ⟨auth, payload⟩
  cases auth with
  | none => cases hau
  | proposer s => cases hau
  | seat label i =>
      cases label with
      | head s => cases hau
      | fg =>
          have he : (⟨i, payload.height_pair, payload.finality_pair⟩ : Row (Fin n)) = u :=
            Option.some.inj hau
          exact by rw [← he]

end AvailableChain.FGSA.Run
end

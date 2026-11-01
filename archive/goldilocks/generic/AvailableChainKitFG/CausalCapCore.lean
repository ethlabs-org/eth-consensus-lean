module
public import AvailableChainKitFG.AccountableCore

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- A positive finality certificate contains a row from outside the faulty set.
The row has the exact finality key, and the row premise gives its release fact. -/
theorem finalityCap_row_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (faulty : Finset V) (hcap : E.weightOf faulty < E.q) (y : Height) (B : FGBlock V)
    (R : Row V → Prop)
    (hrows : ∀ a ∈ chainRows B, a.signer ∉ faulty → R a)
    (hy : 0 < y) (hF : y ≤ (f B).h_F) :
    ∃ a ∈ chainRows B, a.signer ∉ faulty ∧ R a ∧
      a.finality_pair = some ⟨(f B).h_F, (f B).F.root⟩ := by
  obtain ⟨F, _, rfl, Q, hQ, hw⟩ := finality_certificate_of_certificate E H f hc B
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le hy hF))
  obtain ⟨i, hiQ, hif⟩ := honest_in_quorum E faulty hQ hcap
  obtain ⟨carrier, a, hcarrier, ha, hai, hf⟩ := hw i hiQ
  have haB : a ∈ chainRows B := mem_chainRows_of_carrier hcarrier ha
  have haf : a.signer ∉ faulty := hai ▸ hif
  exact ⟨a, haB, haf, hrows a haB haf, hf⟩

end AvailableChain.KitFG
end

module
public import ConsensusLean.Spec.Model.Conditions

public section

/-! # A lawful vote issuer and verifier

From an embedding of the claimed vote data (`claim d` defined) into the evidence type, every
protocol and selection have a vote-authentication mechanism satisfying `Run.VoteVerification`:
the issuer embeds the data of a claimed vote (canonical claims are determined by their data) and
is constant off that domain; the verifier accepts exactly the issued evidence of a canonical claim
whose signer the selection gives that role. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V}

open Classical in
/-- The issuer: the embedded vote data on claimed data, a fixed token off it. -/
noncomputable def lawfulIssue (emb : {d : (protoOf F E).VoteData // ((protoOf F E).claim d).isSome}
    ↪ (protoOf F E).Token) :
    Fin (Fintype.card V) × (protoOf F E).Role × (protoOf F E).VoteData → (protoOf F E).Token :=
  fun q => if h : ((protoOf F E).claim q.2.2).isSome then emb ⟨q.2.2, h⟩
    else Classical.arbitrary _

open Classical in
/-- The verifier: canonical, selected, and the issued evidence. -/
noncomputable def lawfulVerify (emb : {d : (protoOf F E).VoteData // ((protoOf F E).claim d).isSome}
    ↪ (protoOf F E).Token) (sel : (protoOf F E).Role → Finset (Fin (Fintype.card V))) :
    Fin (Fintype.card V) × (protoOf F E).Role × (protoOf F E).VoteData → (protoOf F E).Token →
      Bool :=
  fun q z => decide ((protoOf F E).claim q.2.2 = some (q.1, q.2.1) ∧ q.1 ∈ sel q.2.1 ∧
    z = lawfulIssue (V := V) emb q)

/-- **A run with the lawful issuer and verifier (for its own selection) satisfies
`VoteVerification`.** -/
private theorem Run.voteVerification_of_lawful (rho : Run F E)
    (emb : {d : (protoOf F E).VoteData // ((protoOf F E).claim d).isSome} ↪ (protoOf F E).Token)
    (hi : rho.issue = lawfulIssue emb) (hv : rho.verify = lawfulVerify emb rho.sel) :
    rho.VoteVerification := by
  refine ⟨fun q q' hq hq' he => ?_, fun k r d z => ?_⟩
  · obtain ⟨k, r, d⟩ := q
    obtain ⟨k', r', d'⟩ := q'
    simp only [Run.Canonical] at hq hq'
    have hs : ((protoOf F E).claim d).isSome := by simp [hq]
    have hs' : ((protoOf F E).claim d').isSome := by simp [hq']
    rw [hi] at he
    simp only [lawfulIssue, hs, hs', dite_true] at he
    have hd : d = d' := congrArg Subtype.val (emb.injective he)
    subst hd
    rw [hq] at hq'
    cases hq'
    rfl
  · rw [hv, hi]
    simp [lawfulVerify, Run.Canonical]

/-- The standard lawful issuer of a protocol: `lawfulIssue` at the embedding its token cover
gives (`Protocol.tokensCover`). -/
noncomputable def stdIssue (F : ProtocolFamily O) (E : Env V) :
    Fin (Fintype.card V) × (protoOf F E).Role × (protoOf F E).VoteData → (protoOf F E).Token :=
  lawfulIssue (protoOf F E).tokensCover.some

/-- The standard lawful verifier of a protocol for the selection `sel`. -/
noncomputable def stdVerify (F : ProtocolFamily O) (E : Env V)
    (sel : (protoOf F E).Role → Finset (Fin (Fintype.card V))) :
    Fin (Fintype.card V) × (protoOf F E).Role × (protoOf F E).VoteData → (protoOf F E).Token →
      Bool :=
  lawfulVerify (protoOf F E).tokensCover.some sel

/-- A run with the standard issuer and verifier for its own selection satisfies
`VoteVerification`. -/
theorem Run.voteVerification_std (rho : Run F E) (hi : rho.issue = stdIssue F E)
    (hv : rho.verify = stdVerify F E rho.sel) : rho.VoteVerification :=
  rho.voteVerification_of_lawful _ hi hv

end Consensus.Model

end

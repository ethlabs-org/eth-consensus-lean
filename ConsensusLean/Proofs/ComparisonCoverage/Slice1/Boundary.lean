module
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.Domain

public section

/-! # Slice 1 coverage: the exercised split

`cov1_split_witness`: at a point of the coverage domain with a split class (held or not), the
Slice 1 witness of `cov1_witness` that moreover exercises the class (`Exercised`): both groups
keep a validator honest at the horizon, and an honest message sent during the incident is held
across the groups until the incident ends.

The construction is that of the Slice 0 split witness (`healCoverage0_split`), on the Slice 1
witness point: healthy liveness (`ShapeClaimsAt.healthyLive`, at `fcap < β·n`) on a synchronous
reference run gives an honest proposal; the incident starts at its first release, and the held
split's delivery filter holds it from the opposite group until `b₁`. With sleepers the witness
point's sleep window starts at that first release, so the reference run is in another environment
and its schedule before the incident has to be transported to the witness's environment. -/

namespace Consensus.Comparison

open Shape Blocks
open Consensus.Model (pubOf protoOf sysOf Obj Msg)

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]

/-- **The exercised Slice 1 witness** at a point of the coverage domain with a split class. -/
theorem cov1_split_witness (F : ChainShapeFamily O Info) (K : Contract ProgressReq)
    (hcl : ShapeClaimsAt F K V) (hf : ProgressFits K F) (hnfg : ProposalsNotFGAtt F)
    (hfg : 1 ≤ K.params.fgDelay) (cap : Capability) (i : K.Idx) (g : O.Id)
    (hg : O.output cap = some g) (q : HealQ V) (hq : q.DomainFeasible) (hsplit : q.a.IsSplit)
    (hadm : AdmitsFaults (K.progress cap i) q.fcap)
    (hforge : 0 < q.hpre ∨ 0 < q.hpost → ForgeableRole F)
    (hβ : (q.fcap : ℚ) < K.params.β * Fintype.card V) (hsq hlq latq : WithTop ℕ) :
    ∃ (r : (Sys F V).Run) (b₀ b₁ : Time), (Sys F V).Valid r ∧ ¬ (Sys F V).Excuse r ∧
      HealClass (compiled F) K (shapeRoleFloor F V) q b₀ b₁ r ∧
      (Sys F V).prog (shapeProgress F V) K cap i ((Sys F V).ready K b₁ r)
        ((Sys F V).pt r).horizon r ∧
      Attains (compiled F) (shapeRoleFloor F V) q b₀ b₁ r ∧
      (∀ c : ℕ, hsq = c → SafeActive (q.readerDur (Sys F V) r) (healAt (Sys F V) b₁ c r)
        ((Sys F V).pt r)) ∧
      (∀ c d : ℕ, hlq = c → latq = d → ((Sys F V).pt r).TxLiveActive (q.readerDur (Sys F V) r)
        (healAt (Sys F V) b₁ c r) ((d : Time) * ((Sys F V).pt r).env.ΔAC)) := by
  sorry

end Consensus.Comparison

end

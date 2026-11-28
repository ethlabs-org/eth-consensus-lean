module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.WeakBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.StoreCache

public section

/-! # Cache facts of honest stores

`h_j < h_max` in every honest store and `h_j` is monotone along an honest node's run. The
frame key itself is the milestone `Generic.frameKey''`. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp}

/-- `h_j < h_max` in every honest store. -/
theorem hj_lt_hmax {ini} (hrun : GoldilocksRun proposer dg H tr ini) {y : Fin sp.n} (hy : y ∈ H)
    (i : Nat) : (tr.state y i).fg.hj < (tr.state y i).fg.hmax :=
  Store.hj_lt_hmax_of_reachable (Compose.fg_reachable hrun.toLocalRun hy i)

/-- `h_j` of an honest store does not decrease, for any node AC from any starts `ini`. -/
theorem hj_mono {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n}
    {tr : RunTrace A} {ini : Fin P.n → A.State}
    (hrun : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {i j : Nat} (hij : i ≤ j) : (tr.state y i).fg.hj ≤ (tr.state y j).fg.hj := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    apply ih.trans
    by_cases hc : ∃ c, tr.CallAt y j c
    · obtain ⟨c, hc⟩ := hc
      rw [tr.state_succ_of_call hc]
      have h := hrun.cutLaw y hy j c hc
      cases c with
      | ac ℓ => rw [h.2.2.1]
      | fg c =>
        cases c with
        | block B ok =>
          cases ok with
          | false => rw [h.2]
          | true =>
            obtain ⟨pr, σ, _, _, _, _, _, he⟩ := Store.onBlock_eq_some h.2.1
            rw [he]
            obtain ⟨atts, hatt⟩ := Store.addAtts_eq
              (Store.updateFinality _ σ) B.fgPayload
            rw [hatt]
            exact Healing.updateFinality_hj_le
              { (tr.state y j).fg with
                blocks := Function.update (tr.state y j).fg.blocks B.root (some B),
                σ := Function.update (tr.state y j).fg.σ B.root σ } σ
        | attestation a =>
          rw [h.1]
          obtain ⟨atts, he⟩ := Store.onAttestation_eq (tr.state y j).fg a
          rw [he]
        | attest C att =>
          cases att with
          | none => rw [h.2]
          | some att => rw [h.2.1]
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]

end Consensus.Goldilocks.Healing

end

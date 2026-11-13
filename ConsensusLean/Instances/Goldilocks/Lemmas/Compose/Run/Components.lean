module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups

public section

/-! # Component states of a run over any AC

The AC and FG projections keep the corresponding cuts, and their states commute with the
node run at honest nodes. Every honest FG state is reachable. These facts use only the
generic node cut law, not the AC's execution or a concrete AC implementation. -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P}
variable {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- A call of the AC projection is an AC cut of the run. -/
theorem projAC_callAt {y : Fin P.n} {i : Nat} {ℓ : ACLabel A} :
    tr.projAC.CallAt y i ℓ ↔ tr.CallAt y i (.ac ℓ) := by
  unfold Trace.CallAt
  change tr.node i = y ∧ (tr.label i).bind RunTrace.acLabel = some ℓ ↔ _
  cases tr.label i with
  | none => simp
  | some c => cases c <;> simp [RunTrace.acLabel]

/-- A call of the FG projection is an FG cut of the run. -/
theorem projFG_callAt {y : Fin P.n} {i : Nat} {ℓ : FGLabel P A.Payload} :
    tr.projFG.CallAt y i ℓ ↔ tr.CallAt y i (.fg ℓ) := by
  unfold Trace.CallAt
  change tr.node i = y ∧ (tr.label i).bind RunTrace.fgLabel = some ℓ ↔ _
  cases tr.label i with
  | none => simp
  | some c => cases c <;> simp [RunTrace.fgLabel]


/-- **The AC projection's state is the AC part of the run's state** (honest node). -/
theorem projAC_state (h : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    (i : Nat) :
    tr.projAC.state y i = (tr.state y i).ac := by
  induction i with
  | zero => simp [Trace.state, RunTrace.projAC, h.init y hy]
  | succ i ih =>
    by_cases hn : tr.node i = y
    · cases hl : tr.label i with
      | none =>
        rw [tr.state_succ_of_not fun ℓ hc => by simp [hc.2] at hl]
        rw [← ih]
        simp [Trace.state, RunTrace.projAC, hl]
      | some c =>
        have hc : tr.CallAt y i c := ⟨hn, hl⟩
        have hlaw := h.cutLaw y hy i c hc
        rw [tr.state_succ_of_call hc]
        cases c with
        | ac ℓ => simp [Trace.state, RunTrace.projAC, hn, hl, RunTrace.acLabel]
        | fg ℓ =>
          rw [show (tr.post i).ac = (tr.state y i).ac by
            cases ℓ with
            | block B acc =>
              cases acc
              · rw [hlaw.2]
              · exact hlaw.2.2.1
            | attestation a => exact hlaw.2.1
            | attest C s =>
              cases s
              · rw [hlaw.2]
              · exact hlaw.2.2, ← ih]
          simp [Trace.state, RunTrace.projAC, hl, RunTrace.acLabel]
    · rw [tr.state_succ_of_not fun ℓ hc => hn hc.1, ← ih]
      simp [Trace.state, RunTrace.projAC, hn]

/-- **The FG projection's state is the FG part and the record of the run's state** (honest
node). -/
theorem projFG_state (h : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    (i : Nat) : tr.projFG.state y i = ((tr.state y i).fg, (tr.state y i).record) := by
  induction i with
  | zero => simp [Trace.state, RunTrace.projFG, h.init y hy]
  | succ i ih =>
    by_cases hn : tr.node i = y
    · cases hl : tr.label i with
      | none =>
        rw [tr.state_succ_of_not fun ℓ hc => by simp [hc.2] at hl, ← ih]
        simp [Trace.state, RunTrace.projFG, hl]
      | some c =>
        have hc : tr.CallAt y i c := ⟨hn, hl⟩
        have hlaw := h.cutLaw y hy i c hc
        rw [tr.state_succ_of_call hc]
        cases c with
        | fg ℓ => simp [Trace.state, RunTrace.projFG, hn, hl, RunTrace.fgLabel]
        | ac ℓ =>
          rw [hlaw.2.2.1, hlaw.2.2.2, ← ih]
          simp [Trace.state, RunTrace.projFG, hl, RunTrace.fgLabel]
    · rw [tr.state_succ_of_not fun ℓ hc => hn hc.1, ← ih]
      simp [Trace.state, RunTrace.projFG, hn]

/-- **Every honest FG state of a run is reachable.** -/
theorem fg_reachable (h : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    (i : Nat) :
    (tr.state y i).fg.Reachable A.genesisPayload := by
  induction i with
  | zero => rw [Trace.state, h.init y hy]; exact .refl
  | succ i ih =>
    by_cases hc : ∃ c, tr.CallAt y i c
    · obtain ⟨c, hc⟩ := hc
      rw [tr.state_succ_of_call hc]
      exact (chain_fg y (.cons (h.cutLaw y hy i c hc) (.nil _)) ih).1
    · rw [tr.state_succ_of_not fun c hc' => hc ⟨c, hc'⟩]
      exact ih

end Consensus.Goldilocks.Compose

end

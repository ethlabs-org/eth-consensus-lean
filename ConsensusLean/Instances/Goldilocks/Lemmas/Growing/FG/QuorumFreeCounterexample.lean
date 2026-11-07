module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Run

public section

/-! # A quorum created after the namer-count horizon

Four validators are honest at time zero; validators 1, 2 and 3 are compromised at time one.
At time two their forged target attestations justify genesis. They never sign in the trace,
so the honest-signing quiet-window premise does not exclude these rows.
-/

namespace Consensus.Goldilocks.Growing.QuorumFree

def params : Params where
  n := 4
  hn := by decide
  Δ := 1
  hΔ := one_pos
  slotTime s := s
  slotTime_zero := rfl
  slotTime_strictMono := fun _ _ h => Nat.cast_lt.mpr h
  slotTime_public := fun _ => one_dvd _
  genesisRoot := 0
  δt := 2

def honest (t : Time) : Set (Fin params.n) := {v | t < 1 ∨ v.val = 0}

def row (v : Fin params.n) : FG.Att params.n := ⟨v, 1, 0, false, none⟩

def carrier : NodeBlock params Unit :=
  ⟨1, some 0, 2, ⟨1, by decide⟩, 0,
    [row ⟨1, by decide⟩, row ⟨2, by decide⟩, row ⟨3, by decide⟩], ()⟩

def replay : FG.ChainState params.n where
  L := 1
  s := 2
  h := 2
  Th := 1
  ThSlot := 2
  target := ∅
  prog := ∅
  pending := [(1, 0)]
  fin := Function.update (fun _ => ∅) 1 ∅
  J := 0
  hj := 1
  F := 0
  hF := 0

private theorem transition : params.fg.stateTransition (FG.ChainState.init params.fg)
    carrier.fgView = some replay := rfl

/-- A concrete adaptive-forgery obstruction to counting namers only at `T₀`:
no validator was faulty at time zero, the three rows have no honest-at-use signer,
and their accepted chain transition leaves the genesis height. -/
theorem quorum_after_compromise :
    Antitone honest ∧ (honest 0)ᶜ = ∅ ∧
      (∀ a ∈ carrier.fgPayload, a.val ∉ honest 2) ∧
      params.fg.q = 3 ∧
      params.fg.stateTransition (FG.ChainState.init params.fg) carrier.fgView = some replay ∧
      replay.h ≠ (FG.ChainState.init params.fg).h := by
  refine ⟨?_, ?_, ?_, rfl, transition, by decide⟩
  · intro s t hst v hv
    exact hv.elim (fun ht => Or.inl (lt_of_le_of_lt hst ht)) Or.inr
  · ext v
    simp [honest]
  · intro a ha
    simp only [carrier, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> simp [honest, row]

end Consensus.Goldilocks.Growing.QuorumFree

end

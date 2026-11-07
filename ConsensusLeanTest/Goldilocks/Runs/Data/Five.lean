module
public import ConsensusLeanTest.Goldilocks.Mirror.CutLaw
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart
@[expose] public section

/-! # Shared five-validator parameters for finite run witnesses

The block table, digest and schedule belong to each witness. Only the parameters and validator
identities are shared here, so importing them does not import another witness's run checks. -/

namespace Consensus.Goldilocks.Test.HalfCommittee.Five

/-- Five validators, unit delay, four ticks per slot, genesis root `2`, timeout `6`. -/
abbrev P5 : Params where
  n := 5
  hn := by decide
  Δ := 1
  hΔ := one_pos
  slotTime := fun s => 4 * (s : Int)
  slotTime_zero := by simp
  slotTime_strictMono := fun a b h => by change 4 * (a : Int) < 4 * (b : Int); omega
  slotTime_public := fun _ => one_dvd _
  genesisRoot := 2
  δt := 6

/-- The shared SA parameters, with `k = 4` and `c = 2`. -/
abbrev sp5 : SA.SAParams where
  toParams := P5
  slotTime_eq := fun s => by change 4 * (s : Int) = 4 * 1 * s; omega
  k := 4
  two_le_k := by decide
  c := 2
  two_le_c := le_rfl

/-- The honest validators `a, b, c, d` and the faulty proposer `f`. -/
abbrev va : Fin 5 := ⟨0, by decide⟩
@[inherit_doc va] abbrev vb : Fin 5 := ⟨1, by decide⟩
@[inherit_doc va] abbrev vc : Fin 5 := ⟨2, by decide⟩
@[inherit_doc va] abbrev vd : Fin 5 := ⟨3, by decide⟩
@[inherit_doc va] abbrev vf : Fin 5 := ⟨4, by decide⟩

/-- The honest validators. -/
def H : Set (Fin 5) := {y | y ≠ vf}

/-- The honest validators, in order. -/
def honest : List (Fin 5) := [va, vb, vc, vd]

theorem mem_honest : ∀ y : Fin 5, y ≠ vf → y ∈ honest := by decide

/-- The content digested by the fixtures. -/
abbrev Content := Option Nat × Nat × Nat × List (FG.Att 5) × SA.Payload 5

end Consensus.Goldilocks.Test.HalfCommittee.Five

end

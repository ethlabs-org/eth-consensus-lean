module
public import AvailableChainSAPC.Proofs.Paths
public import AvailableChainSAPC.Proofs.CertificateValidity

@[expose] public section

/-! E4 hook facts for SA-PC (design §2 E4). Each run-level fact has the
statement of the matching `HooksSound` field with `P := sapc p`; the
Registry assembles them. This library does not import the framework.

`sapc` sets `excludes := fun _ _ => false`. This is the E4 classification,
not an omission: SA-PC has no permanent refusal at the level of `processed`.
- A HEAD is processed when it is in the archive `receivedHeads`.
  `receiveHead` refuses only a HEAD of a future label, and the clock of a
  run goes forward. The Grid CO old-label and equivocation refusals act
  only on the base cache, not on the archive.
- A proposal is processed when its block is stored. The shared block
  admission refuses a future slot or an unknown parent until they change.
  Its stored-block test is `processed` itself, and its slot and proposer
  tests are wire tests of `wellFormed`.
- A PC is processed when it is valid. The handler refuses it only before
  `pcEnvelopeReady`, whose paths and label test become true later; its
  shape test is the wire test of `wellFormed`.
A wire that fails `wellFormed` is outside `ExecutionValid`. -/

namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- SA-PC excludes no object. -/
theorem sapc_excludes (p : Params) (st : State p.n) (o : Wire p.n) :
    (sapc p).excludes st o = false := rfl

theorem excludes_inert (p : Params) :
    ∀ st o, (sapc p).excludes st o = true → (sapc p).process st o = st := by
  set_option backward.isDefEq.respectTransparency false in
  intro st o h
  simp [sapc_excludes] at h

-- The run-level facts keep the `HooksSound` field shape, `[Fintype V]` included.
set_option linter.unusedFintypeInType false in
theorem excludes_stable (p : Params) :
    ∀ {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
      (rho : Run V (sapc p)), ScheduleWellFormed E rho → ∀ v o i j, i ≤ j →
        (sapc p).excludes (Run.stateBefore (sapc p) rho i v) o = true →
        (sapc p).excludes (Run.stateBefore (sapc p) rho j v) o = true := by
  set_option backward.isDefEq.respectTransparency false in
  intro V _ _ E rho _ v o i j _ h
  simp [sapc_excludes] at h

set_option linter.unusedFintypeInType false in
/-- `processed` is monotone along a run: the archive, the block store and
PC validity only grow. -/
theorem processed_stable (p : Params) :
    ∀ {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
      (rho : Run V (sapc p)), ScheduleWellFormed E rho → ∀ v o i j, i ≤ j →
        (sapc p).processed (Run.stateBefore (sapc p) rho i v) o = true →
        (sapc p).processed (Run.stateBefore (sapc p) rho j v) o = true := by
  intro V _ _ E rho _ v o i j hij h
  change processed p _ o = true at h ⊢
  have hb := stateBefore_blocks_mono p rho hij v
  have hh := stateBefore_archive_mono p rho hij v
  obtain ⟨auth, payload⟩ := o
  cases payload with
  | head x =>
      simp only [processed, decide_eq_true_eq] at h ⊢
      exact hh h
  | proposal b raw support c =>
      simp only [processed, GridCO.blockKnown, decide_eq_true_eq] at h ⊢
      exact hb h
  | pc c =>
      simp only [processed] at h ⊢
      exact pcValid_mono p _ _ hb hh c h

set_option linter.unusedFintypeInType false in
/-- `depsPresent` is monotone along a run: the block store only grows. -/
theorem deps_stable (p : Params) :
    ∀ {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
      (rho : Run V (sapc p)), ScheduleWellFormed E rho → ∀ v o i j, i ≤ j →
        (sapc p).depsPresent (Run.stateBefore (sapc p) rho i v) o = true →
        (sapc p).depsPresent (Run.stateBefore (sapc p) rho j v) o = true := by
  intro V _ _ E rho _ v o i j hij h
  change depsPresent _ o = true at h ⊢
  have hb := stateBefore_blocks_mono p rho hij v
  obtain ⟨auth, payload⟩ := o
  cases payload with
  | head x => rfl
  | proposal b raw support c =>
      simp only [depsPresent, GridCO.blockKnown, decide_eq_true_eq] at h ⊢
      exact hb h
  | pc c =>
      simp only [depsPresent] at h ⊢
      exact pcPaths_mono _ _ hb c h

/-- A handled member is carried: a proposal handles `raw ++ pcMembers c`
and carries `raw ++ support ++ pcMembers c`; a PC handles and carries its
witnesses. -/
theorem handles_carries (p : Params) :
    ∀ st o o', (sapc p).handles st o o' → o = o' ∨ (sapc p).carries o o' := by
  intro st o o' h
  change handles p st o o' at h
  change o = o' ∨ carries o o'
  rcases h with h | h
  · exact Or.inl h
  · right
    obtain ⟨auth, payload⟩ := o
    cases auth <;> cases payload <;> simp only at h
    · rename_i s b raw support c
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h.2
      simp only [carries, List.mem_map, List.mem_append]
      refine ⟨x, ?_, rfl⟩
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inr hx
    · exact h.2

end AvailableChain.SAPC
end

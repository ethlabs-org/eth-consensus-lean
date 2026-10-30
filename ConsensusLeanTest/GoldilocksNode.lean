module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Node
@[expose] public section

/-! # Witnesses for the Goldilocks Compose/AnyAC statements

On `Spec/Node` with the AC `rootAC` (one validator, `Δ = 1`, slot `s` starts at `s`; the AC
keeps no state, proposes `fc_root` with a unit payload, vouches for nothing and sends nothing),
labelled by kind (CONTRIBUTING "Statements"):

* (a) `rootAC_requirements`: `rootAC` meets requirements 1–5, so the hypothesis
  `A.Requirements` of `ThreeTips`, `HonestBlockAccepted`, `ACStatesReachable` and `SourcesHeld`
  is satisfiable by an AC that proposes.
* (a) `init_reachable`, `tick_at_zero`: the initial configuration is reachable and the tick of
  time `0` is a `Node.Step` from it (the hypotheses of `ExecIsCutChain`'s users and of
  `SourcesHeld`).
* (a) `proposer_tick`: the tick of time `1 = t_1` is a step from the initial configuration, the
  validator proposes at `1`, and `ac_proposal` returns a proposal there, with genesis's root its
  digest under `dg₁`: the hypotheses of `HonestBlockAccepted` hold together and its conclusion
  is not vacuous.
* (b) `reachable_after_tick`: the configuration after that tick is reachable (the hypotheses of
  `FinalizedMonotone`, `ACStatesReachable`, `FGStatesReachable`, `RecordIsClientRun`). -/

namespace Consensus.Goldilocks.Compose.Test

/-- One validator, `Δ = 1`, slot `s` starts at `s`, genesis root `0`, `δ_t = 2`. -/
def P₁ : Params where
  n := 1
  hn := le_rfl
  Δ := 1
  hΔ := one_pos
  slotTime s := s
  slotTime_zero := rfl
  slotTime_strictMono := fun _ _ h => Nat.cast_lt.mpr h
  slotTime_public := fun _ => one_dvd _
  proposer _ := ⟨0, Nat.one_pos⟩
  genesisRoot := 0
  δt := 2

/-- The validator. -/
def v₀ : Fin P₁.n := ⟨0, Nat.one_pos⟩

/-- An AC with no state and no messages: it proposes `fc_root` with a unit payload, returns
`fg_confirmed = ⊥`, `ac_confirmed = Φ.F`, `ac_head = Φ.fcRoot`, and sends nothing. -/
def rootAC : NodeAC P₁ where
  State := Unit
  Msg := Empty
  Payload := Unit
  validPayload _ := True
  validMsg _ := True
  holdsMsg _ _ := False
  genesisPayload := ()
  initial := ()
  onMessage _ s _ _ _ := (s, [])
  onBlock _ s _ _ _ := (s, [])
  onTick _ s _ _ := (s, [])
  proposal s Φ _ := (s, some (⟨Φ.fcRoot, Φ.fcRoot, ∅⟩, ()))
  toFG s Φ _ := (s, (none, ⟨Φ.fcRoot, Φ.fcRoot, ∅⟩))
  confirmed _ Φ _ := Φ.F
  head _ Φ _ := Φ.fcRoot
  restart _ s _ _ := (s, [])

/-- The digest: the slot (genesis, of slot `0`, has root `0`). -/
def dg₁ : Digest (List (FG.Att P₁.n)) Unit := fun _ s _ _ _ => s

/-- The frame of the last call of a reachable AC state is well formed. -/
theorem frameOK_of_reachableAt {P : Params} {FGP : Type} {A : ACInterface P FGP} {self : Fin P.n}
    {U : Set A.Blk} {s : A.State} {Φ : A.Frm} {t : Time} (h : A.ReachableAt self U s Φ t) :
    FrameOK Φ := by
  induction h with
  | init _ _ hin => exact hin.1
  | step _ _ _ hok => exact hok.1.1

/-- `rootAC` sends nothing. -/
theorem rootAC_step_emits (self : Fin P₁.n) (s : rootAC.State) (Φ : rootAC.Frm) (t : Time)
    (c : rootAC.Call) : (rootAC.step self s Φ t c).2 = [] := by
  cases c <;> rfl

/-- The duty head `(fc_root, fc_root, ∅)` is good at every frame. -/
theorem headOK_fcRoot (Φ : rootAC.Frm) : rootAC.HeadOK Φ ⟨Φ.fcRoot, Φ.fcRoot, ∅⟩ := by
  refine ⟨Relation.ReflTransGen.refl, fun h => ?_⟩
  exact absurd h.1 (Set.notMem_empty _)

/-- (a) `rootAC` meets requirements 1–5. -/
theorem rootAC_requirements : rootAC.Requirements where
  heads := by
    intro self U _ s Φ t₀ _
    refine ⟨fun _ _ d p h => ?_, fun _ _ => headOK_fcRoot Φ, fun t c Φ' _ _ e he => ?_⟩
    · simp only [rootAC, Option.some.injEq] at h
      injection h with hd _
      subst hd
      exact headOK_fcRoot Φ
    · rw [rootAC_step_emits] at he
      exact absurd he (List.not_mem_nil)
  source := by
    intro _ _ _ s Φ _ _ _ _ C h
    exact absurd h (by simp [rootAC])
  outputs := by
    intro _ _ _ s Φ t₀ hr t _
    have hok := frameOK_of_reachableAt hr
    exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl,
      hok.rooted.2 Φ.fcRoot hok.fcRoot_mem⟩
  parent := by
    intro _ _ _ s Φ _ _ σ _ s' d p h
    simp only [rootAC] at h
    injection h with hs hp
    injection hp with hp
    injection hp with hd _
    rw [← hd]
    rfl
  payload := by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    trivial

/-- (a) The initial configuration is reachable. -/
theorem init_reachable : Node.Reachable dg₁ v₀ (Node.Config.init rootAC) :=
  Relation.ReflTransGen.refl

/-- Time `0` is public. -/
theorem public_zero : P₁.IsPublic 0 := ⟨0, rfl⟩

/-- (a) The tick of time `0` is a step from the initial configuration. -/
theorem tick_at_zero :
    Node.Step dg₁ v₀ (Node.Config.init rootAC) (.tick 0) 0
      ⟨(Node.exec dg₁ v₀ (Node.init rootAC) 0 (.tick 0)).1, 0, .post⟩ :=
  ⟨le_rfl, ⟨public_zero, by simp [Node.Phase.at, Node.Config.init]⟩, trivial, rfl, rfl, rfl⟩

/-- The slot of time `1` is `1`. -/
theorem slotOf_one : P₁.slotOf 1 = 1 := by decide

/-- (a) The validator proposes at time `1 = t_1`. -/
theorem proposes_at_one : Node.Proposes (P := P₁) v₀ 1 := by
  refine ⟨by rw [slotOf_one]; exact Nat.one_pos, by rw [slotOf_one]; rfl, ?_⟩
  rw [slotOf_one]; rfl

/-- (a) The tick of time `1` is a step from the initial configuration, the validator proposes
there, `ac_proposal` returns a proposal after the AC's tick step, and genesis's root is its
digest: the hypotheses of `HonestBlockAccepted` hold together. -/
theorem proposer_tick :
    (P₁.genesisBlock rootAC.genesisPayload).RootOk dg₁ ∧
    Node.Step dg₁ v₀ (Node.Config.init rootAC) (.tick 0) 1
      ⟨(Node.exec dg₁ v₀ (Node.init rootAC) 1 (.tick 0)).1, 1, .post⟩ ∧
    Node.Proposes (P := P₁) v₀ 1 ∧
    ∃ d p, (Node.acProposal (Node.tickStep dg₁ v₀ (Node.init rootAC) 1 0 .acTick).1 1).2.2 =
      some (d, p) := by
  refine ⟨rfl, ⟨by decide, ⟨one_dvd _, by simp [Node.Phase.at, Node.Config.init]⟩, trivial, rfl,
    rfl, rfl⟩, proposes_at_one, _, (), rfl⟩

/-- (b) The configuration after the tick of time `1` is reachable. -/
theorem reachable_after_tick :
    Node.Reachable dg₁ v₀ ⟨(Node.exec dg₁ v₀ (Node.init rootAC) 1 (.tick 0)).1, 1, .post⟩ :=
  Relation.ReflTransGen.single ⟨.tick 0, 1, proposer_tick.2.1⟩

end Consensus.Goldilocks.Compose.Test

end

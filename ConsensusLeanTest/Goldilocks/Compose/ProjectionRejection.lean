module
public import ConsensusLeanTest.Goldilocks.Runs.OneValidator.TickRun
public import ConsensusLeanTest.Goldilocks.Compose.Statements
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.ACProjection
@[expose] public section

/-! # Rejection: C0.5's AC projection needs requirement 5

Kind (r) (CONTRIBUTING "Statements") for `Compose.ACProjection`
(`Statements/Compose/Run.lean`), whose docstring says requirement 5 is needed: the own block's
`ac_on_block` call must satisfy `CallOK`, whose `validPayload` the FG does not check.

`payloadAC` is `rootAC` of `ConsensusLeanTest/Goldilocks/Compose/Statements` (one validator,
`Δ = 1`, slot `s` starts at `s`; it proposes `fc_root` with a unit payload) with no valid payload.
On its tick run (`Witness.tickRun`: the validator ticks at every time `t ≥ 0`) with a collision-free
digest `dgP`:

* `payloadAC_reqHeads`, `payloadAC_reqSource`, `payloadAC_reqOutputs`, `payloadAC_reqParent`:
  requirements 1–4 hold;
* `tickRun_localRun` and `dgP_noColl`: the run is a `Node.LocalRun` with `NoCollRun`;
* `tickCuts_one`: at time `1 = t_1` the validator proposes, the FG accepts the own block, and the
  node calls `ac_on_block` with it;
* `acProjection_needs_payload`: all of these hold, and the AC projection is not an `ACLocalRun`,
  because that call breaks the frame law's input contract (`validPayload`). So requirement 5
  cannot be dropped from `ACProjection`;
* `payloadAC_not_reqPayload`: requirement 5 is what fails (by `Compose.ac_projection`). -/

namespace Consensus.Goldilocks.Compose.Test.ProjectionRejection

open Node Witness

/-- `rootAC` with no valid payload: requirement 5 fails, requirements 1–4 are `rootAC`'s. -/
def payloadAC : NodeAC P₁ := { rootAC with validPayload := fun _ => False }

/-- `payloadAC` sends nothing. -/
theorem payloadAC_step_emits (self : Fin P₁.n) (s : payloadAC.State) (Φ : payloadAC.Frm)
    (t : Time) (c : payloadAC.Call) : (payloadAC.step self s Φ t c).2 = [] := by
  cases c <;> rfl

/-- Requirement 1 holds. -/
theorem payloadAC_reqHeads : payloadAC.ReqHeads := by
  intro self U _ s Φ t₀ _
  refine ⟨fun _ _ d p h => ?_, fun t c Φ' _ _ e he => ?_⟩
  · simp only [payloadAC, rootAC, Option.some.injEq] at h
    injection h with hd _
    subst hd
    exact ⟨Relation.ReflTransGen.refl, fun h => absurd h.1 (Set.notMem_empty _)⟩
  · rw [payloadAC_step_emits] at he
    exact absurd he List.not_mem_nil

/-- Requirement 2 holds. -/
theorem payloadAC_reqSource : payloadAC.ReqSource := by
  intro _ _ _ s Φ _ _ _ _ C h
  exact absurd h (by simp [payloadAC, rootAC])

/-- Requirement 3 holds. -/
theorem payloadAC_reqOutputs : payloadAC.ReqOutputs := by
  intro _ _ _ s Φ t₀ hr t _
  have hok := frameOK_of_reachableAt hr
  exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl,
    hok.rooted.2 Φ.fcRoot hok.fcRoot_mem⟩

/-- Requirement 4 holds. -/
theorem payloadAC_reqParent : payloadAC.ReqParent := by
  intro _ _ _ s Φ _ _ σ _ s' d p h
  simp only [payloadAC, rootAC] at h
  injection h with hs hp
  injection hp with hp
  injection hp with hd _
  rw [← hd]
  rfl

instance : Countable payloadAC.Payload := inferInstanceAs (Countable Unit)

instance (n : Nat) : Countable (FG.Att n) :=
  Function.Injective.countable (f := fun a : FG.Att n => (a.val, a.h, a.T, a.timeout, a.fin))
    (by rintro ⟨⟩ ⟨⟩ h; simp_all)

/-- The content of a block (what its root digests). -/
abbrev Content := Option Nat × Nat × Nat × List (FG.Att P₁.n) × payloadAC.Payload

/-- An injective code of block contents. -/
noncomputable def code : Content → Nat := (Countable.exists_injective_nat Content).choose

theorem code_injective : Function.Injective code :=
  (Countable.exists_injective_nat Content).choose_spec

/-- The genesis content. -/
def genContent : Content := (none, 0, 0, [], ())

open Classical in
/-- A collision-free digest whose value at the genesis content is the genesis root `0`. -/
noncomputable def dgP : Digest (List (FG.Att P₁.n)) payloadAC.Payload := fun p s x a q =>
  if (p, s, x, a, q) = genContent then 0 else code (p, s, x, a, q) + 1

theorem dgP_injective {p s x a q p' s' x' a' q'} (h : dgP p s x a q = dgP p' s' x' a' q') :
    (p, s, x, a, q) = ((p', s', x', a', q') : Content) := by
  unfold dgP at h
  by_cases h₁ : (p, s, x, a, q) = genContent <;> by_cases h₂ : (p', s', x', a', q') = genContent
  · exact h₁.trans h₂.symm
  · rw [ite_eq_left h₁, ite_eq_right h₂] at h; omega
  · rw [ite_eq_right h₁, ite_eq_left h₂] at h; omega
  · rw [ite_eq_right h₁, ite_eq_right h₂] at h; exact code_injective (Nat.add_right_cancel h)

/-- `NoColl` holds of every run under `dgP`. -/
theorem dgP_noColl (tr : RunTrace payloadAC) : NoCollRun dgP tr := by
  intro B _ C _ h
  have h' := dgP_injective h
  injection h' with h₁ h'
  injection h' with h₂ h'
  injection h' with h₃ h'
  injection h' with h₄ h₅
  exact ⟨h₁, h₂, h₃, h₄, h₅⟩


/-- The state before the tick of time `1` is the initial one. -/
theorem tickState_one : tickState payloadAC dgP 1 = Node.init payloadAC := by
  have hnp : ¬ Node.Proposes (P := P₁) (fun _ => v0) v0 ((0 : Nat) : Int) := fun h => by
    have := h.1; rw [show P₁.slotOf ((0 : Nat) : Int) = 0 by decide] at this; omega
  simp only [tickState, Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, Node.tickStep, hnp,
    Node.acCall, Node.acToFG, ite_false, List.foldl]
  rfl

/-- The fork-choice root of the initial FG state is genesis. -/
theorem init_fcRoot : (Store.init (P := P₁) ()).fcRoot = P₁.genesisBlock () := by
  unfold Store.fcRoot; split_ifs <;> rfl

/-- The own block of time `1`, on the initial FG state. -/
noncomputable abbrev ownBlock : payloadAC.Blk :=
  mkBlock dgP v0 (Store.init (P := P₁) ()) 1 0 (P₁.genesisBlock ()) ()

/-- The FG accepts the own block of time `1` on the initial FG state. -/
theorem init_onBlock : ∃ fg', (Store.init (P := P₁) ()).onBlock ownBlock = some fg' := by
  have hslot : P₁.slotOf (1 : Time) = 1 := by decide
  have hroot : dgP (some 0) 1 0 [] () ≠ 0 := by
    unfold dgP
    split_ifs with h
    · exact absurd (congrArg Prod.fst h) (by simp [genContent])
    · omega
  have hB : ownBlock = ⟨dgP (some 0) 1 0 [] (), some 0, 1, v0, 0, [], ()⟩ := by
    simp only [ownBlock, mkBlock, hslot]
    rfl
  rw [hB]
  have hg : P₁.genesisBlock () ∈ (Store.init (P := P₁) ()).tree := rfl
  have h1 : ((Store.init (P := P₁) ()).blocks (dgP (some 0) 1 0 [] ())).isSome = false := by
    change (if dgP (some 0) 1 0 [] () = 0 then some (P₁.genesisBlock ()) else none).isSome = false
    rw [ite_eq_right hroot]; rfl
  have h2 : ((Store.init (P := P₁) ()).blocks 0).isNone = false := rfl
  unfold Store.onBlock
  dsimp only
  split_ifs with hc
  · exfalso
    rcases hc with hc | hc | hc
    · rw [h1] at hc; cases hc
    · rw [h2] at hc; cases hc
    · exact hc (Relation.ReflTransGen.single ⟨Set.mem_insert_of_mem _ hg, Set.mem_insert _ _, rfl⟩)
  · split
    · rename_i hn
      unfold FG.FGParams.stateTransition at hn
      rw [ite_eq_left ⟨by decide, fun a ha => absurd ha List.not_mem_nil⟩] at hn
      cases hn
    · exact ⟨_, rfl⟩

/-- At time `1 = t_1` the validator proposes, the FG accepts the own block, and the node calls
`ac_on_block` with it: the fourth cut of the tick of time `1`. -/
theorem tickCuts_one :
    ∃ Φ, (tickCuts payloadAC dgP 1)[3]? = some (.ac ⟨.block ownBlock, Φ, []⟩) := by
  have hp : Node.Proposes (P := P₁) (fun _ => v0) v0 (1 : Time) := ⟨by decide, by decide, rfl⟩
  have hprop : ∀ s Φ t, payloadAC.proposal s Φ t = (s, some (⟨Φ.fcRoot, Φ.fcRoot, ∅⟩, ())) :=
    fun _ _ _ => rfl
  have hfr : (frame (acCall v0 (Node.init payloadAC) 1 .tick).1).fcRoot = P₁.genesisBlock () :=
    init_fcRoot
  have hfg : (acCall v0 (Node.init payloadAC) 1 .tick).1.fg = Store.init () := rfl
  have hsl : ¬ P₁.slotOf (1 : Time) < ownBlock.slot := lt_irrefl _
  obtain ⟨fg', hon⟩ := init_onBlock
  simp only [ownBlock] at hon hsl ⊢
  have hob : ∀ st : NodeState payloadAC, st.fg = Store.init () →
      (Node.onBlock v0 st 1 (mkBlock dgP v0 (Store.init ()) 1 0 (P₁.genesisBlock ()) ())).2 =
        [.fg (.block (mkBlock dgP v0 (Store.init ()) 1 0 (P₁.genesisBlock ()) ()) true),
          .ac ⟨.block (mkBlock dgP v0 (Store.init ()) 1 0 (P₁.genesisBlock ()) ()),
            frame { st with fg := fg' }, []⟩] := by
    intro st hst
    simp only [Node.onBlock, hsl, ite_false, hst]
    split
    · next h => exact absurd (h.symm.trans hon) (by simp)
    · next fg'' h =>
      obtain rfl : fg'' = fg' := Option.some.inj (h.symm.trans hon)
      simp only [acCall, payloadAC_step_emits]
  simp only [tickCuts, tickState_one, Nat.cast_one, Node.exec, Node.onTick, Node.runSteps,
    Node.tickSteps, Node.tickStep, hp, ite_true, List.foldl, Node.acProposal, hprop,
    Node.proposeBlock, hfr, hfg]
  erw [hob _ rfl]
  exact ⟨_, rfl⟩

/-- The AC projection of the tick run is not an `ACLocalRun`: the `ac_on_block` call of the own
block of time `1` (cut `8 + 3`) breaks the frame law's input contract, `validPayload`. -/
theorem not_acLocalRun : ¬ ACLocalRun payloadAC Set.univ
    ((tickRun payloadAC dgP).HonestBlocks Set.univ) (tickRun payloadAC dgP).projAC := by
  intro h
  obtain ⟨Φ, hc⟩ := tickCuts_one
  have hcall : (tickRun payloadAC dgP).projAC.CallAt v0 11 ⟨.block ownBlock, Φ, []⟩ := by
    refine ⟨rfl, ?_⟩
    change ((tickCuts payloadAC dgP 1)[3]?).bind RunTrace.acLabel = _
    rw [hc]
    rfl
  rcases h.frameLaw v0 trivial 11 _ hcall with ⟨-, Φ₀, -, -, hok⟩ | ⟨j, ℓ', -, -, -, hok⟩
  · exact hok.2.2.1
  · exact hok.2.2.1

/-- **Requirement 5 is needed in `ACProjection`.** Requirements 1–4 hold of `payloadAC`, its tick
run is a `Node.LocalRun` with `NoCollRun`, and the AC projection of that run is not an
`ACLocalRun`. -/
theorem acProjection_needs_payload (sg : payloadAC.Msg → Fin P₁.n) :
    payloadAC.ReqHeads ∧ payloadAC.ReqSource ∧ payloadAC.ReqOutputs ∧ payloadAC.ReqParent ∧
      Node.LocalRun (fun _ => v0) dgP Set.univ sg (tickRun payloadAC dgP) ∧
      NoCollRun dgP (tickRun payloadAC dgP) ∧
      ¬ ACLocalRun payloadAC Set.univ ((tickRun payloadAC dgP).HonestBlocks Set.univ)
        (tickRun payloadAC dgP).projAC :=
  ⟨payloadAC_reqHeads, payloadAC_reqSource, payloadAC_reqOutputs, payloadAC_reqParent,
    tickRun_localRun (A := payloadAC) (dg := dgP) rfl rfl sg, dgP_noColl _, not_acLocalRun⟩

/-- Requirement 5 is what fails: with it, `Compose.ac_projection` would make the projection an
`ACLocalRun`. -/
theorem payloadAC_not_reqPayload : ¬ payloadAC.ReqPayload := fun h5 =>
  not_acLocalRun (ac_projection P₁ payloadAC dgP Set.univ (fun m => (m : Empty).elim)
    (tickRun payloadAC dgP) (fun _ => v0)
    ⟨payloadAC_reqHeads, payloadAC_reqSource, payloadAC_reqOutputs, payloadAC_reqParent, h5⟩
    (tickRun_localRun (A := payloadAC) (dg := dgP) rfl rfl _) (dgP_noColl _))

end Consensus.Goldilocks.Compose.Test.ProjectionRejection

end

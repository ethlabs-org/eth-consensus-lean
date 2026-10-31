module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run
public import ConsensusLeanTest.GoldilocksFGStore
public import ConsensusLeanTest.GoldilocksRun
public import Mathlib.Tactic.Ring
@[expose] public section

/-! # Witnesses for the Goldilocks run-level healing statements (HR.1–HR.4)

Labelled by kind (CONTRIBUTING "Statements"):

* (a) `idle_phaseCount_premises`: the idle FG trace of `ConsensusLeanTest/GoldilocksFGStore` (one
  honest validator, no FG call) is an `FGLocalRun` with `f < 2q − n`: the hypotheses of
  `PhaseCount` (HR.2) hold together.
* (a) `idle_phaseAt`: on that trace the effective phase is defined at every cut: frontier `1`,
  the top-`J` case with `J = genesis` (so `PhaseAt` is inhabited, and HR.2 (b) is not vacuous in
  its phase hypothesis).
* (a) `oneTickRun_catch_noRestart`: the one-tick run of `ConsensusLeanTest/GoldilocksRun` is a
  `Node.LocalRun` that satisfies `CatchRun` (for every `g`, `κ`; vacuously: no acceptance) and
  `NoRestartAfter` (for every time), over `idleAC`, not the Goldilocks SA.
* (a) `periodicRun_healthy_catch_noRestart`: the infinite periodic run of
  `ConsensusLeanTest/GoldilocksRun` satisfies `Healthy(0)`, `CatchRun` (vacuously: no acceptance)
  and `NoRestartAfter` with the run laws: the generic `RunTrace` premises hold together on an
  infinite run over `idleAC`; `GoldilocksRun`, `HSShared` and `PropPlus` have no witness here.
* Arithmetic check (no witness kind): `C_HS_closed_form`, `bound_closed_form` and
  `T_heal_closed_form`, the closed forms of `C_HS`, of `ḡ + 24Δ + 12C_HS` (HR.3 (c)) and of `T_heal`
  (H.4), hold at every parameter (a check of the transcription of the constants).

**Not provided, too costly here** (a follow-up): a non-vacuous run witness (kind (b)) for HR.1,
HR.3, HR.4, H.2 (run), H.3 and H.4, and premise witnesses over Goldilocks traces for `HSShared`
and `PropPlus`, and over driven SA traces for H.1 and H.2. `Healthy(g)` keeps every honest validator
awake from `ḡ` on, and a run's awake function is clamped to its horizon
(`Node.LocalRun.awake_in_horizon`), so every run satisfying `Healthy(g)` is infinite; the periodic
run above is one, but over `idleAC`, not the Goldilocks SA. A Goldilocks witness needs a tick of
the node at every public time, each expanded through `Node.exec` (with proposals at every slot
start and the FG's `state_transition` on each block), and a reset `a_z` needs honest attestations
at height `H_z + 1`, i.e. a justified chain under the Goldilocks SA. `Prop⁺(G_p)` needs honest
proposals in every window from `ḡ`, so it is not satisfied by an idle run. -/

namespace Consensus.Goldilocks.Healing.Test

/-- (a) The idle FG trace is an `FGLocalRun` for the honest set `{0}` with `f < 2q − n` (here
`f = 0`, `n = 1`, `q = 1`). -/
theorem idle_phaseCount_premises :
    FGLocalRun () {⟨0, Nat.one_pos⟩} {Store.Test.P₁.genesisBlock ()} Store.Test.idleTrace ∧
      ({⟨0, Nat.one_pos⟩} : Set (Fin Store.Test.P₁.n))ᶜ.ncard <
        2 * Store.Test.P₁.fg.q - Store.Test.P₁.n := by
  refine ⟨Store.Test.idle_localRun, ?_⟩
  have hc : ({⟨0, Nat.one_pos⟩} : Set (Fin Store.Test.P₁.n))ᶜ = ∅ := by
    ext y; simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false, not_not]; exact Fin.ext (Nat.lt_one_iff.mp y.isLt)
  rw [hc, Set.ncard_empty]
  decide

/-- A block of the initial FG state's tree is genesis. -/
theorem init_tree {B : NodeBlock Store.Test.P₁ Unit}
    (hB : B ∈ (Store.init (P := Store.Test.P₁) ()).tree) : B = Store.Test.P₁.genesisBlock () := by
  change (Store.init (P := Store.Test.P₁) ()).blocks B.root = some B at hB
  simp only [Store.init] at hB
  split at hB
  · exact (Option.some_inj.mp hB).symm
  · exact absurd hB (by simp)

/-- Genesis is in the initial FG state's tree. -/
theorem genesis_mem_init :
    Store.Test.P₁.genesisBlock () ∈ (Store.init (P := Store.Test.P₁) ()).tree := by
  change (Store.init (P := Store.Test.P₁) ()).blocks _ = some _
  simp [Store.init, Params.genesisBlock]

/-- (a) At every cut of the idle trace, the effective phase is frontier `1`, top `J = genesis`. -/
theorem idle_phaseAt (i : Nat) :
    PhaseAt Store.Test.idleTrace {⟨0, Nat.one_pos⟩} i 1 (.top (Store.Test.P₁.genesisBlock ())) := by
  have hs : ∀ y, Store.Test.idleTrace.store y i = Store.init () := fun y => by
    rw [FGTrace.store, Store.Test.idleTrace_state]
  refine ⟨⟨⟨⟨0, Nat.one_pos⟩, rfl, by rw [hs]; rfl⟩, fun y _ => by rw [hs]; exact le_rfl⟩,
    ⟨⟨0, Nat.one_pos⟩, rfl, by rw [hs]; exact genesis_mem_init,
      Store.Test.P₁.genesisBlock (), by rw [hs]; exact genesis_mem_init, by rw [hs]; rfl,
      by rw [hs]; rfl⟩, ?_⟩
  rintro ⟨y, -, B, hB, -, hanc⟩
  rw [hs] at hB hanc
  exact hanc (by rw [init_tree hB]; exact Relation.ReflTransGen.refl)

/-- (a) The one-tick run is a `Node.LocalRun` with `CatchRun` and `NoRestartAfter`: it accepts no
block and has no restart (its cuts are `ac_on_tick` and `ac_to_fg`). -/
theorem oneTickRun_catch_noRestart (sg : Compose.Test.rootAC.Msg → Fin Compose.Test.P₁.n)
    (g κ t : Time) :
    Node.LocalRun (fun _ => Compose.Test.v₀) Compose.Test.dg₁ Set.univ sg Compose.Test.oneTickRun ∧
      CatchRun Compose.Test.oneTickRun Set.univ g κ ∧
      NoRestartAfter Compose.Test.oneTickRun Set.univ t := by
  refine ⟨Compose.Test.oneTickRun_localRun sg, ?_, ?_⟩
  · intro x _ i B hB
    obtain ⟨_, hℓ, -⟩ := Compose.Test.oneTickRun_label_ac hB.2
    cases hℓ
  · intro y _ k hk
    obtain ⟨ℓ, hc, hr⟩ := hk
    obtain ⟨ℓ', hℓ', hcall⟩ := Compose.Test.oneTickRun_label_ac hc.2
    cases hℓ'
    rcases hcall with h | h <;> rw [h] at hr <;> cases hr

/-- Every labelled cut of the periodic run is an AC call: a tick, a proposal or `ac_to_fg`. -/
theorem periodicRun_label_ac {i : Nat} {c : Cut Compose.Test.idleAC}
    (h : Compose.Test.periodicRun.label i = some c) :
    ∃ ℓ : ACLabel Compose.Test.idleAC, c = .ac ℓ ∧
      (ℓ.call = .tick ∨ ℓ.call = .proposal ∨ ℓ.call = .toFG) := by
  have hm : c ∈ Compose.Test.idleTickCuts ((i / 3 : Nat) : Int) :=
    List.mem_of_getElem? h
  obtain ⟨ℓ, hc, -, -, hcall⟩ := Compose.Test.idleTickCuts_mem (Int.natCast_nonneg _) hm
  exact ⟨ℓ, hc, hcall⟩

/-- (a) The infinite periodic run of `ConsensusLeanTest/GoldilocksRun` (one honest validator
ticking at every time) satisfies `Healthy(0)` (with `Δ_F = 1`), `CatchRun` (for every `κ`) and
`NoRestartAfter` (for every time) together with the run laws, on an infinite run over `idleAC`
(`CatchRun` vacuously: no block is accepted). `GoldilocksRun`, `HSShared` and `Prop⁺` need the
Goldilocks SA: a follow-up. -/
theorem periodicRun_healthy_catch_noRestart
    (sg : Compose.Test.idleAC.Msg → Fin Compose.Test.P₁.n) (κ t : Time) :
    Node.LocalRun (fun _ => Compose.Test.v₀) Compose.Test.dg₁ Set.univ sg Compose.Test.periodicRun ∧
      Compose.Test.periodicRun.HealthyRun Set.univ 1 0 ∧
      CatchRun Compose.Test.periodicRun Set.univ 0 κ ∧
      NoRestartAfter Compose.Test.periodicRun Set.univ t := by
  refine ⟨Compose.Test.periodicRun_localRun sg, Compose.Test.periodicRun_healthy, ?_, ?_⟩
  · intro x _ i B hB
    obtain ⟨_, hℓ, -⟩ := periodicRun_label_ac hB.2
    cases hℓ
  · intro y _ k hk
    obtain ⟨ℓ, hc, hr⟩ := hk
    obtain ⟨ℓ', hℓ', hcall⟩ := periodicRun_label_ac hc.2
    cases hℓ'
    rcases hcall with h | h | h <;> rw [h] at hr <;> cases hr

/-- Arithmetic check: `C_HS = (8k + 49 + 4δ_t)Δ + Δ_F + 3G` (claims HR.3 (c)). -/
theorem C_HS_closed_form (sp : SA.SAParams) (ΔF G : Time) :
    C_HS sp ΔF G = (8 * (sp.k : Time) + 49 + 4 * (sp.toParams.δt : Time)) * sp.Δ + ΔF + 3 * G := by
  simp only [C_HS, D_HS]; ring

/-- Arithmetic check: `ḡ + 24Δ + 12C_HS = ḡ + (96k + 612 + 48δ_t)Δ + 12Δ_F + 36G` (claims
HR.3 (c)). -/
theorem bound_closed_form (sp : SA.SAParams) (g ΔF G : Time) :
    SA.gbar g + 24 * sp.Δ + 12 * C_HS sp ΔF G =
      SA.gbar g + (96 * (sp.k : Time) + 612 + 48 * (sp.toParams.δt : Time)) * sp.Δ + 12 * ΔF +
        36 * G := by
  simp only [C_HS, D_HS]; ring

/-- Arithmetic check: `T_heal = ḡ + (104k + 628 + 48δ_t)Δ + 12Δ_F + 36G + T_b` (claims H.4). -/
theorem T_heal_closed_form (sp : SA.SAParams) (g ΔF G Tb : Time) :
    T_heal sp g ΔF G Tb =
      SA.gbar g + (104 * (sp.k : Time) + 628 + 48 * (sp.toParams.δt : Time)) * sp.Δ + 12 * ΔF +
        36 * G + Tb := by
  simp only [T_heal, C_HS, D_HS, SA.Θ]; ring

end Consensus.Goldilocks.Healing.Test

end

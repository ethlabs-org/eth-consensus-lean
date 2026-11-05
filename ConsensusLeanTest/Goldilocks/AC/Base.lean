module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Base
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
public import Mathlib.Data.Set.Finite.Basic
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Handlers
@[expose] public section

/-! # Witnesses for the Goldilocks ACBase statements, and `CaseOneA13`

On `Spec/AC` and `Spec/SA`, labelled by kind (CONTRIBUTING "Statements"), with one validator,
`Δ = 1`, `t_s = 4s`, `k = 2`:

* (a) `initial_reachable`: the initial SA state is reachable with the genesis frame inside the
  coherent set `{genesis}` (the hypothesis of every `AtReachable` statement: A0.1–A0.6, A0.9).
* (a) `proposal_at_slot_one`: from it, `ac_proposal` at `t_1` returns a proposal (the hypothesis
  of requirements 4 and 5, `ReqParent` and `ReqPayload`).
* (a) `localRun_one_tick`: an AC trace in which the validator makes one `on_tick` call at time
  `0` satisfies the AC trace contract `ACLocalRun` (the hypothesis of F.1 (c), A0.7's joined
  clause and A0.8).
* (a) `acRun_one_tick`: that trace also satisfies the honest-object facts, so `ACRun` (the
  hypothesis of every ACSteps statement) is satisfiable.

`CaseOneA13` is a test case written against the AC trace contract (a test of the
contract, not a milestone statement: A1.3 is stated in ACSteps): A1.3 per vote, with the claims'
hypotheses, `Sync_AC`, `Carry_y` and `f < h_τ` over the trace, and no FG state. -/

namespace Consensus.Goldilocks.SA.Test

/-- The shared parameters: one validator, `Δ = 1`, `t_s = 4s`, genesis root `0`. -/
abbrev P1 : Params where
  n := 1
  hn := le_rfl
  Δ := 1
  hΔ := one_pos
  slotTime := fun s => 4 * (s : Int)
  slotTime_zero := by simp
  slotTime_strictMono := fun a b h => by change 4 * (a : Int) < 4 * (b : Int); omega
  slotTime_public := fun _ => one_dvd _
  genesisRoot := 0
  δt := 0

/-- The SA parameters: `P1` with `k = 2`. -/
abbrev sp1 : SAParams where
  toParams := P1
  slotTime_eq := fun s => by change 4 * (s : Int) = 4 * 1 * s; omega
  k := 2
  two_le_k := le_rfl
  c := 2
  two_le_c := le_rfl

/-- The validator. -/
abbrev v0 : Fin sp1.n := ⟨0, Nat.one_pos⟩

/-- A replay order for restarts. -/
noncomputable abbrev ro1 : ReplayOrder sp1 Unit := ReplayOrder.choice sp1

/-- The Goldilocks SA with these parameters. -/
noncomputable abbrev GA1 : ACInterface sp1.toParams Unit := goldilocksSA sp1 Unit ro1

/-- Genesis: root `0`, no parent, slot `0`, empty payloads. -/
def g : Blk sp1.n Unit := ⟨0, none, 0, v0, 0, (), ([], [])⟩

/-- The genesis frame. -/
def Φ₀ : Frm sp1.n Unit := ⟨{g}, g, g, {g}⟩

/-- The genesis frame is well formed. -/
theorem frameOK_Φ₀ : FrameOK Φ₀ where
  finite := Set.finite_singleton g
  coherent := ⟨Set.injOn_singleton _ _, fun B hB C hC h => by
    rw [Set.mem_singleton_iff.mp hB, Set.mem_singleton_iff.mp hC] at h; simp [g] at h⟩
  rooted := ⟨rfl, fun C hC => by rw [Set.mem_singleton_iff.mp hC]; exact Relation.ReflTransGen.refl⟩
  fcRoot_mem := rfl
  F_anc_fcRoot := Relation.ReflTransGen.refl
  viableHeads_subset := le_rfl
  fcRoot_anc_viableHeads := fun W hW => by
    rw [Set.mem_singleton_iff.mp hW]; exact Relation.ReflTransGen.refl

/-- `{genesis}` is coherent. -/
theorem coherent_g : Coherent ({g} : Set (Blk sp1.n Unit)) := frameOK_Φ₀.coherent

/-- (a) The initial SA state is reachable, with the genesis frame, inside `{genesis}`. -/
theorem initial_reachable :
    (GA1).ReachableAt v0 ({g} : Set (Blk sp1.n Unit)) (SAState.initial 0) Φ₀ 0 :=
  ACInterface.ReachableAt.init (A := GA1) (self := v0) (U := {g}) Φ₀
    ⟨rfl, rfl, rfl, rfl, rfl⟩ ⟨frameOK_Φ₀, le_rfl⟩

/-- (a) From the initial state, `ac_proposal` at `t_1` returns a proposal. -/
theorem proposal_at_slot_one :
    ((GA1).proposal (SAState.initial 0) Φ₀ (sp1.toParams.slotTime 1)).2.isSome
      := by
  simp [acProposal, joined, SAState.initial]

/-- The one-tick trace: validator `0` makes one `on_tick` call at time `0` with the genesis
frame, then the AC stutters; the validator is always awake. -/
noncomputable def oneTick : SATrace sp1 Unit ro1 where
  init := fun _ => SAState.initial 0
  node := fun _ => v0
  time := fun _ => 0
  event := fun i => i
  pos := fun _ => 0
  label := fun i =>
    if i = 0 then some ⟨.tick, Φ₀, (acOnTick sp1 v0 (SAState.initial 0) Φ₀ 0).2⟩ else none
  post := fun _ => (acOnTick sp1 v0 (SAState.initial 0) Φ₀ 0).1
  awake := fun _ _ => True

/-- A labelled cut of `oneTick` is the tick at cut `0`. -/
theorem oneTick_label {i : Nat} {ℓ} (h : oneTick.label i = some ℓ) :
    i = 0 ∧ ℓ = ⟨.tick, Φ₀, (acOnTick sp1 v0 (SAState.initial 0) Φ₀ 0).2⟩ := by
  simp only [oneTick] at h
  split_ifs at h with h0
  · exact ⟨h0, (Option.some.inj h).symm⟩

/-- (a) The one-tick trace satisfies the AC trace contract for the honest set `{0}` inside
`{genesis}`. -/
theorem localRun_one_tick :
    ACLocalRun (GA1) Set.univ ({g} : Set (Blk sp1.n Unit)) oneTick where
  coherent := coherent_g
  init := fun _ _ => rfl
  exec := fun i ℓ h _ => by
    obtain ⟨rfl, rfl⟩ := oneTick_label h
    rfl
  frameLaw := fun y _ i ℓ h => by
    obtain ⟨rfl, rfl⟩ := oneTick_label h.2
    exact Or.inl ⟨fun k _ hk => absurd hk (Nat.not_lt_zero k), Φ₀, ⟨rfl, rfl, rfl, rfl, rfl⟩,
      ⟨frameOK_Φ₀, le_rfl⟩, ⟨frameOK_Φ₀, le_rfl⟩, rfl⟩
  time_nonneg := fun _ => le_rfl
  time_mono := fun _ _ _ => le_rfl
  awake_of_call := fun _ _ _ _ _ => trivial
  restart_of_sleep := fun _ _ _ _ _ _ _ _ hu _ => absurd trivial hu
  restart_at_wake := fun _ _ _ _ _ _ hu _ => absurd trivial hu
  sleep_of_restart := fun y _ i ℓ h hr => by
    obtain ⟨rfl, rfl⟩ := oneTick_label h.2
    cases hr

/-- **A1.3 per vote over an AC trace** (claims A1.3; a test of the AC trace contract, not a
milestone statement). For an
honest `y` and its own vote emission `e` of slot `m + 1` at cut `i` (time `τ`): if every honest
slot-`m` vote extends `B`, the honest slot-`m` voters are at least half of the committee,
`Carry_y(m, S_m, B)` holds for their votes, `f < h_τ`, `Sync[t_m, τ]` holds, at `e` the block `B` is
in `y`'s viable voter block tree or at or below its `fc_root`, and every honest slot-`(m+1)` vote at
an earlier cut extends `B`, then `e`'s vote extends `B`. -/
def CaseOneA13 (sp : SAParams) : Prop :=
  ∀ (FGP : Type) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (ro : ReplayOrder sp FGP)
    (tr : SATrace sp FGP ro),
    ACLocalRun (goldilocksSA sp FGP ro) H U tr →
    ∀ (m : Nat) (B : Blk sp.n FGP) (y : Fin sp.n) (i : Nat) (ℓ : ACLabel (goldilocksSA sp FGP ro))
      (e : Em sp FGP), y ∈ H → tr.CallAt y i ℓ → e ∈ ℓ.emits → e.msg.slot = m + 1 →
    (∀ x ∈ H, ∀ j e', VoteAt tr x j e' → e'.msg.slot = m → VoteExtends U e'.msg B) →
    sp.n ≤ 2 * {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = m}.ncard →
    CarryAt tr U y i e m {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = m} →
    FaultBound tr H (tr.time i) →
    SyncAC (goldilocksSA sp FGP ro) H U (sp.ts m) (tr.time i) tr →
    (B ∈ ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame (m + 1)) ∨
      ℓ.frame.Anc B ℓ.frame.fcRoot) →
    (∀ x ∈ H, ∀ j < i, ∀ e', VoteAt tr x j e' → e'.msg.slot = m + 1 → VoteExtends U e'.msg B) →
    VoteExtends U e.msg B

end Consensus.Goldilocks.SA.Test

namespace Consensus.Goldilocks.SA.Test

/-- The one-tick trace's tick changes nothing: at time `0` neither the vote check nor the update
runs. -/
theorem oneTick_post (i : Nat) : oneTick.post i = SAState.initial 0 := by
  have h0 : sp1.slot 0 = 0 := by simp [Params.slotOf]
  have hΔ : sp1.Δ = 1 := rfl
  simp [oneTick, acOnTick, joined, SAParams.ts, h0, hΔ, SAState.initial]

/-- Every state of the one-tick trace is the initial state. -/
theorem oneTick_state (y : Fin sp1.n) (i : Nat) : oneTick.state y i = SAState.initial 0 := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Trace.state]; split_ifs <;> simp [oneTick_post, ih]

/-- (a) The one-tick trace satisfies the AC trace contract and the honest-object facts (the
hypothesis `ACRun` of every ACSteps statement). -/
theorem acRun_one_tick : ACRun (fun _ => 0) oneTick Set.univ ({g} : Set (Blk sp1.n Unit)) where
  localRun := localRun_one_tick
  honest :=
    { pool_vote := fun y _ i σ v hv _ => by
        rw [oneTick_state] at hv; simp [SAState.initial] at hv
      message_vote := fun y _ i ℓ v h hc _ => by
        obtain ⟨rfl, rfl⟩ := oneTick_label h.2
        cases hc
      carried_vote := fun y _ i ℓ h B hB v hv => by
        obtain ⟨rfl, rfl⟩ := oneTick_label h.2
        rw [Set.mem_singleton_iff.mp hB] at hv; simp [g, blockVotes] at hv
      proposer := fun B ⟨y, _, i, ℓ, h, hB⟩ hg => by
        obtain ⟨rfl, rfl⟩ := oneTick_label h.2
        rw [Set.mem_singleton_iff.mp hB] at hg; exact absurd rfl hg
      one_block := fun B B' ⟨_, _, i, ℓ, h, hB⟩ ⟨_, _, i', ℓ', h', hB'⟩ _ _ _ => by
        obtain ⟨rfl, rfl⟩ := oneTick_label h.2
        obtain ⟨rfl, rfl⟩ := oneTick_label h'.2
        rw [Set.mem_singleton_iff.mp hB, Set.mem_singleton_iff.mp hB'] }

/-- Earlier admission satisfies retained service without pretending that it processed again.
The numerical readpoint data are the source-time counterexample: admission at 4, a new
source at 5, and recipient deadline 8. This checks the adapter on those reduced facts,
not a replay of the engine execution supplying them. -/
theorem earlier_admission_served {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
    (tr : SATrace sp FGP ro) (y : Fin sp.n) (v : Vote sp.n) {q j : Nat}
    (hqj : q ≤ j) (hp : v ∈ (tr.state y q).pool v.slot)
    (hst : (tr.state y q).voteStamp v = ETime.of 4)
    (hd : tr.deadline y j 5 = 8)
    (hnr : ∀ r, q ≤ r → r < j → ¬ tr.RestartAt y r)
    (hno : ∀ k ≤ j, 5 ≤ tr.time k → ¬ tr.ProcessAt y k v) :
    MessageServedBefore tr y j 5 v ∧
      ¬ (∃ k ≤ j, 5 ≤ tr.time k ∧ tr.ProcessAt y k v ∧
        tr.time k < tr.deadline y k 5) := by
  refine ⟨messageServedBefore_of_retained y hqj ⟨hp, ?_⟩ hnr, ?_⟩
  · rw [hst, hd]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by decide : (4 : Time) < 8))
  · rintro ⟨k, hk, ht, hm, -⟩
    exact hno k hk ht hm

end Consensus.Goldilocks.SA.Test

end

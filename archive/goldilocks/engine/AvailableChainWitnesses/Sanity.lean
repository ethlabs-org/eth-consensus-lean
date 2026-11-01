module
public import AvailableChainStatements
public import Mathlib.Tactic

@[expose] public section

namespace AvailableChain.Witnesses.Sanity

open AvailableChain AvailableChain.Generic AvailableChain.Statements.Generic

def proposed (s : Slot) : Block := .node .genesis s (nodeRoot genesisRoot s 0) 0

/-- This protocol proposes blocks but never advances either output. -/
def alwaysGenesis (n : Nat) : ProtocolSpec n where
  State := Unit
  Label := Unit
  Payload := Block
  init := ()
  clock := fun st _ => st
  actTime := fun _ => 0
  duties := fun t => if t = 0 then [()] else []
  duties_spec := by
    intro ℓ t
    cases ℓ
    change (() ∈ if t = 0 then [()] else []) ↔ (0 : Int) = t
    by_cases h : t = 0
    · simp [h]
    · simp only [ite_eq_right h, List.not_mem_nil, false_iff]
      exact fun he => h he.symm
  duties_nodup := by intro t; split_ifs <;> simp
  act := fun _ _ => none
  proposalTime := fun s => s
  slotsAt := fun t => if 0 ≤ t then [t.toNat] else []
  slotsAt_spec := by
    intro s t
    change (s ∈ if 0 ≤ t then [t.toNat] else []) ↔ (s : Int) = t
    by_cases h : 0 ≤ t
    · simp only [ite_eq_left h, List.mem_singleton]
      constructor
      · intro he
        have hc : (t.toNat : Int) = t := Int.toNat_of_nonneg h
        rw [he]
        exact hc
      · intro he
        have hc : (t.toNat : Int) = t := Int.toNat_of_nonneg h
        exact_mod_cast (hc.trans he.symm).symm
    · simp only [ite_eq_right h, List.not_mem_nil, false_iff]
      intro he
      have hn : (0 : Int) ≤ s := Int.natCast_nonneg s
      exact h (he ▸ hn)
  slotsAt_nodup := by intro t; split_ifs <;> simp
  propose := fun _ s => if s = 0 then none else some (proposed s)
  gossip := fun _ _ => []
  process := fun st _ => st
  wellFormed := fun _ => true
  depsPresent := fun _ _ => true
  processed := fun _ _ => false
  excludes := fun _ _ => true
  handles := fun _ o o' => o = o'
  carries := fun _ _ => False

def interface (n : Nat) : Interface (alwaysGenesis n) where
  confirmed := fun _ => .genesis
  stable := fun _ => .genesis
  block := some
  opening := fun _ => True

theorem safe (n : Nat) (V : Type) [DecidableEq V]
    (rho : Run V (alwaysGenesis n)) (t₀ : Time) :
    SafeFrom (alwaysGenesis n) rho (interface n).confirmed t₀ := by
  constructor
  · intro u hu v hv t t' ht hth ht' ht'h
    change Block.compatible .genesis .genesis = true
    decide
  · intro v hv t t' ht htt ht'h
    exact (by decide : Block.Preceq .genesis .genesis)

theorem confirmedSafe (n : Nat) (V : Type) [DecidableEq V] [Fintype V]
    (E : Env V) (rho : Run V (alwaysGenesis n)) (t₀ : Time)
    (_ : SleepyRegime (alwaysGenesis n) E (interface n) rho t₀) :
    SafeFrom (alwaysGenesis n) rho (interface n).confirmed t₀ := safe n V rho t₀

theorem stableSafe (n : Nat) (V : Type) [DecidableEq V] [Fintype V]
    (E : Env V) (rho : Run V (alwaysGenesis n)) (t₀ : Time)
    (_ : SleepyRegime (alwaysGenesis n) E (interface n) rho t₀) :
    SafeFrom (alwaysGenesis n) rho (interface n).stable t₀ := safe n V rho t₀

theorem monotone (n : Nat) (V : Type) [DecidableEq V] [Fintype V]
    (E : Env V) (rho : Run V (alwaysGenesis n)) (t₀ : Time)
    (_ : SleepyRegime (alwaysGenesis n) E (interface n) rho t₀) :
    MonotoneFrom (alwaysGenesis n) rho (interface n).confirmed t₀ ∧
    MonotoneFrom (alwaysGenesis n) rho (interface n).stable t₀ :=
  ⟨(safe n V rho t₀).monotone, (safe n V rho t₀).monotone⟩

theorem nested (n : Nat) (V : Type) [DecidableEq V]
    (rho : Run V (alwaysGenesis n)) : OutputOrder (alwaysGenesis n) (interface n) rho := by
  constructor
  intro v hv t
  exact (by decide : Block.Preceq .genesis .genesis)

def exampleEnv : Env (Fin 1) where
  Δ := 1
  Δ_pos := by decide
  t_GST := 0
  t_GST_nonneg := by decide
  awake := fun _ _ => true

def exampleRun (D : Time) : Run (Fin 1) (alwaysGenesis 1) where
  honest := {0}
  horizon := max 1 (1 + D)
  events := (List.range ((max 1 (1 + D)).toNat + 1)).map
    (fun (k : Nat) => .tick 0 (k : Time))
  seatOf := fun _ => Equiv.refl (Fin 1)
  proposerOf := fun _ => 0

private theorem no_delivery (D : Time) (i : Nat) (v : Fin 1)
    (o : (alwaysGenesis 1).Object) (t : Time) :
    (exampleRun D).events[i]? ≠ some (.deliver v o t) := by
  intro h
  have hm : Event.deliver v o t ∈ (exampleRun D).events :=
    List.mem_iff_getElem?.2 ⟨i, h⟩
  simp [exampleRun, List.mem_map] at hm

theorem exampleExecution (D : Time) :
    ExecutionValid (alwaysGenesis 1) exampleEnv (exampleRun D) := by
  refine { horizon_nonneg := by simp [exampleRun]
           sorted := ?_
           nodup := ?_
           in_horizon := ?_
           honest_only := ?_
           tick_public := ?_
           tick_total := ?_
           wire := ?_
           deps := ?_
           fresh := ?_
           unforgeable := ?_
           carried := ?_ }
  · simp only [exampleRun, List.pairwise_map]
    apply List.Pairwise.imp _ List.pairwise_lt_range
    intro a b hab
    change toLex ((a : Time), 0) ≤ toLex ((b : Time), 0)
    apply Prod.Lex.toLex_le_toLex.mpr
    exact Or.inl (by simpa using (show (a : Time) < (b : Time) by exact_mod_cast hab))
  · simp only [exampleRun]
    apply List.Nodup.map (l := List.range ((max 1 (1 + D)).toNat + 1))
      (fun a b h => by
      cases h
      rfl)
    exact List.nodup_range
  · intro e he
    change e ∈ (List.range ((max 1 (1 + D)).toNat + 1)).map
      (fun (k : Nat) => Event.tick 0 (k : Time)) at he
    rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
    simp only [List.mem_range] at hk
    have hmax : 0 ≤ max 1 (1 + D) :=
      le_trans (by decide : (0 : Time) ≤ 1) (le_max_left _ _)
    have hcast : ((max 1 (1 + D)).toNat : Time) = max 1 (1 + D) :=
      Int.toNat_of_nonneg hmax
    have hk_le : k ≤ (max 1 (1 + D)).toNat := by omega
    have hkc : (k : Time) ≤ max 1 (1 + D) := by
      simpa only [hcast] using
        (show (k : Time) ≤ ((max 1 (1 + D)).toNat : Time) by exact_mod_cast hk_le)
    exact ⟨Int.natCast_nonneg _, hkc⟩
  · intro e he
    change e ∈ (List.range ((max 1 (1 + D)).toNat + 1)).map
      (fun (k : Nat) => Event.tick 0 (k : Time)) at he
    rcases List.mem_map.mp he with ⟨k, hk, rfl⟩
    simp [exampleRun, Event.node]
  · intro v t h
    change Event.tick v t ∈ (List.range ((max 1 (1 + D)).toNat + 1)).map
      (fun (k : Nat) => Event.tick 0 (k : Time)) at h
    rcases List.mem_map.mp h with ⟨k, hk, he⟩
    cases he
    exact ⟨k, by simp [exampleEnv]⟩
  · intro v hv t ht h0 hh
    rcases ht with ⟨k, hk⟩
    have hv' : v = 0 := by simpa [exampleRun] using hv
    subst v
    have hmax : 0 ≤ max 1 (1 + D) :=
      le_trans (by decide : (0 : Time) ≤ 1) (le_max_left _ _)
    have hcast : ((max 1 (1 + D)).toNat : Time) = max 1 (1 + D) :=
      Int.toNat_of_nonneg hmax
    have htk : t = (k : Time) := by simpa [exampleEnv] using hk
    have hk' : k < (max 1 (1 + D)).toNat + 1 := by
      change t ≤ max 1 (1 + D) at hh
      have hc : (k : Time) ≤ ((max 1 (1 + D)).toNat : Time) := by
        rw [hcast, ← htk]
        exact hh
      have hkn : k ≤ (max 1 (1 + D)).toNat := by exact_mod_cast hc
      omega
    change Event.tick 0 t ∈ (List.range ((max 1 (1 + D)).toNat + 1)).map
      (fun (j : Nat) => Event.tick 0 (j : Time))
    apply List.mem_map.mpr
    exact ⟨k, List.mem_range.mpr hk', by simp [htk]⟩
  · intro i v o t h
    exact (no_delivery D i v o t h).elim
  · intro i v o t h
    exact (no_delivery D i v o t h).elim
  · intro i v o t h
    exact (no_delivery D i v o t h).elim
  · intro v o t h
    rcases h with ⟨i, hi⟩
    exact (no_delivery D i v o t hi).elim
  · intro v o t h
    rcases h with ⟨i, hi⟩
    exact (no_delivery D i v o t hi).elim

theorem exampleSynchrony (D : Time) :
    PartialSynchrony (alwaysGenesis 1) exampleEnv (exampleRun D) := by
  constructor
  · intro v hv o t hem w hw hdeadline hex
    simp [alwaysGenesis] at hex
  · intro v hv i o t ha w hw hp hdeadline hex
    rcases ha.1 with ⟨o', hi, _⟩
    exact (no_delivery D i v o' t hi).elim

/-- Roots are computed from block content, so they are injective on every block. -/
theorem exampleRootInjective (D : Time) :
    RootInjective exampleEnv (interface 1) (exampleRun D) :=
  by
    have scope : ∀ B, BlockInRun exampleEnv (interface 1) (exampleRun D) B →
        B = .genesis ∨ ∃ s, B = proposed s := by
      intro B hB
      rcases hB with hg | ⟨v, o, t, tip, hobj, htip, hp⟩
      · exact Or.inl hg
      · have hpay : o.payload = tip := Option.some.inj htip
        rcases hobj with ⟨i, hi⟩ | ⟨i, _, ho⟩
        · exact False.elim (no_delivery D i v o t hi)
        · have hex : ∃ s, o.payload = proposed s := by
            have hv : v = 0 := Subsingleton.elim _ _
            subst v
            by_cases ht : 0 ≤ t <;> by_cases hz : t.toNat = 0
            all_goals simp [Run.emittedAt, alwaysGenesis, exampleEnv, exampleRun, ht, hz] at ho
            all_goals first
              | exact False.elim (List.not_mem_nil ho)
              | exact ⟨t.toNat, congrArg Signed.payload (List.mem_singleton.mp ho)⟩
          obtain ⟨s, hs⟩ := hex
          rw [← hpay, hs] at hp
          simp only [proposed, Block.Preceq, Block.preceq, Bool.or_eq_true,
            decide_eq_true_eq] at hp
          exact hp.elim (fun he => Or.inr ⟨s, he⟩) Or.inl
    intro B C hB hC hr
    rcases scope B hB with rfl | ⟨s, rfl⟩ <;>
      rcases scope C hC with rfl | ⟨t, rfl⟩
    · rfl
    · simp [proposed, Block.root, nodeRoot, genesisRoot] at hr
    · simp [proposed, Block.root, nodeRoot, genesisRoot] at hr
    · simp only [proposed, Block.root, nodeRoot, BlockId.mk.injEq,
        Nat.add_right_cancel_iff] at hr
      exact congrArg proposed (epair_inj (epair_inj hr).2).1

theorem exampleSleepy (D : Time) : SleepyRegime (alwaysGenesis 1) exampleEnv
    (interface 1) (exampleRun D) 0 := by
  refine { rootInjective := exampleRootInjective D
           execution := exampleExecution D
           partialSynchrony := exampleSynchrony D
           gst_zero := by decide
           start_zero := rfl
           participation := ?_ }
  intro t h0 h1
  simp [AwakeMajority, faulty, awakeAt, exampleRun, exampleEnv]

theorem confirmedIncluded_fails (D : Time) :
    ¬ IncludedFrom (alwaysGenesis 1) exampleEnv (interface 1) (exampleRun D)
        (interface 1).confirmed 0 D := by
  intro hi
  obtain ⟨B, hproposal, hin⟩ := hi 1 (by decide)
    (by simp [HonestAwakeProposer, exampleRun, exampleEnv, alwaysGenesis])
    (by change 1 + D ≤ max 1 (1 + D); exact le_max_right _ _)
  obtain ⟨_, p, hp, hemit⟩ := hproposal
  have hpB : B = proposed 1 := by
    rcases hemit with ⟨i, htick, hobj⟩
    simp [Run.emittedAt, alwaysGenesis, exampleEnv, exampleRun, interface] at hobj hp
    change ({ auth := Auth.proposer 1, payload := p } : (alwaysGenesis 1).Object) ∈
      [({ auth := Auth.proposer 1, payload := proposed 1 } : (alwaysGenesis 1).Object)] at hobj
    have heq : p = proposed 1 := congrArg Signed.payload (List.mem_singleton.mp hobj)
    exact (Option.some.inj hp).symm.trans heq
  have hg := hin 0 (by simp [exampleRun])
  rw [hpB] at hg
  exact (by decide : ¬ Block.Preceq (proposed 1) .genesis) hg

theorem confirmedIncluded_claim_fails :
    ∀ D : Time, ¬ (∀ rho t₀,
      SleepyRegime (alwaysGenesis 1) exampleEnv (interface 1) rho t₀ →
      IncludedFrom (alwaysGenesis 1) exampleEnv (interface 1) rho
        (interface 1).confirmed t₀ D) := by
  intro D h
  exact confirmedIncluded_fails D (h (exampleRun D) 0 (exampleSleepy D))

end AvailableChain.Witnesses.Sanity
end

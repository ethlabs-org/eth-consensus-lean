module
import all AvailableChainFGCompose.Tests.P0d5db
import all tests.POP6bMixedFixture
import all tests.POP6bMixedFacts

noncomputable section
namespace AvailableChain.FGCompose.Tests.POP6bMixed
open AvailableChain.SimplexFG AvailableChain.KitFG
open P0d5db

private theorem promotion_premises_sat :
    PromotionSlotProposal core env run v5T iface ∧
    PromotionProposalRead core reads env run obs iface decodeProposal v5erase FGBlock.rows
      parentFG parentHeight validFor fold ∧
    PromotionRowSigner reads env run v5T wire ∧
    PromotionSourceParent core env run obs v5T iface 12 ∧
    TRowsReceipt core reads env run v5T (fun _ => []) 1 ∧
    (∀ r h U X, BatchPrem core reads obs v5T env run iface wire v5E decodeProposal v5erase
      FGBlock.rows (fun _ => []) parentFG parentHeight validFor 1 .progress r h U X →
      (obs.height X.parent).h = h → ProgressCoveredByChild v5E obs.height X U h) ∧
    (∀ q Q K, HonestProposal env run iface q Q → v5erase K = Q → K.slot = q) ∧
    (∀ i x A K, K ∈ (core.core (run.stateBefore env i x)).fg.TF →
      FGBlock.Preceq A K → A.slot ≤ K.slot) ∧
    PromotionCapReceipt core env run obs v5T iface := by
  have parent (s : Nat) : (chain s).parent = chain (s - 1) := by cases s <;> rfl
  have eraseSlot (X : FGBlock (Fin 1)) : (v5erase X).slot = X.slot := by cases X <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs _ hh
    have h64 : s ≤ 64 := by
      change 4 * (s : Int) ≤ 256 at hh
      exact_mod_cast (show (s : Int) ≤ 64 by omega)
    exact ⟨chain s, (proposal_premises_sat ⟨s, Nat.lt_succ_of_le h64⟩ hs.1).2.1.1,
      chain_slot s⟩
  · intro s X hp _
    obtain ⟨h1, h64, he⟩ := classification_premises_sat.1 s _ hp
    have hX : X = chain s := v5erase_inj he
    subst X
    have data := proposal_premises_sat ⟨s, Nat.lt_succ_of_le h64⟩ h1
    refine ⟨⟨(chain s).rows, data.2.1, ?_⟩, s - 1, ?_, ?_, rfl, rfl, rfl,
      fun _ => rfl⟩
    · simp
    · change postClock env run (V2.D.proposerOf run iface s) (v5T.proposal s) = _
      rw [data.1]
      exact data.2.2
    · change some (chain ((v5erase (chain s)).parent.slot)) = some (chain s).parent
      rw [v9erase_parent, eraseSlot, parent, chain_slot]
  · refine ⟨fun _ _ _ a _ => ⟨a, rfl⟩, ?_⟩
    intro i j r a _
    exact congrArg some (Subsingleton.elim a.signer i)
  · intro u m J c r s X x K _ _ _ _ hafter hp hx hK
    obtain ⟨_, rfl⟩ := observed_premises_sat.1 r x K hx hK
    obtain ⟨_, _, he⟩ := classification_premises_sat.1 s _ hp
    have hX : X = chain s := v5erase_inj he
    subst X
    rw [parent]
    change r * 2 + 2 ≤ s at hafter
    exact core_premises_sat.2.2.2.2.1 (2 * r) (s - 1) (by
      simp only [Slot] at *
      omega)
  · intro j y r a ha _ x _
    obtain ⟨hr, _, rfl⟩ := classification_premises_sat.2 j y r a ha
    exact Or.inl (List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩)
  · intro q h U X hb _
    obtain ⟨s, hslot⟩ : ∃ s, X.slot = s := ⟨_, rfl⟩
    obtain ⟨rows, hcar, _⟩ := hb.carrier
    have hp := hcar.1
    rw [hslot] at hp
    obtain ⟨_, _, he⟩ := classification_premises_sat.1 s _ hp
    have hX : X = chain s := v5erase_inj he
    have hafter : q * 2 + 2 ≤ s := hb.after.trans_eq hslot
    obtain ⟨Q, _, hq, hall⟩ := hb.valid
    subst X
    refine ⟨Q, hq, ?_⟩
    intro i hi
    obtain ⟨j, r, a, t, hrq, ha, hsign, hn, _⟩ := hall i hi
    obtain ⟨_, _, rfl⟩ := classification_premises_sat.2 j _ r a ha
    refine Or.inr ⟨wireAt r, chain_premises_sat.2.2 r s (by omega), ?_⟩
    exact ⟨Option.some.inj hsign, hn⟩
  · intro q Q K hp he
    obtain ⟨_, _, hQ⟩ := classification_premises_sat.1 q Q hp
    have hk : K = chain q := v5erase_inj (he.trans hQ)
    rw [hk, chain_slot]
  · intro i x A K hK hA
    change K ∈ stored (run.stateBefore env i x) at hK
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hK)
    obtain ⟨a, ha, rfl⟩ := chain_premises_sat.1 A s hA
    simpa only [chain_slot] using ha
  · intro m s Qfg X hp _ _ _ _ hh
    obtain ⟨h1, _, he⟩ := classification_premises_sat.1 s _ hp
    have hX : X = chain s := v5erase_inj he
    subst X
    have hs63 : s ≤ 63 := by
      change 4 * (s : Int) + 1 ≤ 256 at hh
      exact_mod_cast (show (s : Int) ≤ 63 by omega)
    have hs : @LT.lt Nat _ (4 * s + 1) 257 := by
      simp only [Slot] at *
      omega
    refine ⟨7, by decide, ?_⟩
    change chain s ∈ stored (run.stateBeforeTime env (v5T.proposal s + v5T.delta) 7)
    have ht : v5T.proposal s + v5T.delta = ((4 * s + 1 : Nat) : Time) := by dsimp [v5T]
    rw [ht, (clock_premises_sat.1 ⟨4 * s + 1, hs⟩).1]
    have hn : @Eq Nat ((4 * s + 1 - 1) / 4) s := by omega
    rw [hn]
    change chain s ∈ ((List.range (min s 64 + 1)).map chain).toFinset
    rw [Nat.min_eq_left (by omega)]
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨s, List.mem_range.mpr (Nat.lt_succ_self s), rfl⟩)

#print axioms promotion_premises_sat

private theorem phase_premises_sat :
    (∀ st, (obs.controls st).contest = false ∧ (obs.controls st).Z = .genesis) ∧
    (∀ u v m J c q, PhaseInterval core env run obs u v m J c →
      u ≤ v5T.proposal q → v5T.gate q ≤ v → m = heightAt (q + 1) ∧ c = false) ∧
    AttemptProposalFloor core env run obs v5T iface 12 ∧
    (∀ u v m J c q Q, (12 : Time) ≤ u → PhaseInterval core env run obs u v m J c →
      FrontierSeedQualification v5T 1 env.t_GST u q → v5T.gate q ≤ v →
      HonestProposal env run iface q Q → ∃ i x Qfg,
      V2.D.Run.idxBefore run u ≤ i ∧ i ≤ timeIdx run v ∧ x ∈ run.honest ∧
      Qfg ∈ (core.core (run.stateBefore env i x)).fg.TF ∧ v5erase Qfg = Q) := by
  have bits (st : Nat) : (obs.controls st).contest = false ∧
      (obs.controls st).Z = .genesis := by
    have hn : ¬ ∃ W ∈ stored st, FGBlock.Preceq .genesis W ∧
        (v5H W).h = heightAt (min st 64) ∧ ¬ FGBlock.Preceq .genesis W := by
      rintro ⟨W, _, _, _, h⟩
      exact h (genesis_preceq W)
    constructor
    · change (decide (heightAt (min st 64) = 1) && decide (∃ W ∈ stored st,
        FGBlock.Preceq .genesis W ∧ (v5H W).h = heightAt (min st 64) ∧
          ¬ FGBlock.Preceq .genesis W)) = false
      rw [decide_eq_false hn, Bool.and_false]
    · change (if (obs.controls st).rootIsJ then FGBlock.genesis else .genesis) = .genesis
      split <;> rfl
  have gate (q : Nat) (hq : v5T.gate q ≤ run.horizon) :
      q ≤ 62 ∧ run.stateBeforeTime env (v5T.gate q) 7 = q + 1 := by
    simp only [Time] at *
    have hz : (q : Int) ≤ 62 := by change 4 * (q : Int) + 6 ≤ 256 at hq; omega
    have hn : q ≤ 62 := by exact_mod_cast hz
    refine ⟨hn, ?_⟩
    have ht : v5T.gate q = ((4 * q + 6 : Nat) : Time) := by dsimp [v5T]
    rw [ht, (clock_premises_sat.1 ⟨4 * q + 6, by omega⟩).1]
    change @Eq Nat ((4 * q + 6 - 1) / 4) (q + 1)
    omega
  have height (u v : Time) (m : Nat) (J : Option (FGBlock (Fin 1))) (c : Bool) (q : Nat)
      (hp : PhaseInterval core env run obs u v m J c) (hu : u ≤ v5T.proposal q)
      (hg : v5T.gate q ≤ v) : m = heightAt (q + 1) ∧ c = false := by
    simp only [Time] at *
    have hread := gate q (hg.trans hp.2.1)
    have hug : u ≤ v5T.gate q := by
      change u ≤ 4 * (q : Int) + 6
      change u ≤ 4 * (q : Int) at hu
      simp only [Time] at *
      omega
    have hf := hp.2.2.2 (V2.D.Run.idxBefore run (v5T.gate q)) 7
      (v9idxBefore_mono run hug)
      ((v9idxBefore_le_timeIdx run _).trans (frontierSearch_timeIdx_mono run hg)) (by decide)
    rw [Gen.V2.Duty.stateBefore_idxBefore env run _ execution_premises_sat.1,
      hread.2] at hf
    have hh := hf.1
    change heightAt (min (q + 1) 64) = m at hh
    rw [Nat.min_eq_left (by omega)] at hh
    exact ⟨hh.symm, hf.2.1.symm.trans (bits (q + 1)).1⟩
  refine ⟨bits, height, ?_, ?_⟩
  · intro u v m J c q Q Qfg _ hp hu hg hQ he
    obtain ⟨h1, h64, hprop⟩ := classification_premises_sat.1 q Q hQ
    have hQfg : Qfg = chain q := v5erase_inj (he.trans hprop)
    subst Qfg
    obtain ⟨hm, rfl⟩ := height u v m J c q hp hu hg
    simp only [Slot, Time] at *
    have parent (s : Nat) : (chain s).parent = chain (s - 1) := by cases s <;> rfl
    rw [parent, (chain_facts_premises_sat ⟨q - 1, by omega⟩).1]
    change m - 1 ≤ heightAt (q - 1)
    dsimp only [heightAt] at hm ⊢
    omega
  · intro u v m J c q Q _ hp seed hg hQ
    obtain ⟨_, _, hprop⟩ := classification_premises_sat.1 q Q hQ
    have hu := frontierSearch_seed_after v5T 1 v5TLaws le_rfl seed
    simp only [Slot, Time] at *
    have hug : u ≤ v5T.gate q := by
      change u ≤ 4 * (q : Int) + 6
      change u ≤ 4 * (q : Int) at hu
      simp only [Time] at *
      omega
    have hread := gate q (hg.trans hp.2.1)
    refine ⟨V2.D.Run.idxBefore run (v5T.gate q), 7, chain q,
      v9idxBefore_mono run hug,
      (v9idxBefore_le_timeIdx run _).trans (frontierSearch_timeIdx_mono run hg), by decide,
      ?_, hprop.symm⟩
    rw [Gen.V2.Duty.stateBefore_idxBefore env run _ execution_premises_sat.1, hread.2]
    change chain q ∈ stored (q + 1)
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨q, List.mem_range.mpr (by omega), rfl⟩)

#print axioms phase_premises_sat

private abbrev receipt (B : Block) (d : Time) (y : Nat) : Prop :=
  ∃ W, v5erase W = B ∧ W ∈ (core.core (run.stateBeforeTime env d y)).fg.TF

private theorem receipt_premises_sat :
    (∀ i (ev : V2.Event Nat protocol.Object) m, run.events[i]? = some ev →
      (12 : Time) ≤ ev.time → 1 ≤ m → frontierAtIdx core env run (i + 1) = m →
      ev.time + v5T.delta ≤ run.horizon → PhaseWitnessReceiptScope core env run obs
        (fun _ => true) receipt (i + 1) m (ev.time + v5T.delta)) ∧
    (∀ W d y, y ∈ run.honest → receipt (v5erase W) d y →
      W ∈ (core.core (run.stateBeforeTime env d y)).fg.TF) := by
  constructor
  · intro i ev m hi _ _ hf hhor
    let d := ev.time + v5T.delta
    have hd0 : 0 ≤ d := by
      have h := (execution_premises_sat.1.in_horizon _ (List.mem_of_getElem? hi)).1
      change 0 ≤ ev.time + 1
      simp only [Time] at *
      omega
    have hdNat : (d.toNat : Time) = d := Int.toNat_of_nonneg hd0
    have hdlim : d.toNat < 257 := by
      change ev.time + 1 ≤ 256 at hhor
      dsimp only [d, v5T]
      simp only [Time] at *
      omega
    have same (x y : Nat) (hx : x ∈ run.honest) (hy : y ∈ run.honest) :
        run.stateBeforeTime env d x = run.stateBeforeTime env d y := by
      have all (z : Nat) (hz : z ∈ run.honest) :
          run.stateBeforeTime env d z = (d.toNat - 1) / 4 := by
        rw [← hdNat]
        have hz' : z = 7 ∨ z = 9 := by simpa [run] using hz
        rcases hz' with rfl | rfl
        · exact (clock_premises_sat.1 ⟨d.toNat, hdlim⟩).1
        · exact (clock_premises_sat.1 ⟨d.toNat, hdlim⟩).2
      exact (all x hx).trans (all y hy).symm
    have future {x : Nat} {W : FGBlock (Fin 1)} (hx : x ∈ run.honest)
        (hW : W ∈ (core.core (run.stateBefore env (i + 1) x)).fg.TF)
        (y : Nat) (hy : y ∈ run.honest) :
        W ∈ (core.core (run.stateBeforeTime env d y)).fg.TF := by
      have hij : i < V2.D.Run.idxBefore run d :=
        (Gen.V2.Duty.index_lt_idxBefore_iff execution_premises_sat.1 hi d).mpr (by
          change ev.time < ev.time + 1
          simp only [Time] at *
          omega)
      have held := core_premises_sat.2.2.1 (i + 1) (V2.D.Run.idxBefore run d) hij x hW
      change W ∈ (core.core (run.stateBefore env (V2.D.Run.idxBefore run d) x)).fg.TF at held
      rw [Gen.V2.Duty.stateBefore_idxBefore env run d execution_premises_sat.1,
        same x y hx hy] at held
      exact held
    have scope {x : Nat} {W : FGBlock (Fin 1)} (hx : x ∈ run.honest)
        (hW : W ∈ (core.core (run.stateBefore env (i + 1) x)).fg.TF) :
        WitnessReceiptScope core env run (fun _ => true) receipt W d :=
      ⟨fun _ y _ hy _ _ _ _ => ⟨W, rfl, future hx hW y hy⟩⟩
    have hs : frontierAtIdx core env run (i + 1) =
        max (core.core (run.stateBefore env (i + 1) 7)).fg.h_max
          (core.core (run.stateBefore env (i + 1) 9)).fg.h_max := by
      unfold frontierAtIdx
      change ({7, 9} : Finset Nat).sup _ = _
      rw [Finset.sup_insert, Finset.sup_singleton]
    obtain ⟨x, hx, hmax⟩ : ∃ x ∈ run.honest,
        (core.core (run.stateBefore env (i + 1) x)).fg.h_max = m := by
      rw [hs] at hf
      by_cases h : (core.core (run.stateBefore env (i + 1) 7)).fg.h_max ≤
          (core.core (run.stateBefore env (i + 1) 9)).fg.h_max
      · exact ⟨9, by decide, (max_eq_right h).symm.trans hf⟩
      · exact ⟨7, by decide, (max_eq_left (Nat.le_of_not_ge h)).symm.trans hf⟩
    obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness (R := core) (E := env) (rho := run)
      (O := obs) (Ef := v5E) (cert := v5cert)
      (inv := fun _ _ => geometry_premises_sat.2.2 _) (i + 1) x
    refine ⟨⟨x, W, ⟨hx, hW⟩, hh.trans hmax, scope hx hW⟩, ?_, ?_⟩
    · rintro ⟨z, _, ht⟩
      have hm : m = 1 := by change 0 + 1 = m at ht; omega
      have hg := (geometry_premises_sat.2.2 (run.stateBefore env (i + 1) 9)).gen
      have hh : (obs.height FGBlock.genesis).h = 1 := by decide +kernel
      have hj : (obs.height FGBlock.genesis).h_j + 1 = 1 := by decide +kernel
      exact ⟨9, .genesis, ⟨by decide, hg⟩, hh.trans hm.symm,
        hj.trans hm.symm, rfl, scope (by decide) hg⟩
    · rintro ⟨z, _, _, hc⟩
      rw [(phase_premises_sat.1 _).1] at hc
      cases hc
  · intro W d y _ h
    obtain ⟨W', he, hW⟩ := h
    exact v5erase_inj he ▸ hW

#print axioms receipt_premises_sat

private theorem owner_premises_sat :
    (∀ q Q, HonestProposal env run iface q Q →
      FrontierProposalService core env run v5T q Q) ∧
    (∀ u m J c q Q Qfg r, (12 : Time) ≤ u → HonestProposal env run iface q Q →
      v5erase Qfg = Q → FrontierProposalService core env run v5T q Q →
      FrontierSeedQualification v5T 1 env.t_GST u q → u ≤ v5T.proposal q →
      q ≤ r * v5T.roundSlots → (∀ r', q ≤ r' * v5T.roundSlots → r ≤ r') →
      PhaseInterval core env run obs u (v5T.action r) m J c →
      OpeningCoveredFG core reads env run obs.height v5T wire.heightPair
        (FGHonestSeats reads run) r Q ∧
      ((obs.height Qfg).h = m - 1 → OpeningEntry core env run obs.height v5T r (m - 1) ∨
        ∃ x K, x ∈ run.honest ∧ actionSourceFG core env run v5T x r = some (some K) ∧
          (obs.height K).h = m)) ∧
    (∀ u v m J c q Q Qfg, (12 : Time) ≤ u → HonestProposal env run iface q Q →
      v5erase Qfg = Q → (obs.height Qfg).h = m →
      FrontierProposalService core env run v5T q Q →
      FrontierSeedQualification v5T 1 env.t_GST u q → u ≤ v5T.proposal q →
      PhaseInterval core env run obs u (v5T.gate q) m J c → v5T.gate q ≤ v →
      v ≤ run.horizon →
      (∀ i x, timeIdx run u ≤ i → i ≤ timeIdx run v → x ∈ run.honest →
        (core.core (run.stateBefore env i x)).fg.h_max ≤ m) →
      FrontierLocalServiceFG core reads env run obs v5T iface wire.heightPair q Q Qfg m v) := by
  have service (q : Nat) (Q : Block) (hp : HonestProposal env run iface q Q) :
      FrontierProposalService core env run v5T q Q := by
    intro hv x hx _
    obtain ⟨_, _, he⟩ := classification_premises_sat.1 q Q hp
    have hq : q < 64 := by
      change 4 * (q : Int) + 1 ≤ 256 at hv
      exact_mod_cast (show (q : Int) < 64 by omega)
    exact (observed_premises_sat.2.2 ⟨q, hq⟩ x hx).trans (congrArg some he.symm)
  refine ⟨service, ?_, ?_⟩
  · intro u m J c q Q Qfg r _ hp _ _ _ huq hqr _ phase
    obtain ⟨_, _, he⟩ := classification_premises_sat.1 q Q hp
    rw [he]
    have hqr' : q ≤ 2 * r := by
        change q ≤ r * 2 at hqr
        exact hqr.trans_eq (Nat.mul_comm r 2)
    have hr : @LT.lt Nat _ r 32 := by
      have hh := phase.2.1
      change 8 * (r : Int) + 6 ≤ 256 at hh
      simp only [Slot] at *
      omega
    have hu : u ≤ v5T.proposal (2 * r) := by
      change u ≤ 4 * (q : Int) at huq
      change u ≤ 4 * ((2 * r : Nat) : Int)
      push_cast
      simp only [Slot, Time] at *
      omega
    have hg : v5T.gate (2 * r) ≤ v5T.action r := by
      change 4 * ((2 * r : Nat) : Int) + 6 ≤ 8 * (r : Int) + 6
      push_cast
      omega
    have hm := (phase_premises_sat.2.1 u _ m J c (2 * r) phase hu hg).1
    have hh : (obs.height (chain (2 * r))).h = m := by
      rw [(chain_facts_premises_sat ⟨2 * r, by omega⟩).1]
      dsimp only [heightAt] at hm ⊢
      simp only [Height, Slot] at *
      omega
    refine ⟨entry_premises_sat.2.1 q r hqr' hr, fun _ => Or.inr
      ⟨9, chain (2 * r), by decide, (action_premises_sat ⟨r, hr⟩ 9 (by decide)).2, hh⟩⟩
  · intro u v m J c q Q Qfg _ hp he hheight _ _ huq _ _ hhor cap
    obtain ⟨h1, h64, hQ⟩ := classification_premises_sat.1 q Q hp
    have hfg : Qfg = chain q := v5erase_inj (he.trans hQ)
    subst Qfg
    subst Q
    have parent (s : Nat) : (chain s).parent = chain (s - 1) := by cases s <;> rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro x s H hx hqs htime head
      have hs : s < 64 := by
        have ht := htime.trans hhor
        change 4 * (s : Int) + 1 ≤ 256 at ht
        exact_mod_cast (show (s : Int) < 64 by omega)
      have hH : H = v5erase (chain s) := Option.some.inj
        (head.symm.trans (observed_premises_sat.2.2 ⟨s, hs⟩ x hx))
      rw [hH]
      exact v5erase_mono (core_premises_sat.2.2.2.2.1 q s (by simp only [Slot] at *; omega))
    · intro s B hqs _ hB
      obtain ⟨_, _, hB'⟩ := classification_premises_sat.1 s B hB
      rw [hB', v9erase_parent, parent]
      exact v5erase_mono (core_premises_sat.2.2.2.2.1 q (s - 1) (by simp only [Slot] at *; omega))
    · intro i x _ _ _ _
      exact v5erase_mono (core_premises_sat.2.2.2.2.1 q 64 h64)
    · intro s B _ _ hB
      exact service s B hB
    · intro r hqr hrv
      have hqr' : q ≤ 2 * r := by
        change q ≤ r * 2 at hqr
        exact hqr.trans_eq (Nat.mul_comm r 2)
      have hr : @LT.lt Nat _ r 32 := by
        have ht := hrv.trans hhor
        change 8 * (r : Int) + 6 ≤ 256 at ht
        simp only [Slot] at *
        omega
      have data := action_premises_sat ⟨r, hr⟩ 9 (by decide)
      obtain ⟨j, hj, hn⟩ := postClock_tick env run data.1
      have hua : u < v5T.action r := by
        change u ≤ 4 * (q : Int) at huq
        change u < 8 * (r : Int) + 6
        simp only [Slot, Time] at *
        omega
      have low : timeIdx run u ≤ j := by
        by_contra h
        have ht := (V2.D.Engine.index_lt_read_length_iff execution_premises_sat.1 u hj).mp
          (show j < timeIdx run u by omega)
        exact (not_le_of_gt hua) ht
      have high : j ≤ timeIdx run v :=
        ((V2.D.Engine.index_lt_read_length_iff execution_premises_sat.1 v hj).mpr hrv).le
      have bound := cap j 9 low high (by decide)
      change run.stateBefore env j 9 = 2 * r + 1 at hn
      change heightAt (min (run.stateBefore env j 9) 64) ≤ m at bound
      rw [hn, Nat.min_eq_left (by omega)] at bound
      have mono := v5cert.height.h_mono (core_premises_sat.2.2.2.2.1 q (2 * r) hqr')
      rw [hheight] at mono
      have hm : m = (obs.height (chain (2 * r))).h := by
        rw [(chain_facts_premises_sat ⟨2 * r, by omega⟩).1] at mono ⊢
        dsimp only [heightAt] at bound mono ⊢
        simp only [Height, Slot] at *
        omega
      refine ⟨entry_premises_sat.2.1 q r hqr' hr, ?_, ?_, ?_⟩
      · refine ⟨(obs.height (chain (2 * r))).T_h.root, ?_⟩
        intro x K hx hK
        obtain ⟨_, rfl⟩ := observed_premises_sat.1 r x K hx hK
        exact ⟨hm.symm, rfl⟩
      · intro x K hx hK
        obtain ⟨_, rfl⟩ := observed_premises_sat.1 r x K hx hK
        exact (v5cert.height.entry_plateau (core_premises_sat.2.2.2.2.1 q (2 * r) hqr')
          (hheight.trans hm)).symm
      · intro first
        have hu := first ((q + 1) / 2) (by
          change q ≤ ((q + 1) / 2) * 2
          simp only [Slot] at *
          omega)
        change 8 * (r : Int) + 6 - (4 * (q : Int) + 6) ≤ 4
        simp only [Slot] at *
        omega

#print axioms owner_premises_sat

private theorem cap_premises_sat : RCap core reads env run obs v5T
    (fun a => namedEntry (wire.heightPair a)) (fun _ _ => allRows) := by
  unfold RCap
  dsimp only [Height]
  intro y i x W hheld hy
  obtain ⟨hx, hW⟩ := hheld
  have hle := healing_phase_height_le (R := core) (E := env) (rho := run) (O := obs)
    (inv := fun _ _ => geometry_premises_sat.2.2 _) hW
  have hhy := hy.trans hle
  have hmin : min (run.stateBefore env i x) 64 ≤ 64 := Nat.min_le_right _ _
  change y + 2 ≤ heightAt (min (run.stateBefore env i x) 64) at hhy
  have hy15 : y ≤ 15 := by dsimp only [heightAt] at hhy; omega
  have hr : 2 * y < 32 := by omega
  have hmul : 2 * (2 * y) = 4 * y := by omega
  have hh : heightAt (4 * y) = y + 1 := by dsimp only [heightAt]; omega
  have hj : rowIndex (2 * y) < i := by
    by_contra h
    have hij : i ≤ rowIndex (2 * y) := by omega
    have mono := (core_premises_sat.2.2.2.1.mono i (rowIndex (2 * y)) x hx hij).2.2
    have hjmax := healing_phase_local_le_frontier (R := core) (E := env) (rho := run)
      (i := rowIndex (2 * y)) hx
    rw [clock_premises_sat.2.2 ⟨2 * y, hr⟩, hmul, hh] at hjmax
    exact (Nat.not_succ_le_self (y + 1)) (hhy.trans (mono.trans hjmax))
  have hn := entry_premises_sat.1 ⟨2 * y, hr⟩
  rw [hmul, (chain_facts_premises_sat ⟨4 * y, by omega⟩).1, hh] at hn
  exact ⟨rowIndex (2 * y), 9, 2 * y, wireAt (2 * y),
    (obs.height (chain (4 * y))).T_h.root, hj, observed_premises_sat.2.1 ⟨2 * y, hr⟩, hn,
    List.mem_map.mpr ⟨2 * y, List.mem_range.mpr hr, rfl⟩⟩

#print axioms cap_premises_sat

private theorem family_premises_sat :
    (FGTimingLaws v5T) ∧
    (1 ≤ 1) ∧
    (RXing core env run obs) ∧
    (V2.D.ScheduleWellFormed env run) ∧
    (FGRunOrderLaws env run core) ∧
    (∀ y ∈ run.honest, ∀ t, env.t_GST ≤ t → t ≤ run.horizon → env.awake y t = true) ∧
    (∀ iy y t, y ∈ run.honest → run.events[iy]? = some (.tick y t) → t ≤ run.horizon →
      env.t_GST ≤ slotStartZ v5T (((slotAt v5T t : Slot) : Int) - 1) → (fun _ => true)
      (protocol.clock (run.stateBefore env iy y) t) = true) ∧
    (∀ t, 12 ≤ t → env.t_GST ≤ slotStartZ v5T (((slotAt v5T t : Slot) : Int) - 1)) ∧
    (∀ i (ev : V2.Event Nat protocol.Object) m, run.events[i]? = some ev → 12 ≤ ev.time → 1 ≤ m →
      frontierAtIdx core env run (i + 1) = m → ev.time + v5T.delta ≤ run.horizon →
      PhaseWitnessReceiptScope core env run obs (fun _ => true) receipt (i + 1) m
      (ev.time + v5T.delta)) ∧
    (∀ W d y, y ∈ run.honest → receipt (core.erase W) d y → W ∈ (core.core
      (run.stateBeforeTime env d y)).fg.TF) ∧
    (v5E.weightOf (historyFaulty reads run) < v5E.q) ∧
    (env.Δ ≤ 1) ∧
    (env.Δ = v5T.delta) ∧
    (∀ t, env.t_GST ≤ t → t + 4 ≤ run.horizon → ∃ s, t < v5T.proposal s ∧ v5T.proposal s ≤ t
      + 4 ∧ Gen.V2.Duty.HonestSlot run iface s) ∧
    (env.t_GST ≤ 12) ∧
    (4 * v5T.delta ≤ 4) ∧
    (PromotionSlotProposal core env run v5T iface) ∧
    (PromotionProposalRead core reads env run obs iface decodeProposal v5erase FGBlock.rows
      parentFG parentHeight validFor fold) ∧
    (PromotionRowOrder core env run obs iface) ∧
    (PromotionRowSigner reads env run v5T wire) ∧
    (PromotionSourceParent core env run obs v5T iface 12) ∧
    (TRowsReceipt core reads env run v5T (fun _ => []) 1) ∧
    (∀ (r height : Nat) (U X : FGBlock (Fin 1)), BatchPrem core reads obs v5T env run iface
      wire v5E decodeProposal v5erase FGBlock.rows (fun _ => []) parentFG parentHeight validFor 1
      .progress r height U X → (obs.height X.parent).h = height → ProgressCoveredByChild v5E
      obs.height X U height) ∧
    (ProgressFoldAdvance v5E obs.height 4) ∧
    (∃ Q : Finset (Fin 1), (∀ i ∈ Q, safetyHolder reads run i ∈ run.honest) ∧ v5E.q ≤
      v5E.weightOf Q) ∧
    (∀ r x y K L, x ∈ run.honest → y ∈ run.honest → actionSourceFG core env run v5T x
      r = some (some K) → actionSourceFG core env run v5T y r = some (some L) → (obs.height
      K).T_h.root = (obs.height L).T_h.root → (obs.height K).T_h = (obs.height L).T_h) ∧
    (∀ r x K, x ∈ run.honest → actionSourceFG core env run v5T x r = some (some K) →
      K.slot ≤ r * v5T.roundSlots) ∧
    (∀ r x K A, x ∈ run.honest → actionSourceFG core env run v5T x r = some (some K) →
      FGBlock.Preceq A K → A.slot ≤ K.slot) ∧
    (∀ A B : FGBlock (Fin 1), Block.Preceq (core.erase A) (core.erase B) → FGBlock.Preceq A B) ∧
    (AttemptProposalFloor core env run obs v5T iface 12) ∧
    (∀ u v m J contested q Q, 12 ≤ u → PhaseInterval core env run obs u v m J contested →
      FrontierSeedQualification v5T 1 env.t_GST u q → v5T.gate q ≤ v → HonestProposal env
      run iface q Q → ∃ i x Qfg, V2.D.Run.idxBefore run u ≤ i ∧ i ≤ timeIdx run v ∧ x ∈
      run.honest ∧ Qfg ∈ (core.core (run.stateBefore env i x)).fg.TF ∧ core.erase Qfg =
      Q) ∧
    (∀ u v m J contested q Q Qfg, 12 ≤ u → HonestProposal env run iface q Q → core.erase Qfg
      = Q → (obs.height Qfg).h = m → FrontierProposalService core env run v5T q Q →
      FrontierSeedQualification v5T 1 env.t_GST u q → u ≤ v5T.proposal q → PhaseInterval core
      env run obs u (v5T.gate q) m J contested → v5T.gate q ≤ v → v ≤ run.horizon → (∀ i
      x, timeIdx run u ≤ i → i ≤ timeIdx run v → x ∈ run.honest → (core.core
      (run.stateBefore env i x)).fg.h_max ≤ m) → FrontierLocalServiceFG core reads env run
      obs v5T iface wire.heightPair q Q Qfg m v) ∧
    (∀ u m J contested q Q Qfg r, 12 ≤ u → HonestProposal env run iface q Q → core.erase Qfg
      = Q → FrontierProposalService core env run v5T q Q → FrontierSeedQualification v5T 1
      env.t_GST u q → u ≤ v5T.proposal q → q ≤ r * v5T.roundSlots → (∀ r', q ≤ r' *
      v5T.roundSlots → r ≤ r') → PhaseInterval core env run obs u (v5T.action r) m J
      contested → OpeningCoveredFG core reads env run obs.height v5T wire.heightPair
      (FGHonestSeats reads run) r Q ∧
      ((obs.height Qfg).h = m - 1 → OpeningEntry core env run obs.height v5T r (m - 1) ∨ ∃
      x K, x ∈ run.honest ∧ actionSourceFG core env run v5T x r = some (some K) ∧
      (obs.height K).h = m)) ∧
    (∀ i x A K, K ∈ (core.core (run.stateBefore env i x)).fg.TF → FGBlock.Preceq A K →
      A.slot ≤ K.slot) ∧
    (∀ q Q K, HonestProposal env run iface q Q → core.erase K = Q → K.slot = q) ∧
    (∀ i x, x ∈ run.honest → (core.core (run.stateBefore env i x)).fg.h_j ≠ 0 → ∃ j y r a
      K, j < i ∧ HonestRowAt reads env run v5T j y r a ∧ actionSourceFG core env run v5T
      y r = some (some K) ∧ (obs.height K).T_h = (core.core (run.stateBefore env i
      x)).fg.J) ∧
    (∀ q Q, HonestProposal env run iface q Q → ∃ j, run.events[j]? = some (.tick
      (V2.D.proposerOf run iface q) (v5T.proposal q)) ∧ ∀ Qfg, core.erase Qfg = Q →
      FGBlock.Preceq (obs.controls (run.stateBefore env j (V2.D.proposerOf run iface
      q))).Z Qfg.parent) ∧
    (∀ X : FGBlock (Fin 1), (core.erase X).parent = core.erase X.parent) ∧
    (PromotionCapReceipt core env run obs v5T iface) ∧
    (RCap core reads env run obs v5T (fun a => namedEntry (wire.heightPair a)) (fun _ _ =>
      allRows)) ∧
    (run.honest.Nonempty) := by
  obtain ⟨slot, read, signer, sourceParent, rowsReceipt, progress, proposalSlot,
    heldSlot, capReceipt⟩ := promotion_premises_sat
  have crossing : RXing core env run obs := by
    intro i i' x y K W _ _ _ _ _ _
    exact genesis_preceq W
  have gap : ∀ t, env.t_GST ≤ t → t + 4 ≤ run.horizon → ∃ s,
      t < v5T.proposal s ∧ v5T.proposal s ≤ t + 4 ∧ Gen.V2.Duty.HonestSlot run iface s := by
    intro t ht _
    obtain ⟨z, hz⟩ : ∃ z : Int, z = t := ⟨t, rfl⟩
    subst hz
    change (0 : Int) ≤ z at ht
    have hs : (((z / 4 + 1).toNat : Nat) : Int) = z / 4 + 1 :=
      Int.toNat_of_nonneg (by omega)
    have hpos : 0 < (z / 4 + 1).toNat := by omega
    refine ⟨(z / 4 + 1).toNat, ?_, ?_, hpos, ?_⟩
    · change z < 4 * (((z / 4 + 1).toNat : Nat) : Int)
      rw [hs]
      omega
    · change 4 * (((z / 4 + 1).toNat : Nat) : Int) ≤ z + 4
      rw [hs]
      omega
    · have hp : V2.D.proposerOf run iface (z / 4 + 1).toNat = 7 := by
        change (if 4 * (((z / 4 + 1).toNat : Nat) : Int) = 6 then 9 else 7) = 7
        rw [ite_eq_right (by omega)]
      rw [hp]
      decide
  have quorum : ∃ Q : Finset (Fin 1),
      (∀ i ∈ Q, safetyHolder reads run i ∈ run.honest) ∧ v5E.q ≤ v5E.weightOf Q := by
    refine ⟨{0}, ?_, by decide⟩
    intro i hi
    have hi' : i = 0 := by simpa using hi
    subst i
    decide
  have agreement : ∀ r x y K L, x ∈ run.honest → y ∈ run.honest →
      actionSourceFG core env run v5T x r = some (some K) →
      actionSourceFG core env run v5T y r = some (some L) →
      (obs.height K).T_h.root = (obs.height L).T_h.root →
      (obs.height K).T_h = (obs.height L).T_h := by
    intro r x y K L hx hy hK hL _
    obtain ⟨_, rfl⟩ := observed_premises_sat.1 r x K hx hK
    obtain ⟨_, rfl⟩ := observed_premises_sat.1 r y L hy hL
    rfl
  have sourceSlot : ∀ r x K, x ∈ run.honest →
      actionSourceFG core env run v5T x r = some (some K) → K.slot ≤ r * v5T.roundSlots := by
    intro r x K hx hK
    obtain ⟨_, rfl⟩ := observed_premises_sat.1 r x K hx hK
    rw [chain_slot]
    change 2 * r ≤ r * 2
    simp only [Slot] at *
    omega
  have ancestorSlot : ∀ r x K A, x ∈ run.honest →
      actionSourceFG core env run v5T x r = some (some K) →
      FGBlock.Preceq A K → A.slot ≤ K.slot := by
    intro r x K A hx hK hA
    obtain ⟨_, rfl⟩ := observed_premises_sat.1 r x K hx hK
    obtain ⟨a, ha, rfl⟩ := chain_premises_sat.1 A (2 * r) hA
    simpa only [chain_slot] using ha
  have justified : ∀ i x, x ∈ run.honest →
      (core.core (run.stateBefore env i x)).fg.h_j ≠ 0 → ∃ j y r a K,
      j < i ∧ HonestRowAt reads env run v5T j y r a ∧
      actionSourceFG core env run v5T y r = some (some K) ∧
      (obs.height K).T_h = (core.core (run.stateBefore env i x)).fg.J :=
    fun _ _ _ h => (h rfl).elim
  have frame : ∀ q Q, HonestProposal env run iface q Q → ∃ j,
      run.events[j]? = some (.tick (V2.D.proposerOf run iface q) (v5T.proposal q)) ∧
      ∀ Qfg, core.erase Qfg = Q → FGBlock.Preceq
        (obs.controls (run.stateBefore env j (V2.D.proposerOf run iface q))).Z Qfg.parent := by
    intro q Q hp
    obtain ⟨_, o, ⟨j, hj, _⟩, _⟩ := hp
    refine ⟨j, hj, ?_⟩
    intro Qfg _
    rw [(phase_premises_sat.1 _).2]
    exact genesis_preceq _
  exact ⟨v5TLaws, le_rfl, crossing, execution_premises_sat.1, core_premises_sat.2.2.2.1,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl, ladready,
    receipt_premises_sat.1, receipt_premises_sat.2, execution_premises_sat.2.2.1,
    le_rfl, rfl, gap, by decide, by decide, slot, read, chain_premises_sat.2.1,
    signer, sourceParent, rowsReceipt, progress, v9foldAdvance, quorum, agreement,
    sourceSlot, ancestorSlot, v9erase_reflect, phase_premises_sat.2.2.1,
    phase_premises_sat.2.2.2, owner_premises_sat.2.2, owner_premises_sat.2.1,
    heldSlot, proposalSlot, justified, frame, v9erase_parent, capReceipt, cap_premises_sat,
    ⟨7, by decide⟩⟩

#print axioms family_premises_sat

private theorem mixed_family :
    FrontierSearchFamilyStatement core reads env run obs v5T iface wire.heightPair
      12 1 4 4 1 16 := by
  obtain ⟨hT, hk, crossing, schedule, mono, awake, joinedTick, readyCut, hServices,
    receiptHeld, faultWeight, deltaF, hdelta, gap, hJst, hG, slotProposal, read, order,
    signer, sourceParent, rowsReceipt, progressCoverage, hfold, honestQuorum, entryAgreement,
    sourceSlot, ancestorSlot, eraseReflect, floor, gateCopy, service, common, heldSlot,
    proposalSlot, justifiedSource, parentFrame, eraseParent, capReceipt, cap, hne⟩ :=
    family_premises_sat
  exact frontierSearch_family_holder (R := core) (S := reads) (O := obs) (T := v5T)
    (E := env) (rho := run)
    (I := iface) (D := wire) (Ef := v5E) (decodeProposal := decodeProposal) (bodyErase := v5erase)
    (bodyRows := FGBlock.rows) (blockWireRows := fun _ => []) (parentFG := parentFG)
    (parentHeight := parentHeight) (validFor := validFor) (fold := fold) (Jst := 12)
    (leaseSlots := 1) (obs := geometry_premises_sat.2.1) (cert := v5cert)
    (inv := fun _ _ => geometry_premises_sat.2.2 _) (justif := v5justif)
    (keep := core_premises_sat.2.2.1) (positive := by decide) (coreLaws := core_premises_sat.1)
    (erasePreceq := fun h => v5erase_mono h) (joined := fun _ => true) (receipt := receipt)
    (chainRows := fun _ _ => allRows) (G := 4) (ΔF := 1) (deltaT := 4)
    hT hk crossing schedule mono awake joinedTick readyCut hServices receiptHeld faultWeight
    deltaF hdelta gap hJst hG slotProposal read order signer sourceParent rowsReceipt
    progressCoverage hfold honestQuorum entryAgreement sourceSlot ancestorSlot eraseReflect
    floor gateCopy service common heldSlot proposalSlot justifiedSource parentFrame eraseParent
    capReceipt cap hne 16


#print axioms mixed_family

private theorem allowance_premises_sat (u ρ : Time) (hu : 12 ≤ u) (hρ : 16 ≤ ρ) :
    FrontierRepairAllowance core env run obs v5T iface 12 1 4 ρ u := by
  let b : Nat := ((u + 2) / 4).toNat
  have hb : (b : Int) = (u + 2) / 4 := Int.toNat_of_nonneg (by
    simp only [Time] at *
    omega)
  have after : u ≤ v5T.vote b := by
    change u ≤ 4 * (b : Int) + 1
    simp only [Time] at *
    omega
  have least : ∀ i, u ≤ v5T.vote i → b ≤ i := by
    intro i hi
    change u ≤ 4 * (i : Int) + 1 at hi
    simp only [Time] at *
    omega
  have sync : env.t_GST ≤ v5T.vote (b + 1 - 1) := by
    change 0 ≤ 4 * ((b + 1 - 1 : Nat) : Int) + 1
    omega
  refine ⟨by simp only [Time] at *; omega, b + 1,
    FrontierRepairStart.one b after least (by omega) sync, ?_⟩
  intro _ v m J c _ hp
  refine ⟨fun s Q _ _ hQ => owner_premises_sat.1 s Q hQ, ?_⟩
  intro hv
  have gate : v5T.gate (b + 2) ≤ u + ρ := by
    change 4 * ((b + 2 : Nat) : Int) + 6 ≤ u + ρ
    push_cast
    simp only [Time] at *
    omega
  have bound : b + 2 ≤ 64 := by
    have hg := gate.trans (hv.trans hp.2.1)
    change 4 * ((b + 2 : Nat) : Int) + 6 ≤ 256 at hg
    have hz : ((b + 2 : Nat) : Int) ≤ 64 := by omega
    exact_mod_cast hz
  have prop := (proposal_premises_sat ⟨b + 2, Nat.lt_succ_of_le bound⟩
    (Nat.le_trans (by decide) (Nat.le_add_left 2 b))).2.1.1
  refine ⟨b + 2, v5erase (chain (b + 2)), ?_, gate, prop,
    owner_premises_sat.1 _ _ prop⟩
  change 4 * ((b + 1 : Nat) : Int) < 4 * ((b + 2 : Nat) : Int)
  push_cast
  omega

#print axioms allowance_premises_sat

private theorem search_premises_sat :
    (4 : Nat) = 2 * v5T.roundSlots ∧ LivenessBoundW v5T 1 ∧
    (12 : Time) ≤ v5T.action 1 ∧
    (∀ r, (12 : Time) ≤ v5T.action r → 1 ≤ r) ∧
    (30 : Time) = v5T.action (1 + 2) ∧ 12 + 2 * FGCompose.P v5T ≤ (30 : Time) ∧
    (2 : Nat) = honestFrontier core env run 30 ∧
    (∀ j y r a h e t, HonestRowAt reads env run v5T j y r a →
      run.events[j]? = some (.tick y t) → t ≤ (30 : Time) →
      namedEntry (wire.heightPair a) = some (h, e) → h ≤ 2) ∧
    (∀ i ev m kind, FrontierSearchStart core env run obs v5T 12 i ev m kind →
      12 + 2 * FGCompose.P v5T ≤ ev.time →
      FrontierRepairAllowance core env run obs v5T iface 12 1 4 16 (ev.time + 3 * v5T.delta)) ∧
    (30 + frontierSearchRiseBudget v5T 4 1 16 + frontierSearchRowBudget v5T 4 1 16 ≤
      run.horizon) ∧
    timeIdx run 30 = 76 ∧ frontierAtIdx core env run 76 = 2 ∧
    frontierAtIdx core env run 80 = 2 ∧ frontierAtIdx core env run 81 = 3 ∧
    run.events[80]? = some (.deliver 7 ⟨.none, .inr (chain 8)⟩ 32) ∧
    HeightRow reads env run v5T (fun a => namedEntry (wire.heightPair a)) 4 3 ∧
    (∀ r, HeightRow reads env run v5T (fun a => namedEntry (wire.heightPair a)) r 3 → 4 ≤ r) ∧
    (∀ ρ : Time, 0 ≤ ρ → 32 ≤ 30 + frontierSearchRiseBudget v5T 4 1 ρ ∧
      38 ≤ 32 + frontierSearchRowBudget v5T 4 1 ρ) := by
  have indices : timeIdx run 30 = 76 := by decide +kernel
  have points : frontierAtIdx core env run 76 = 2 ∧ frontierAtIdx core env run 80 = 2 ∧
      frontierAtIdx core env run 81 = 3 := by
    refine ⟨?_, ?_, ?_⟩
    all_goals
      unfold frontierAtIdx
      change ({7, 9} : Finset Nat).sup _ = _
      simp only [Finset.sup_insert, Finset.sup_singleton, fold_premises_sat.1]
      decide +kernel
  have cutFrontier : honestFrontier core env run 30 = 2 := by
    rw [reset_inclusive_frontier (R := core) (E := env) (rho := run)
      execution_premises_sat.1 30, indices, points.1]
  have first : resetFirstRound v5T v5TLaws 12 = 1 :=
    ladfirst (reset_rG_after v5T v5TLaws 12) (reset_rG_first v5T v5TLaws 12)
  have cut : resetCutTime v5T v5TLaws 12 = 30 := by
    rw [reset_cut, first]
    rfl
  have cutM : resetCutFrontier core env run v5T v5TLaws 12 = 2 := by
    rw [reset_frontier, cut, cutFrontier]
  have rowCap := healing_reset_rowCap (T := v5T) (L := v5TLaws) (Jst := 12)
    (R := core) (S := reads) (E := env) (rho := run) (O := obs) (pair := wire.heightPair)
    (CL := core_premises_sat.1) (K := core_premises_sat.2.1)
    (storeInv := fun _ _ => geometry_premises_sat.2.2 _)
    (emittedName := entry_premises_sat.2.2) execution_premises_sat.1
  rw [cut, cutM] at rowCap
  have row4 : HeightRow reads env run v5T (fun a => namedEntry (wire.heightPair a)) 4 3 := by
    refine ⟨rowIndex 4, 9, wireAt 4, (obs.height (chain 8)).T_h.root, ?_, ?_⟩
    · exact observed_premises_sat.2.1 (⟨4, by decide⟩ : Fin 32)
    · have hn := entry_premises_sat.1 (⟨4, by decide⟩ : Fin 32)
      change namedEntry (wire.heightPair (wireAt 4)) =
        some ((obs.height (chain 8)).h, (obs.height (chain 8)).T_h.root) at hn
      rw [(chain_facts_premises_sat (⟨8, by decide⟩ : Fin 65)).1] at hn
      exact hn
  have lower (r : Nat)
      (hr : HeightRow reads env run v5T (fun a => namedEntry (wire.heightPair a)) r 3) :
      4 ≤ r := by
    obtain ⟨j, x, a, e, ha, he⟩ := hr
    obtain ⟨hr, _, rfl⟩ := classification_premises_sat.2 j x r a ha
    have hh := congrArg Prod.fst (Option.some.inj
      (he.symm.trans (entry_premises_sat.1 ⟨r, hr⟩)))
    rw [(chain_facts_premises_sat ⟨2 * r, by omega⟩).1] at hh
    dsimp only [heightAt] at hh
    simp only [Height] at *
    omega
  refine ⟨rfl, ⟨by decide⟩, by decide, ?_, rfl, by decide, cutFrontier.symm, rowCap,
    ?_, by decide +kernel, indices, points.1, points.2.1, points.2.2, by decide +kernel,
    row4, lower, ?_⟩
  · intro r hr
    change 12 ≤ 8 * (r : Int) + 6 at hr
    simp only [Time] at *
    omega
  · intro i ev m kind _ hd
    apply allowance_premises_sat _ 16 ?_ le_rfl
    change 12 + 16 ≤ ev.time at hd
    change 12 ≤ ev.time + 3
    simp only [Time] at *
    omega
  · intro ρ hρ
    have hm : (16 : Time) ≤ max (ρ + 15) 16 := le_max_right _ _
    constructor
    · norm_num [frontierSearchRiseBudget, E_gF, E_jF, B_cF, FGCompose.P, Γ, epsF,
        betaF, kappaF, v5T]
      simp only [Time] at *
      omega
    · norm_num [frontierSearchRowBudget, E_gF, E_jF, D_cF, FGCompose.P, Γ, epsF,
        betaF, kappaF, v5T]
      simp only [Time] at *
      omega

#print axioms search_premises_sat

-- The production family selects the witnesses; inspection retains every original budget.
private theorem mixed_full :
    FrontierSearchStatement core reads env run obs v5T iface wire.heightPair 12 1 4 4 1 := by
  obtain ⟨hd, hb, hafter, hfirst, hcut, hdelay, hM, rowCap, family, hhor, idx,
    atCut, beforeRise, afterRise, event, row4, lower, bounds⟩ := search_premises_sat
  have mono (a b : Nat) (hab : a ≤ b) :
      frontierAtIdx core env run a ≤ frontierAtIdx core env run b := by
    unfold frontierAtIdx
    apply Finset.sup_le
    intro x hx
    exact (core_premises_sat.2.2.2.1.mono a b x hx hab).2.2.trans
      (Finset.le_sup (f := fun y => (core.core (run.stateBefore env b y)).fg.h_max) hx)
  apply (FrontierSearchStatement_def core reads env run obs v5T iface wire.heightPair
    12 1 4 4 1).mpr
  intro hδ hbound rG u₀ M hgst first hu₀ _ hfront _
  have hrG := ladfirst hgst first
  rcases hrG with rfl
  have hu : u₀ = 30 := hu₀
  rcases hu with rfl
  have hm : M = 2 := hfront.trans hM.symm
  rcases hm with rfl
  obtain ⟨_, rows⟩ := (FrontierSearchFamilyStatement_def core reads env run obs v5T iface
    wire.heightPair 12 1 4 4 1 16).mp mixed_family hδ hbound (by decide) family
      1 30 2 hafter hfirst hcut hdelay hM rowCap
  obtain ⟨rStar, hr, hmin, j, ev, hj, hev, _, hh, cap, _⟩ := rows hhor
  have jlow : 80 ≤ j := by
    by_contra hn
    have hi : j + 1 ≤ 80 := by omega
    exact (Nat.not_lt_of_ge ((mono _ _ hi).trans_eq beforeRise)) hh
  have jhigh : j ≤ 80 := by
    by_contra hn
    have hc := cap 81 (by rw [idx]; decide) (show 81 ≤ j by omega)
    rw [afterRise] at hc
    omega
  have hj80 : j = 80 := Nat.le_antisymm jhigh jlow
  rcases hj80 with rfl
  have he : ev = .deliver 7 ⟨.none, .inr (chain 8)⟩ 32 :=
    Option.some.inj (hev.symm.trans event)
  rcases he with rfl
  have hr4 : rStar = 4 := Nat.le_antisymm (hmin 4 row4) (lower rStar hr)
  rcases hr4 with rfl
  refine ⟨?_, ?_⟩
  · intro ρ allow _
    exact ⟨80, _, hj, hev, (bounds ρ allow.1).1, hh, cap⟩
  · intro _
    refine ⟨4, hr, hmin, ?_⟩
    intro ρ allow _
    exact ⟨80, _, hj, hev, (bounds ρ allow.1).1, hh, cap, (bounds ρ allow.1).2⟩

#print axioms mixed_full

private theorem reset_premises_sat :
    FGHeightLaws v5E obs.height ∧ FGCoreLaws core ∧ FGTreeKeepLaws core ∧
    (∀ i x, FGStoreInvariant obs.height obs.finality
      (core.core (run.stateBefore env i x)).fg) ∧
    (∀ {j : Nat} {x : Nat} {r : Nat} {a : Row (Fin 1)} {e : Height × BlockId},
      HonestRowAt reads env run v5T j x r a → namedEntry (Row.height_pair a) = some e →
      ∃ C, actionSourceFG core env run v5T x r = some (some C) ∧
        e = ((obs.height C).h, (obs.height C).T_h.root)) ∧
    V2.D.ScheduleWellFormed env run ∧ (0 : Time) ≤ 12 ∧ env.t_GST ≤ (12 : Time) ∧
    (4 : Nat) = 2 * v5T.roundSlots ∧ LivenessBoundW v5T 1 ∧ (0 : Time) ≤ 16 ∧
    (∀ i ev m kind, FrontierSearchStart core env run obs v5T 12 i ev m kind →
      (12 : Time) + 2 * FGCompose.P v5T ≤ ev.time →
      FrontierRepairAllowance core env run obs v5T iface 12 1 4 16
        (ev.time + 3 * v5T.delta)) ∧
    FrontierSearchFamilyStatement core reads env run obs v5T iface Row.height_pair 12 1 4
      4 1 16 ∧
    (209 : Time) = 3 * FGCompose.P v5T +
      (E_gF v5T 1 4 16 + E_jF v5T 1 4 16 + B_cF v5T 1 4 16) +
      (E_gF v5T 1 4 16 + E_jF v5T 1 4 16 + D_cF v5T 16) ∧
    (12 : Time) + 209 ≤ run.horizon ∧ run.honest.Nonempty := by
  obtain ⟨hd, hb, _, _, _, _, _, _, family, _, _⟩ := search_premises_sat
  have search : FrontierSearchFamilyStatement core reads env run obs v5T iface
      Row.height_pair 12 1 4 4 1 16 := by
    apply (FrontierSearchFamilyStatement_def core reads env run obs v5T iface
      Row.height_pair 12 1 4 4 1 16).mpr
    intro hδ hbound _ _ rG u M ha first hcut hdelay hm cap
    have hu : 12 ≤ u := by
      change 12 + 16 ≤ u at hdelay
      simp only [Time] at *
      omega
    have allow := allowance_premises_sat u 16 hu le_rfl
    obtain ⟨rise, rows⟩ := (FrontierSearchStatement_def core reads env run obs v5T iface
      Row.height_pair 12 1 4 4 1).mp mixed_full hδ hbound rG u M ha first hcut hdelay hm cap
    refine ⟨rise 16 allow, ?_⟩
    intro hor
    obtain ⟨r, hr, hfirst, hall⟩ := rows ⟨16, allow, hor⟩
    exact ⟨r, hr, hfirst, hall 16 allow hor⟩
  exact ⟨v5cert.height, core_premises_sat.1, core_premises_sat.2.1,
    fun _ _ => geometry_premises_sat.2.2 _, entry_premises_sat.2.2,
    execution_premises_sat.1, by decide, by decide, hd, hb, by decide, family, search,
    by decide +kernel, by decide, ⟨7, by decide⟩⟩

#print axioms reset_premises_sat


private theorem mixed_reset : ∃ w : FGResetHistory,
    H0Reset core reads env run obs v5T (fun a => namedEntry (wire.heightPair a)) 12 w ∧
    w.rG = 1 ∧ w.u0 = 30 ∧ w.M = 2 ∧ w.rStar = 4 ∧ w.sStar = 8 ∧
    w.source = v5erase (chain 8) ∧ v5T.action w.rStar = 38 ∧
    v5T.action w.rStar < 12 + 209 := by
  obtain ⟨hl, cl, keep, inv, name, schedule, start, gst, hδ, hb, hρ, family, search,
    budget, hor, _⟩ := reset_premises_sat
  obtain ⟨w, hw, hG, hu, hm, deadline⟩ := healing_resetWitness (T := v5T) (L := v5TLaws)
    (Jst := 12) (R := core) (S := reads) (E := env) (rho := run) (O := obs) (I := iface)
    (pair := Row.height_pair) (Ef := v5E) (HL := hl) (CL := cl) (K := keep) (storeInv := inv)
    (emittedName := name) (leaseSlots := 1) (deltaT := 4) (G := 4) (ΔF := 1) (ρbar := 16)
    (budget := 209) schedule start gst hδ hb hρ family search budget hor
  obtain ⟨_, _, _, _, _, _, hfront, _, _, _, _, _, _, _, _, row4, lower, _⟩ :=
    search_premises_sat
  have first : resetFirstRound v5T v5TLaws 12 = 1 :=
    ladfirst (reset_rG_after v5T v5TLaws 12) (reset_rG_first v5T v5TLaws 12)
  have cut : resetCutTime v5T v5TLaws 12 = 30 := by rw [reset_cut, first]; rfl
  have frontier : resetCutFrontier core env run v5T v5TLaws 12 = 2 := by
    rw [reset_frontier, cut]
    exact hfront.symm
  rw [first] at hG
  rw [cut] at hu
  rw [frontier] at hm
  have hr := hw.reset_row
  rw [hm] at hr
  have hfirst := hw.reset_first
  rw [hm] at hfirst
  have hr4 : w.rStar = 4 := Nat.le_antisymm (hfirst 4 row4) (lower w.rStar hr)
  obtain ⟨j, y, a, C, ha, _, hC, hErase, _⟩ := hw.fresh
  rw [hr4] at hC
  have hC8 : C = chain 8 := (observed_premises_sat.1 4 y C ha.1 hC).2
  refine ⟨w, hw, hG, hu, hm, hr4, ?_, ?_, ?_, deadline⟩
  · rw [hw.label, hr4]
    rfl
  · exact hErase.symm.trans (congrArg v5erase hC8)
  · rw [hr4]
    rfl

#print axioms mixed_reset

private theorem active_premises_sat :
    run.honest = {7, 9} ∧ FGHonestSeats reads run = {0} ∧
    safetyHolder reads run 0 = 9 ∧ V2.D.proposerOf run iface 6 = 7 ∧
    HonestProposal env run iface 6 (v5erase (chain 6)) ∧
    FrontierSeedQualification v5T 1 env.t_GST 17 6 ∧
    PhaseInterval core env run obs 17 30 2 none false ∧
    FrontierProposalService core env run v5T 6 (v5erase (chain 6)) ∧
    (∀ i x, timeIdx run 17 ≤ i → i ≤ timeIdx run 30 → x ∈ run.honest →
      (core.core (run.stateBefore env i x)).fg.h_max ≤ 2) ∧
    HonestRowAt reads env run v5T 75 9 3 (wireAt 3) ∧
    protocol.objSelfVisible (reads.encode (wireAt 3)) = true ∧
    reads.decodeObject (reads.encode (wireAt 3)) = some (wireAt 3) ∧
    (∀ x ∈ run.honest, actionSourceFG core env run v5T x 3 = some (some (chain 6))) ∧
    OpeningCoveredFG core reads env run obs.height v5T wire.heightPair
      (FGHonestSeats reads run) 3 (v5erase (chain 6)) ∧
    FrontierLocalServiceFG core reads env run obs v5T iface wire.heightPair
      6 (v5erase (chain 6)) (chain 6) 2 30 := by
  have table : ∀ i : Fin 77, 42 ≤ i.val →
      heightAt (min (shapeState (eventShape.take i) 7) 64) = 2 ∧
      heightAt (min (shapeState (eventShape.take i) 9) 64) = 2 := by decide +kernel
  have low : V2.D.Run.idxBefore run 17 = 42 := by decide +kernel
  have high : timeIdx run 30 = 76 := by decide +kernel
  have frame (st : Nat) (hh : heightAt (min st 64) = 2) :
      (obs.controls st).H = 2 ∧ (obs.controls st).contest = false ∧
      (obs.controls st).rootIsJ = false := by
    refine ⟨hh, (phase_premises_sat.1 st).1, ?_⟩
    change (decide (heightAt (min st 64) = 1) && !(obs.controls st).contest) = false
    rw [hh]
    rfl
  have phase : PhaseInterval core env run obs 17 30 2 none false := by
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro i x hi hv hx
    rw [low] at hi
    rw [high] at hv
    have ht := table ⟨i, by omega⟩ hi
    simp only [fold_premises_sat.1]
    have hx' : x = 7 ∨ x = 9 := by simpa [run] using hx
    rcases hx' with rfl | rfl
    · exact frame _ ht.1
    · exact frame _ ht.2
  have cap : ∀ i x, timeIdx run 17 ≤ i → i ≤ timeIdx run 30 → x ∈ run.honest →
      (core.core (run.stateBefore env i x)).fg.h_max ≤ 2 := by
    intro i x hi hv hx
    exact (phase.2.2.2 i x ((v9idxBefore_le_timeIdx run 17).trans hi) hv hx).1.le
  have seed : FrontierSeedQualification v5T 1 env.t_GST 17 6 := by
    refine Or.inr ⟨4, by decide, ?_, by decide, by decide, by decide⟩
    intro i hi
    change 17 ≤ 4 * (i : Int) + 1 at hi
    simp only [Slot] at *
    omega
  have prop := (proposal_premises_sat ⟨6, by decide⟩ (by decide)).2.1.1
  have svc := owner_premises_sat.1 6 _ prop
  have common := owner_premises_sat.2.1 17 2 none false 6 (v5erase (chain 6)) (chain 6) 3
    (by decide) prop rfl svc seed (by decide) (by decide) (fun r hr => by
      change 6 ≤ r * 2 at hr
      simp only [Slot] at *
      omega) phase
  have localService := owner_premises_sat.2.2 17 30 2 none false 6 (v5erase (chain 6))
    (chain 6) (by decide) prop rfl (by decide +kernel) svc seed (by decide) phase
      le_rfl (by decide) cap
  have row := observed_premises_sat.2.1 (⟨3, by decide⟩ : Fin 32)
  change HonestRowAt reads env run v5T (rowIndex 3) 9 3 (wireAt 3) at row
  have index : rowIndex 3 = 75 := by decide +kernel
  rw [index] at row
  exact ⟨rfl, execution_premises_sat.2.1, rfl, by decide, prop, seed, phase, svc, cap,
    row, rfl, rfl,
    fun x hx => (action_premises_sat ⟨3, by decide⟩ x hx).2, common.1, localService⟩

#print axioms active_premises_sat

end AvailableChain.FGCompose.Tests.POP6bMixed
end

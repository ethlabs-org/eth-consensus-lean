module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingGate
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingInput -- shake: keep

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- The pending input is local to the consuming receiver and its clocked store. -/
structure ArmingGateInput (p : Params) (P : State p.n) (fast : Bool) (j : Slot)
    (B D : Block) : Prop where
  fresh : GridCO.savedGenuine P.base j = none
  raw : ∃ Cj, SA.Root.confirmationFrom p.toParams (eraseFG P.fg.F) (actView P) j =
    some Cj ∧ Block.Preceq D Cj
  leases : ∀ row ∈ (actView P).obligations, Block.Preceq row.1 D
  active : B ∈ (actView P).blocks
  compatible : Block.Compatible (eraseFG P.fg.F) B
  fast_support : fast = true → SA.releaseThreshold p.toParams ≤
    SA.Root.prefixSupport p.toParams (actView P) j B
  slow_rows : fast = false → p.k ≤ j + 1 ∧ ∀ a < p.k - 1, ∃ Ca,
    GridCO.savedGenuine P.base (j - (a + 1)) = some (some Ca) ∧ Block.Preceq B Ca

/-- A joined-voter batch is retained only in the receiving node's current epoch. -/
theorem arming_joined_batch_at {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {l : Slot} {D : Block} {y : V}
    (hbatch : ∀ q : Fin p.n, rho.seatOf (.base (.head (l + 1))) q ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head (l + 1))) q) (l + 1)
        (SA.voteTime p.toParams (l + 1)) →
      ∃ K k, rho.events[k]? = some (.tick y (SA.earlyTime p.toParams (l + 1))) ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 1))) q)
          (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩) (SA.voteTime p.toParams (l + 1)) ∧
        Block.Preceq D K ∧ K.slot ≤ l + 1 ∧
        baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho k y).base.votes ∧
        K ∈ (storeAt p c E rho k y).base.blocks ∧
        GridCO.stampVote (storeAt p c E rho k y).base
          (baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n)) <
            SA.earlyTime p.toParams (l + 1) ∧
        GridCO.stampBlock (storeAt p c E rho k y).base K <
          SA.earlyTime p.toParams (l + 1))
    {i : Nat} {t : Time} (hi : rho.events[i]? = some (.tick y t))
    (ht : SA.earlyTime p.toParams (l + 1) < t)
    (hEpoch : ∀ k, rho.events[k]? = some (.tick y (SA.earlyTime p.toParams (l + 1))) →
      V2.D.restartFree rho y k i)
    (q : Fin p.n) (hq : rho.seatOf (.base (.head (l + 1))) q ∈ rho.honest)
    (hJ : joinedAt p E rho (rho.seatOf (.base (.head (l + 1))) q) (l + 1)
      (SA.voteTime p.toParams (l + 1))) :
    ∃ K k, rho.events[k]? = some (.tick y (SA.earlyTime p.toParams (l + 1))) ∧ k < i ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 1))) q)
        (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩) (SA.voteTime p.toParams (l + 1)) ∧
      Block.Preceq D K ∧ K.slot ≤ l + 1 ∧
      baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n) ∈
        (storeAt p c E rho k y).base.votes ∧
      baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i y).base.votes ∧
      K ∈ (storeAt p c E rho i y).base.blocks ∧
      GridCO.stampVote (storeAt p c E rho i y).base
        (baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n)) <
          SA.earlyTime p.toParams (l + 1) ∧
      GridCO.stampBlock (storeAt p c E rho i y).base K < SA.earlyTime p.toParams (l + 1) := by
  obtain ⟨K, k, hk, hem, hDK, hslot, hv, hKb, hvs, hbs⟩ := hbatch q hq hJ
  have hki := V2.D.Engine.eventIndex_lt_of_time_lt hs hk hi ht
  obtain ⟨hv', hK', hvs', hbs'⟩ := inclusion_stamps_kept_on E rho hki.le y
    (hEpoch k hk) _ K hv hKb
  exact ⟨K, k, hk, hki, hem, hDK, hslot, hv, hv', hK', hvs' ▸ hvs, hbs' ▸ hbs⟩

/-- The joined denominator and two receiver epochs construct the pending input. -/
theorem arming_sleep_pending_input [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)}
    (hE : V2.D.ExecutionValid E rho) (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    {l : Slot} {B D : Block} (hBD : Block.Preceq B D)
    (hpartv : Gen.Pure.Batch
      (joinedHonest p E rho (SA.voteTime p.toParams (l + 1))).card
      (Gen.V2.Duty.faulty rho).card)
    {i : Nat} {y : V} (hi : IsGateTick p c rho i y (l + 1))
    (hF : ∀ k, k ≤ rho.idxBefore (SA.gateTime p.toParams (l + 1)) →
      Block.Preceq (F_at p c E rho k y) D)
    (hObl : ∀ row ∈ (storeAt p c E rho
      (rho.idxBefore (SA.gateTime p.toParams (l + 1))) y).base.obligations,
      Block.Preceq row.1 D)
    (hbatchF : ∀ q : Fin p.n, rho.seatOf (.base (.head (l + 1))) q ∈ rho.honest →
      joinedAt p E rho (rho.seatOf (.base (.head (l + 1))) q) (l + 1)
        (SA.voteTime p.toParams (l + 1)) →
      ∃ K k, rho.events[k]? = some (.tick y (SA.earlyTime p.toParams (l + 1))) ∧
        V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 1))) q)
          (ofHead p ⟨.seat (.head (l + 1)) q, K.root⟩) (SA.voteTime p.toParams (l + 1)) ∧
        Block.Preceq D K ∧ K.slot ≤ l + 1 ∧
        baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho k y).base.votes ∧
        K ∈ (storeAt p c E rho k y).base.blocks ∧
        GridCO.stampVote (storeAt p c E rho k y).base
          (baseVote (⟨.seat (.head (l + 1)) q, K.root⟩ : HeadWire p.n)) <
            SA.earlyTime p.toParams (l + 1) ∧
        GridCO.stampBlock (storeAt p c E rho k y).base K <
          SA.earlyTime p.toParams (l + 1))
    (hEarlyEpoch : ∀ k, rho.events[k]? =
      some (.tick y (SA.earlyTime p.toParams (l + 1))) → V2.D.restartFree rho y k i)
    (hTickEpoch : V2.D.restartFree rho y
      (rho.idxBefore (SA.gateTime p.toParams (l + 1))) i)
    (fast : Bool)
    (hfast : fast = true → ∀ H : Finset (Fin p.n),
      (∀ q, q ∈ H ↔ rho.seatOf (.base (.head (l + 1))) q ∈ rho.honest ∧
        joinedAt p E rho (rho.seatOf (.base (.head (l + 1))) q) (l + 1)
          (SA.voteTime p.toParams (l + 1))) → SA.releaseThreshold p.toParams ≤ H.card)
    (hslow : fast = false → p.k ≤ l + 2 ∧ ∀ a < p.k - 1, ∃ Ca,
      GridCO.savedGenuine (FGSA.clockPre p (storeAt p c E rho i y)
        (SA.gateTime p.toParams (l + 1))).base (l + 1 - (a + 1)) = some (some Ca) ∧
      Block.Preceq B Ca) :
    ArmingGateInput p (clockPre p (storeAt p c E rho i y)
      (SA.gateTime p.toParams (l + 1))) fast (l + 1) B D := by
  let P := FGSA.clockPre p (storeAt p c E rho i y) (SA.gateTime p.toParams (l + 1))
  have hs := hE.toScheduleWellFormed
  have hiE : rho.events[i]? = some (.tick y (SA.gateTime p.toParams (l + 1))) := hi
  have hst := arming_tick_store_on hs hiE hTickEpoch
  have hFD := hF _ le_rfl
  have hFi : Block.Preceq (F_at p c E rho i y) D := by
    change Block.Preceq (eraseFG (storeAt p c E rho i y).fg.F) D
    rw [hst]
    exact hFD
  have hPF : eraseFG P.fg.F = F_at p c E rho i y := by
    change eraseFG (clockPre p (storeAt p c E rho i y) _).fg.F =
      eraseFG (storeAt p c E rho i y).fg.F
    rw [clockPre_fg]
  have hinvP : CStoreInv p P :=
    cstoreInv_clockPre p _ (storeBundle_stateBefore E rho i y).cstore _
  obtain ⟨H, hH, hbatch⟩ := inclusion_joined_head_seats E rho hC (l + 1) hpartv
  have hgt : SA.earlyTime p.toParams (l + 1) < SA.gateTime p.toParams (l + 1) :=
    (arming_early_next p l).trans_lt ((arming_gate_lt_iff p l (l + 1)).mpr (Nat.lt_succ_self l))
  have hheads : ∀ k ∈ H, ∃ K t,
      rho.seatOf (.base (.head (l + 1))) k ∈ rho.honest ∧
      V2.D.Run.emits E rho (rho.seatOf (.base (.head (l + 1))) k)
        (ofHead p ⟨.seat (.head (l + 1)) k, K.root⟩) t ∧
      baseVote (⟨.seat (.head (l + 1)) k, K.root⟩ : HeadWire p.n) ∈
        (storeAt p c E rho i y).base.votes ∧
      K ∈ (actView P).blocks ∧ K.slot ≤ l + 1 ∧
      GridCO.stampVote (actView P) (baseVote (⟨.seat (.head (l + 1)) k, K.root⟩ : HeadWire p.n)) <
        GridCO.earlyTime p.toParams.engine (l + 1) ∧
      GridCO.stampBlock (actView P) K < GridCO.earlyTime p.toParams.engine (l + 1) ∧
      Block.Preceq (eraseFG P.fg.F) K ∧ Block.Preceq D K := by
    intro w hw
    obtain ⟨hyw, haw⟩ := (hH w).mp hw
    obtain ⟨K, _, _, _, hem, hDK, hslot, _, hv, hKb, hvs, hbs⟩ :=
      arming_joined_batch_at hs hbatchF hiE hgt hEarlyEpoch w hyw haw
    have hFK : Block.Preceq (eraseFG P.fg.F) K := hPF ▸ block_preceq_trans hFi hDK
    refine ⟨K, _, hyw, hem, hv, ?_, hslot, ?_, ?_, hFK, hDK⟩
    · apply (actView_blocks P K).mpr
      refine ⟨?_, block_compatible_of_common (block_preceq_refl K) hFK⟩
      change K ∈ (clockPre p (storeAt p c E rho i y) _).base.blocks
      rw [(clockPre_fields p _ _).2.1]
      exact hKb
    · change GridCO.stampVote (clockPre p (storeAt p c E rho i y) _).base _ < _
      have hkey : baseVote (⟨.seat (.head (l + 1)) w, K.root⟩ : HeadWire p.n) ∈
          (storeAt p c E rho i y).base.voteStamp.map Prod.fst := by
        change _ ∈ (V2.D.Run.stateBefore E rho i y).st.base.voteStamp.map Prod.fst
        rw [fgsa_vote_stamp_keys E rho i y]
        exact hv
      rw [inclusion_stampVote_of_prefix (by rw [(clockPre_stamps p _ _).2]) hkey]
      exact hvs
    · change GridCO.stampBlock (clockPre p (storeAt p c E rho i y) _).base K < _
      have hkey : K ∈ (storeAt p c E rho i y).base.blockStamp.map Prod.fst := by
        change K ∈ (V2.D.Run.stateBefore E rho i y).st.base.blockStamp.map Prod.fst
        rw [(storeBundle_stateBefore E rho i y).«meta».stampKeys]
        exact hKb
      rw [inclusion_stampBlock_of_prefix (by rw [(clockPre_stamps p _ _).1]) hkey]
      exact hbs
  have hcover := fgsa_gate_batch_premises_joined E rho hE hC i y (l + 1) D H hbatch
    (fun q hq haw => (hH q).mpr ⟨hq, haw⟩) hheads
  obtain ⟨Cj, hCj, hDCj⟩ := fgsa_confirmationFrom_covers_majority p (actView P)
    (eraseFG P.fg.F) D (l + 1) D.root (block_compatible_of_common (hPF ▸ hFi) (block_preceq_refl D))
    hcover.1 hcover.2.1 hcover.2.2
  obtain ⟨w0, hw0⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hbatch.lt)
  obtain ⟨K0, _, _, _, _, hK0, _, _, _, _, hDK0⟩ := hheads w0 hw0
  refine ⟨?_, ⟨Cj, hCj, hDCj⟩, ?_,
    actView_ancestor_closed p P hinvP hK0 (block_preceq_trans hBD hDK0),
    block_compatible_of_common (hPF ▸ hFi) hBD, ?_, fun hf => hslow hf⟩
  · rw [savedGenuine_congr (clockPre_genuine p _ _)]
    exact fgsa_gate_fresh E rho hs hiE
  · intro row hrow
    have hm : row ∈ (storeAt p c E rho i y).base.obligations :=
      (clockPre_obligations_sublist p _ _).subset hrow
    rw [hst] at hm
    exact hObl row hm
  · intro hf
    have hsupp : ∀ k ∈ H, Gen.AC.Root.poolSupports (actView P).blocks
        (GridCO.cleanSupport p.toParams.engine (actView P) (l + 1)) k B = true := by
      intro k hk
      obtain ⟨K, t, hh, he, hv, hK, hslot, hvs, hbs, _, hDK⟩ := hheads k hk
      exact fgsa_active_support_of_receipt E rho hE i y (l + 1) k K B t hh he hv hK hslot hvs
        hbs (block_preceq_trans hBD hDK)
    have hc := Gen.AC.Root.batch_counts (actView P).blocks
      (GridCO.lateVotes p.toParams.engine (actView P) (l + 1))
      (GridCO.cleanSupport p.toParams.engine (actView P) (l + 1))
      (GridCO.cleanSupport p.toParams.engine (actView P) (l + 1))
      H H.card (Gen.V2.Duty.faulty rho).card B
      (fun _ ho => fgsa_early_subset_late p _ _ (List.mem_filter.mp ho).1)
      (fun _ ho => ho) rfl (fun q _ => fgsa_cleanSupport_no_equivocation p _ _ q)
      hsupp (fgsa_late_rest_bound_joined E rho hC hE i y (l + 1) H
        (fun q hq haw => (hH q).mpr ⟨hq, haw⟩)) hbatch
    change _ ≤ GridCO.goldfishScoreOn (GridCO.resolutionTree (actView P)) (actView P).blocks
      (GridCO.cleanSupport p.toParams.engine (actView P) (l + 1))
      (GridCO.cleanSupport p.toParams.engine (actView P) (l + 1)) B
    rw [actView_score p P hinvP
      (by rw [clockPre_headDomain]; exact base_headDomain_none p (reachable_stateBefore E rho i y))]
    exact (hfast hf H hH).trans (hc.2.2.1 B (block_preceq_refl B)).1

/-- The Clean history supplies a comparison maximum without an all-honest gate premise. -/
theorem arming_comparison_prefix_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {b₀ : Time}
    (hh : CleanHist p c E rho (timeIdx rho b₀))
    {i : Nat} (hi : i ≤ timeIdx rho b₀) (r : Slot) :
    ∃ D : Block, BelowLabel p c E rho i r D ∧
      ∀ X, BelowLabel p c E rho i r X → Block.Preceq X D := by
  classical
  let candidates : Finset Block := (Finset.range i).image
    (fun j => ((gateResultAt p c E rho j).getD none).getD .genesis)
  let genuine : Finset Block := candidates.filter
    (fun B => ∃ s, (s, B) ∈ cleanResults p c E rho i ∧ s ≤ r)
  let pool := insert Block.genesis genuine
  have hmem {s : Slot} {B : Block} (hB : (s, B) ∈ cleanResults p c E rho i)
      (hsr : s ≤ r) : B ∈ genuine := by
    obtain ⟨j, hj, x, htick, hresult⟩ := hB
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, ?_⟩,
      s, ⟨j, hj, x, htick, hresult⟩, hsr⟩
    simp only [hresult, Option.getD_some]
  have hcompatible {s t : Slot} {B C : Block}
      (hB : (s, B) ∈ cleanResults p c E rho i)
      (hC : (t, C) ∈ cleanResults p c E rho i) : Block.Compatible B C := by
    have hLift {r : Slot} {X : Block}
        (hX : (r, X) ∈ cleanResults p c E rho i) :
        (r, X) ∈ cleanResults p c E rho (timeIdx rho b₀) := by
      obtain ⟨j, hj, x, ht, hJ, hRes⟩ := hX
      exact ⟨j, hj.trans_le hi, x, ht, hJ, hRes⟩
    rcases lt_trichotomy s t with hlt | heq | hgt
    · exact block_compatible_of_common (hh.ordered s t B C (hLift hB) (hLift hC) hlt)
        (block_preceq_refl C)
    · subst t
      exact hh.same s B C (hLift hB) (hLift hC)
    · exact block_compatible_of_common (block_preceq_refl B)
        (hh.ordered t s C B (hLift hC) (hLift hB) hgt)
  have hpool : ∀ B ∈ pool, ∀ C ∈ pool, Block.Compatible B C := by
    intro B hB C hC
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact block_compatible_of_common (block_genesis_preceq C) (block_preceq_refl C)
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact block_compatible_of_common (block_preceq_refl B) (block_genesis_preceq B)
    obtain ⟨s, hB, _⟩ := (Finset.mem_filter.mp hB).2
    obtain ⟨t, hC, _⟩ := (Finset.mem_filter.mp hC).2
    exact hcompatible hB hC
  obtain ⟨D, hD, hmax⟩ := deepest_of_compatible pool ⟨.genesis, Finset.mem_insert_self ..⟩ hpool
  refine ⟨D, ?_, ?_⟩
  · rcases Finset.mem_insert.mp hD with hD | hD
    · exact Or.inl hD
    · obtain ⟨s, hs, hsr⟩ := (Finset.mem_filter.mp hD).2
      exact Or.inr ⟨s, D, hs, hsr, block_preceq_refl D⟩
  · intro X hX
    rcases hX with rfl | ⟨s, B, hB, hsr, hXB⟩
    · exact block_genesis_preceq D
    · exact block_preceq_trans hXB (hmax B (Finset.mem_insert_of_mem (hmem hB hsr)))


/-- A scoped certificate keeps the finality alternative at every consuming gate. -/
structure ArmingSleepCert (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (fast : Bool) (T b₀ : Time)
    (B : Block) (l : Slot) (D : Block) (Dh : FGBlock (Fin p.n)) : Prop where
  origin : ∃ r C, 1 ≤ r ∧ (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧
    SA.gateTime p.toParams r ≤ T ∧ Block.Preceq B C
  max_lift : eraseFG Dh = D
  max_read : Block.Preceq B D
  max_mem : (l, D) ∈ cleanResults p c E rho (timeIdx rho b₀)
  max_le : ∀ r C, (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ l →
    Block.Preceq C D
  gate_le_cut : SA.gateTime p.toParams l ≤ b₀
  cut_lt_pending : b₀ < SA.gateTime p.toParams (l + 1)
  cover_label : coverLabel p b₀ = l + 1
  source_below : ∀ y r C, y ∈ rho.honest →
    p.actionTime r < SA.gateTime p.toParams (l + 1) →
    actionSource p c E rho y r = some (some C) → Block.Preceq C D
  f_below : ∀ i y, i ≤ rho.idxBefore (SA.gateTime p.toParams (l + 1)) →
    y ∈ rho.honest → Block.Preceq (F_at p c E rho i y) D
  pending_input : ∀ i y, IsGateTick p c rho i y (l + 1) →
    y ∈ coveredNodes p E rho fast b₀ →
    Block.Preceq B (F_at p c E rho i y) ∨
      ArmingGateInput p (clockPre p (storeAt p c E rho i y)
        (SA.gateTime p.toParams (l + 1))) fast (l + 1) B D

/-- The last actual enabled result makes the finite comparison maximum a label-l result. -/
theorem arming_last_max_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {b₀ : Time} (hh : CleanHist p c E rho (timeIdx rho b₀))
    {l : Slot} {D₀ : Block} (hLast : (l, D₀) ∈ cleanResults p c E rho (timeIdx rho b₀)) :
    ∃ D, (l, D) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧
      ∀ r C, (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ l →
        Block.Preceq C D := by
  obtain ⟨D, hD, hmax⟩ := arming_comparison_prefix_on hh le_rfl l
  have hBelow r C (hC : (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀)) (hr : r ≤ l) :=
    hmax C (Or.inr ⟨r, C, hC, hr, block_preceq_refl C⟩)
  rcases hD with rfl | ⟨r, C, hC, hr, hDC⟩
  · exact ⟨D₀, hLast, fun r C hC hr =>
      block_preceq_trans (hBelow r C hC hr) (block_genesis_preceq D₀)⟩
  · rcases Nat.lt_or_eq_of_le hr with hlt | rfl
    · exact ⟨D₀, hLast, fun r X hX hr => block_preceq_trans (hBelow r X hX hr)
        (block_preceq_trans hDC (hh.ordered _ _ _ _ hC hLast hlt))⟩
    · exact ⟨C, hC, fun r X hX hr => block_preceq_trans (hBelow r X hX hr) hDC⟩


omit [DecidableEq V] in
/-- The exact joined seat set has the same cardinality as the joined population. -/
theorem arming_joined_head_card {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} (hC : V2.D.CStar (fgsaFamilies p c).fresh rho)
    (r : Slot) (H : Finset (Fin p.n))
    (hH : ∀ q, q ∈ H ↔ rho.seatOf (.base (.head r)) q ∈ rho.honest ∧
      joinedAt p E rho (rho.seatOf (.base (.head r)) q) r (SA.voteTime p.toParams r)) :
    H.card = (joinedHonest p E rho (SA.voteTime p.toParams r)).card := by
  classical
  have hbij := hC (.base (.head r)) trivial
  have hslot : slotAt p (SA.voteTime p.toParams r) = r :=
    slotOf_offset p r p.Δ p.deltaPos.le (by have hd := p.deltaPos; dsimp [Time] at *; omega)
  have himage : H.image (rho.seatOf (.base (.head r))) =
      joinedHonest p E rho (SA.voteTime p.toParams r) := by
    ext y
    change y ∈ H.image _ ↔ y ∈ rho.honest.filter _
    rw [Finset.mem_filter, hslot]
    constructor
    · rintro hy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      exact (hH q).mp hq
    · intro hy
      obtain ⟨q, rfl⟩ := hbij.2 y
      exact Finset.mem_image.mpr ⟨q, (hH q).mpr hy, rfl⟩
  exact (Finset.card_image_of_injective H hbij.1).symm.trans (congrArg Finset.card himage)

/-- Old row entries are bounded by the actual Clean cut state and comparison maximum. -/
theorem arming_sleep_entry_below {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {b₀ : Time}
    (hState : CleanState p c E rho (timeIdx rho b₀)) {l : Slot} {D : Block}
    {Dh : FGBlock (Fin p.n)} (hDh : eraseFG Dh = D)
    (hl : SA.gateTime p.toParams l ≤ b₀)
    (hmax : ∀ r C, (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ l →
      Block.Preceq C D) :
    ∀ i y r (a : RowWire p.n) e, HonestRowAt p c E rho i y r a →
      p.actionTime r < SA.gateTime p.toParams (l + 1) →
      namedEntry a.payload.height_pair = some e → EntryBelow p e Dh := by
  intro i y r a e hrow ht he
  have hrl := arming_action_label p l r ht
  have hg : SA.gateTime p.toParams (r * p.R) ≤ b₀ :=
    ((arming_gate_le_iff p _ _).mpr hrl).trans hl
  have hi := arming_lt_of_tick hs hrow.2.1 hg
  have hRows := hState.sources.1
  rw [CleanRowSources_def] at hRows
  obtain ⟨C, _, heC, hTC, hBelow⟩ := hRows i y r a e hi hrow he
  have hCD : Block.Preceq (eraseFG C) D := by
    rcases hBelow with hgen | ⟨q, X, hX, hq, hCX⟩
    · rw [hgen]; exact block_genesis_preceq D
    · exact block_preceq_trans hCX (hmax q X hX (hq.trans hrl))
  have hTC' : FGBlock.Preceq (heightView p C).T_h C := by
    simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def] using hTC
  have heC' : e = ((heightView p C).h, (heightView p C).T_h.root) := by
    simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def, hOf]
      using heC
  have hh : (heightView p (heightView p C).T_h).h = (heightView p C).h :=
    (Window.windowHeightLaws p p.K_W p.kWLarge).entry_same_height C
  refine ⟨(heightView p C).T_h, KitFG.preceq_trans hTC' (arming_lift (hDh ▸ hCD)), ?_⟩
  rw [heC', hh]

omit [DecidableEq V] in
/-- A protected pending tick has the cut, early-read and same-time receiver epochs. -/
theorem arming_pending_epochs {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {fast : Bool} {b₀ : Time} {l : Slot}
    (hl : SA.gateTime p.toParams l ≤ b₀) (_hcut : b₀ < SA.gateTime p.toParams (l + 1))
    (hLabel : coverLabel p b₀ = l + 1) {i : Nat} {x : V}
    (hx : x ∈ coveredNodes p E rho fast b₀) (hi : IsGateTick p c rho i x (l + 1)) :
    V2.D.restartFree rho x (timeIdx rho b₀)
      (rho.idxBefore (SA.gateTime p.toParams (l + 1))) ∧
    V2.D.restartFree rho x (rho.idxBefore (SA.gateTime p.toParams (l + 1))) i ∧
    ∀ k, rho.events[k]? = some (.tick x (SA.earlyTime p.toParams (l + 1))) →
      V2.D.restartFree rho x k i := by
  classical
  have hScope : (if fast then l + 1 = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ ((l + 1 : Nat) : Int) ∧
        l + 1 ≤ coverLabel p b₀) := by
    rw [hLabel]
    cases fast with
    | true => exact rfl
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      have hk : (1 : Int) ≤ (p.k : Int) := by exact_mod_cast (show 1 ≤ p.k by
        have := p.kLarge; omega)
      exact ⟨by omega, le_rfl⟩
  have hR := arming_receiver_gate_epoch hs hx hScope hi
  have hstart : slotStartZ p ((l + 1 : Nat) : Int) < SA.earlyTime p.toParams (l + 1) := by
    change 4 * p.Δ * ((l + 1 : Nat) : Int) <
      4 * p.Δ * ((l + 1 : Nat) : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  have heg : SA.earlyTime p.toParams (l + 1) < SA.gateTime p.toParams (l + 1) := by
    rw [arming_early_eq, arming_gate_eq]
    linarith [p.deltaPos]
  have hiStart := Gen.V2.Duty.actionCut_le_idxBefore hs (hstart.trans heg)
  have hcutStart : rho.actionCut (slotStartZ p ((l + 1 : Nat) : Int)) ≤ timeIdx rho b₀ :=
    (Gen.V2.Duty.actionCut_le_idxBefore hs
      (hstart.trans_le ((arming_early_next p l).trans_le hl))).trans
        (arming_idxBefore_le_timeIdx rho b₀)
  refine ⟨hR.mono hcutStart ?_, hR.mono hiStart le_rfl, ?_⟩
  · have hidx : rho.idxBefore (SA.gateTime p.toParams (l + 1)) ≤ i := by
      by_contra hn
      have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mp (lt_of_not_ge hn)
      exact (lt_irrefl _ ht).elim
    exact hidx
  · intro k hk
    have hkStart : rho.actionCut (slotStartZ p ((l + 1 : Nat) : Int)) ≤ k := by
      by_contra hn
      have ht := (V2.D.Engine.index_lt_actionCut_iff hs hk _).mp (lt_of_not_ge hn)
      rcases ht with ht | ⟨ht, _⟩
      · exact (not_lt.mpr hstart.le) ht
      · exact (ne_of_lt hstart) ht.symm
    exact hR.mono hkStart le_rfl


/-- The comparison result has its actual FG lift in its producing gate's tree. -/
theorem arming_sleep_comparison_lift {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {r : Slot} {D : Block} (hD : (r, D) ∈ cleanResults p c E rho i) :
    ∃ Dh : FGBlock (Fin p.n), eraseFG Dh = D := by
  obtain ⟨j, _, x, ht, hJ, hres⟩ := hD
  have hG : enabledGateAt p c E rho j x r := ⟨ht, hJ⟩
  have hraw := (arming_gateResult_tick hs hG).symm.trans
    ((gateResultAt_eq_gateResult p c E rho hs ht).symm.trans hres)
  have hc := Option.some.inj hraw
  let st := clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams r)
  have hinv := cstoreInv_clockPre p _ (cstoreInv_stateBefore E rho j x) (SA.gateTime p.toParams r)
  obtain ⟨Dh, _, he⟩ := (hinv.baseTree D).mp (compat_of_confirmation p st hinv hc).2
  exact ⟨Dh, he⟩

/-- Construct the scoped certificate from Clean inputs and a last-label result.
The last-label result is explicit: strict-before-cut participation supplies it,
but participation at a cut equal to this gate is a separate boundary case. -/
theorem arming_sleep_cert_of_last [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    (hSaved : fast = false → ∀ {x : V} {q : Slot} {B : Block}, x ∈ rho.honest →
      SA.gateTime p.toParams q ≤ b₀ →
      AwakeClosed E x (slotStartZ p (q : Int)) b₀ →
      RestartFreeTime rho x (slotStartZ p (q : Int)) b₀ →
      (B = .genesis ∨ ∃ r C, r < q ∧
        (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧ Block.Preceq B C) →
      Block.Preceq B (F_at p c E rho (timeIdx rho b₀) x) ∨
        ∃ C, GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) x).base q =
          some (some C) ∧ Block.Preceq B C)
    {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis)
    (hLast : ∃ C, (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat, C) ∈
      cleanResults p c E rho (timeIdx rho b₀)) :
    ∃ D Dh, ArmingSleepCert p c E rho fast T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh := by
  have hs := h.pre.base.valid.toScheduleWellFormed
  obtain ⟨r, C, hr, hOrigin, hTime, hBC⟩ :=
    arming_protected_origin_on hs h.order.2.1 hState hHist hread hne
  let l := ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat
  have h6 : 6 * p.Δ ≤ b₀ := by
    have hg := (arming_gate_le_iff p 0 r).mpr (Nat.zero_le r)
    simpa only [arming_gate_eq, Nat.cast_zero, mul_zero, zero_add] using
      hg.trans (hTime.trans h.order.2.1)
  obtain ⟨hl, hcut⟩ := arming_label p b₀ h6
  obtain ⟨D₀, hD₀⟩ := hLast
  obtain ⟨D, hD, hmax⟩ := arming_last_max_on hHist hD₀
  obtain ⟨Dh, hDh⟩ := arming_sleep_comparison_lift hs hD
  have hgap : (if fast then r + 2 ≤ l + 1 else r + p.k ≤ l + 1) := by
    cases fast with
    | true => exact arming_fast_gap p r T b₀ hTime h.lag
    | false => exact arming_slow_gap p r T b₀ hTime h.lag
  have hrl : r ≤ l := by
    cases fast <;> simp only [ite_true, Bool.false_eq_true, ite_false] at hgap
    all_goals dsimp only [Slot] at *; have := p.kLarge; omega
  have hBD := block_preceq_trans hBC (hmax r C hOrigin hrl)
  have hentry := arming_sleep_entry_below hs (hState _ le_rfl) hDh hl hmax
  have hF : ∀ i y, i ≤ rho.idxBefore (SA.gateTime p.toParams (l + 1)) →
      y ∈ rho.honest → Block.Preceq (F_at p c E rho i y) D := by
    intro i y hi hy
    exact (arming_frame_below (hroots := h.pre.base.idealization) (hstrat := hf.strat)
      (hScope := hDh.symm ▸ rootScope_result h.pre.base.valid hD)
      hs hf.store hf.frame.1 hsrc hDh hentry hi hy).1
  refine ⟨D, Dh, ⟨r, C, hr, hOrigin, hTime, hBC⟩, hDh, hBD, hD, hmax, hl, hcut,
    rfl, arming_source_below hs htsrc hl hmax, hF, ?_⟩
  intro i y hi hyG
  have hLabel : coverLabel p b₀ = l + 1 := rfl
  have hScope : (if fast then l + 1 = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ ((l + 1 : Nat) : Int) ∧
        l + 1 ≤ coverLabel p b₀) := by
    rw [hLabel]
    cases fast with
    | true => exact rfl
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      have hk : (1 : Int) ≤ (p.k : Int) := by exact_mod_cast (show 1 ≤ p.k by
        have := p.kLarge; omega)
      exact ⟨by omega, le_rfl⟩
  obtain ⟨hy, _, _⟩ := arming_receiver_window hyG hScope
  obtain ⟨hCutEpoch, hTickEpoch, hEarlyEpoch⟩ := arming_pending_epochs hs hl hcut hLabel hyG hi
  have hCutI := (arming_timeIdx_le_idxBefore rho hcut).trans (by
    by_contra hn
    have ht := (Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mp (lt_of_not_ge hn)
    exact (lt_irrefl _ ht).elim)
  by_cases hBF : Block.Preceq B (F_at p c E rho (timeIdx rho b₀) y)
  · exact Or.inl (block_preceq_trans hBF (eraseFG_preceq (hf.mono _ _ y hy hCutI).1))
  right
  have hObl : ∀ row ∈ (storeAt p c E rho
      (rho.idxBefore (SA.gateTime p.toParams (l + 1))) y).base.obligations,
      Block.Preceq row.1 D :=
    arming_leases_interval_on hs hl y (arming_timeIdx_le_idxBefore rho hcut) le_rfl
      hCutEpoch (arming_leases_cut hs hcut
        (fun i y hi _ => (hState i hi).leases y) hmax le_rfl hy)
  have hFloor : Block.Preceq (eraseFG (rho.stateBeforeTime E
      (SA.earlyTime p.toParams (l + 1)) y).st.fg.F) D := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
    exact hF _ y (fgsa_idxBefore_mono rho (by
      rw [arming_early_eq, arming_gate_eq]; linarith [p.deltaPos])) hy
  apply arming_sleep_pending_input h.pre.base.valid h.pre.base.cstar hBD
    ⟨h.sleepPre.joinedPartBefore _ (by rw [arming_vote_eq]; have := p.deltaPos; positivity)
      ((arming_vote_lt_early p _).1.trans_le ((arming_early_next p l).trans_le hl))⟩
    hi (fun k hk => hF k y hk hy) hObl
    (arming_healthy_batch_protected h htransfer hl hD hyG hLabel hFloor)
    hEarlyEpoch hTickEpoch fast
  · intro hf H hH
    change (p.n + 1) / 2 ≤ H.card
    rw [arming_joined_head_card h.pre.base.cstar (l + 1) H hH]
    exact h.joinedFastPart hf _
      (by rw [arming_vote_eq]; have := p.deltaPos; positivity)
      ((arming_vote_lt_early p _).1.trans_le ((arming_early_next p l).trans_le hl))
  · intro hfalse
    subst fast
    have hgap' : r + p.k ≤ l + 1 := by simpa only [Bool.false_eq_true, ite_false] using hgap
    refine ⟨by have := hr; dsimp only [Slot] at *; omega, ?_⟩
    have hrows := arming_slow_current_rows_on h (hState _ le_rfl) (hSaved rfl) hyG
      hr hOrigin hTime hBC hmax
    exact arming_pending_rows_on hs hl hcut hi hCutEpoch hTickEpoch
      (fun k hk => hF k y hk hy) (hrows.resolve_left hBF)


/-- Execute the scoped input, retaining current finality as a separate result. -/
theorem arming_sleep_gate_core {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hvalid : V2.D.ExecutionValid E rho) (hdelta : E.Δ = p.Δ)
    {fast : Bool} {T b₀ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon) :
    ∀ y ∈ coveredNodes p E rho fast b₀,
      let I := afterTicksIdx rho (SA.gateTime p.toParams (l + 1))
      let st := storeAt p c E rho I y
      Block.Preceq B (S_at p c E rho I y) ∧
      (Block.Preceq B (F_at p c E rho I y) ∨
        (Block.Preceq (F_at p c E rho I y) B ∧ F_at p c E rho I y ≠ B ∧
          ∃ dl, FGSA.leaseOf st B = some dl ∧ SA.gateTime p.toParams (l + 1) < dl ∧
            SA.gateTime p.toParams (l + 1) + L p ≤ dl ∧ B ∈ st.base.blocks)) := by
  intro y hyG I st
  have hs := hvalid.toScheduleWellFormed
  have hScope : (if fast then l + 1 = coverLabel p b₀
      else (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ ((l + 1 : Nat) : Int) ∧
        l + 1 ≤ coverLabel p b₀) := by
    rw [hc.cover_label]
    cases fast with
    | true => exact rfl
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      have hk : (1 : Int) ≤ (p.k : Int) := by exact_mod_cast (show 1 ≤ p.k by
        have := p.kLarge; omega)
      exact ⟨by omega, le_rfl⟩
  have hy := (arming_receiver_window hyG hScope).1
  obtain ⟨i, hi⟩ := arming_tick_exists hs hdelta hy (4 * (l + 1) + 6)
    (arming_gate_nat p (l + 1)) hgate (arming_receiver_times hyG hScope).2
  let P := clockPre p (storeAt p c E rho i y) (SA.gateTime p.toParams (l + 1))
  have hI : storeAt p c E rho I y = gateStep p P (l + 1) := by
    change (V2.D.Run.stateBefore E rho I y).st = _
    rw [← afterTicks_eq_stateBefore E rho hs, afterTicks_node E rho hs hi]
    exact (tick_st (c := c) E rho _ y _).trans (arming_clock_gate p _ (l + 1))
  have hFI : F_at p c E rho I y = F_at p c E rho i y := by
    change eraseFG (storeAt p c E rho I y).fg.F = eraseFG (storeAt p c E rho i y).fg.F
    rw [hI, gateStep_fg, clockPre_fg]
  rcases hc.pending_input i y hi hyG with hBF | hIn
  · have hBF' := hFI.symm ▸ hBF
    exact ⟨block_preceq_trans hBF'
      (finalized_preceq_stable p _ (reachable_stateBefore E rho I y)), Or.inl hBF'⟩
  have hG := arming_receiver_enabled hs hyG hScope hi
  have hJoined : joinedNow p P = true := by
    dsimp only [P]
    rw [clockPre_joined]
    exact fgsa_gate_joined_of_enabled E rho hG
  obtain ⟨Cj, hraw, hDCj⟩ := hIn.raw
  have hEpoch := (arming_pending_epochs hs hc.gate_le_cut hc.cut_lt_pending
    hc.cover_label hyG hi).2.1
  have hst := arming_tick_store_on hs hi hEpoch
  have hFD : Block.Preceq (eraseFG P.fg.F) D := by
    dsimp only [P]
    rw [clockPre_fg, hst]
    exact hc.f_below _ y le_rfl hy
  have hlev : SA.releaseThreshold p.toParams ≤
      SA.Root.prefixSupport p.toParams (actView P) (l + 1) B ∨
      GridCO.slowEligible p.toParams.engine (actView P) (l + 1) B = true := by
    cases fast with
    | true => exact Or.inl (hIn.fast_support rfl)
    | false =>
      right
      obtain ⟨hk2, hwin⟩ := hIn.slow_rows rfl
      apply Bool.and_eq_true_iff.mpr
      refine ⟨decide_eq_true hk2, List.all_eq_true.mpr ?_⟩
      intro a ha
      obtain ⟨Ca, hsv, hBCa⟩ := hwin a (List.mem_range.mp ha)
      rw [show GridCO.savedGenuine (actView P) (l + 1 - (a + 1)) = some (some Ca) from hsv]
      exact hBCa
  obtain ⟨_, hblocks, hS, d, hrow, hd⟩ := arming_gate_write p P (l + 1) hJoined hIn.fresh hraw
    (fun row hr => block_compatible_of_common (block_preceq_trans (hIn.leases row hr) hDCj)
      (block_preceq_refl Cj)) (block_preceq_trans hFD hDCj) hIn.active hne
    (block_preceq_trans hc.max_read hDCj) hlev
  refine ⟨?_, ?_⟩
  · change Block.Preceq B (storeAt p c E rho I y).base.stableRecord
    rw [hI]
    exact hS
  by_cases hBF : Block.Preceq B (F_at p c E rho I y)
  · exact Or.inl hBF
  right
  have hFB : Block.Preceq (F_at p c E rho I y) B := by
    rw [hFI]
    have hPF : eraseFG P.fg.F = F_at p c E rho i y := by
      dsimp only [P]
      rw [clockPre_fg]
      rfl
    rcases Bool.or_eq_true_iff.mp hIn.compatible with h | h
    · exact hPF ▸ h
    · exact absurd (hFI.symm ▸ hPF ▸ h) hBF
  refine ⟨hFB, fun he => hBF (he ▸ block_preceq_refl _), d, ?_, ?_, hd, ?_⟩
  · have hm : (B, SA.releaseThreshold p.toParams, d) ∈ st.base.obligations := by
      change _ ∈ (storeAt p c E rho I y).base.obligations
      rw [hI]
      exact hrow
    exact arming_leaseOf p st (cstoreInv_stateBefore E rho I y) hm
  · exact lt_of_lt_of_le (lt_add_of_pos_right _ (arming_L_pos p)) hd
  · change B ∈ (storeAt p c E rho I y).base.blocks
    rw [hI, hblocks]
    exact ((actView_blocks P B).mp hIn.active).1


/-- The scoped frame consumer returns the full lease-or-finality result to P-Ou.
P-Ou supplies compatibility of all earlier honest named rows from its source history. -/
theorem pending_gate_lease_or_F_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hvalid : V2.D.ExecutionValid E rho) (hdelta : E.Δ = p.Δ)
    (hf : FGFoundation p c E rho)
    {fast : Bool} {T b₀ : Time} {B : Block} (hne : B ≠ .genesis)
    {l : Slot} {D : Block} {Dh : FGBlock (Fin p.n)}
    (hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
    (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon)
    (hRows : ∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)) (Bh : FGBlock (Fin p.n)),
      eraseFG Bh = B →
      HonestRowBefore p c E rho (afterTicksIdx rho (SA.gateTime p.toParams (l + 1))) y r a →
      namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
      RootBlockInRun p c E rho (eraseFG e) → FGBlock.Preceq e Bh ∨ FGBlock.Preceq Bh e) :
    ∀ y ∈ coveredNodes p E rho fast b₀,
      let I := afterTicksIdx rho (SA.gateTime p.toParams (l + 1))
      let st := storeAt p c E rho I y
      Block.Preceq B (S_at p c E rho I y) ∧
      (Block.Preceq B (F_at p c E rho I y) ∨
        (Block.Preceq (F_at p c E rho I y) B ∧ F_at p c E rho I y ≠ B ∧
          ∃ dl, FGSA.leaseOf st B = some dl ∧ SA.gateTime p.toParams (l + 1) < dl ∧
            SA.gateTime p.toParams (l + 1) + L p ≤ dl ∧
            ((∃ X ∈ FGSA.fullTree p st, eraseFG X = B) ∨
              Block.Preceq B (eraseFG (FGSA.controls p st).Z)))) := by
  classical
  intro y hyG I st
  obtain ⟨hS, hF | ⟨hFB, hneF, dl, hlease, hdl, hlong, hB⟩⟩ :=
    arming_sleep_gate_core hvalid hdelta hne hc hgate y hyG
  · exact ⟨hS, Or.inl hF⟩
  refine ⟨hS, Or.inr ⟨hFB, hneF, dl, hlease, hdl, hlong, ?_⟩⟩
  have hy : y ∈ rho.honest := (Finset.mem_filter.mp hyG).1
  have hinv : CStoreInv p st := cstoreInv_stateBefore E rho I y
  obtain ⟨Bh, hBh, hBe⟩ := (hinv.baseTree B).1 hB
  have hFBh : FGBlock.Preceq st.fg.F Bh := arming_lift (hBe ▸ hFB)
  obtain ⟨_, _, hdom, _⟩ := (fgsa_cpCompat_of_scopedFrame p c E rho hf.store hf.strat
    I y Bh hy (fun z r a e ha he hScope => hRows z r a e Bh hBe ha he hScope)).2
  rcases hdom hBh hFBh with hZ | hD
  · exact Or.inr (hBe ▸ eraseFG_preceq hZ)
  · left
    refine ⟨Bh, ?_, hBe⟩
    rw [fgsa_fullTree_eq_filtered, ← fgsa_domainR_eq_filtered]
    exact hD


/-- Fast scoped arming from an actual last-label comparison result. -/
theorem fast_arming_on [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c true E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis)
    (hLast : ∃ C, (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat, C) ∈
      cleanResults p c E rho (timeIdx rho b₀)) :
    ∃ D Dh, ArmingSleepCert p c E rho true T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh := by
  exact arming_sleep_cert_of_last h hf hsrc htsrc hState hHist htransfer
    (fun hfalse => nomatch hfalse) hread hne hLast

/-- Slow scoped arming derives the last gate from the protected receiver's own window. -/
theorem slow_arming_on [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c false E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
      joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
      SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
      vHead p c E rho z s = some H → Block.Preceq C H)
    (hSaved : ∀ {x : V} {q : Slot} {B : Block}, x ∈ rho.honest →
      SA.gateTime p.toParams q ≤ b₀ →
      AwakeClosed E x (slotStartZ p (q : Int)) b₀ →
      RestartFreeTime rho x (slotStartZ p (q : Int)) b₀ →
      (B = .genesis ∨ ∃ r C, r < q ∧
        (r, C) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧ Block.Preceq B C) →
      Block.Preceq B (F_at p c E rho (timeIdx rho b₀) x) ∨
        ∃ C, GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b₀) x).base q =
          some (some C) ∧ Block.Preceq B C)
    {x : V} {B : Block}
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis)
    {y : V} (hyG : y ∈ coveredNodes p E rho false b₀) :
    ∃ D Dh, ArmingSleepCert p c E rho false T b₀ B
      (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat) D Dh := by
  have hs := h.pre.base.valid.toScheduleWellFormed
  obtain ⟨r, C, _, _, hTime, _⟩ :=
    arming_protected_origin_on hs h.order.2.1 hState hHist hread hne
  let l := ((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat
  have h6 : 6 * p.Δ ≤ b₀ := by
    have hg := (arming_gate_le_iff p 0 r).mpr (Nat.zero_le r)
    simpa only [arming_gate_eq, Nat.cast_zero, mul_zero, zero_add] using
      hg.trans (hTime.trans h.order.2.1)
  have hl := (arming_label p b₀ h6).1
  have hScope : (coverLabel p b₀ : Int) - (p.k : Int) + 1 ≤ (l : Int) ∧
      l ≤ coverLabel p b₀ := by
    change ((l + 1 : Nat) : Int) - (p.k : Int) + 1 ≤ (l : Int) ∧ l ≤ l + 1
    have hk : (2 : Int) ≤ (p.k : Int) := by exact_mod_cast p.kLarge
    exact ⟨by omega, Nat.le_succ l⟩
  have hy := (arming_receiver_window hyG hScope).1
  obtain ⟨i, hi⟩ := arming_tick_exists hs h.pre.base.delta hy (4 * l + 6)
    (arming_gate_nat p l) (hl.trans h.pre.cut.2) (arming_receiver_times hyG hScope).2
  have hG := arming_receiver_enabled hs hyG hScope hi
  have hicut := arming_lt_of_tick hs hi hl
  obtain ⟨D₀, hD₀, _⟩ := hHist.nonempty i y l hicut hG
  exact arming_sleep_cert_of_last h hf hsrc htsrc hState hHist htransfer (fun _ => hSaved)
    hread hne ⟨D₀, i, hicut, y, hi, hG.2, hD₀⟩


/-- Genesis uses direct prefix order and does not require an arming certificate. -/
theorem arming_genesis_on {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (i : Nat) (y : V) :
    Block.Preceq .genesis (S_at p c E rho i y) ∧
      Block.Preceq .genesis (F_at p c E rho i y) :=
  ⟨block_genesis_preceq _, block_genesis_preceq _⟩

end AvailableChain.FGSA.Run
end

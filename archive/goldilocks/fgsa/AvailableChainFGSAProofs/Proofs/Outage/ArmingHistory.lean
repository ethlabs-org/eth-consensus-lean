module
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingArith
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

/-! Plan O-ARM §6.1, §11 obligations 1 and 2: cut-scoped history. Every
ordering fact is used only for gate times at or before the cut `b₀`. -/

namespace AvailableChain.FGSA.Run

open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; a tick inside the inclusive
read at `b` has time at most `b`. -/
theorem arming_tick_le {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {j : Nat} {x : V} {t b : Time}
    (hj : rho.events[j]? = some (.tick x t)) (hlt : j < timeIdx rho b) : t ≤ b :=
  (arming_lt_timeIdx_iff hs b hj).mp hlt

omit [DecidableEq V] in
/-- Plan O-ARM §2. Class (iii). DC: INTENTIONAL; a tick at time at most `b`
is inside the inclusive read at `b`. -/
theorem arming_lt_of_tick {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {j : Nat} {x : V} {t b : Time}
    (hj : rho.events[j]? = some (.tick x t)) (hle : t ≤ b) : j < timeIdx rho b :=
  (arming_lt_timeIdx_iff hs b hj).mpr hle

/-- Plan O-ARM §6.1, §11 obligation 1. Class (iii). DC: INTENTIONAL; a
cut-scoped clean result is an actual honest gate tick at or before the read. -/
theorem arming_clean_mem {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {b : Time} {i : Nat} {s : Slot} {X : Block}
    (hi : i ≤ timeIdx rho b) (hX : (s, X) ∈ cleanResults p c E rho i) :
    ∃ j x, j < i ∧ x ∈ rho.honest ∧ IsGateTick p c rho j x s ∧
      SA.gateTime p.toParams s ≤ b ∧ gateResultAt p c E rho j = some (some X) ∧
      gateResult p c E rho x s = some (some X) := by
  obtain ⟨j, hj, x, htick, hEnabled, hres⟩ := hX
  refine ⟨j, x, hj, hs.honest_only _ (List.mem_of_getElem? htick), htick,
    arming_tick_le hs htick (lt_of_lt_of_le hj hi), hres, ?_⟩
  rw [← gateResultAt_eq_gateResult p c E rho hs htick]
  exact hres

/-- A passed gate identifies the enabled receiver and label at that event. -/
theorem arming_enabled_of_pass {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {i : Nat} {y : V} {s : Slot} (hi : IsGateTick p c rho i y s)
    (hpass : gatePassedAt p c E rho i) : enabledGateAt p c E rho i y s := by
  obtain ⟨z, q, ⟨hq, hEpoch⟩, _⟩ := hpass
  have he := Option.some.inj (hq.symm.trans hi)
  have hz : z = y := (V2.Event.tick.inj he).1
  have htime := (V2.Event.tick.inj he).2
  have hqs : q = s := le_antisymm ((arming_gate_le_iff p q s).mp htime.le)
    ((arming_gate_le_iff p s q).mp htime.symm.le)
  subst z
  subst q
  exact ⟨hi, hEpoch⟩

/-- A nonempty executed gate result proves the inclusive join marker bound. -/
theorem arming_enabled_of_result {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {y : V} {s : Slot} {C : Block}
    (hi : IsGateTick p c rho i y s)
    (hres : gateResultAt p c E rho i = some (some C)) :
    enabledGateAt p c E rho i y s := by
  have hresult : gateResult p c E rho y s = some (some C) := by
    rwa [← gateResultAt_eq_gateResult p c E rho hs hi]
  have hJ := (fgsa_gate_raw_of_nonempty p c E rho hs hi hresult).1
  have hslot : p.slotOf (SA.gateTime p.toParams s) = s + 1 :=
    (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho i y) _).2.symm.trans
      (fgsa_gate_slot (c := c) (V2.D.Run.stateBefore E rho i y) s)
  refine ⟨hi, ?_⟩
  cases hr : (storeAt p c E rho i y).restartTime with
  | none => trivial
  | some w =>
    change (V2.D.Run.stateBefore E rho i y).st.restartTime = some w at hr
    simp only [joinedAtTime, hr, hslot, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, decide_eq_true_eq] at hJ
    exact hJ

/-- Plan O-ARM §6.1, §11 obligation 1. Class (iii). DC: INTENTIONAL; an
actual honest gate tick at or before the cut is a clean result of the cut. -/
theorem arming_clean_of_tick {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {b : Time} {j : Nat} {x : V} {s : Slot}
    {X : Block} (hEnabled : enabledGateAt p c E rho j x s) (hb : SA.gateTime p.toParams s ≤ b)
    (hX : gateResult p c E rho x s = some (some X)) :
    j < timeIdx rho b ∧ (s, X) ∈ cleanResults p c E rho (timeIdx rho b) := by
  have hj := hEnabled.1
  have hlt := arming_lt_of_tick hs hj hb
  refine ⟨hlt, j, hlt, x, hj, hEnabled.2, ?_⟩
  rw [gateResultAt_eq_gateResult p c E rho hs hj]
  exact hX

/-- Plan O-ARM §6.1, §11 obligation 1. Class (iii). DC: INTENTIONAL; clean
results of a cut read are ordered by label and compatible at one label. -/
theorem arming_clean_ordered {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {b₀ : Time}
    (hordered : ∀ y z r s C D, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams r ≤ b₀ → SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y r = some (some C) →
      gateResult p c E rho z s = some (some D) →
      (r < s → Block.Preceq C D) ∧ (r = s → Block.Compatible C D))
    {i : Nat} (hi : i ≤ timeIdx rho b₀) {r s : Slot} {X Y : Block}
    (hX : (r, X) ∈ cleanResults p c E rho i) (hY : (s, Y) ∈ cleanResults p c E rho i) :
    (r < s → Block.Preceq X Y) ∧ (r = s → Block.Compatible X Y) := by
  obtain ⟨_, x, _, hx, _, hrb, _, hXr⟩ := arming_clean_mem hs hi hX
  obtain ⟨_, y, _, hy, _, hsb, _, hYs⟩ := arming_clean_mem hs hi hY
  exact hordered x y r s X Y hx hy hrb hsb hXr hYs

/-- Plan O-ARM §6.1 step 4, §11 obligation 1. Class (iii). DC: INTENTIONAL;
the cut-scoped variant of `inclusion_comparison_prefix`. Only the ordering
of gates at or before the cut is used. -/
theorem arming_comparison_prefix {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {b₀ : Time}
    (hordered : ∀ y z r s C D, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams r ≤ b₀ → SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y r = some (some C) →
      gateResult p c E rho z s = some (some D) →
      (r < s → Block.Preceq C D) ∧ (r = s → Block.Compatible C D))
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
    have hBC := arming_clean_ordered hs hordered hi hB hC
    rcases lt_trichotomy s t with hlt | heq | hgt
    · exact block_compatible_of_common (hBC.1 hlt) (block_preceq_refl C)
    · exact hBC.2 heq
    · exact block_compatible_of_common (block_preceq_refl B)
        ((arming_clean_ordered hs hordered hi hC hB).1 hgt)
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

/-- Plan O-ARM §4 field 2, §6.1 steps 4–5. Class (iii). DC: INTENTIONAL; the
comparison maximum through label `l` is attained by an actual label-`l` clean
result. `hcleanGate` supplies one label-`l` result at the honest node `x`. -/
theorem arming_max_label {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {b₀ : Time}
    (hordered : ∀ y z r s C D, y ∈ rho.honest → z ∈ rho.honest →
      SA.gateTime p.toParams r ≤ b₀ → SA.gateTime p.toParams s ≤ b₀ →
      gateResult p c E rho y r = some (some C) →
      gateResult p c E rho z s = some (some D) →
      (r < s → Block.Preceq C D) ∧ (r = s → Block.Compatible C D))
    {l : Slot} {x : V} {Cl : Block} {k : Nat} (hk : enabledGateAt p c E rho k x l)
    (hl : SA.gateTime p.toParams l ≤ b₀) (hCl : gateResult p c E rho x l = some (some Cl)) :
    ∃ D, (l, D) ∈ cleanResults p c E rho (timeIdx rho b₀) ∧
      ∀ r X, (r, X) ∈ cleanResults p c E rho (timeIdx rho b₀) → r ≤ l →
        Block.Preceq X D := by
  obtain ⟨_, hmemCl⟩ := arming_clean_of_tick hs hk hl hCl
  obtain ⟨D₀, hD₀, hmax⟩ := arming_comparison_prefix hs hordered le_rfl l
  have hClD₀ : Block.Preceq Cl D₀ :=
    hmax Cl (Or.inr ⟨l, Cl, hmemCl, le_rfl, block_preceq_refl Cl⟩)
  have hbelow (r : Slot) (X : Block) (hX : (r, X) ∈ cleanResults p c E rho (timeIdx rho b₀))
      (hr : r ≤ l) : Block.Preceq X D₀ :=
    hmax X (Or.inr ⟨r, X, hX, hr, block_preceq_refl X⟩)
  rcases hD₀ with hgen | ⟨s, B', hB', hsl, hD₀B'⟩
  · subst hgen
    exact ⟨Cl, hmemCl, fun r X hX hr =>
      block_preceq_trans (hbelow r X hX hr) (block_genesis_preceq Cl)⟩
  · rcases Nat.lt_or_eq_of_le hsl with hlt | heq
    · have hB'Cl := (arming_clean_ordered hs hordered le_rfl hB' hmemCl).1 hlt
      exact ⟨Cl, hmemCl, fun r X hX hr =>
        block_preceq_trans (hbelow r X hX hr) (block_preceq_trans hD₀B' hB'Cl)⟩
    · subst heq
      exact ⟨B', hB', fun r X hX hr =>
        block_preceq_trans (hbelow r X hX hr) hD₀B'⟩

/-- Plan O-ARM §6.1 step 1. Class (iii). DC: INTENTIONAL; the protected stable
read is the stored stable record at the inclusive read index. -/
theorem arming_stable_read {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) (x : V) (T : Time) :
    V2.D.outputAt E rho (fgsaInterface p c).stable x T = S_at p c E rho (timeIdx rho T) x := by
  change (V2.D.Run.readAt E rho T x).st.base.stableRecord = _
  rw [V2.D.Engine.readAt_eq_stateBefore hs T]
  rfl

/-- Plan O-ARM §6.1 step 2. Class (iii). DC: INTENTIONAL; a non-genesis read
below an actual clean result at or before `T` has an actual successful origin
of positive label. -/
theorem arming_origin_of_clean {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {T b₀ : Time} (hT : T ≤ b₀)
    (hnonempty : ∀ i y s, i < timeIdx rho b₀ → y ∈ rho.honest →
      IsGateTick p c rho i y s →
      ∃ C, gateResultAt p c E rho i = some (some C) ∧ (s = 0 → C = .genesis))
    (hcleanGate : ∀ r y, SA.gateTime p.toParams r ≤ b₀ → y ∈ rho.honest →
      ∃ C, gateResult p c E rho y r = some (some C) ∧
        (∃ i, IsGateTick p c rho i y r ∧ gatePassedAt p c E rho i) ∧
        Block.Preceq C (S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams r)) y) ∧
        ∀ r' < r, ∀ C', gateResult p c E rho y r' = some (some C') → Block.Preceq C' C)
    {B : Block} (hne : B ≠ .genesis) {q : Nat} (hq : q ≤ timeIdx rho T) {s : Slot}
    {X : Block} (hX : (s, X) ∈ cleanResults p c E rho q) (hBX : Block.Preceq B X) :
    ∃ u s C iₛ, u ∈ rho.honest ∧ 1 ≤ s ∧ IsGateTick p c rho iₛ u s ∧
      gatePassedAt p c E rho iₛ ∧ gateResultAt p c E rho iₛ = some (some C) ∧
      SA.gateTime p.toParams s ≤ T ∧ Block.Preceq B C := by
  obtain ⟨j, u, _, hu, htick, hsT, hres, hgr⟩ := arming_clean_mem hs hq hX
  have hsb : SA.gateTime p.toParams s ≤ b₀ := hsT.trans hT
  obtain ⟨_, _, ⟨i', hi', hpass⟩, _⟩ := hcleanGate s u hsb hu
  have hij : i' = j := fgsa_tick_unique E rho hs hi' htick
  subst hij
  refine ⟨u, s, X, i', hu, ?_, htick, hpass, hres, hsT, hBX⟩
  rcases Nat.eq_zero_or_pos s with h0 | hpos
  · exfalso
    obtain ⟨C', hC', hgen⟩ := hnonempty i' u s (arming_lt_of_tick hs htick hsb) hu htick
    have hXC : X = C' := by
      rw [hres] at hC'
      exact Option.some.inj (Option.some.inj hC')
    have hXg : X = .genesis := hXC.trans (hgen h0)
    subst hXg
    exact hne (block_preceq_antisymm hBX (block_genesis_preceq B))
  · exact hpos

/-- Plan O-ARM §4 field 1, §6.1 steps 1–3, §11 obligation 2. Class (iii).
DC: INTENTIONAL; the actual origin of a non-genesis protected stable read.
The gate branch and the F-normalized branch of `hsOrigin` both reach an actual
honest successful gate tick at or before `T`. -/
theorem arming_origin {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    (hs : V2.D.ScheduleWellFormed E rho) {T b₀ : Time} (hT : T ≤ b₀)
    (hnonempty : ∀ i y s, i < timeIdx rho b₀ → y ∈ rho.honest →
      IsGateTick p c rho i y s →
      ∃ C, gateResultAt p c E rho i = some (some C) ∧ (s = 0 → C = .genesis))
    (hbelow : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      let below := BelowLabel p c E rho i (labelBoundAt p c rho i)
      below (F_at p c E rho i y) ∧ below (J_at p c E rho i y) ∧
        below (S_at p c E rho i y))
    (hsOrigin : ∀ i y, i ≤ timeIdx rho b₀ → y ∈ rho.honest →
      S_at p c E rho i y = .genesis ∨
      (∃ q < i, ∃ s, IsGateTick p c rho q y s ∧
        gateResultAt p c E rho q = some (some (S_at p c E rho i y))) ∨
      (∃ q ≤ i, S_at p c E rho i y = F_at p c E rho q y))
    (hcleanGate : ∀ r y, SA.gateTime p.toParams r ≤ b₀ → y ∈ rho.honest →
      ∃ C, gateResult p c E rho y r = some (some C) ∧
        (∃ i, IsGateTick p c rho i y r ∧ gatePassedAt p c E rho i) ∧
        Block.Preceq C (S_at p c E rho (afterTicksIdx rho (SA.gateTime p.toParams r)) y) ∧
        ∀ r' < r, ∀ C', gateResult p c E rho y r' = some (some C') → Block.Preceq C' C)
    {x : V} {B : Block} (hx : x ∈ rho.honest)
    (hread : Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x T))
    (hne : B ≠ .genesis) :
    ∃ u s C iₛ, u ∈ rho.honest ∧ 1 ≤ s ∧ IsGateTick p c rho iₛ u s ∧
      gatePassedAt p c E rho iₛ ∧ gateResultAt p c E rho iₛ = some (some C) ∧
      SA.gateTime p.toParams s ≤ T ∧ Block.Preceq B C := by
  rw [arming_stable_read hs x T] at hread
  have hTb : timeIdx rho T ≤ timeIdx rho b₀ := arming_timeIdx_mono rho hT
  have hnotgen {X : Block} (hBX : Block.Preceq B X) : X ≠ .genesis := by
    rintro rfl
    exact hne (block_preceq_antisymm hBX (block_genesis_preceq B))
  rcases hsOrigin (timeIdx rho T) x hTb hx with hgen | ⟨q, hq, s, htick, hres⟩ |
      ⟨q, hq, hF⟩
  · exact absurd hgen (hnotgen hread)
  · have hsT := arming_tick_le hs htick hq
    obtain ⟨_, _, ⟨k, hk, hpass⟩, _⟩ := hcleanGate s x (hsT.trans hT) hx
    have hkq : k = q := fgsa_tick_unique E rho hs hk htick
    subst k
    exact arming_origin_of_clean hs hT hnonempty hcleanGate hne le_rfl
      ⟨q, hq, x, htick, (arming_enabled_of_pass htick hpass).2, hres⟩ hread
  · have hb := (hbelow q x (hq.trans hTb) hx).1
    rw [hF] at hread
    rcases hb with hgen | ⟨s, X, hX, _, hFX⟩
    · exact absurd hgen (hnotgen hread)
    · exact arming_origin_of_clean hs hT hnonempty hcleanGate hne hq hX
        (block_preceq_trans hread hFX)

end AvailableChain.FGSA.Run
end

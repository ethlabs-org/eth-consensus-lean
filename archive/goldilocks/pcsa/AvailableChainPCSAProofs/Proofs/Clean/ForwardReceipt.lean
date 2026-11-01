module
public import AvailableChainPCSAProofs.Proofs.Clean.InputTransport
public import AvailableChainPCSAProofs.Proofs.Clean.WalkInputs
public import AvailableChainPCSAProofs.Proofs.Clean.BodyRelayTime
public import AvailableChainPCSAProofs.Proofs.Clean.ResolutionDomain

public section

/-! C6 ForwardReceipt: concrete receipt and count support. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
private theorem forward_head_read (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (a k : Nat) (y : V) (s : Slot) (i : Fin p.n) (r : BlockId) (u : Time)
    (ha : a ≤ V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) (hak : a ≤ k)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho a y).st.base.votes) :
    (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (clock p (V2.D.Run.stateBefore E rho k y).st u).base.votes ∧
    GridCO.stampVote (clock p (V2.D.Run.stateBefore E rho k y).st u).base
      ⟨.seat s i, .head r⟩ < SA.freezeTime p.toParams s := by
  obtain ⟨row, hr⟩ := pcsa_head_stamp_lookup E rho a y ⟨.seat s i, .head r⟩ hm
  have hp : (V2.D.Run.stateBefore E rho a y).st.base.voteStamp <+:
      (clock p (V2.D.Run.stateBefore E rho k y).st u).base.voteStamp := by
    rw [pcsa_clock_headStamps]
    exact pcsa_headStamps_stateBefore_prefix E rho h.noRestart y hak
  refine ⟨?_, ?_⟩
  · rw [pcsa_clock_heads]
    exact pcsa_heads_stateBefore_mono E rho h.noRestart y hak hm
  · rw [pcsa_stampVote_eq_of_prefix _ _ _ row hp hr]
    exact pcsa_head_stamp_lt_of_index_cut E rho h.valid.toScheduleWellFormed h.noRestart
      a y s i r _ ha hm
private theorem forward_body_clock_stamp (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (k : Nat) (y : V) (B : Block) (u : Time)
    (hm : B ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks) :
    GridCO.stampBlock (clock p (V2.D.Run.stateBefore E rho k y).st u).base B =
      GridCO.stampBlock (V2.D.Run.stateBefore E rho k y).st.base B := by
  obtain ⟨row, hr⟩ := pcsa_body_stamp_lookup E rho k y B hm
  delta GridCO.stampBlock
  rw [pcsa_clock_bodyStamps, hr]
  rfl
/-- Genesis remains held with its initial first stamp. -/
theorem pcsa_genesis_body_stamp (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (hn : V2.D.NoRestart rho) (k : Nat) (y : V) :
    Block.genesis ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks ∧
      GridCO.stampBlock (V2.D.Run.stateBefore E rho k y).st.base .genesis = 0 := by
  have hz : Block.genesis ∈ (V2.D.Run.stateBefore E rho 0 y).st.base.blocks := by
    exact List.mem_singleton_self _
  refine ⟨pcsa_body_stateBefore_mono E rho hn y (Nat.zero_le k) hz, ?_⟩
  rw [pcsa_body_stamp_stateBefore_eq E rho hn y (Nat.zero_le k) .genesis hz]
  rfl
/-- In the delivery window: Early receipt gives an exact pre-freeze HEAD at the later read, or a
voter-list cap. -/
theorem pcsa_early_head_relay_frozen_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId) (u : Time)
    (hT : T₀ ≤ SA.earlyTime p.toParams s) (hc : SA.freezeTime p.toParams s ≤ cut)
    (hk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho a x).st.base.votes)
    (ht : GridCO.stampVote (V2.D.Run.stateBefore E rho a x).st.base
      ⟨.seat s i, .head r⟩ < SA.earlyTime p.toParams s) :
    ((⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (clock p (V2.D.Run.stateBefore E rho k y).st u).base.votes ∧
      GridCO.stampVote (clock p (V2.D.Run.stateBefore E rho k y).st u).base
        ⟨.seat s i, .head r⟩ < SA.freezeTime p.toParams s) ∨
    (GridCO.equivocates (headVotes p (clock p (V2.D.Run.stateBefore E rho k y).st u) (s + 1)) i =
      true ∧
      GridCO.equivocates (proposerVotes (clock p (V2.D.Run.stateBefore E rho k y).st u) (s + 1))
        i = true) := by
  have he : SA.earlyTime p.toParams s + E.Δ = SA.freezeTime p.toParams s := by
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + 2 * p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 3 * p.Δ
    ring
  have hpub : V2.PublicTime E (SA.earlyTime p.toParams s) := by
    refine ⟨4 * s + 2, ?_⟩
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + 2 * p.Δ = ((4 * s + 2 : Nat) : Int) * p.Δ
    push_cast
    ring
  have hz : 0 ≤ SA.earlyTime p.toParams s := by
    have hp := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    positivity
  have hg : SA.earlyTime p.toParams s + E.Δ ≤ SA.gateTime p.toParams s := by
    rw [he]
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hp := p.deltaPos
    linarith
  have relay := pcsa_head_before_public_cut_relay_late_floor E rho h hD (hT := hT) a
    (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) x y hx hy s i r _ u
    hpub hz (by rwa [he]) hg (by rw [he]) hm ht
  have lift (r : BlockId) (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      GridCO.lateVotes p.toParams.engine (actView (clock p
        (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) y).st
          u)) s) :
      (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
        (clock p (V2.D.Run.stateBefore E rho k y).st u).base.votes ∧
      GridCO.stampVote (clock p (V2.D.Run.stateBefore E rho k y).st u).base
        ⟨.seat s i, .head r⟩ < SA.freezeTime p.toParams s := by
    have hh := (List.mem_filter.mp (List.mem_filter.mp hm).1).1
    change _ ∈ (clock p _ u).base.votes at hh
    rw [pcsa_clock_heads] at hh
    exact forward_head_read E rho h _ k y s i r u (le_refl _) hk hh
  rcases relay with hm | hcap
  · exact Or.inl (lift r hm)
  · right
    obtain ⟨v, hv, w, hw, hne, hvi, hwi⟩ := (Gen.AC.Root.cap_pair _ i).mp hcap
    have hvl : GridCO.headLabel? v = some s :=
      beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp hv).1).2
    have hwl : GridCO.headLabel? w = some s :=
      beq_iff_eq.mp (List.mem_filter.mp (List.mem_filter.mp hw).1).2
    obtain ⟨rv, rfl⟩ := pcsa_count_head_shape v s i hvl hvi
    obtain ⟨rw, rfl⟩ := pcsa_count_head_shape w s i hwl hwi
    have mem (r : BlockId) (hh : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      GridCO.lateVotes p.toParams.engine (actView (clock p
        (V2.D.Run.stateBefore E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s)) y).st
          u)) s) :
      (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
        headVotes p (clock p (V2.D.Run.stateBefore E rho k y).st u) (s + 1) := by
      obtain ⟨hm, ht⟩ := lift r hh
      apply pcsa_headVotes_of_frozen
      · apply List.mem_filter.mpr
        exact ⟨hm, by
          change (some s == some (s + 1 - 1)) = true
          rw [Nat.add_sub_cancel]
          exact beq_self_eq_true _⟩
      · simpa only [Nat.add_sub_cancel] using ht
    refine ⟨(Gen.AC.Root.cap_pair _ i).mpr ⟨_, mem rv hv, _, mem rw hw, hne, hvi, hwi⟩, ?_⟩
    apply (Gen.AC.Root.cap_pair _ i).mpr
    refine ⟨_, List.mem_filter.mpr ⟨(lift rv hv).1, ?_⟩,
      _, List.mem_filter.mpr ⟨(lift rw hw).1, ?_⟩, hne, hvi, hwi⟩
    all_goals change (some s == some (s + 1 - 1)) = true
    all_goals rw [Nat.add_sub_cancel]; exact beq_self_eq_true _
/-- Early receipt gives an exact pre-freeze HEAD at the later read, or a voter-list cap. -/
theorem pcsa_early_head_relay_frozen (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (r : BlockId) (u : Time)
    (hc : SA.freezeTime p.toParams s ≤ cut)
    (hk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k)
    (hm : (⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (V2.D.Run.stateBefore E rho a x).st.base.votes)
    (ht : GridCO.stampVote (V2.D.Run.stateBefore E rho a x).st.base
      ⟨.seat s i, .head r⟩ < SA.earlyTime p.toParams s) :
    ((⟨.seat s i, .head r⟩ : GridCO.Wire p.n .root) ∈
      (clock p (V2.D.Run.stateBefore E rho k y).st u).base.votes ∧
      GridCO.stampVote (clock p (V2.D.Run.stateBefore E rho k y).st u).base
        ⟨.seat s i, .head r⟩ < SA.freezeTime p.toParams s) ∨
    (GridCO.equivocates (headVotes p (clock p (V2.D.Run.stateBefore E rho k y).st u) (s + 1)) i =
      true ∧
      GridCO.equivocates (proposerVotes (clock p (V2.D.Run.stateBefore E rho k y).st u) (s + 1))
        i = true) :=
  pcsa_early_head_relay_frozen_win E rho h (pcsa_strictFrom_of_healthy E rho hD 0) a k x y hx hy s
    i r u (pcsa_floor_early (pcsa_zero_le_proposal s)) hc hk hm ht
end AvailableChain.PCSA.Run

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}
/-- In the delivery window: A body resolved early arrives with a strict freeze stamp, including
genesis. -/
theorem pcsa_early_body_relay_frozen_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (B : Block) (v u : Time)
    (hT : T₀ ≤ SA.earlyTime p.toParams s) (hc : SA.freezeTime p.toParams s ≤ cut)
    (hk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k)
    (hm : B ∈ (clock p (V2.D.Run.stateBefore E rho a x).st v).base.blocks)
    (ht : GridCO.stampBlock (clock p (V2.D.Run.stateBefore E rho a x).st v).base B <
      SA.earlyTime p.toParams s) :
    B ∈ (clock p (V2.D.Run.stateBefore E rho k y).st u).base.blocks ∧
      GridCO.stampBlock (clock p (V2.D.Run.stateBefore E rho k y).st u).base B <
        SA.freezeTime p.toParams s := by
  rw [pcsa_clock_blocks] at hm
  rw [forward_body_clock_stamp E rho a x B v hm] at ht
  have he : SA.earlyTime p.toParams s + E.Δ = SA.freezeTime p.toParams s := by
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + 2 * p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 3 * p.Δ
    ring
  have hresult : B ∈ (V2.D.Run.stateBefore E rho k y).st.base.blocks ∧
      GridCO.stampBlock (V2.D.Run.stateBefore E rho k y).st.base B < SA.freezeTime p.toParams s
        := by
    by_cases hg : B = .genesis
    · subst B
      obtain ⟨hm, ht⟩ := pcsa_genesis_body_stamp E rho h.noRestart k y
      refine ⟨hm, ?_⟩
      rw [ht]
      have hp := p.deltaPos
      change 0 < 4 * p.Δ * (s : Int) + 3 * p.Δ
      positivity
    · have hpub : V2.PublicTime E (SA.earlyTime p.toParams s) := by
        refine ⟨4 * s + 2, ?_⟩
        rw [h.delta]
        change 4 * p.Δ * (s : Int) + 2 * p.Δ = ((4 * s + 2 : Nat) : Int) * p.Δ
        push_cast
        ring
      have hz : 0 ≤ SA.earlyTime p.toParams s := by
        have hp := p.deltaPos
        change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
        positivity
      have hh := pcsa_body_before_public_cut_relay_win E rho h hF hD (hT := hT) a
          k x y hx hy
        B _ hpub hz (by rwa [he]) (by rwa [he]) hg hm ht
      rwa [he] at hh
  refine ⟨?_, ?_⟩
  · rw [pcsa_clock_blocks]
    exact hresult.1
  · rw [forward_body_clock_stamp E rho k y B u hresult.1]
    exact hresult.2
/-- A body resolved early arrives with a strict freeze stamp, including genesis. -/
theorem pcsa_early_body_relay_frozen (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (B : Block) (v u : Time)
    (hc : SA.freezeTime p.toParams s ≤ cut)
    (hk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k)
    (hm : B ∈ (clock p (V2.D.Run.stateBefore E rho a x).st v).base.blocks)
    (ht : GridCO.stampBlock (clock p (V2.D.Run.stateBefore E rho a x).st v).base B <
      SA.earlyTime p.toParams s) :
    B ∈ (clock p (V2.D.Run.stateBefore E rho k y).st u).base.blocks ∧
      GridCO.stampBlock (clock p (V2.D.Run.stateBefore E rho k y).st u).base B <
        SA.freezeTime p.toParams s :=
  pcsa_early_body_relay_frozen_win E rho h hF (pcsa_strictFrom_of_healthy E rho hD 0) a k x y hx
    hy s B v u (pcsa_floor_early (pcsa_zero_le_proposal s)) hc hk hm ht
/-- In the delivery window: An early resolved HEAD enters the next voter support list, or its seat
is capped. -/
theorem pcsa_early_input_relay_support_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (B : Block) (v u : Time)
    (hT : T₀ ≤ SA.earlyTime p.toParams s) (hc : SA.freezeTime p.toParams s ≤ cut)
    (hk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k)
    (hm : (⟨.seat s i, .head B.root⟩ : GridCO.Wire p.n .root) ∈
      GridCO.earlyVotes p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) s)
    (hr : GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho a x).st v))
      ⟨.seat s i, .head B.root⟩ = some B) :
    ((⟨.seat s i, .head B.root⟩ : GridCO.Wire p.n .root) ∈
      headSupport p (clock p (V2.D.Run.stateBefore E rho k y).st u) (s + 1) ∧
      (⟨.seat s i, .head B.root⟩ : GridCO.Wire p.n .root) ∈
        proposerSupport (clock p (V2.D.Run.stateBefore E rho k y).st u) (s + 1) ∧
      GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho k y).st u))
        ⟨.seat s i, .head B.root⟩ = some B) ∨
    (GridCO.equivocates (headVotes p (clock p (V2.D.Run.stateBefore E rho k y).st u) (s + 1)) i =
      true ∧
      GridCO.equivocates (proposerVotes (clock p (V2.D.Run.stateBefore E rho k y).st u) (s + 1))
        i = true) := by
  obtain ⟨hm, htime⟩ := List.mem_filter.mp hm
  have hpool := (List.mem_filter.mp hm).1
  change _ ∈ (clock p (V2.D.Run.stateBefore E rho a x).st v).base.votes at hpool
  rw [pcsa_clock_heads] at hpool
  delta GridCO.resolvedBefore at htime
  rw [hr] at htime
  obtain ⟨⟨hslot, hvote⟩, hbody⟩ := Bool.and_eq_true_iff.mp htime |>.imp_left
    Bool.and_eq_true_iff.mp
  have hbs : B.slot ≤ s := of_decide_eq_true hslot
  have hvs : GridCO.stampVote (clock p (V2.D.Run.stateBefore E rho a x).st v).base
      ⟨.seat s i, .head B.root⟩ < SA.earlyTime p.toParams s := of_decide_eq_true hvote
  obtain ⟨row, hlookup⟩ := pcsa_head_stamp_lookup E rho a x ⟨.seat s i, .head B.root⟩ hpool
  have heq : GridCO.stampVote (clock p (V2.D.Run.stateBefore E rho a x).st v).base
      ⟨.seat s i, .head B.root⟩ = GridCO.stampVote (V2.D.Run.stateBefore E rho a x).st.base
      ⟨.seat s i, .head B.root⟩ := by
    delta GridCO.stampVote
    rw [pcsa_clock_headStamps, hlookup]
    rfl
  rw [heq] at hvs
  rcases pcsa_early_head_relay_frozen_win E rho h hD (hT := hT) a k x y hx hy s i B.root u hc hk
      hpool hvs with
    hh | hcap
  · have hbm := (List.mem_filter.mp (FGSA.resolvedHead_mem _ _ hr)).1
    obtain ⟨hbm', hbt'⟩ := pcsa_early_body_relay_frozen_win E rho h hF hD (hT := hT) a k x y hx hy
        s B v u
      hc hk hbm (of_decide_eq_true hbody)
    have hbm0 := hbm'
    rw [pcsa_clock_blocks] at hbm0
    have hr' := pcsa_resolved_head_of_held_body E rho h hF k y hy s i B u hbm0
    have hprop : (⟨.seat s i, .head B.root⟩ : GridCO.Wire p.n .root) ∈
        proposerSupport (clock p (V2.D.Run.stateBefore E rho k y).st u) (s + 1) := by
      apply List.mem_filter.mpr
      refine ⟨List.mem_filter.mpr ⟨hh.1, ?_⟩, ?_⟩
      · change (some s == some (s + 1 - 1)) = true
        rw [Nat.add_sub_cancel]
        exact beq_self_eq_true _
      · rw [hr']
        simpa only [Nat.add_sub_cancel] using decide_eq_true hbs
    refine Or.inl ⟨?_, hprop, hr'⟩
    delta headSupport
    apply List.mem_eraseDups.mpr
    apply List.mem_append_left
    apply List.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · apply List.mem_filter.mpr
      exact ⟨hh.1, by
          change (some s == some (s + 1 - 1)) = true
          rw [Nat.add_sub_cancel]
          exact beq_self_eq_true _⟩
    · delta GridCO.resolvedBefore
      rw [hr']
      simp only [Nat.add_sub_cancel]
      exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
        ⟨decide_eq_true hbs, decide_eq_true hh.2⟩, decide_eq_true hbt'⟩
  · exact Or.inr hcap
/-- An early resolved HEAD enters the next voter support list, or its seat is capped. -/
theorem pcsa_early_input_relay_support (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (a k : Nat) (x y : V) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (s : Slot) (i : Fin p.n) (B : Block) (v u : Time)
    (hc : SA.freezeTime p.toParams s ≤ cut)
    (hk : V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) ≤ k)
    (hm : (⟨.seat s i, .head B.root⟩ : GridCO.Wire p.n .root) ∈
      GridCO.earlyVotes p.toParams.engine
        (actView (clock p (V2.D.Run.stateBefore E rho a x).st v)) s)
    (hr : GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho a x).st v))
      ⟨.seat s i, .head B.root⟩ = some B) :
    ((⟨.seat s i, .head B.root⟩ : GridCO.Wire p.n .root) ∈
      headSupport p (clock p (V2.D.Run.stateBefore E rho k y).st u) (s + 1) ∧
      (⟨.seat s i, .head B.root⟩ : GridCO.Wire p.n .root) ∈
        proposerSupport (clock p (V2.D.Run.stateBefore E rho k y).st u) (s + 1) ∧
      GridCO.resolvedHead? (actView (clock p (V2.D.Run.stateBefore E rho k y).st u))
        ⟨.seat s i, .head B.root⟩ = some B) ∨
    (GridCO.equivocates (headVotes p (clock p (V2.D.Run.stateBefore E rho k y).st u) (s + 1)) i =
      true ∧
      GridCO.equivocates (proposerVotes (clock p (V2.D.Run.stateBefore E rho k y).st u) (s + 1))
        i = true) :=
  pcsa_early_input_relay_support_win E rho h hF (pcsa_strictFrom_of_healthy E rho hD 0) a k x y hx
    hy s i B v u (pcsa_floor_early (pcsa_zero_le_proposal s)) hc hk hm hr
end AvailableChain.PCSA.Run

end

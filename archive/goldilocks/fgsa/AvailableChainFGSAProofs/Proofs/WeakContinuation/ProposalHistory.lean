module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Epoch

public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

/-! WC J3, plan §6.9; DC proposal comparison prefix.
Blueprint 23 §11 restricts the finite maximum to the seed and labels through s−2. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

/-- WC J3, plan §6.9; DC comparison prefix: a finite compatible history has a maximum.
Only actual completed suffix results enter the set; the seed makes it nonempty. -/
theorem wc_historyMax
    (hS : V2.D.ScheduleWellFormed E rho)
    (hi : WCInv p c E rho w iStar rho.events.length) (r : Slot) :
    ∃ D, (D = w.QStar ∨ ∃ j x s,
      WCResult p c E rho w iStar rho.events.length j x s D ∧ s ≤ r) ∧
      Block.Preceq w.QStar D ∧
      ∀ j x s B, WCResult p c E rho w iStar rho.events.length j x s B →
        s ≤ r → Block.Preceq B D := by
  classical
  let candidates : Finset Block := (Finset.range rho.events.length).image
    (fun j => ((gateResultAt p c E rho j).getD none).getD .genesis)
  let genuine := candidates.filter (fun B => ∃ j x s,
    WCResult p c E rho w iStar rho.events.length j x s B ∧ s ≤ r)
  let pool := insert w.QStar genuine
  have hseed {j x s B}
      (hB : WCResult p c E rho w iStar rho.events.length j x s B) :
      Block.Preceq w.QStar B := by
    obtain ⟨C, hC, hQC, _⟩ := hi.nonempty j x s hB.afterCut hB.completed
      hB.honest (hB.enabled hS) hB.label
    have he : C = B := Option.some.inj (Option.some.inj (hC.symm.trans hB.value))
    exact he ▸ hQC
  have hmem {j x s B}
      (hB : WCResult p c E rho w iStar rho.events.length j x s B) (hs : s ≤ r) :
      B ∈ genuine := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hB.completed, ?_⟩,
      j, x, s, hB, hs⟩
    rw [hB.value]
    rfl
  have hcompatible {j k x y s t B C}
      (hB : WCResult p c E rho w iStar rho.events.length j x s B)
      (hC : WCResult p c E rho w iStar rho.events.length k y t C) :
      Block.Compatible B C := by
    rcases lt_trichotomy s t with h | h | h
    · exact block_compatible_of_common (hi.ordered j k x y s t B C hB hC h)
        (block_preceq_refl C)
    · subst t
      exact hi.sameLabel j k x y s B C hB hC
    · exact block_compatible_of_common (block_preceq_refl B)
        (hi.ordered k j y x t s C B hC hB h)
  have hpool : ∀ B ∈ pool, ∀ C ∈ pool, Block.Compatible B C := by
    intro B hB C hC
    rcases Finset.mem_insert.mp hB with rfl | hB
    · rcases Finset.mem_insert.mp hC with rfl | hC
      · exact block_compatible_of_common (block_preceq_refl _) (block_preceq_refl _)
      · obtain ⟨j, x, s, hC, _⟩ := (Finset.mem_filter.mp hC).2
        exact block_compatible_of_common (hseed hC) (block_preceq_refl _)
    · rcases Finset.mem_insert.mp hC with rfl | hC
      · obtain ⟨j, x, s, hB, _⟩ := (Finset.mem_filter.mp hB).2
        exact block_compatible_of_common (block_preceq_refl _) (hseed hB)
      · obtain ⟨j, x, s, hB, _⟩ := (Finset.mem_filter.mp hB).2
        obtain ⟨k, y, t, hC, _⟩ := (Finset.mem_filter.mp hC).2
        exact hcompatible hB hC
  obtain ⟨D, hD, hmax⟩ := deepest_of_compatible pool
    ⟨w.QStar, Finset.mem_insert_self ..⟩ hpool
  refine ⟨D, ?_, hmax _ (Finset.mem_insert_self ..), ?_⟩
  · rcases Finset.mem_insert.mp hD with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_filter.mp h).2
  · intro j x s B hB hs
    exact hmax B (Finset.mem_insert_of_mem (hmem hB hs))

/-- WC J3, plan §6.9; DC slot separation: gates read before v_s have label at most s−2. -/
theorem wc_gateLabel_beforeVote (r s : Slot)
    (h : SA.gateTime p.toParams r ≤ SA.voteTime p.toParams s) : r + 2 ≤ s := by
  by_contra hn
  have hsr : s ≤ r + 1 := by
    simp only [Slot] at hn ⊢
    omega
  have hcast : (s : Time) ≤ (r : Time) + 1 := by exact_mod_cast hsr
  have hd := p.deltaPos
  have hscaled := mul_le_mul_of_nonneg_left hcast
    (mul_nonneg (by decide : (0 : Time) ≤ 4) hd.le)
  change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤ 4 * p.Δ * (s : Time) + p.Δ at h
  nlinarith

/-- WC J3, plan §6.9; DC selected-source history: high rows at the compared reads
have sources below the maximum. The pre-cut branch uses the seed bound only. -/
theorem wc_highSource_beforeVote
    (hi : WCInv p c E rho w iStar rho.events.length)
    (s : Slot) (D : Block) (hseedD : Block.Preceq w.QStar D)
    (hmax : ∀ j x r B, WCResult p c E rho w iStar rho.events.length j x r B →
      r ≤ s - 2 → Block.Preceq B D)
    {i j : Nat} {y : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId}
    {K : SimplexFG.FGBlock (Fin p.n)} (hiN : i ≤ rho.events.length) (hji : j < i)
    (hbefore : ∀ k < i, ∀ event, rho.events[k]? = some event →
      event.time ≤ SA.voteTime p.toParams s)
    (hrow : HonestRowAt p c E rho j y r a)
    (hentry : namedEntry a.payload.height_pair = some e) (hhigh : w.M + 1 ≤ e.1)
    (hsource : actionSourceFG p c E rho y r = some (some K)) :
    Block.Preceq (eraseFG K) D := by
  by_cases hjcut : j < iStar
  · obtain ⟨C, hC, _, hCQ⟩ := hi.preCutHigh j y r a e hjcut hrow hentry hhigh
    have he : C = K := Option.some.inj (Option.some.inj (hC.symm.trans hsource))
    exact block_preceq_trans (he ▸ hCQ) hseedD
  · obtain ⟨B, hB, hKB⟩ := hi.suffixSources j y r K (Nat.le_of_not_lt hjcut)
      (hji.trans_le hiN) hrow.1 hrow.2.1 hsource
    have hlabel := wc_gateLabel_beforeVote (r * p.R) s (hbefore j hji _ hrow.2.1)
    have hr : r * p.R ≤ s - 2 := by
      simp only [Slot] at hlabel ⊢
      omega
    exact block_preceq_trans hKB (hmax j y (r * p.R) B hB hr)

/-- WC J3, plan §6.9; DC retrospective HEAD: enlarge only the covered prefix. -/
private theorem wc_headRead_of_prefix {i : Nat} {x : V} {s : Slot} {A B : Block}
    (h : WCHeadRead p c E rho i x s B) (hAB : Block.Preceq A B) :
    WCHeadRead p c E rho i x s A := by
  exact ⟨h.event, block_preceq_trans hAB h.covers,
    fun C hCA => h.path C (block_preceq_trans hCA hAB), h.receipts⟩

omit [DecidableEq V] in
/-- WC J3, plan §6.9; DC prefix agreement: a later tick is after the selected cut. -/
theorem wc_cut_le_laterTick
    (hs : V2.D.ScheduleWellFormed E rho) {a t : Time} {j : Nat} {x : V}
    (he : rho.events[j]? = some (.tick x t)) (hat : a < t) :
    afterTicksIdx rho a ≤ j := by
  refine (preIdx_le_afterTicksIdx E rho hs a).2.trans ?_
  change (rho.events.filter (fun e => decide (e.time ≤ a))).length ≤ j
  have hbound : a ≤ t - 1 := by
    simp only [Time] at hat ⊢
    omega
  have hmono := V2.D.Engine.read_length_mono (rho := rho) a (t - 1) hbound
  have hidx := (V2.D.Engine.index_lt_read_length_iff hs (t - 1) he).not.mpr
    (by simp : ¬ t ≤ t - 1)
  exact hmono.trans (Nat.le_of_not_lt hidx)

/-- WC J3, plan §6.9; DC comparison prefix: previous HEADs cover every maximum member.
At the first eligible slot, the source seed supplies the pending HEAD read. -/
theorem wc_history_previousHeads [Fintype V]
    (hs : V2.D.ScheduleWellFormed E rho) (hdelta : E.Δ = p.Δ)
    (hV : V2.D.ExecutionValid E rho)
    (hpart : ∀ t, SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon →
      (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card)
    (hseed : WCSeed p c E rho w iStar)
    (hi : WCInv p c E rho w iStar rho.events.length)
    (s : Slot) (D : Block) (hstart : w.u + 2 ≤ s)
    (hgate : SA.gateTime p.toParams s ≤ rho.horizon)
    (hmember : D = w.QStar ∨ ∃ j x r,
      WCResult p c E rho w iStar rho.events.length j x r D ∧ r ≤ s - 2) :
    ∀ y ∈ rho.honest,
      joinedAt p E rho y (s - 1) (SA.voteTime p.toParams (s - 1)) →
      ∃ k, WCHeadRead p c E rho k y (s - 1) D := by
  intro y hy hJ
  have hs2 : 2 ≤ s := by
    simp only [Slot] at hstart ⊢
    omega
  have hlabels : s - 2 + 1 = s - 1 := by
    simp only [Slot] at hs2 ⊢
    omega
  by_cases hfirst : s = w.u + 2
  · have hD : D = w.QStar := by
      rcases hmember with h | ⟨j, x, r, hresult, hr⟩
      · exact h
      · have hlabel := hresult.label
        simp only [hfirst, Slot] at hr hlabel
        omega
    subst D
    obtain ⟨k, _, hhead⟩ := hseed.nextHeads y hy
    refine ⟨k, ?_⟩
    have he : s - 1 = w.u + 1 := by
      simp only [Slot] at hfirst ⊢
      omega
    exact he.symm ▸ hhead
  · have hq : w.u < s - 2 := by
      simp only [Slot] at hstart hfirst ⊢
      omega
    have hd := p.deltaPos
    have htime : SA.gateTime p.toParams w.u < SA.gateTime p.toParams (s - 2) := by
      change 4 * p.Δ * (w.u : Time) + 6 * p.Δ <
        4 * p.Δ * ((s - 2 : Nat) : Time) + 6 * p.Δ
      have hcast : (w.u : Time) < ((s - 2 : Nat) : Time) := Nat.cast_lt.mpr hq
      nlinarith
    have hqtime : SA.gateTime p.toParams (s - 2) ≤ rho.horizon := by
      refine le_trans ?_ hgate
      change 4 * p.Δ * ((s - 2 : Nat) : Time) + 6 * p.Δ ≤
        4 * p.Δ * (s : Time) + 6 * p.Δ
      have hcast : ((s - 2 : Nat) : Time) ≤ (s : Time) :=
        Nat.cast_le.mpr (Nat.sub_le s 2)
      nlinarith
    have hcovered : SA.voteTime p.toParams (w.u + 1) ≤
        SA.gateTime p.toParams (s - 2) := by
      have hcast : ((w.u + 1 : Nat) : Time) ≤ (s - 2 : Nat) :=
        Int.ofNat_le.mpr (Nat.succ_le_of_lt hq)
      change 4 * p.Δ * ((w.u + 1 : Nat) : Time) + p.Δ ≤
        4 * p.Δ * ((s - 2 : Nat) : Time) + 6 * p.Δ
      nlinarith
    obtain ⟨z, j, hz, hG, _⟩ := wc_joined_gate_witness hV hdelta (s - 2)
      (hpart _ hcovered hqtime) hqtime
    have hj := hG.1
    have hjcut : iStar ≤ j := by
      rw [hseed.cut]
      exact wc_cut_le_laterTick hs hj htime
    have hjlength := (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨C, hC, hQC, _⟩ := hi.nonempty j z (s - 2) hjcut hjlength hz hG hq
    have hresult : WCResult p c E rho w iStar rho.events.length j z (s - 2) C :=
      ⟨hz, hjcut, hjlength, hq, hj, hC⟩
    rcases hmember with h | ⟨k, x, r, hD, hr⟩
    · subst D
      obtain ⟨k, _, hk⟩ := hi.retrospective j z (s - 2) C hresult y hy (hlabels.symm ▸ hJ)
      exact ⟨k, hlabels ▸ wc_headRead_of_prefix hk hQC⟩
    · rcases Nat.lt_or_eq_of_le hr with hr | rfl
      · have hDC := hi.ordered k j x z r (s - 2) D C hD hresult hr
        obtain ⟨l, _, hl⟩ := hi.retrospective j z (s - 2) C hresult y hy (hlabels.symm ▸ hJ)
        exact ⟨l, hlabels ▸ wc_headRead_of_prefix hl hDC⟩
      · obtain ⟨l, _, hl⟩ := hi.retrospective k x (s - 2) D hD y hy (hlabels.symm ▸ hJ)
        exact ⟨l, hlabels ▸ hl⟩


end AvailableChain.FGSA.Run
end

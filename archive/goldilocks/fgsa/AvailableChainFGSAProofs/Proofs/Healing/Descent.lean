module
public import AvailableChainFGSAClaims.Statements.ChannelProps
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainFGSAProofs.Proofs.Shared.Roots

public section

/-! H-DESCENT (H.13): source timing, restricted descent, first failure, and
causal finality sources. The descent is coverage-aware: the view must hold
only the earlier sources that extend the kept block (B18). No lemma here
reads RExcl or TDel (B15, B18). -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21:2640–2653, 2704; plan S25, H-DESCENT/D1 (ruling B16).
DC: SAME earlier-action order; INTENTIONAL FG action offset of 6Δ.
An earlier source row is an earlier event, so its gate time is at most the
time of every later event. This is the base form for every duty read. -/
theorem healing_source_gate (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {C : FGBlock (Fin p.n)} {s : Slot} {ev}
    (hsource : SourceBefore p c E rho i C s) (hi : rho.events[i]? = some ev) :
    SA.gateTime p.toParams s ≤ ev.time := by
  obtain ⟨j, y, r, a, hji, ha, _hc, rfl⟩ := hsource
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp ha.2.1
  have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
  rw [hie, hje] at hk
  exact V2.D.Engine.time_le_of_key_le _ _ hk

/-- Blueprint 21:2640–2653, 2704; plan S25, H-DESCENT/D1 (ruling B16).
DC: SAME earlier-action order; INTENTIONAL FG action offset of 6Δ.
At a freeze or release read of slot u an earlier source has label below u.
At a gate read of slot u its label is at most u. -/
theorem healing_source_read (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {C : FGBlock (Fin p.n)} {s u : Slot} {t : Time}
    (hsource : SourceBefore p c E rho i C s)
    (hi : rho.events[i]? = some (.tick x t)) :
    (t = SA.freezeTime p.toParams u → s + 1 ≤ u) ∧
      (t = SA.releaseTime p.toParams u → s + 1 ≤ u) ∧
      (t = SA.gateTime p.toParams u → s ≤ u) := by
  have h := healing_source_gate p c E rho hs hsource hi
  change SA.gateTime p.toParams s ≤ t at h
  have hd := p.deltaPos
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_⟩ <;> subst ht
  · change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * (u : Int) + 3 * p.Δ at h
    have hlt : (s : Int) < u := by
      by_contra hn
      have hus : (u : Int) ≤ s := Int.not_lt.mp hn
      nlinarith
    exact_mod_cast hlt
  · change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * (u : Int) + 5 * p.Δ at h
    have hlt : (s : Int) < u := by
      by_contra hn
      have hus : (u : Int) ≤ s := Int.not_lt.mp hn
      nlinarith
    exact_mod_cast hlt
  · change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * (u : Int) + 6 * p.Δ at h
    have hle : (s : Int) ≤ u := by
      by_contra hn
      have hus : (u : Int) < s := Int.not_le.mp hn
      nlinarith
    exact_mod_cast hle

/-- ROOT-DIGEST W2b. FG compatibility follows from compatibility of the erased blocks. -/
private theorem desc_compat_of_erase {A B : FGBlock (Fin p.n)}
    (h : Block.Compatible (eraseFG A) (eraseFG B)) :
    FGBlock.Preceq A B ∨ FGBlock.Preceq B A := by
  change (Block.preceq (eraseFG A) (eraseFG B) ||
    Block.preceq (eraseFG B) (eraseFG A)) = true at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Or.inl (eraseFG_preceq_iff.mp h)
  · exact Or.inr (eraseFG_preceq_iff.mp h)

/-- Erased compatibility is symmetric. -/
private theorem desc_compat_symm {A B : Block} (h : Block.Compatible A B) :
    Block.Compatible B A := by
  change (Block.preceq A B || Block.preceq B A) = true at h
  change (Block.preceq B A || Block.preceq A B) = true
  rw [Bool.or_comm]
  exact h

/-- A quorum of member-wise rows has a choice function. -/
private theorem desc_choose_rows {Q : Finset (Fin p.n)}
    {P : Fin p.n → FGBlock (Fin p.n) → Row (Fin p.n) → Prop}
    (h : ∀ k ∈ Q, ∃ W a, P k W a) :
    ∃ rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n),
      ∀ k ∈ Q, P k (rows k).1 (rows k).2 := by
  classical
  refine ⟨fun k => if hk : k ∈ Q then
      (Classical.choose (h k hk), Classical.choose (Classical.choose_spec (h k hk)))
    else (.genesis, ⟨k, .empty, none⟩), ?_⟩
  intro k hk
  simp only [hk, ↓reduceDIte]
  exact Classical.choose_spec (Classical.choose_spec (h k hk))

/-- ROOT-DIGEST W2b. A crossed height of a held block has an earlier honest source at its entry. -/
private theorem desc_cross_source (hroots : NamedRootCollisionFree p c E rho) (origin : RQCOrigin
    p c E rho) {i : Nat} {x : V}
    {W : FGBlock (Fin p.n)} {m : Nat} (hx : x ∈ rho.honest)
    (hW : W ∈ (storeAt p c E rho i x).fg.TF) (hm : 1 ≤ m)
    (hmW : m < (heightView p W).h) :
    ∃ Y, FGBlock.Preceq Y W ∧ (heightView p Y).h = m ∧
      ∃ K s, SourceBefore p c E rho i K s ∧ (heightView p K).h = m ∧
        (heightView p K).T_h = Y := by
  obtain ⟨Y, hYW, hYm, Q, hQ, hrows⟩ :=
    (fgCertificateLaws p).height.height_crossing W m hm hmW
  obtain ⟨rows, hr⟩ := desc_choose_rows p hrows
  obtain ⟨h1, -, -⟩ := origin i x W hx hW
  obtain ⟨k, hk, y, r, wire, ⟨j, hj, hrow⟩, -, -, K, G, hK, hn, -⟩ :=
    h1 m Y Q rows hm hmW hYW hYm hQ hr
  obtain ⟨-, -, -, hmatch⟩ := hr k hk
  refine ⟨Y, hYW, hYm, K, r * p.R, ⟨j, y, r, wire, hj, hrow, hK, rfl⟩, ?_⟩
  cases hp : (rows k).2.height_pair with
  | empty =>
    rw [hp] at hmatch
    exact absurd hmatch Bool.false_ne_true
  | vote h e t =>
    rw [hp] at hmatch hn
    obtain ⟨rfl, rfl⟩ : h = m ∧ e = Y.root := of_decide_eq_true hmatch
    obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hn)
    exact ⟨h1.symm, rootScope_eq hroots (rootScope_entry (rootScope_source hrow.1 hK))
      (rootScope_ancestor (rootScope_store hx hW) hYW) h2.symm⟩

/-- ROOT-DIGEST W2b. A justified entry of a held block has an earlier honest source. -/
private theorem desc_just_source (hroots : NamedRootCollisionFree p c E rho) (origin : RQCOrigin p
    c E rho) {i : Nat} {x : V}
    {W : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hW : W ∈ (storeAt p c E rho i x).fg.TF) (hj : (heightView p W).h_j ≠ 0) :
    ∃ K s, SourceBefore p c E rho i K s ∧ (heightView p K).h = (heightView p W).h_j ∧
      (heightView p K).T_h = (heightView p W).J := by
  obtain ⟨Q, hQ, hrows⟩ := (fgCertificateLaws p).height.justification_certificate W hj
  obtain ⟨rows, hr⟩ := desc_choose_rows p hrows
  obtain ⟨-, h2, -⟩ := origin i x W hx hW
  obtain ⟨k, hk, y, r, wire, ⟨j, hjl, hrow⟩, -, -, K, G, hK, hn, -⟩ := h2 Q rows hj hQ hr
  obtain ⟨-, -, -, hpair⟩ := hr k hk
  rw [hpair] at hn
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hn)
  exact ⟨K, r * p.R, ⟨j, y, r, wire, hjl, hrow, hK, rfl⟩, h1.symm,
    rootScope_eq hroots (rootScope_entry (rootScope_source hrow.1 hK))
      (rootScope_justified (rootScope_store hx hW)) h2.symm⟩

/-- ROOT-DIGEST W2b. A finalized entry of a held block has an earlier honest target source. -/
private theorem desc_final_source (hroots : NamedRootCollisionFree p c E rho) (origin : RQCOrigin
    p c E rho) {i : Nat} {x : V}
    {W : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hW : W ∈ (storeAt p c E rho i x).fg.TF) (hF : (finalityView p W).F ≠ .genesis) :
    ∃ K s, SourceBefore p c E rho i K s ∧
      (heightView p K).h = (finalityView p W).h_F ∧
      (heightView p K).T_h = (finalityView p W).F := by
  obtain ⟨-, -, h3⟩ := origin i x W hx hW
  obtain ⟨C0, -, hJ, hj, Q, rows, -, hr, k, hk, y, r, wire, ⟨j, hjl, hrow⟩, -, -,
    K, G, hK, hn, -⟩ := h3 hF
  obtain ⟨-, -, -, hpair⟩ := hr k hk
  rw [hpair] at hn
  obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hn)
  refine ⟨K, r * p.R, ⟨j, y, r, wire, hjl, hrow, hK, rfl⟩, h1.symm.trans hj, ?_⟩
  exact rootScope_eq hroots (rootScope_entry (rootScope_source hrow.1 hK))
    (rootScope_finalized (rootScope_store hx hW)) (h2.symm.trans (congrArg FGBlock.root hJ))

/-- ROOT-DIGEST W2b. Blueprint 21:2689–2716, 2767–2813 (fj.descent.v3); plan S25, H-DESCENT/D3
(rulings B1, B18). DC: INTENTIONAL FJ contest exclusion; DC removes the J-root
case with an NJ height (21:2742–2747). Restricted coverage-aware descent at one
read. A block C of the view X is kept, or an earlier honest source conflicts
with C at a height at least that of C, or two earlier honest sources share a
height above C with different entries. The view must hold only the earlier
sources above F that extend C and are higher than C, or F must cover them.
It needs no reset witness; H.13/H.14 apply it under H0Reset. -/
theorem healing_descent (hroots : NamedRootCollisionFree p c E rho) (xing : RXing p c E rho)
    (origin : RQCOrigin p c E rho)
    {i : Nat} {x : V} {X : Finset (FGBlock (Fin p.n))} {C : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hX : X ⊆ (storeAt p c E rho i x).fg.TF) (hC : C ∈ X)
    (cover : ∀ K s, SourceBefore p c E rho i K s →
      FGBlock.Preceq (storeAt p c E rho i x).fg.F K → FGBlock.Preceq C K →
      (heightView p C).h < (heightView p K).h →
      K ∈ X ∨ FGBlock.Preceq K (storeAt p c E rho i x).fg.F) :
    KeepOrCause p c E rho i x X C := by
  have hI : KitFG.FGStoreInvariant (heightView p) (finalityView p)
      (storeAt p c E rho i x).fg := (cstoreInv_stateBefore E rho i x).fg
  have hH := (fgCertificateLaws p).height
  have hJL := fgJustificationLaws p
  have hCT : C ∈ (storeAt p c E rho i x).fg.TF := hX hC
  set st := (storeAt p c E rho i x).fg with hst
  have hCH : (heightView p C).h ≤ st.h_max := by
    rw [hI.hmax]
    exact le_sup_of_le_left (Finset.le_sup (f := fun B => (heightView p B).h) hCT)
  have cause : ∀ K s, SourceBefore p c E rho i K s →
      ¬ (FGBlock.Preceq C K ∨ FGBlock.Preceq K C) →
      (heightView p C).h ≤ (heightView p K).h → KeepOrCause p c E rho i x X C :=
    fun K s hK hn hh => Or.inr (Or.inl ⟨K, s, hK, fun h => hn (desc_compat_of_erase p h), hh⟩)
  have keep : ∀ W ∈ X, FGBlock.Preceq C W →
      (R_at p c E rho i x).lo ≤ (heightView p W).h →
      FGBlock.Preceq (R_at p c E rho i x).F C → FGBlock.Preceq (R_at p c E rho i x).Z C →
      KeepOrCause p c E rho i x X C :=
    fun W hW hCW hlo hF hZ => Or.inl (Or.inr (Or.inl
      ((KitFG.mem_filteredFromView (heightView p) (R_at p c E rho i x) X C).2
        ⟨hC, hF, hZ, W, hW, hCW, hlo⟩)))
  by_cases hCF : FGBlock.Preceq C st.F
  · exact Or.inl (Or.inr (Or.inr hCF))
  by_cases hFC : FGBlock.Preceq st.F C
  swap
  · -- IF.3(c): a conflicting F has a target source at least as high as C.
    obtain ⟨D, hD, hDF⟩ := hI.Fcar
    have hle : (heightView p C).h ≤ (finalityView p D).h_F := by
      by_contra hlt
      exact hFC (xing i i x x D C hx le_rfl hD hDF ⟨hx, hCT⟩ (Nat.lt_of_not_le hlt))
    have hFg : (finalityView p D).F ≠ .genesis := by
      rw [hDF]
      intro h
      exact hFC (h ▸ KitFG.genesis_preceq C)
    obtain ⟨K, s, hK, hh, hT⟩ := desc_final_source (hroots := hroots) p c E rho origin hx hD hFg
    have hFK : FGBlock.Preceq st.F K := by
      have he := hH.entry_preceq K
      rwa [hT, hDF] at he
    refine cause K s hK ?_ (by rw [hh]; exact hle)
    rintro (h | h)
    · rcases KitFG.preceq_total_of_common hFK h with h' | h'
      · exact hFC h'
      · exact hCF h'
    · exact hFC (KitFG.preceq_trans hFK h)
  obtain ⟨C1, hC1, -, hj1, hJ1⟩ := hI.pair.1
  have hJz : st.h_j = 0 → st.J = .genesis := fun hz => by
    rw [hJ1]
    exact hJL.J_zero C1 (by rw [← hj1]; exact hz)
  have hJh : st.h_j ≠ 0 → (heightView p st.J).h = st.h_j := fun hnz => by
    rw [hJ1, hj1]
    exact hJL.J_height C1 (by rw [← hj1]; exact hnz)
  have hJe : (heightView p st.J).T_h = st.J := by
    rw [hJ1]
    exact hJL.J_entry C1
  have hJent : st.h_j ≠ 0 → ∃ K s, SourceBefore p c E rho i K s ∧
      (heightView p K).h = st.h_j ∧ (heightView p K).T_h = st.J := fun hnz => by
    obtain ⟨K, s, hK, hh, hT⟩ :=
      desc_just_source (hroots := hroots) p c E rho origin hx hC1 (by rw [← hj1]; exact hnz)
    exact ⟨K, s, hK, by rw [hh, hj1], by rw [hT, hJ1]⟩
  cases hct : (R_at p c E rho i x).contest with
  | true =>
    have hct' := hct
    change (decide (st.h_max = st.h_j + 1) && decide (∃ W ∈ st.TF,
      FGBlock.Preceq st.F W ∧ (heightView p W).h = st.h_max ∧
        ¬ FGBlock.Preceq st.J W)) = true at hct'
    obtain ⟨htop, W₀, hW₀, _hFW₀, hh₀, hn₀⟩ : st.h_max = st.h_j + 1 ∧ ∃ W ∈ st.TF,
        FGBlock.Preceq st.F W ∧ (heightView p W).h = st.h_max ∧ ¬ FGBlock.Preceq st.J W := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hct'
    have hZ : (R_at p c E rho i x).Z = st.F := by
      change (if (R_at p c E rho i x).rootIsJ then _ else _) = _
      have hr : (R_at p c E rho i x).rootIsJ = false := by
        change (decide (st.h_max = st.h_j + 1) && !(R_at p c E rho i x).contest) = false
        rw [hct]
        simp
      rw [hr]
      rfl
    have hlo : (R_at p c E rho i x).lo = st.h_max := by
      change (if (R_at p c E rho i x).contest then _ else _) = _
      rw [hct]
      rfl
    by_cases hCtop : st.h_max ≤ (heightView p C).h
    · exact keep C hC (KitFG.preceq_refl C) (by rw [hlo]; exact hCtop) hFC
        (by rw [hZ]; exact hFC)
    have hjnz : st.h_j ≠ 0 := by
      intro hz
      exact hn₀ (by rw [hJz hz]; exact KitFG.genesis_preceq W₀)
    obtain ⟨Y, hYW, hYh, K2, s2, hK2, hK2h, hK2T⟩ :=
      desc_cross_source (hroots := hroots) p c E rho origin hx hW₀ (Nat.one_le_iff_ne_zero.mpr hjnz)
        (by rw [hh₀, htop]; exact Nat.lt_succ_self _)
    obtain ⟨K1, s1, hK1, hK1h, hK1T⟩ := hJent hjnz
    have hYe : (heightView p Y).T_h = Y := by
      rw [← hK2T]
      exact hH.entry_idem K2
    have hJY : ¬ (FGBlock.Preceq st.J Y ∨ FGBlock.Preceq Y st.J) := by
      rintro (h | h)
      · exact hn₀ (KitFG.preceq_trans h hYW)
      · have hp := hH.entry_plateau h (by rw [hYh, hJh hjnz])
        rw [hYe, hJe] at hp
        exact hn₀ (hp ▸ hYW)
    by_cases hlt : (heightView p C).h < st.h_j
    · refine Or.inr (Or.inr ⟨K1, K2, s1, s2, hK1, hK2, hK1h.trans hK2h.symm,
        by rw [hK1h]; exact hlt, ?_⟩)
      rw [hK1T, hK2T]
      intro hr
      exact hJY (Or.inl (by
        have he := viewRootInj_TF p _ (cstoreInv_stateBefore E rho i x) _ _
          ⟨st.J, J_mem p _ (cstoreInv_stateBefore E rho i x), KitFG.preceq_refl _⟩
          ⟨W₀, hW₀, hYW⟩ hr
        rw [he]
        exact KitFG.preceq_refl Y))
    have hCe : (heightView p C).h = st.h_j := by simp only [Height] at *; omega
    have entry_of : ∀ K, (FGBlock.Preceq C K ∨ FGBlock.Preceq K C) →
        (heightView p K).h = st.h_j → (heightView p C).T_h = (heightView p K).T_h := by
      rintro K (h | h) hk
      · exact hH.entry_plateau h (hCe.trans hk.symm)
      · exact (hH.entry_plateau h (hk.trans hCe.symm)).symm
    by_cases c1 : FGBlock.Preceq C K1 ∨ FGBlock.Preceq K1 C
    · by_cases c2 : FGBlock.Preceq C K2 ∨ FGBlock.Preceq K2 C
      · exfalso
        have e1 := entry_of K1 c1 hK1h
        have e2 := entry_of K2 c2 hK2h
        rw [hK1T] at e1
        rw [hK2T] at e2
        exact hJY (Or.inl (by rw [← e1, e2]; exact KitFG.preceq_refl Y))
      · exact cause K2 s2 hK2 c2 (by simp only [Height] at *; omega)
    · exact cause K1 s1 hK1 c1 (by simp only [Height] at *; omega)
  | false =>
    have hlo : (R_at p c E rho i x).lo = st.h_max - 1 := by
      change (if (R_at p c E rho i x).contest then _ else _) = _
      rw [hct]
      rfl
    have hZC : FGBlock.Preceq (R_at p c E rho i x).Z C ∨ KeepOrCause p c E rho i x X C := by
      by_cases htop : st.h_max = st.h_j + 1
      · have hZ : (R_at p c E rho i x).Z = st.J := by
          change (if (R_at p c E rho i x).rootIsJ then _ else _) = _
          have hr : (R_at p c E rho i x).rootIsJ = true := by
            change (decide (st.h_max = st.h_j + 1) && !(R_at p c E rho i x).contest) = true
            rw [hct]
            simp [htop]
          rw [hr]
          rfl
        by_cases hCJ : FGBlock.Preceq C st.J
        · exact Or.inr (Or.inl (Or.inl (by rw [hZ]; exact hCJ)))
        by_cases hJC : FGBlock.Preceq st.J C
        · exact Or.inl (by rw [hZ]; exact hJC)
        right
        have hCj : (heightView p C).h ≤ st.h_j := by
          by_contra hgt
          have hCt : (heightView p C).h = st.h_max := by simp only [Height] at *; omega
          have hc : (R_at p c E rho i x).contest = true := by
            change (decide (st.h_max = st.h_j + 1) && decide (∃ W ∈ st.TF,
              FGBlock.Preceq st.F W ∧ (heightView p W).h = st.h_max ∧
                ¬ FGBlock.Preceq st.J W)) = true
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨htop, C, hCT, hFC, hCt, hJC⟩
          rw [hct] at hc
          exact Bool.false_ne_true hc
        have hjnz : st.h_j ≠ 0 := fun hz =>
          hJC (by rw [hJz hz]; exact KitFG.genesis_preceq C)
        obtain ⟨K1, s1, hK1, hK1h, hK1T⟩ := hJent hjnz
        have hJK : FGBlock.Preceq st.J K1 := by
          have he := hH.entry_preceq K1
          rwa [hK1T] at he
        refine cause K1 s1 hK1 ?_ (by simp only [Height] at *; omega)
        rintro (h | h)
        · rcases KitFG.preceq_total_of_common hJK h with h' | h'
          · exact hJC h'
          · exact hCJ h'
        · exact hJC (KitFG.preceq_trans hJK h)
      · have hZ : (R_at p c E rho i x).Z = st.F := by
          change (if (R_at p c E rho i x).rootIsJ then _ else _) = _
          have hr : (R_at p c E rho i x).rootIsJ = false := by
            change (decide (st.h_max = st.h_j + 1) && !(R_at p c E rho i x).contest) = false
            simp [htop]
          rw [hr]
          rfl
        exact Or.inl (by rw [hZ]; exact hFC)
    rcases hZC with hZC | hk
    swap
    · exact hk
    by_cases hw : st.h_max - 1 ≤ (heightView p C).h
    · exact keep C hC (KitFG.preceq_refl C) (by rw [hlo]; exact hw) hFC hZC
    obtain ⟨W₀, hW₀, hsup⟩ :=
      Finset.exists_mem_eq_sup st.TF ⟨_, hI.gen⟩ (fun W => (heightView p W).h)
    have hC1 := hH.one_le_h C
    have hw₀ : (heightView p W₀).h = st.h_max := by
      have hm := hI.hmax
      rw [hsup] at hm
      simp only [Height] at *
      omega
    obtain ⟨-, -, -, K2, s2, hK2, hK2h, -⟩ :=
      desc_cross_source (hroots := hroots) p c E rho origin hx hW₀ (m := st.h_max - 1)
        (by simp only [Height] at *; omega) (by simp only [Height] at *; omega)
    by_cases hc : FGBlock.Preceq C K2 ∨ FGBlock.Preceq K2 C
    · have hCK : FGBlock.Preceq C K2 := hc.resolve_right (fun h => by
        have := hH.h_mono h
        simp only [Height] at *
        omega)
      have hCK2 : (heightView p C).h < (heightView p K2).h := by
        simp only [Height] at *
        omega
      rcases cover K2 s2 hK2 (KitFG.preceq_trans hFC hCK) hCK hCK2 with hin | hKF
      · exact keep K2 hin hCK (by rw [hlo, hK2h]) hFC hZC
      · exact absurd (KitFG.preceq_trans hCK hKF) hCF
    · exact cause K2 s2 hK2 hc (by simp only [Height] at *; omega)

/-- Blueprint 21:2706–2716, 2724–2728; plan S25, H-DESCENT/D2.
DC: INTENTIONAL FJ entry identity of the contested floor. Two sources of one
height with different entries are incompatible: this is the pair cause. -/
theorem healing_entry_pair_incompatible {C₁ C₂ : FGBlock (Fin p.n)}
    (hh : (heightView p C₁).h = (heightView p C₂).h)
    (hr : (heightView p C₁).T_h.root ≠ (heightView p C₂).T_h.root) :
    ¬ Block.Compatible (eraseFG C₁) (eraseFG C₂) := by
  intro h
  apply hr
  rcases desc_compat_of_erase p h with h | h
  · rw [(fgCertificateLaws p).height.entry_plateau h hh]
  · rw [(fgCertificateLaws p).height.entry_plateau h hh.symm]

/-- Blueprint 21:2724–2737, 2785–2813; plan S25, H-DESCENT/D2.
DC: INTENTIONAL global event-index measure. A descent cause for a source C
of height at least c₀, emitted before the read, is an incompatible pair of
earlier sources of height at least c₀. -/
theorem healing_descent_pair {i : Nat} {x : V} {X : Finset (FGBlock (Fin p.n))}
    {C : FGBlock (Fin p.n)} {c₀ : Nat} {s : Slot}
    (hsrc : SourceBefore p c E rho i C s) (hc₀ : c₀ ≤ (heightView p C).h)
    (hk : KeepOrCause p c E rho i x X C) :
    Kept p c E rho i x X C ∨
      ∃ K K' s₁ s₂, SourceBefore p c E rho i K s₁ ∧ SourceBefore p c E rho i K' s₂ ∧
        c₀ ≤ (heightView p K).h ∧ c₀ ≤ (heightView p K').h ∧
        ¬ Block.Compatible (eraseFG K) (eraseFG K') := by
  rcases hk with hk | ⟨C', s', hC', hn, hh⟩ | ⟨C₁, C₂, s₁, s₂, h₁, h₂, hh, hlt, hr⟩
  · exact Or.inl hk
  · exact Or.inr ⟨C, C', s, s', hsrc, hC', hc₀, hc₀.trans hh, hn⟩
  · have hc₁ : c₀ ≤ (heightView p C₁).h := by
      simp only [Height] at *
      omega
    exact Or.inr ⟨C₁, C₂, s₁, s₂, h₁, h₂, hc₁, hh ▸ hc₁,
      healing_entry_pair_incompatible p hh hr⟩

/-- Blueprint 21:2718–2723, 2730–2741 (fj.descent.v3); plan S25, H-DESCENT/D2.
DC: INTENTIONAL global event-index measure, not the source label.
`Lost B s k`: the source B of label s is lost at event k. Before the first
loss, all earlier sources of height at least c₀ are pairwise compatible:
same labels by IF.6 (`same`), different labels by the supporter of the later
source (`support`), whose HEAD is an earlier loss of the earlier source.
`support` reads only an earlier source B with a row before i and height at
least c₀ (D2 blocker B1): the loss of an arbitrary block is not constructible. -/
theorem healing_high_pair_compat (c₀ : Nat) (Lost : FGBlock (Fin p.n) → Slot → Nat → Prop)
    (same : ∀ i K K' s, SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s →
      c₀ ≤ (heightView p K).h → c₀ ≤ (heightView p K').h →
      Block.Compatible (eraseFG K) (eraseFG K'))
    (support : ∀ i K s B sB, SourceBefore p c E rho i K s → c₀ ≤ (heightView p K).h →
      SourceBefore p c E rho i B sB → c₀ ≤ (heightView p B).h →
      sB < s → ¬ Block.Compatible (eraseFG B) (eraseFG K) → ∃ k < i, Lost B sB k)
    {i : Nat} (noLoss : ∀ k < i, ∀ B sB, ¬ Lost B sB k)
    {K K' : FGBlock (Fin p.n)} {s s' : Slot}
    (hK : SourceBefore p c E rho i K s) (hK' : SourceBefore p c E rho i K' s')
    (hc : c₀ ≤ (heightView p K).h) (hc' : c₀ ≤ (heightView p K').h) :
    Block.Compatible (eraseFG K) (eraseFG K') := by
  by_contra hn
  rcases lt_trichotomy s s' with hlt | rfl | hgt
  · obtain ⟨k, hk, hL⟩ := support i K' s' K s hK' hc' hK hc hlt hn
    exact noLoss k hk K s hL
  · exact hn (same i K K' s hK hK' hc hc')
  · obtain ⟨k, hk, hL⟩ :=
      support i K s K' s' hK hc hK' hc' hgt (fun h => hn (desc_compat_symm h))
    exact noLoss k hk K' s' hL

/-- Blueprint 21:2677–2741, 2767–2813 (fj.descent.v3); plan S25,
H-DESCENT/D2 `high_source_first_failure`. DC: INTENTIONAL global event-index
measure. If each loss at event k, with no earlier loss, has an incompatible
pair of high sources emitted before k, then no loss occurs and all high
sources are pairwise compatible. `healing_descent` and `healing_descent_pair`
supply that pair; H-POST supplies `Lost`, `same`, `support` and the lease and
score cases (H.1, H.2) of `cause`. -/
theorem healing_high_source_first_failure (c₀ : Nat)
    (Lost : FGBlock (Fin p.n) → Slot → Nat → Prop)
    (same : ∀ i K K' s, SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s →
      c₀ ≤ (heightView p K).h → c₀ ≤ (heightView p K').h →
      Block.Compatible (eraseFG K) (eraseFG K'))
    (support : ∀ i K s B sB, SourceBefore p c E rho i K s → c₀ ≤ (heightView p K).h →
      SourceBefore p c E rho i B sB → c₀ ≤ (heightView p B).h →
      sB < s → ¬ Block.Compatible (eraseFG B) (eraseFG K) → ∃ k < i, Lost B sB k)
    (cause : ∀ k K s, (∀ k' < k, ∀ B sB, ¬ Lost B sB k') → Lost K s k →
      ∃ K₁ K₂ s₁ s₂, SourceBefore p c E rho k K₁ s₁ ∧ SourceBefore p c E rho k K₂ s₂ ∧
        c₀ ≤ (heightView p K₁).h ∧ c₀ ≤ (heightView p K₂).h ∧
        ¬ Block.Compatible (eraseFG K₁) (eraseFG K₂)) :
    (∀ k K s, ¬ Lost K s k) ∧
      ∀ i K K' s s', SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s' →
        c₀ ≤ (heightView p K).h → c₀ ≤ (heightView p K').h →
        Block.Compatible (eraseFG K) (eraseFG K') := by
  have none : ∀ k K s, ¬ Lost K s k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro K s hL
      obtain ⟨K₁, K₂, s₁, s₂, h₁, h₂, hc₁, hc₂, hn⟩ :=
        cause k K s (fun k' hk B sB => ih k' hk B sB) hL
      exact hn (healing_high_pair_compat p c E rho c₀ Lost same support
        (fun k' hk B sB => ih k' hk B sB) h₁ h₂ hc₁ hc₂)
  exact ⟨none, fun i K K' s s' hK hK' hc hc' =>
    healing_high_pair_compat p c E rho c₀ Lost same support
      (fun k _ B sB => none k B sB) hK hK' hc hc'⟩

/-- ROOT-DIGEST W2b. Blueprint 21:526–546 (W3), 2693–2695 (IF.3(c)); plan S27, H-DESCENT/D4.
DC: INTENTIONAL target QC of the prior justification as the finality source.
A non-genesis finalized block has a held carrier D and an earlier honest
source K whose entry is F at the certificate height of D. The source gate
time is at most the time of the read event. -/
theorem healing_finality_source (hs : V2.D.ScheduleWellFormed E rho)
    (origin : RQCOrigin p c E rho) {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hF : (storeAt p c E rho i x).fg.F ≠ .genesis)
    (hroots : NamedRootCollisionFree p c E rho) :
    ∃ D ∈ (storeAt p c E rho i x).fg.TF,
      (finalityView p D).F = (storeAt p c E rho i x).fg.F ∧
      ∃ K s, SourceBefore p c E rho i K s ∧
        (heightView p K).h = (finalityView p D).h_F ∧
        (heightView p K).T_h = (storeAt p c E rho i x).fg.F ∧
        ∀ ev, rho.events[i]? = some ev → SA.gateTime p.toParams s ≤ ev.time := by
  obtain ⟨D, hD, hDF⟩ := (cstoreInv_stateBefore E rho i x).fg.Fcar
  obtain ⟨K, s, hK, hh, hT⟩ :=
    desc_final_source (hroots := hroots) p c E rho origin hx hD (by rw [hDF]; exact hF)
  exact ⟨D, hD, hDF, K, s, hK, hh, hT.trans hDF,
    fun _ hi => healing_source_gate p c E rho hs hK hi⟩

/-- ROOT-DIGEST W2b. Blueprint 21:526–546 (W3), 2696–2699; plan S27, H-DESCENT/D4.
DC: SAME justification target QC. A positive cached justification J has an
earlier honest source K whose entry is J at height h_j. The source gate time
is at most the time of the read event. -/
theorem healing_justified_source (hs : V2.D.ScheduleWellFormed E rho)
    (origin : RQCOrigin p c E rho) {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hj : (storeAt p c E rho i x).fg.h_j ≠ 0)
    (hroots : NamedRootCollisionFree p c E rho) :
    ∃ K s, SourceBefore p c E rho i K s ∧
      (heightView p K).h = (storeAt p c E rho i x).fg.h_j ∧
      (heightView p K).T_h = (storeAt p c E rho i x).fg.J ∧
      ∀ ev, rho.events[i]? = some ev → SA.gateTime p.toParams s ≤ ev.time := by
  obtain ⟨C1, hC1, -, hj1, hJ1⟩ := (cstoreInv_stateBefore E rho i x).fg.pair.1
  obtain ⟨K, s, hK, hh, hT⟩ :=
    desc_just_source (hroots := hroots) p c E rho origin hx hC1 (by rw [← hj1]; exact hj)
  exact ⟨K, s, hK, hh.trans hj1.symm, hT.trans hJ1.symm,
    fun _ hi => healing_source_gate p c E rho hs hK hi⟩

/-- ROOT-DIGEST W2b. Blueprint 21:2767–2813 (fj.descent.v2/v3); plan S25, H-DESCENT/D5.
DC: INTENTIONAL FJ descent alternatives. RExcl is a direct corollary of
`healing_descent`: its view holds every earlier source, so the restricted
cover holds. Consumers use `healing_descent`, not RExcl (B18). -/
theorem healing_rExcl (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    (hroots : NamedRootCollisionFree p c E rho) :
    RExcl p c E rho := by
  intro i x X C hx hX hanc _hF hsrc
  exact healing_descent (hroots := hroots) p c E rho xing origin hx hX (hanc C (KitFG.preceq_refl
    C))
    (fun K s hK _ _ _ => hsrc K s hK)

end AvailableChain.FGSA.Run
end

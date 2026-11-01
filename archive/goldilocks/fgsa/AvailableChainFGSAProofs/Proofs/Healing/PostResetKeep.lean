module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetInvariant
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetCompat
public import AvailableChainFGSAProofs.Proofs.Healing.Delivery

public section

/-! Blueprint 21 H.14:2815–2884; plan J3, "Induction design";
B1/B13/B15/B17/B18. The general kept-path clause uses each duty's own
covered view. DC: SAME prefix transport; INTENTIONAL FJ descent causes. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem keep_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

private theorem keep_comparable {A B : FGBlock (Fin p.n)}
    (h : Block.Compatible (eraseFG A) (eraseFG B)) :
    FGBlock.Preceq A B ∨ FGBlock.Preceq B A := by
  change (Block.preceq (eraseFG A) (eraseFG B) ||
    Block.preceq (eraseFG B) (eraseFG A)) = true at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Or.inl (keep_lift p h)
  · exact Or.inr (keep_lift p h)

private theorem keep_prefix {i : Nat} {x : V}
    {X : Finset (FGBlock (Fin p.n))} {B C : FGBlock (Fin p.n)}
    (hB : B ∈ X) (hBC : FGBlock.Preceq B C) (hC : Kept p c E rho i x X C) :
    Kept p c E rho i x X B := by
  rcases hC with hCZ | hCD | hCF
  · exact Or.inl (KitFG.preceq_trans hBC hCZ)
  · obtain ⟨_, hFC, hZC, W, hW, hCW, hlo⟩ :=
      (KitFG.mem_filteredFromView (heightView p) (R_at p c E rho i x) X C).1 hCD
    rcases KitFG.preceq_total_of_common hBC hZC with hBZ | hZB
    · exact Or.inl hBZ
    rcases KitFG.preceq_total_of_common hBC hFC with hBF | hFB
    · exact Or.inr (Or.inr hBF)
    exact Or.inr (Or.inl
      ((KitFG.mem_filteredFromView (heightView p) (R_at p c E rho i x) X B).2
        ⟨hB, hFB, hZB, W, hW, KitFG.preceq_trans hBC hCW, hlo⟩))
  · exact Or.inr (Or.inr (KitFG.preceq_trans hBC hCF))

/-- ROOT-DIGEST W2b. Blueprint 21 H.14:2847–2861; plan J3 C; B1/B13/B17/B18.
DC: SAME geometric keep for every compatible body with its support path.
The high case excludes both descent causes. A lower body is a prefix of
the held reset copy. No ProtectedBody guard is needed.
Assembly supplies fgsa_rXing as xing and sourceDiscipline_qcOrigin as origin. -/
theorem postReset_general_kept (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {x : V} {X : Finset (FGBlock (Fin p.n))} {C B : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hX : X ⊆ (storeAt p c E rho i x).fg.TF)
    (hC : C ∈ X) (he : eraseFG C = w.CStar)
    (cover : ∀ K s, SourceBefore p c E rho i K s → high p w K → K ∈ X)
    (path : ∀ A, FGBlock.Preceq A B → A ∈ X)
    (hBC : Block.Compatible (eraseFG B) w.CStar)
    (hBK : ∀ K s, SourceBefore p c E rho i K s → high p w K →
      Block.Compatible (eraseFG B) (eraseFG K))
    (hroots : NamedRootCollisionFree p c E rho) : Kept p c E rho i x X B := by
  have hB := path B (KitFG.preceq_refl B)
  by_cases hhB : high p w B
  · have hhigh := hinv.high_compatible
    rw [PostResetHighCompatible_def] at hhigh
    rcases healing_descent (hroots := hroots) p c E rho xing origin hx hX hB
      (fun K s hK _ _ hlt => Or.inl (cover K s hK (by
        rw [high_def] at hhB ⊢
        exact hhB.trans (Nat.le_of_lt hlt)))) with
      hk | ⟨K, s, hK, hn, hh⟩ | ⟨K, K', s, s', hK, hK', hh, hlt, hr⟩
    · exact hk
    · have hhK : high p w K := by
        rw [high_def] at hhB ⊢
        exact hhB.trans hh
      exact False.elim (hn (hBK K s hK hhK))
    · have hhK : high p w K := by
        rw [high_def] at hhB ⊢
        exact hhB.trans (Nat.le_of_lt hlt)
      have hhK' : high p w K' := by
        rw [high_def] at hhK ⊢
        rwa [← hh]
      exact False.elim (healing_entry_pair_incompatible p hh hr
        (hhigh K K' s s' hK hK' hhK hhK'))
  · obtain ⟨_, _, _, C0, _, _, _, he0, hh0⟩ := h0r.fresh
    have hCC : C = C0 := eraseFG_injective (he.trans he0.symm)
    have hhC : high p w C := by rw [hCC, high_def, hh0]
    have hkC := postReset_descent_kept (hroots := hroots) p c E rho xing origin hinv hx hX hC hhC
      (Or.inr he) (fun K s hK _ _ hlt => Or.inl (cover K s hK (by
        rw [high_def] at hhC ⊢
        exact hhC.trans (Nat.le_of_lt hlt))))
    have hBC' : FGBlock.Preceq B C :=
      (keep_comparable p (he ▸ hBC)).resolve_right (fun hCB => by
        apply hhB
        rw [high_def] at hhC ⊢
        exact hhC.trans ((fgCertificateLaws p).height.h_mono hCB))
    exact keep_prefix p c E rho hB hBC' hkC

private theorem keep_cross_source (hroots : NamedRootCollisionFree p c E rho) (origin : RQCOrigin
    p c E rho) {i : Nat} {x : V}
    {W : FGBlock (Fin p.n)} {m : Nat} (hx : x ∈ rho.honest)
    (hW : W ∈ (storeAt p c E rho i x).fg.TF) (hm : 1 ≤ m)
    (hmW : m < (heightView p W).h) :
    ∃ Y, FGBlock.Preceq Y W ∧ (heightView p Y).h = m ∧
      ∃ K s, SourceBefore p c E rho i K s ∧ (heightView p K).h = m ∧
        (heightView p K).T_h = Y := by
  classical
  obtain ⟨Y, hYW, hYm, Q, hQ, hrows⟩ :=
    (fgCertificateLaws p).height.height_crossing W m hm hmW
  let rows : Fin p.n → FGBlock (Fin p.n) × Row (Fin p.n) := fun k =>
    if hk : k ∈ Q then
      (Classical.choose (hrows k hk), Classical.choose (Classical.choose_spec (hrows k hk)))
    else (.genesis, ⟨k, .empty, none⟩)
  have hr : ∀ k ∈ Q, FGBlock.Preceq (rows k).1 W ∧
      (rows k).2 ∈ (rows k).1.rows ∧ (rows k).2.signer = k ∧
      (rows k).2.height_pair.matchesEntry m Y.root = true := fun k hk => by
    simpa only [rows, hk, ↓reduceDIte] using
      Classical.choose_spec (Classical.choose_spec (hrows k hk))
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

private theorem keep_final_source (hroots : NamedRootCollisionFree p c E rho) (origin : RQCOrigin
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

private theorem keep_reset_height {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {C : FGBlock (Fin p.n)} (he : eraseFG C = w.CStar) :
    (heightView p C).h = w.M + 1 := by
  obtain ⟨_, _, _, C0, _, _, _, he0, hh0⟩ := h0r.fresh
  exact eraseFG_injective (he.trans he0.symm) ▸ hh0

private theorem keep_symm {A B : Block} (h : Block.Compatible A B) :
    Block.Compatible B A := by
  change (Block.preceq A B || Block.preceq B A) = true at h
  change (Block.preceq B A || Block.preceq A B) = true
  rwa [Bool.or_comm]

private theorem keep_source_mono {a b : Nat} (hab : a ≤ b)
    {K : FGBlock (Fin p.n)} {s : Slot} (hK : SourceBefore p c E rho a K s) :
    SourceBefore p c E rho b K s := by
  obtain ⟨j, y, r, row, hj, hrow, hsrc, hs⟩ := hK
  exact ⟨j, y, r, row, lt_of_lt_of_le hj hab, hrow, hsrc, hs⟩

section Delivery
variable (mono : RMonoAll p c E rho)
    (origin : RQCOrigin p c E rho) {w : HealingWitness}
    (lowFinality : ∀ {i : Nat} {x : V} {D : FGBlock (Fin p.n)}, x ∈ rho.honest →
      afterTicksIdx rho (p.actionTime w.rStar) ≤ i →
      D ∈ (storeAt p c E rho i x).fg.TF →
      (finalityView p D).F = (storeAt p c E rho i x).fg.F →
      (finalityView p D).h_F ≤ w.M → Block.Preceq (F_at p c E rho i x) w.CStar)
    (highCompat : ∀ i, PostResetHighCompatible p c E rho w i)
    (resetCompat : ∀ i, PostResetResetCompatible p c E rho w i)

include mono origin lowFinality highCompat resetCompat

/-- ROOT-DIGEST W2b. Blueprint 21 H.14:2847–2849, 2880–2883; plan J3 A;
B1/B13/B15/B17/B18; hint 1 and its addendum. DC: SAME receiver-F split.
Assembly supplies fgsa_rMono, sourceDiscipline_qcOrigin, J1's
healing_low_finality_after_reset, and J2's all-cut compatibility results.
The lowFinality input keeps every producer guard. For an earlier read j,
compare the same receiver at max j resetCut, then use F monotonicity back to j. -/
theorem postReset_receiver_compatible {j l : Nat} {x : V}
    {K : FGBlock (Fin p.n)} {s : Slot} (hx : x ∈ rho.honest)
    (hK : SourceBefore p c E rho l K s) (hhK : high p w K)
    (hroots : NamedRootCollisionFree p c E rho) :
    Block.Compatible (eraseFG K) (F_at p c E rho j x) := by
  let a := max j (afterTicksIdx rho (p.actionTime w.rStar))
  have hj : j ≤ a := le_max_left _ _
  have ha : afterTicksIdx rho (p.actionTime w.rStar) ≤ a := le_max_right _ _
  have hfuture : Block.Compatible (F_at p c E rho a x) (eraseFG K) := by
    by_cases hgen : (storeAt p c E rho a x).fg.F = .genesis
    · change (Block.preceq (eraseFG (storeAt p c E rho a x).fg.F) (eraseFG K) || _) = true
      rw [hgen]
      exact Bool.or_eq_true_iff.mpr (Or.inl (eraseFG_preceq (KitFG.genesis_preceq K)))
    have hI : KitFG.FGStoreInvariant (heightView p) (finalityView p)
        (storeAt p c E rho a x).fg := (cstoreInv_stateBefore E rho a x).fg
    obtain ⟨D, hD, hDF⟩ := hI.Fcar
    by_cases hl : (finalityView p D).h_F ≤ w.M
    · have hlow := lowFinality hx ha hD hDF hl
      have hr := resetCompat l
      rw [PostResetResetCompatible_def] at hr
      exact Gen.Pure.block_compatible_of_preceq_compatible hlow (hr K s hK hhK)
    · obtain ⟨KF, sF, hKF, hhF, heF⟩ :=
        keep_final_source (hroots := hroots) p c E rho origin hx hD (by rw [hDF]; exact hgen)
      have hhKF : high p w KF := by
        rw [high_def, hhF]
        simp only [Height] at *
        omega
      have hf : Block.Preceq (F_at p c E rho a x) (eraseFG KF) := by
        have hp := (fgCertificateLaws p).height.entry_preceq KF
        rw [heF, hDF] at hp
        exact eraseFG_preceq hp
      have hc := highCompat (max a l)
      rw [PostResetHighCompatible_def] at hc
      exact Gen.Pure.block_compatible_of_preceq_compatible hf
        (hc KF K sF s (keep_source_mono p c E rho (le_max_left _ _) hKF)
          (keep_source_mono p c E rho (le_max_right _ _) hK) hhKF hhK)
  have hm := mono
  rw [RMonoAll_def] at hm
  exact keep_symm (Gen.Pure.block_compatible_of_preceq_compatible
    (eraseFG_preceq (hm j a x hx hj).1) hfuture)

/-- ROOT-DIGEST W2b. Blueprint 21 IF.5:550–567, H.12:2646–2652, H.14:2847–2861;
plan J3 A; B1/B13/B15/B17/B18. DC: SAME conditional admission discharge.
Assembly supplies sourceDiscipline_tSrc as source; all other inputs have
the producers listed at postReset_receiver_compatible. hCompat is proved
at the receiver's actual freeze read, including reads before resetCut. -/
theorem postReset_tDel [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (source : TSrc p c E rho)
    (hServices : ∀ y r K, y ∈ rho.honest →
      actionSourceFG p c E rho y r = some (some K) →
      recoveryStart p E ≤ SA.voteTime p.toParams (r * p.R) →
      SA.freezeTime p.toParams (r * p.R) ≤ rho.horizon →
      ∀ x ∈ rho.honest, FGBlock.Preceq
        (rho.stateBeforeTime E (SA.freezeTime p.toParams (r * p.R)) x).st.fg.F K →
      ∀ j z W, z ∈ rho.honest →
      rho.events[j]? = some (.tick z (SA.voteTime p.toParams (r * p.R))) →
      W ∈ (storeAt p c E rho j z).fg.TF →
      FGBlock.Preceq K W →
      FGBlock.Preceq
        (rho.stateBeforeTime E (SA.earlyTime p.toParams (r * p.R)) x).st.fg.F W →
      TargetReceiptService E rho (eraseFG W) (SA.earlyTime p.toParams (r * p.R)) x)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (h0r : H0Reset p c E rho w)
    {y x : V} {r l : Nat} {K : FGBlock (Fin p.n)}
    (hy : y ∈ rho.honest) (hsrc : actionSourceFG p c E rho y r = some (some K))
    (hK : SourceBefore p c E rho l K (r * p.R)) (hhK : high p w K)
    (hhor : SA.freezeTime p.toParams (r * p.R) ≤ rho.horizon) (hx : x ∈ rho.honest) :
    Gen.V2.Duty.HoldsBefore E rho (fun nd =>
      (∀ B, FGBlock.Preceq B K → B ∈ nd.st.fg.TF) ∨ FGBlock.Preceq K nd.st.fg.F)
      (SA.freezeTime p.toParams (r * p.R)) x := by
  have hready := healing_high_source_recoveryStart p c E rho
    emittedNonempty emittedName hK (by
      have := h0r.mu_le
      have := hhK
      change w.M + 1 ≤ (heightView p K).h at this
      omega)
  have hCompat := postReset_receiver_compatible (hroots := hrec.base.idealization) p c E rho
    mono origin
    lowFinality highCompat resetCompat (j := V2.D.Run.idxBefore rho
      (SA.freezeTime p.toParams (r * p.R))) hx hK hhK
  have hdel := healing_tDel E rho hrec source mono hServices y r K hy hsrc hready hhor x hx
  rw [Gen.V2.Duty.HoldsBefore_def] at hdel ⊢
  apply hdel
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hrec.base.valid.toScheduleWellFormed]
  exact hCompat

end Delivery

/-- Blueprint 21 H.14:2832–2835; plan J3 B, height field step;
B1/B13/B17/B18. DC: SAME frontier lower bound from the held reset copy. -/
theorem postReset_keep_height {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {i : Nat} {x : V} {C : FGBlock (Fin p.n)}
    (hC : C ∈ (storeAt p c E rho i x).fg.TF) (he : eraseFG C = w.CStar) :
    w.M + 1 ≤ (storeAt p c E rho i x).fg.h_max := by
  have hI : KitFG.FGStoreInvariant (heightView p) (finalityView p)
      (storeAt p c E rho i x).fg := (cstoreInv_stateBefore E rho i x).fg
  rw [hI.hmax]
  exact (keep_reset_height p c E rho h0r he).symm ▸
    le_sup_of_le_left (Finset.le_sup (f := fun B => (heightView p B).h) hC)

/-- ROOT-DIGEST W2b. Blueprint 21 H.14:2832–2835, 2847–2861; plan J3 B, contest field step;
B1/B13/B17/B18. DC: INTENTIONAL FJ contest exclusion by two high entries.
Assembly supplies sourceDiscipline_qcOrigin as origin. -/
theorem postReset_keep_contest (hs : V2.D.ScheduleWellFormed E rho)
    (origin : RQCOrigin p c E rho) {w : HealingWitness}
    {i : Nat} {x : V} (hhigh : PostResetHighCompatible p c E rho w i)
    (hbound : w.M + 1 ≤ (storeAt p c E rho i x).fg.h_max)
    (hx : x ∈ rho.honest)
    (hroots : NamedRootCollisionFree p c E rho) :
    (R_at p c E rho i x).contest = true →
      (storeAt p c E rho i x).fg.h_max = w.M + 1 := by
  intro hct
  let st := (storeAt p c E rho i x).fg
  change (decide (st.h_max = st.h_j + 1) && decide (∃ W ∈ st.TF,
    FGBlock.Preceq st.F W ∧ (heightView p W).h = st.h_max ∧
      ¬ FGBlock.Preceq st.J W)) = true at hct
  obtain ⟨htop, W, hW, _hFW, hhW, hn⟩ : st.h_max = st.h_j + 1 ∧ ∃ W ∈ st.TF,
      FGBlock.Preceq st.F W ∧ (heightView p W).h = st.h_max ∧
        ¬ FGBlock.Preceq st.J W := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using hct
  by_contra hne
  have hhighj : w.M + 1 ≤ st.h_j := by dsimp only [st] at *; simp only [Height] at *; omega
  have hjnz : st.h_j ≠ 0 := by simp only [Height] at *; omega
  obtain ⟨K1, s1, hK1, hh1, he1, -⟩ :=
    healing_justified_source (hroots := hroots) p c E rho hs origin hx hjnz
  obtain ⟨Y, hYW, hhY, K2, s2, hK2, hh2, he2⟩ :=
    keep_cross_source (hroots := hroots) p c E rho origin hx hW (Nat.one_le_iff_ne_zero.mpr hjnz)
      (by rw [hhW, htop]; simp only [Height] at *; omega)
  have hh : (heightView p K1).h = (heightView p K2).h := hh1.trans hh2.symm
  have hhK1 : high p w K1 := by rw [high_def, hh1]; exact hhighj
  have hhK2 : high p w K2 := by rw [high_def, hh2]; exact hhighj
  rw [PostResetHighCompatible_def] at hhigh
  have hp := keep_comparable p (hhigh K1 K2 s1 s2 hK1 hK2 hhK1 hhK2)
  have heq : (heightView p K1).T_h = (heightView p K2).T_h := by
    rcases hp with hp | hp
    · exact (fgCertificateLaws p).height.entry_plateau hp hh
    · exact ((fgCertificateLaws p).height.entry_plateau hp hh.symm).symm
  rw [he1, he2] at heq
  exact hn (heq ▸ hYW)

/-- Blueprint 21 H.14:2832–2835; plan J3 B, floor field step;
B1/B17/B18. DC: INTENTIONAL FJ floor uses the contest flag. -/
theorem postReset_keep_floor {w : HealingWitness} {i : Nat} {x : V}
    (hcontest : (R_at p c E rho i x).contest = true →
      (storeAt p c E rho i x).fg.h_max = w.M + 1) :
    (R_at p c E rho i x).lo ≤ max (w.M + 1) ((storeAt p c E rho i x).fg.h_max - 1) := by
  cases hct : (R_at p c E rho i x).contest
  · change (if (R_at p c E rho i x).contest then
      (storeAt p c E rho i x).fg.h_max else (storeAt p c E rho i x).fg.h_max - 1) ≤ _
    rw [hct]
    exact le_max_right _ _
  · change (if (R_at p c E rho i x).contest then
      (storeAt p c E rho i x).fg.h_max else (storeAt p c E rho i x).fg.h_max - 1) ≤ _
    rw [hct, hcontest hct]
    exact le_max_left _ _

/-- ROOT-DIGEST W2b. Blueprint 21 H.14:2847–2861; plan J3 B, root field step;
B1/B13/B17/B18. DC: INTENTIONAL FJ root is F or the selected J.
Assembly supplies fgsa_rXing and sourceDiscipline_qcOrigin. -/
theorem postReset_keep_roots (hs : V2.D.ScheduleWellFormed E rho)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {i : Nat} {x : V} {C : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hC : C ∈ (storeAt p c E rho i x).fg.TF) (he : eraseFG C = w.CStar)
    (hroots : NamedRootCollisionFree p c E rho) :
    ∀ B ∈ [(R_at p c E rho i x).Z, (storeAt p c E rho i x).fg.F],
      FGBlock.Preceq B C ∨
        ∃ K s, SourceBefore p c E rho i K s ∧ high p w K ∧ FGBlock.Preceq B K := by
  let st := (storeAt p c E rho i x).fg
  have hCh := keep_reset_height p c E rho h0r he
  have hF : FGBlock.Preceq st.F C ∨
      ∃ K s, SourceBefore p c E rho i K s ∧ high p w K ∧ FGBlock.Preceq st.F K := by
    by_cases hFn : st.F = .genesis
    · exact Or.inl (hFn ▸ KitFG.genesis_preceq C)
    obtain ⟨D, hD, hDF⟩ := (cstoreInv_stateBefore E rho i x).fg.Fcar
    by_cases hl : (finalityView p D).h_F ≤ w.M
    · exact Or.inl (xing i i x x D C hx le_rfl hD hDF ⟨hx, hC⟩ (by
        rw [hCh]
        simp only [Height] at *
        omega))
    · obtain ⟨K, s, hK, hh, hT⟩ :=
        keep_final_source (hroots := hroots) p c E rho origin hx hD (by rw [hDF]; exact hFn)
      refine Or.inr ⟨K, s, hK, ?_, ?_⟩
      · rw [high_def, hh]
        simp only [Height] at *; omega
      · have hp := (fgCertificateLaws p).height.entry_preceq K
        rwa [hT, hDF] at hp
  have hZ : FGBlock.Preceq (R_at p c E rho i x).Z C ∨
      ∃ K s, SourceBefore p c E rho i K s ∧ high p w K ∧
        FGBlock.Preceq (R_at p c E rho i x).Z K := by
    cases hr : (R_at p c E rho i x).rootIsJ
    · have hz : (R_at p c E rho i x).Z = st.F := by
        change (if (R_at p c E rho i x).rootIsJ then _ else _) = _
        rw [hr]
        rfl
      simpa only [hz] using hF
    · have hz : (R_at p c E rho i x).Z = st.J := by
        change (if (R_at p c E rho i x).rootIsJ then _ else _) = _
        rw [hr]
        rfl
      have hr' := hr
      change (decide (st.h_max = st.h_j + 1) && !(R_at p c E rho i x).contest) = true at hr'
      obtain ⟨htop, hct⟩ : st.h_max = st.h_j + 1 ∧
          (R_at p c E rho i x).contest = false := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] using hr'
      by_cases hl : st.h_j ≤ w.M
      · have hbound := postReset_keep_height p c E rho h0r hC he
        have htopC : (heightView p C).h = st.h_max := by
          dsimp only [st] at *
          simp only [Height] at *
          omega
        have hJC : FGBlock.Preceq st.J C := by
          by_contra hn
          have hbad : (R_at p c E rho i x).contest = true := by
            change (decide (st.h_max = st.h_j + 1) && decide _) = true
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨htop, C, hC,
              (healing_phase_frontier_root p c E rho xing hx hC htopC).1, htopC, hn⟩
          rw [hct] at hbad
          contradiction
        exact Or.inl (hz ▸ hJC)
      · obtain ⟨K, s, hK, hh, hT, -⟩ :=
          healing_justified_source (hroots := hroots) p c E rho hs origin hx (by
            change st.h_j ≠ 0
            simp only [Height] at *
            omega)
        refine Or.inr ⟨K, s, hK, ?_, ?_⟩
        · rw [high_def, hh]
          dsimp only [st] at hl
          simp only [Height] at *; omega
        · have hp := (fgCertificateLaws p).height.entry_preceq K
          rwa [hT, ← hz] at hp
  intro B hB
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl
  · exact hZ
  · exact hF

/-- ROOT-DIGEST W2b. Blueprint 21 H.14:2853–2861; plan J3 B, witness field step;
B1/B13/B17/B18. DC: SAME crossed-height source in the duty's own view.
Assembly supplies sourceDiscipline_qcOrigin as origin. -/
theorem postReset_keep_witness (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {i : Nat} {x : V} {X : Finset (FGBlock (Fin p.n))} {C : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (_hX : X ⊆ (storeAt p c E rho i x).fg.TF)
    (hC : C ∈ X) (he : eraseFG C = w.CStar)
    (cover : ∀ K s, SourceBefore p c E rho i K s → high p w K → K ∈ X)
    (hroots : NamedRootCollisionFree p c E rho) :
    ∃ B ∈ X, (heightView p B).h =
      max (w.M + 1) ((storeAt p c E rho i x).fg.h_max - 1) := by
  classical
  by_cases hl : (storeAt p c E rho i x).fg.h_max - 1 ≤ w.M + 1
  · exact ⟨C, hC, by rw [max_eq_left hl]; exact keep_reset_height p c E rho h0r he⟩
  · let st := (storeAt p c E rho i x).fg
    have hI : KitFG.FGStoreInvariant (heightView p) (finalityView p) st :=
      (cstoreInv_stateBefore E rho i x).fg
    obtain ⟨W, hW, hsup⟩ :=
      Finset.exists_mem_eq_sup st.TF ⟨_, hI.gen⟩ (fun W => (heightView p W).h)
    have hhW : (heightView p W).h = st.h_max := by
      have hm := hI.hmax
      rw [hsup] at hm
      dsimp only [st] at *
      simp only [Height] at *
      omega
    obtain ⟨_, _, _, K, s, hK, hhK, -⟩ :=
      keep_cross_source (hroots := hroots) p c E rho origin hx hW (m := st.h_max - 1)
        (by dsimp only [st] at *; simp only [Height] at *; omega)
        (by dsimp only [st] at *; simp only [Height] at *; omega)
    have hh : high p w K := by
      rw [high_def, hhK]
      dsimp only [st] at *
      simp only [Height] at *
      omega
    refine ⟨K, cover K s hK hh, ?_⟩
    rw [max_eq_right (by simp only [Height] at *; omega), hhK]

/-- ROOT-DIGEST W2b. Blueprint 21 H.12:2652–2666, H.14:2815–2884; plan J3 B, kept field step;
B1/B13/B15/B17/B18. DC: SAME reset transfer at the first release duty.
The unused reset-transfer and release inputs stay for signature uniformity.
Later reads use geometric descent in their own covered view. -/
theorem postReset_keep_body (_hs : V2.D.ScheduleWellFormed E rho)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    (_htransfer : ResetTransferCore p c E rho w)
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    {x : V} {X : Finset (FGBlock (Fin p.n))} {C B : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hX : X ⊆ (storeAt p c E rho i x).fg.TF)
    (_htick : ∃ t, rho.events[i]? = some (.tick x t) ∧ SA.releaseTime p.toParams w.sStar ≤ t)
    (hC : C ∈ X) (he : eraseFG C = w.CStar)
    (cover : ∀ K s, SourceBefore p c E rho i K s → high p w K → K ∈ X)
    (_hreset : ∀ K s, SourceBefore p c E rho i K s → high p w K →
      Block.Compatible (eraseFG K) w.CStar)
    (_hhigh : ∀ K K' s s', SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s' →
      high p w K → high p w K' → Block.Compatible (eraseFG K) (eraseFG K'))
    (path : ∀ A, FGBlock.Preceq A B → A ∈ X)
    (hBC : Block.Compatible (eraseFG B) w.CStar)
    (hBK : ∀ K s, SourceBefore p c E rho i K s → high p w K →
      Block.Compatible (eraseFG B) (eraseFG K))
    (hroots : NamedRootCollisionFree p c E rho) : Kept p c E rho i x X B := by
  exact postReset_general_kept (hroots := hroots) p c E rho xing origin h0r hinv
    hx hX hC he cover path hBC hBK

/-- ROOT-DIGEST W2b. Blueprint 21 H.14:2815–2884; plan J3 B, protected_kept successor;
B1/B13/B15/B17/B18. DC: SAME event-prefix history extension.
The old prefix uses the prior field. Only the new read at i needs the
separate height, contest, floor, roots, witness and kept field lemmas.
No other carrier field at i + 1 is used. -/
theorem postReset_protected_kept_succ (hs : V2.D.ScheduleWellFormed E rho)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    (htransfer : ResetTransferCore p c E rho w)
    {i : Nat} (hinv : PostResetInv p c E rho w i)
    (hroots : NamedRootCollisionFree p c E rho) :
    PostResetProtectedKept p c E rho w (i + 1) := by
  rw [PostResetProtectedKept_def]
  intro j hj x X C hx hX htick hC he cover hreset hhigh
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
  · have hprior := hinv.protected_kept
    rw [PostResetProtectedKept_def] at hprior
    exact hprior j hj x X C hx hX htick hC he cover hreset hhigh
  · have hbound := postReset_keep_height p c E rho h0r (hX hC) he
    have hcontest := postReset_keep_contest (hroots := hroots) p c E rho hs origin
      hinv.high_compatible hbound hx
    refine ⟨hbound, hcontest, postReset_keep_floor p c E rho hcontest,
      postReset_keep_roots (hroots := hroots) p c E rho hs xing origin h0r hx (hX hC) he,
      postReset_keep_witness (hroots := hroots) p c E rho origin h0r hx hX hC he cover, ?_⟩
    intro B s _hprotected path hBC hBK
    exact postReset_keep_body (hroots := hroots) p c E rho hs xing origin h0r htransfer hinv
      hx hX htick hC he cover hreset hhigh path hBC hBK

/-- ROOT-DIGEST W2b. Blueprint 21 H.14:2815–2884; plan J3 D1; B1/B13/B17/B18.
DC: SAME RKeep body over the reset witness. The last clause is supplied
by postReset_general_kept, including bodies outside ProtectedBody.
This internal projection has no H0 or first-proposal input. -/
theorem postReset_rKeep_body (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    (inv : ∀ i, PostResetInv p c E rho w i)
    (hroots : NamedRootCollisionFree p c E rho) :
    ∀ i x (X : Finset (FGBlock (Fin p.n))) C,
    x ∈ rho.honest → X ⊆ (storeAt p c E rho i x).fg.TF →
    (∃ t, rho.events[i]? = some (.tick x t) ∧ SA.releaseTime p.toParams w.sStar ≤ t) →
    C ∈ X → eraseFG C = w.CStar →
    (∀ K s, SourceBefore p c E rho i K s → high p w K → K ∈ X) →
    (∀ K s, SourceBefore p c E rho i K s → high p w K →
      Block.Compatible (eraseFG K) w.CStar) →
    (∀ K K' s s', SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s' →
      high p w K → high p w K' → Block.Compatible (eraseFG K) (eraseFG K')) →
    let st := storeAt p c E rho i x
    let R := R_at p c E rho i x
    w.M + 1 ≤ st.fg.h_max ∧ (R.contest = true → st.fg.h_max = w.M + 1) ∧
    R.lo ≤ max (w.M + 1) (st.fg.h_max - 1) ∧
    (∀ B ∈ [R.Z, st.fg.F], FGBlock.Preceq B C ∨
      ∃ K s, SourceBefore p c E rho i K s ∧ high p w K ∧ FGBlock.Preceq B K) ∧
    (∃ B ∈ X, (heightView p B).h = max (w.M + 1) (st.fg.h_max - 1)) ∧
    (∀ B, (∀ A, FGBlock.Preceq A B → A ∈ X) → Block.Compatible (eraseFG B) w.CStar →
      (∀ K s, SourceBefore p c E rho i K s → high p w K →
        Block.Compatible (eraseFG B) (eraseFG K)) → Kept p c E rho i x X B) := by
  intro i x X C hx hX htick hC he cover hreset hhigh
  have h := (inv (i + 1)).protected_kept
  rw [PostResetProtectedKept_def] at h
  obtain ⟨hh, hc, hl, hr, hw, -⟩ :=
    h i (Nat.lt_succ_self i) x X C hx hX htick hC he cover hreset hhigh
  exact ⟨hh, hc, hl, hr, hw, fun B path hBC hBK =>
    postReset_general_kept (hroots := hroots) p c E rho xing origin h0r (inv i) hx hX hC he cover
      path hBC hBK⟩

end AvailableChain.FGSA.Run
end

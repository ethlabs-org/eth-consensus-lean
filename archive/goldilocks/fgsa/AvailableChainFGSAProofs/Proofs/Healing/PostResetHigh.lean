module
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetInvariant -- shake: keep J6 port
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetCompat
public import AvailableChainFGSAProofs.Proofs.Healing.PostResetKeep
public import AvailableChainFGSAProofs.Proofs.Healing.DescentTimingRFProv

public section

/-! Blueprint 21 H.13:2668–2813, H.14:2826–2861; post-reset plan J3,
Risks; B1/B13/B17/B18. Compatibility-only keep inputs and selected-source
label cases use H0Reset. DC: SAME label bound and prefix transport;
INTENTIONAL FJ descent and cumulative controls. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem high_lift {A B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG A) (eraseFG B)) : FGBlock.Preceq A B :=
  eraseFG_preceq_iff.mp h

private theorem high_comparable {A B : FGBlock (Fin p.n)}
    (h : Block.Compatible (eraseFG A) (eraseFG B)) :
    FGBlock.Preceq A B ∨ FGBlock.Preceq B A := by
  change (Block.preceq (eraseFG A) (eraseFG B) ||
    Block.preceq (eraseFG B) (eraseFG A)) = true at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Or.inl (high_lift p h)
  · exact Or.inr (high_lift p h)

private theorem high_prefix {i : Nat} {x : V}
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

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.13:2785–2813, H.14:2815–2830; plan J3 D0;
B1/B13/B15/B17/B18. DC: INTENTIONAL FJ single-source and pair causes.
J3/H.14 uses this restricted descent in the duty's own covered view.
The two compatibility inputs exclude both causes for a high source or a high copy of C*. -/
theorem postReset_descent_kept_of_compat (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} {i : Nat} (highCompat : PostResetHighCompatible p c E rho w i)
    (resetCompat : PostResetResetCompatible p c E rho w i)
    {x : V} {X : Finset (FGBlock (Fin p.n))} {C : FGBlock (Fin p.n)}
    (hx : x ∈ rho.honest) (hX : X ⊆ (storeAt p c E rho i x).fg.TF) (hC : C ∈ X)
    (hhC : high p w C)
    (hsource : (∃ s, SourceBefore p c E rho i C s) ∨ eraseFG C = w.CStar)
    (cover : ∀ K s, SourceBefore p c E rho i K s →
      FGBlock.Preceq (storeAt p c E rho i x).fg.F K → FGBlock.Preceq C K →
      (heightView p C).h < (heightView p K).h →
      K ∈ X ∨ FGBlock.Preceq K (storeAt p c E rho i x).fg.F)
    (hroots : NamedRootCollisionFree p c E rho) :
    Kept p c E rho i x X C := by
  have hhigh := highCompat
  have hreset := resetCompat
  rw [PostResetHighCompatible_def] at hhigh
  rw [PostResetResetCompatible_def] at hreset
  rcases healing_descent (hroots := hroots) p c E rho xing origin hx hX hC cover with
    hk | ⟨K, s, hK, hn, hh⟩ | ⟨K, K', s, s', hK, hK', hh, hlt, hr⟩
  · exact hk
  · have hhK : high p w K := by
      rw [high_def] at hhC ⊢
      exact hhC.trans hh
    apply False.elim
    apply hn
    rcases hsource with ⟨sC, hsrcC⟩ | he
    · exact hhigh C K sC s hsrcC hK hhC hhK
    · rw [he]
      exact hreset K s hK hhK
  · have hhK : high p w K := by
      rw [high_def] at hhC ⊢
      exact hhC.trans (Nat.le_of_lt hlt)
    have hhK' : high p w K' := by
      rw [high_def] at hhK ⊢
      rwa [← hh]
    exact False.elim (healing_entry_pair_incompatible p hh hr
      (hhigh K K' s s' hK hK' hhK hhK'))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.14:2847–2861; plan J3 D0; B1/B13/B17/B18.
DC: SAME geometric keep for every compatible body with its support path.
The high case excludes both descent causes. A lower body is a prefix of
the held reset copy. No ProtectedBody guard is needed.
Assembly supplies fgsa_rXing as xing and sourceDiscipline_qcOrigin as origin. -/
theorem postReset_general_kept_of_compat (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {i : Nat} (highCompat : PostResetHighCompatible p c E rho w i)
    (resetCompat : PostResetResetCompatible p c E rho w i)
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
  · have hhigh := highCompat
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
    have hkC := postReset_descent_kept_of_compat (hroots := hroots) p c E rho xing origin
      highCompat resetCompat hx hX hC hhC
      (Or.inr he) (fun K s hK _ _ hlt => Or.inl (cover K s hK (by
        rw [high_def] at hhC ⊢
        exact hhC.trans (Nat.le_of_lt hlt))))
    have hBC' : FGBlock.Preceq B C :=
      (high_comparable p (he ▸ hBC)).resolve_right (fun hCB => by
        apply hhB
        rw [high_def] at hhC ⊢
        exact hhC.trans ((fgCertificateLaws p).height.h_mono hCB))
    exact high_prefix p c E rho hB hBC' hkC

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.14:2815–2884; plan J3 D0; B1/B13/B17/B18.
DC: SAME RKeep body over the reset witness. The last clause is supplied
by postReset_general_kept_of_compat, including bodies outside ProtectedBody.
This internal projection has no full H0 or first-proposal input. -/
theorem postReset_rKeep_body_of_compat (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    (hs : V2.D.ScheduleWellFormed E rho)
    (highCompat : ∀ i, PostResetHighCompatible p c E rho w i)
    (resetCompat : ∀ i, PostResetResetCompatible p c E rho w i)
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
  intro i x X C hx hX _htick hC he cover _hreset _hhigh
  have hh := postReset_keep_height p c E rho h0r (hX hC) he
  have hc := postReset_keep_contest (hroots := hroots) p c E rho hs origin (highCompat i) hh hx
  exact ⟨hh, hc, postReset_keep_floor p c E rho hc,
    postReset_keep_roots (hroots := hroots) p c E rho hs xing origin h0r hx (hX hC) he,
    postReset_keep_witness (hroots := hroots) p c E rho origin h0r hx hX hC he cover,
    fun B path hBC hBK => postReset_general_kept_of_compat (hroots := hroots) p c E rho xing
      origin h0r
      (highCompat i) (resetCompat i) hx hX hC he cover path hBC hBK⟩

section KeepReset
variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (hScopes : LossServiceScope p c E rho)
    (mono : RMonoAll p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)

include hrec hScopes mono emittedNonempty emittedName writes xing origin h0r

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21 H.14:2847–2861; plan J3 D0; B1/B13/B17/B18.
DC: SAME RKeep body. J2 supplies both compatibility inputs at every cut.
No lease, raw, service, full carrier or first-proposal input is used.
Assembly supplies fgsa_rMono, emittedName_window,
sourceDiscipline_emittedNonempty, fgsa_leaseOrigins_lastWrite,
fgsa_rXing and sourceDiscipline_qcOrigin. -/
theorem postReset_rKeep_body_reset :
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
        Block.Compatible (eraseFG B) (eraseFG K)) → Kept p c E rho i x X B) :=
  postReset_rKeep_body_of_compat (hroots := hrec.base.idealization) p c E rho xing origin h0r
    hrec.base.valid.toScheduleWellFormed
    (postReset_high_compatible_all p c E rho hrec hScopes mono emittedNonempty emittedName
      writes xing origin h0r)
    (postReset_reset_compatible_all p c E rho hrec hScopes mono emittedNonempty emittedName
      writes xing origin h0r)

end KeepReset

section Label

private theorem high_action_round_le {r r' : Nat}
    (ht : p.actionTime r' ≤ p.actionTime r) : r' ≤ r := by
  change 4 * p.Δ * ((r' * p.R : Nat) : Int) + 6 * p.Δ ≤
    4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ at ht
  have hR : 0 < p.R := by have := p.RLarge; omega
  have hd := p.deltaPos
  by_contra hn
  have hmul : r * p.R < r' * p.R :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_ge hn) hR
  have hcast : ((r * p.R : Nat) : Int) < ((r' * p.R : Nat) : Int) := by
    exact_mod_cast hmul
  nlinarith

private theorem high_earlier_row_round (hs : V2.D.ScheduleWellFormed E rho)
    {i j r r' : Nat} {x y : V} {a : RowWire p.n}
    (hi : rho.events[i]? = some (.tick x (p.actionTime r)))
    (hji : j < i) (ha : HonestRowAt p c E rho j y r' a) : r' ≤ r := by
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp ha.2.1
  have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
  rw [hie, hje] at hk
  exact high_action_round_le p (V2.D.Engine.time_le_of_key_le _ _ hk)

private theorem high_selected_tick {x : V} {r : Nat} {C : FGBlock (Fin p.n)}
    (hsrc : actionSourceFG p c E rho x r = some (some C)) :
    ∃ i : Nat, rho.events[i]? = some (V2.Event.tick x (p.actionTime r)) := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hsrc
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none] at hsrc; contradiction
  | some i => exact ⟨i, V2.D.Run.tickIdx?_spec hi⟩

private theorem high_cap_label (hs : V2.D.ScheduleWellFormed E rho)
    (cap : RCap p c E rho) {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {i r : Nat} {x : V} {W : FGBlock (Fin p.n)}
    (hi : rho.events[i]? = some (.tick x (p.actionTime r)))
    (hW : HeldAt p c E rho i x W) (hh : w.M + 2 ≤ (heightView p W).h) :
    w.sStar ≤ r * p.R := by
  obtain ⟨j, y, r', a, e, hji, ha, he, -⟩ := cap w.M i x W hW hh
  have hfirst := h0r.reset_first r' ⟨j, y, a, e, ha, he⟩
  rw [h0r.label]
  exact Nat.mul_le_mul_right p.R
    (hfirst.trans (high_earlier_row_round p c E rho hs hi hji ha))

private theorem high_label_above (hs : V2.D.ScheduleWellFormed E rho)
    (cap : RCap p c E rho) {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {x : V} {r : Nat} {C : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho x r = some (some C))
    (hh : w.M + 2 ≤ (heightView p C).h) : w.sStar ≤ r * p.R := by
  obtain ⟨i, hi⟩ := high_selected_tick p c E rho hsrc
  exact high_cap_label p c E rho hs cap h0r hi
    ⟨hx, healing_action_source_held p c E rho hs hi hsrc⟩ hh

variable [Fintype V]
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

include rowCovered in
private theorem high_label_in_band {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {x : V} {r : Nat} {C : FGBlock (Fin p.n)} {nd : Node p}
    (hx : x ∈ rho.honest) (hnd : postClock E rho x (p.actionTime r) = some nd)
    (hsrc : actionSourceFG p c E rho x r = some (some C))
    (hC : C ∈ FGSA.fullTree p nd.st)
    (hh : (heightView p C).h = w.M + 1)
    (hband : (FGSA.controls p nd.st).lo ≤ (heightView p C).h)
    (hawake : E.awake x (p.actionTime r) = true) : w.sStar ≤ r * p.R := by
  obtain ⟨j, rSent, a, hr, ha, he⟩ :=
    rowCovered hrec.base hrec.fault x hx r nd hnd C hsrc hC hband hawake
  rw [hh] at he
  rw [h0r.label]
  exact Nat.mul_le_mul_right p.R
    ((h0r.reset_first rSent ⟨j, x, a, _, ha, he⟩).trans hr)

omit [Fintype V] in
private theorem high_label_out_of_band (hs : V2.D.ScheduleWellFormed E rho)
    (cap : RCap p c E rho) {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {x : V} {r : Nat} {nd : Node p}
    (hx : x ∈ rho.honest) (hnd : postClock E rho x (p.actionTime r) = some nd)
    (hband : w.M + 1 < (FGSA.controls p nd.st).lo) : w.sStar ≤ r * p.R := by
  classical
  rw [postClock_def, preTick_def] at hnd
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none] at hnd; contradiction
  | some i =>
    simp only [hi, Option.map_some] at hnd
    have hnd := Option.some.inj hnd
    subst nd
    have hfg := FGSA.clock_fg p (storeAt p c E rho i x) (p.actionTime r)
    have hlo : (FGSA.controls p (FGSA.clock p (storeAt p c E rho i x)
        (p.actionTime r))).lo ≤ (storeAt p c E rho i x).fg.h_max := by
      change (if _ then (FGSA.clock p (storeAt p c E rho i x)
        (p.actionTime r)).fg.h_max else (FGSA.clock p (storeAt p c E rho i x)
        (p.actionTime r)).fg.h_max - 1) ≤ _
      rw [hfg]
      split
      · exact le_rfl
      · exact Nat.sub_le _ _
    have hI : KitFG.FGStoreInvariant (heightView p) (finalityView p)
        (storeAt p c E rho i x).fg := (cstoreInv_stateBefore E rho i x).fg
    obtain ⟨W, hW, hsup⟩ := Finset.exists_mem_eq_sup
      (storeAt p c E rho i x).fg.TF ⟨_, hI.gen⟩ (fun W => (heightView p W).h)
    have hhW : w.M + 2 ≤ (heightView p W).h := by
      have hm := hI.hmax
      rw [hsup] at hm
      have hmax : w.M + 1 < (storeAt p c E rho i x).fg.h_max := hband.trans_le hlo
      simp only [Height] at *
      omega
    exact high_cap_label p c E rho hs cap h0r (V2.D.Run.tickIdx?_spec hi) ⟨hx, hW⟩ hhW

omit [Fintype V] in
private theorem high_selected_after_cut (hs : V2.D.ScheduleWellFormed E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {x : V} {r : Nat} {C : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho x r = some (some C)) (hh : high p w C) :
    w.u₀ < p.actionTime r := by
  obtain ⟨i, hi⟩ := high_selected_tick p c E rho hsrc
  by_contra hn
  have hidx : i ≤ timeIdx rho w.u₀ :=
    ((V2.D.Engine.index_lt_read_length_iff hs w.u₀ hi).mpr (le_of_not_gt hn)).le
  have hheld := healing_action_source_held p c E rho hs hi hsrc
  have hcut := (fgsa_store_durable p c E rho hidx x).1 hheld
  have hI : KitFG.FGStoreInvariant (heightView p) (finalityView p)
      (storeAt p c E rho (timeIdx rho w.u₀) x).fg :=
    (cstoreInv_stateBefore E rho (timeIdx rho w.u₀) x).fg
  have hheight : (heightView p C).h ≤
      (storeAt p c E rho (timeIdx rho w.u₀) x).fg.h_max := by
    rw [hI.hmax]
    exact le_sup_of_le_left (Finset.le_sup (f := fun B => (heightView p B).h) hcut)
  have hfront : honestFrontier p c E rho w.u₀ =
      rho.honest.sup (fun y => (storeAt p c E rho (timeIdx rho w.u₀) y).fg.h_max) := by
    unfold honestFrontier storeAt timeIdx
    rw [V2.D.Engine.readAt_eq_stateBefore hs w.u₀]
  have hmax := Finset.le_sup
    (f := fun y => (storeAt p c E rho (timeIdx rho w.u₀) y).fg.h_max) hx
  rw [← hfront, ← h0r.frontier] at hmax
  rw [high_def] at hh
  simp only [Height] at *
  omega

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14:2837–2839; plan J3 THigh A1; B1/B13/B17/B18.
DC: SAME crossing of M + 1. Assembly supplies fgsa_rCap_channel.
The selected action need not emit a row or be awake. -/
theorem postReset_selected_label_above (hs : V2.D.ScheduleWellFormed E rho)
    (cap : RCap p c E rho) {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {x : V} {r : Nat} {C : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho x r = some (some C))
    (hh : w.M + 2 ≤ (heightView p C).h) : w.sStar ≤ r * p.R :=
  high_label_above p c E rho hs cap h0r hx hsrc hh

include rowCovered in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14:2837–2845; plan J3 THigh A; B1/B13/B17/B18.
DC: SAME crossing and SO-COV routes. Assembly supplies fgsa_rCap_channel
and rowPermission_covered with its full type. The inclusive frontier
excludes high selected actions before the cut; Recovery₂.awake then
supplies the SO-COV guard. No row of the selected action is assumed. -/
theorem postReset_selected_label {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    (cap : RCap p c E rho) {w : HealingWitness} (h0r : H0Reset p c E rho w)
    {x : V} {r : Nat} {C : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho x r = some (some C)) (hh : high p w C)
    : w.sStar ≤ r * p.R := by
  have hs := hrec.base.valid.toScheduleWellFormed
  have hcut := high_selected_after_cut p c E rho hs h0r hx hsrc hh
  have hGST : E.t_GST ≤ p.actionTime r := by
    have hP : 0 ≤ P p := by
      change 0 ≤ 4 * (p.R : Int) * p.Δ
      have := p.deltaPos
      positivity
    linarith [h0r.cut_lower, healing_recoveryStart_ge p E]
  obtain ⟨i, hi⟩ := high_selected_tick p c E rho hsrc
  have hhor : p.actionTime r ≤ rho.horizon :=
    (hs.in_horizon _ (List.mem_of_getElem? hi)).2
  have hawake := hrec.awake x hx _ hGST hhor
  by_cases habove : w.M + 2 ≤ (heightView p C).h
  · exact high_label_above p c E rho hrec.base.valid.toScheduleWellFormed cap h0r hx hsrc
      habove
  have heq : (heightView p C).h = w.M + 1 := by
    rw [high_def] at hh
    simp only [Height] at *
    omega
  have hread := hsrc
  rw [actionSourceFG_def] at hread
  obtain ⟨nd, hnd, hfg⟩ := Option.map_eq_some_iff.mp hread
  have hC : C ∈ FGSA.fullTree p nd.st := by
    change FGSA.deepest _ = some C at hfg
    exact (Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hfg).1).1
  by_cases hband : (FGSA.controls p nd.st).lo ≤ (heightView p C).h
  · exact high_label_in_band p c E rho rowCovered hrec h0r hx hnd hsrc hC heq hband hawake
  · exact high_label_out_of_band p c E rho hrec.base.valid.toScheduleWellFormed cap h0r
      hx hnd (by rw [heq] at hband; exact Nat.lt_of_not_ge hband)

end Label

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.13:2668–2813, H.14:2826–2845; plan J3 THigh B;
B1/B13/B17/B18. DC: SAME event-prefix order. Selected actions include
send-once suppression; no emitted-row witness is part of this predicate. -/
def SelectedBefore (i : Nat) (C : FGBlock (Fin p.n)) (s : Slot) : Prop :=
  ∃ j y r, j < i ∧ y ∈ rho.honest ∧
    rho.events[j]? = some (V2.Event.tick y (p.actionTime r)) ∧
    actionSourceFG p c E rho y r = some (some C) ∧ s = r * p.R

private theorem high_selected_unfold (i : Nat) (C : FGBlock (Fin p.n)) (s : Slot) :
    SelectedBefore p c E rho i C s =
      (∃ j y r, j < i ∧ y ∈ rho.honest ∧
        rho.events[j]? = some (V2.Event.tick y (p.actionTime r)) ∧
        actionSourceFG p c E rho y r = some (some C) ∧ s = r * p.R) := rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14:2826–2845; plan J3 THigh B; B1/B17/B18/B3a.
DC: SAME event-prefix selected source. Equation export for this predicate. -/
theorem SelectedBefore_def (i : Nat) (C : FGBlock (Fin p.n)) (s : Slot) :
    SelectedBefore p c E rho i C s =
      (∃ j y r, j < i ∧ y ∈ rho.honest ∧
        rho.events[j]? = some (V2.Event.tick y (p.actionTime r)) ∧
        actionSourceFG p c E rho y r = some (some C) ∧ s = r * p.R) :=
  high_selected_unfold p c E rho i C s

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.14:2826–2845; plan J3 THigh B; B1/B17/B18.
DC: SAME every emitted source is selected. Existing row-based fields
keep their types; the projection discards only the emission witness. -/
theorem selectedBefore_of_sourceBefore {i : Nat} {C : FGBlock (Fin p.n)} {s : Slot}
    (h : SourceBefore p c E rho i C s) : SelectedBefore p c E rho i C s := by
  obtain ⟨j, y, r, a, hj, ha, hsrc, hs⟩ := h
  exact ⟨j, y, r, hj, ha.1, ha.2.1, hsrc, hs⟩

private theorem high_selected_gate (source : TSrc p c E rho)
    {x : V} {r : Nat} {C : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho x r = some (some C)) :
    ∃ B, gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B := by
  have he : actionSource p c E rho x r = some (some (eraseFG C)) := by
    change (actionSourceFG p c E rho x r).map (Option.map eraseFG) = _
    rw [hsrc]
    rfl
  obtain ⟨X, B, -, hC, hB, hbelow, -⟩ := source x r (eraseFG C) hx he
  exact ⟨B, hB, hbelow _ hC⟩

private theorem high_selected_supporter [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (source : TSrc p c E rho)
    {x : V} {r : Nat} {C : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho x r = some (some C)) :
    ∃ j z, z ∈ rho.honest ∧
      rho.events[j]? = some (V2.Event.tick z (SA.voteTime p.toParams (r * p.R))) ∧
      Block.Preceq (eraseFG C) (headAtIdx p c E rho j (r * p.R)) := by
  have he : actionSource p c E rho x r = some (some (eraseFG C)) := by
    change (actionSourceFG p c E rho x r).map (Option.map eraseFG) = _
    rw [hsrc]
    rfl
  obtain ⟨X, -, -, hC, -, -, hfast, -⟩ := source x r (eraseFG C) hx he
  obtain ⟨st, hst, hτ⟩ := hfast _ hC
  rw [gateIn_def, preTick_def] at hst
  cases hi : V2.D.Run.tickIdx? rho x (SA.gateTime p.toParams (r * p.R)) with
  | none => rw [hi] at hst; cases hst
  | some i =>
    rw [hi] at hst
    have hst := Option.some.inj hst
    subst st
    obtain ⟨k, o, hh, ho, hk, hsup⟩ := healing_support_honest_seat rho
      hrec.base.cstar hrec.fault _ _ _ hτ
    obtain ⟨H, hH, hHm, -, -, hm, hl⟩ := healing_support_clean_target E rho o ho
    obtain ⟨j, hj, hhead⟩ := healing_support_honest_head E rho hrec.base.valid hm hl hk hh
    refine ⟨j, _, hh, hj, ?_⟩
    change Gen.AC.Root.voteSupports
      (GridCO.resolutionTree (actView (clockPre p (storeAt p c E rho i x)
        (SA.gateTime p.toParams (r * p.R))))) (eraseFG C) o = true at hsup
    rw [Gen.AC.Root.voteSupports_def, resolvedHead_target _ o hH] at hsup
    have heq := stored_eq_headVote E rho hrec.base.idealization i x hHm j
      (rho.seatOf (.base (.head (r * p.R))) k)
      (SA.voteTime p.toParams (r * p.R)) (r * p.R)
      (Option.some.inj ((resolvedHead_root _ o hH).symm.trans hhead))
    rw [healing_headAtIdx_tick p c E rho hj]
    exact heq ▸ (Bool.and_eq_true_iff.mp hsup).2


section SelectedReset
variable [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) (hScopes : LossServiceScope p c E rho)
    (mono : RMonoAll p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {w : HealingWitness} (h0r : H0Reset p c E rho w)
    (hSame : SameLabelServiceScope E rho w.sStar)

include hrec hScopes mono emittedNonempty emittedName writes xing origin h0r hSame

variable (cap : RCap p c E rho) (source : TSrc p c E rho)
    (rowCovered : ∀ (_hb : Base₂ p c E rho)
      (_hf : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
      (x : V), x ∈ rho.honest → ∀ (r : Nat) (nd : Node p),
      postClock E rho x (p.actionTime r) = some nd → ∀ C : FGBlock (Fin p.n),
      actionSourceFG p c E rho x r = some (some C) →
      C ∈ FGSA.fullTree p nd.st → (FGSA.controls p nd.st).lo ≤ (heightView p C).h →
      E.awake x (p.actionTime r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt p c E rho j x rSent a ∧
        namedEntry a.payload.height_pair =
          some ((heightView p C).h, (heightView p C).T_h.root))

include cap source rowCovered

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21 H.13:2730–2741, H.14:2826–2845; plan J3 THigh B2;
B1/B13/B17/B18. DC: SAME reset-source HEAD retention. The selected
source has a real honest supporter even if its action emits no row.
Equal labels use IF.6; later labels use H.13 for the emitted reset source.
Inputs have the D0 producer map; cap is fgsa_rCap_channel, source is
sourceDiscipline_tSrc, and rowCovered is rowPermission_covered. -/
theorem postReset_selected_reset_compatible {x : V} {r : Nat}
    {C : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG p c E rho x r = some (some C)) (hh : high p w C) :
    Block.Compatible (eraseFG C) w.CStar := by
  have hlabel := postReset_selected_label p c E rho rowCovered hrec.toRecovery₂ cap h0r hx hsrc hh
  obtain ⟨j, y, a, C0, ha, -, hsrc0, he0, hh0⟩ := h0r.fresh
  have hsource0 : SourceBefore p c E rho (j + 1) C0 w.sStar :=
    ⟨j, y, w.rStar, a, Nat.lt_succ_self j, ha, hsrc0, h0r.label⟩
  have hheight0 : muOf p c E rho + 1 ≤ (heightView p C0).h := by
    rw [hh0]
    exact Nat.succ_le_succ h0r.mu_le
  by_cases heq : w.sStar = r * p.R
  · obtain ⟨B, hB, hCB⟩ := high_selected_gate p c E rho source hx hsrc
    obtain ⟨B0, hB0, hC0B⟩ := high_selected_gate p c E rho source ha.1 hsrc0
    rw [← heq] at hB
    rw [← h0r.label] at hB0
    have hc := fgsa_sameLabel_on p c E rho hrec.base.valid w.sStar hSame hrec.base.idealization
      x y B B0 hx ha.1 hB hB0
    change (Block.preceq B B0 || Block.preceq B0 B) = true at hc
    have hcompat : Block.Compatible (eraseFG C) (eraseFG C0) := by
      rcases Bool.or_eq_true_iff.mp hc with hc | hc
      · exact Gen.Pure.block_compatible_of_common
          (Gen.Pure.block_preceq_trans hCB hc) hC0B
      · exact Gen.Pure.block_compatible_of_common hCB
          (Gen.Pure.block_preceq_trans hC0B hc)
    simpa only [he0] using hcompat
  · obtain ⟨k, z, hz, hk, hCH⟩ := high_selected_supporter p c E rho hrec.toRecovery₂ source hx hsrc
    have hsrcN : SrcN p c E rho C0 w.sStar :=
      healing_srcN_of_source p c E rho hsource0
    have hhigh0 : HighSrcN p c E rho C0 w.sStar := by
      rw [HighSrcN_def]
      exact ⟨hsrcN, hheight0⟩
    have hnoLoss := (healing_high_source_compat p c E rho hrec hScopes mono
      emittedNonempty emittedName writes xing origin).1
    have hC0H : Block.Preceq (eraseFG C0) (headAtIdx p c E rho k (r * p.R)) := by
      by_contra hn
      apply hnoLoss k C0 w.sStar
      rw [Lost_def]
      exact ⟨hhigh0, z, r * p.R, hz, Nat.succ_le_of_lt
        (lt_of_le_of_ne hlabel heq), hk, hn⟩
    simpa only [he0] using Gen.Pure.block_compatible_of_common hCH hC0H

end SelectedReset

end AvailableChain.FGSA.Run
end

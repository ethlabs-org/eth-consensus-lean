module
public import AvailableChainFGSAProofs.Proofs.Healing.Descent
public import AvailableChainFGSAProofs.Proofs.Healing.DescentLossFirst
public import AvailableChainFGSAProofs.Proofs.Healing.DescentLossLease
public import AvailableChainFGSAProofs.Proofs.Healing.DescentLossNext

public section

/-! H-DESCENT D2 (H.13): the `cause` input of `healing_high_source_first_failure`
at c₀ = μ + 1, from the descent at the loss read. Finality and root coverage
exclude the F and Z keep cases. A single conflicting earlier source gives an
earlier loss, for every loss label (also the first transfer l = sB + 1, which
has no row of B before the loss: blocker B2). Two earlier sources of one
height give the incompatible high pair. The HEAD view is the store before the
freeze z_(l-1): F is below B (R-XING or an earlier loss), each source above F
reaches it by the per-block relay, and a domain block is covered by the
moving-frame H.1 (l = sB + 1) or H.2 (l ≥ sB + 2) transfer. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Filtering a view above the frame F preserves its canonical domain. -/
theorem healing_domain_filter_F (st : State p.n) (X : Finset (FGBlock (Fin p.n))) :
    domainR p st (X.filter (fun A => FGBlock.Preceq st.fg.F A)) = domainR p st X := by
  ext B
  constructor
  · intro hB
    obtain ⟨hB, hFB, hZB, W, hW, hBW, hlo⟩ :=
      (KitFG.mem_filteredFromView _ _ _ _).mp hB
    exact (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨(Finset.mem_filter.mp hB).1, hFB, hZB, W, (Finset.mem_filter.mp hW).1, hBW, hlo⟩
  · intro hB
    obtain ⟨hB, hFB, hZB, W, hW, hBW, hlo⟩ :=
      (KitFG.mem_filteredFromView _ _ _ _).mp hB
    exact (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨Finset.mem_filter.mpr ⟨hB, hFB⟩, hFB, hZB, W,
        Finset.mem_filter.mpr ⟨hW, KitFG.preceq_trans hFB hBW⟩, hBW, hlo⟩

/-- Object services at actual high-source and moving-frame reads. -/
structure LossServiceScope (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) : Prop where
  same : ∀ i K K' s, SourceBefore p c E rho i K s →
    SourceBefore p c E rho i K' s →
    muOf p c E rho + 1 ≤ (heightView p K).h →
    muOf p c E rho + 1 ≤ (heightView p K').h →
    SameLabelServiceScope E rho s
  first : ∀ B sB (iy : Nat) (y : V), HighSrcN p c E rho B sB → y ∈ rho.honest →
    rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (sB + 1))) →
    joinedAt p E rho y (sB + 1) (SA.voteTime p.toParams (sB + 1)) →
    ∀ ix xs, xs ∈ rho.honest → IsGateTick p c rho ix xs sB →
    (∃ C, gateResultAt p c E rho ix = some (some C) ∧
      Block.Preceq (eraseFG B) C) →
    FirstTransferScope E rho ix iy xs y sB
  next : ∀ B sB i (iy : Nat) (y : V), HighSrcN p c E rho B sB → sB + 1 ≤ i →
    y ∈ rho.honest →
    rho.events[iy]? = some (.tick y (SA.voteTime p.toParams (i + 1))) →
    joinedAt p E rho y (i + 1) (SA.voteTime p.toParams (i + 1)) →
    NextTransferScope E rho iy y i
  fast : ∀ B sB l (k : Nat) (x : V), HighSrcN p c E rho B sB → sB + 2 ≤ l →
    x ∈ rho.honest →
    rho.events[k]? = some (.tick x (SA.voteTime p.toParams l)) →
    ∀ y nd, y ∈ rho.honest →
    postClock E rho y (SA.gateTime p.toParams sB) = some nd →
    eraseFG B ∈ (fastWriteAt nd.st sB).getD [] →
    FastSupportScope E rho sB (SA.voteTime p.toParams l) y
  receipts : ∀ i K s u (k : Nat) (x : V), SourceBefore p c E rho i K s → s ≤ u →
    E.t_GST ≤ SA.voteTime p.toParams u → x ∈ rho.honest →
    rho.events[k]? = some (.tick x (SA.voteTime p.toParams (u + 1))) →
    joinedAt p E rho x (u + 1) (SA.voteTime p.toParams (u + 1)) →
    FGBlock.Preceq (storeAt p c E rho k x).fg.F K →
    TargetReceiptService E rho (eraseFG K) (SA.freezeTime p.toParams u) x

private theorem loss_freeze_epoch [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF) {x : V} (hx : x ∈ rho.honest) {u : Slot}
    (hgst : E.t_GST ≤ SA.voteTime p.toParams u) (k : Nat) :
    V2.D.restartFree rho x (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams u)) k := by
  have hTime : E.t_GST + 1 ≤ SA.freezeTime p.toParams u := by
    have hp : (0 : Int) < p.Δ := p.deltaPos
    have hd : (1 : Int) ≤ p.Δ := by omega
    change E.t_GST ≤ 4 * p.Δ * (u : Int) + p.Δ at hgst
    change E.t_GST + 1 ≤ 4 * p.Δ * (u : Int) + 3 * p.Δ
    linarith
  exact healing_recovery_epoch E rho hrec hx (fgsa_idxBefore_mono rho hTime)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B `cause` (finality coverage first); blueprint
21:2689–2716. DC: SAME HEAD walk from the live root above Z. A block below the
root Z or below F of the store at a HEAD tick is an ancestor of that HEAD. -/
theorem healing_head_covers_root {k : Nat} {x : V} {t : Time}
    (hk : rho.events[k]? = some (.tick x t)) {l : Slot} (hl : l ≠ 0)
    {B : FGBlock (Fin p.n)}
    (hB : FGBlock.Preceq B (R_at p c E rho k x).Z ∨
      FGBlock.Preceq B (storeAt p c E rho k x).fg.F) :
    Block.Preceq (eraseFG B) (headAtIdx p c E rho k l) := by
  have hI : CStoreInv p (storeAt p c E rho k x) := cstoreInv_stateBefore E rho k x
  have hBZ : FGBlock.Preceq B (R_at p c E rho k x).Z := by
    rcases hB with h | h
    · exact h
    · refine KitFG.preceq_trans h ?_
      change FGBlock.Preceq _ (if (R_at p c E rho k x).rootIsJ then
        (storeAt p c E rho k x).fg.J else (storeAt p c E rho k x).fg.F)
      split
      · exact hI.fg.FJ
      · exact KitFG.preceq_refl _
  rw [healing_headAtIdx_tick p c E rho hk]
  change Block.Preceq _ (FGSA.headVote p (FGSA.clock p (storeAt p c E rho k x) t) l)
  have hc : FGSA.controls p (FGSA.clock p (storeAt p c E rho k x) t) = R_at p c E rho k x := by
    change KitFG.treeStoreControlsView (heightView p) (FGSA.clock p (storeAt p c E rho k x) t).fg =
      KitFG.treeStoreControlsView (heightView p) (storeAt p c E rho k x).fg
    rw [clock_fg]
  rw [fgsa_headVote_eq_filtered, ite_eq_right hl]
  have hZ := fgsa_Z_preceq_liveRoot p (FGSA.clock p (storeAt p c E rho k x) t)
  rw [hc] at hZ
  exact Gen.Pure.block_preceq_trans (eraseFG_preceq hBZ)
    (Gen.Pure.block_preceq_trans hZ (liveRoot_preceq_headInTree p _ _ _ _))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B `cause` (l ≥ sB + 2); blueprint 21:2777–2798.
DC: SAME schedule arithmetic. At a HEAD tick of label at least sB + 2 the row
of a source of label sB is an earlier event: d_sB < v_(sB+2). -/
theorem healing_loss_late_source (hs : V2.D.ScheduleWellFormed E rho)
    {B : FGBlock (Fin p.n)} {sB : Slot} (hB : SrcN p c E rho B sB)
    {k : Nat} {x : V} {l : Slot} (hl : sB + 2 ≤ l)
    (hk : rho.events[k]? = some (.tick x (SA.voteTime p.toParams l))) :
    SourceBefore p c E rho k B sB := by
  rw [SrcN_def] at hB
  obtain ⟨j, y, r, a, -, ha, hBs, rfl⟩ := hB
  refine ⟨j, y, r, a, healing_idx_lt_of_time_lt p c E rho hs ha.2.1 hk ?_, ha, hBs, rfl⟩
  have hl' : ((r * p.R : Nat) : Int) + 2 ≤ (l : Int) := by exact_mod_cast hl
  change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ < 4 * p.Δ * (l : Int) + p.Δ
  nlinarith [p.deltaPos]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B `cause` (old/same/later origin; first transfer
handled separately, blocker B2); blueprint 21:2730–2741.
DC: INTENTIONAL global event-index measure. At a loss of the high source B at
a HEAD tick of label l > sB, no earlier source C, as high as B, conflicts with
B unless an earlier loss exists. Label below sB: the supporter of B at v_sB
loses C. Label sB: `same`. Label above sB: the supporter of C loses B before
v_l. No row of B before the loss is used, so l = sB + 1 is included. -/
theorem healing_loss_single_cause [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hScopes : LossServiceScope p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {k : Nat} (noLoss : ∀ k' < k, ∀ B sB, ¬ Lost p c E rho B sB k')
    {B : FGBlock (Fin p.n)} {sB : Slot} {x : V} {l : Slot}
    (hB : HighSrcN p c E rho B sB) (hl : sB + 1 ≤ l)
    (hk : rho.events[k]? = some (.tick x (SA.voteTime p.toParams l)))
    {C : FGBlock (Fin p.n)} {s' : Slot} (hC : SourceBefore p c E rho k C s')
    (hn : ¬ Block.Compatible (eraseFG B) (eraseFG C))
    (hh : (heightView p B).h ≤ (heightView p C).h) : False := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hB' := hB
  rw [HighSrcN_def, SrcN_def] at hB'
  have hcC : muOf p c E rho + 1 ≤ (heightView p C).h := hB'.2.trans hh
  have hCh : HighSrcN p c E rho C s' := by
    rw [HighSrcN_def]
    exact ⟨healing_srcN_of_source p c E rho hC, hcC⟩
  have hd := p.deltaPos
  have hvote : ∀ u : Slot, u < l → SA.voteTime p.toParams u <
      (V2.Event.tick x (SA.voteTime p.toParams l) : V2.Event V (fgsa p c).Object).time := by
    intro u hu
    have hu' : (u : Int) + 1 ≤ (l : Int) := by exact_mod_cast hu
    change 4 * p.Δ * (u : Int) + p.Δ < 4 * p.Δ * (l : Int) + p.Δ
    nlinarith
  have hCl : s' < l := by
    have hg := healing_source_gate p c E rho hS hC hk
    change 4 * p.Δ * (s' : Int) + 6 * p.Δ ≤ 4 * p.Δ * (l : Int) + p.Δ at hg
    have hlt : (s' : Int) < l := by
      by_contra hn'
      have : (l : Int) ≤ s' := Int.not_lt.mp hn'
      nlinarith
    exact_mod_cast hlt
  rcases lt_trichotomy s' sB with hlt | rfl | hgt
  · obtain ⟨k₀, hL, hord⟩ := healing_loss_of_supporter p c E rho hrec.toRecovery₂ emittedNonempty
      emittedName hB'.1 hCh hlt (fun h => hn (by
        change (Block.preceq _ _ || Block.preceq _ _) = true at h ⊢
        rw [Bool.or_comm]
        exact h))
    exact noLoss k₀ (hord k _ hk (hvote sB hl)) C s' hL
  · exact hn (healing_loss_same p c E rho hrec.toRecovery₂ emittedNonempty emittedName
      hScopes.same _ B C s' hB'.1
      ((SrcN_def p c E rho C s') ▸ healing_srcN_of_source p c E rho hC) hB'.2 hcC)
  · obtain ⟨k₀, hL, hord⟩ := healing_loss_of_supporter p c E rho hrec.toRecovery₂ emittedNonempty
      emittedName hC hB hgt hn
    exact noLoss k₀ (hord k _ hk (hvote s' hCl)) B sB hL

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan fgsa-s5-m5-d2d4 B `cause`; blueprint 21:2689–2741, 2767–2813
(fj.descent.v3). DC: INTENTIONAL global event-index measure. At a loss read
with no earlier loss, the restricted descent of B in a view X of the store
gives the incompatible high pair of earlier sources. The F and Z keep cases
contradict the loss by root coverage; the single-source cause contradicts
`noLoss`. `domain` is the H.1/H.2 HEAD coverage of a kept domain block. -/
theorem healing_loss_cause_of_view [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hScopes : LossServiceScope p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {k : Nat} (noLoss : ∀ k' < k, ∀ B sB, ¬ Lost p c E rho B sB k')
    {B : FGBlock (Fin p.n)} {sB : Slot} {x : V} {l : Slot}
    (hB : HighSrcN p c E rho B sB) (hx : x ∈ rho.honest) (hl : sB + 1 ≤ l)
    (hk : rho.events[k]? = some (.tick x (SA.voteTime p.toParams l)))
    (hn : ¬ Block.Preceq (eraseFG B) (headAtIdx p c E rho k l))
    {X : Finset (FGBlock (Fin p.n))} (hX : X ⊆ (storeAt p c E rho k x).fg.TF) (hBX : B ∈ X)
    (cover : ∀ K s, SourceBefore p c E rho k K s →
      FGBlock.Preceq (storeAt p c E rho k x).fg.F K → FGBlock.Preceq B K →
      (heightView p B).h < (heightView p K).h →
      K ∈ X ∨ FGBlock.Preceq K (storeAt p c E rho k x).fg.F)
    (domain : B ∈ D_at p c E rho k x X → Block.Preceq (eraseFG B) (headAtIdx p c E rho k l)) :
    ∃ K₁ K₂ s₁ s₂, SourceBefore p c E rho k K₁ s₁ ∧ SourceBefore p c E rho k K₂ s₂ ∧
      muOf p c E rho + 1 ≤ (heightView p K₁).h ∧ muOf p c E rho + 1 ≤ (heightView p K₂).h ∧
      ¬ Block.Compatible (eraseFG K₁) (eraseFG K₂) := by
  have hl0 : l ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.succ_pos sB) hl)
  rcases healing_descent (hroots := hrec.base.idealization) p c E rho xing origin hx hX hBX cover
    with
    (hZ | hD | hF) | ⟨C, s', hC, hnC, hh⟩ | ⟨C₁, C₂, s₁, s₂, h₁, h₂, hh, hlt, hr⟩
  · exact absurd (healing_head_covers_root p c E rho hk hl0 (Or.inl hZ)) hn
  · exact absurd (domain hD) hn
  · exact absurd (healing_head_covers_root p c E rho hk hl0 (Or.inr hF)) hn
  · exact (healing_loss_single_cause p c E rho hrec hScopes emittedNonempty emittedName noLoss hB hl
      hk hC hnC hh).elim
  · have hc₁ : muOf p c E rho + 1 ≤ (heightView p C₁).h := by
      have := ((HighSrcN_def p c E rho B sB) ▸ hB).2
      simp only [Height] at *
      omega
    exact ⟨C₁, C₂, s₁, s₂, h₁, h₂, hc₁, hh ▸ hc₁,
      healing_entry_pair_incompatible p hh hr⟩

omit [DecidableEq V] in
private theorem cause_compat_of_erase {A B : FGBlock (Fin p.n)}
    (h : Block.Compatible (eraseFG A) (eraseFG B)) :
    FGBlock.Preceq A B ∨ FGBlock.Preceq B A := by
  change (Block.preceq (eraseFG A) (eraseFG B) ||
    Block.preceq (eraseFG B) (eraseFG A)) = true at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact Or.inl (eraseFG_preceq_iff.mp h)
  · exact Or.inr (eraseFG_preceq_iff.mp h)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B `cause` (the H.2 coverage input); blueprint
21:709–715. DC: INTENTIONAL global event-index measure. Before the first
loss, every honest HEAD at a label above sB whose vote time is before the time
of event k covers the high source B: its tick is an earlier event. -/
theorem healing_noLoss_heads (hs : V2.D.ScheduleWellFormed E rho)
    {k : Nat} (noLoss : ∀ k' < k, ∀ B sB, ¬ Lost p c E rho B sB k')
    {B : FGBlock (Fin p.n)} {sB : Slot} (hB : HighSrcN p c E rho B sB)
    {ev : V2.Event V (fgsa p c).Object} (hk : rho.events[k]? = some ev)
    {w : Slot} (hw : sB + 1 ≤ w) (hwt : SA.voteTime p.toParams w < ev.time) :
    ∀ z ∈ rho.honest, ∀ K, headAtLabel p c E rho z w = some K → Block.Preceq (eraseFG B) K := by
  intro z hz K hK
  delta headAtLabel at hK
  rw [postClock_def, preTick_def] at hK
  cases hjz' : V2.D.Run.tickIdx? rho z (SA.voteTime p.toParams w) with
  | none => rw [hjz'] at hK; cases hK
  | some jz =>
  rw [hjz'] at hK
  have hjz := V2.D.Run.tickIdx?_spec hjz'
  have hKe : K = headAtIdx p c E rho jz w := by
    rw [healing_headAtIdx_tick p c E rho hjz]
    exact (Option.some.inj hK).symm
  have hlt : jz < k := healing_idx_lt_of_time_lt p c E rho hs hjz hk hwt
  by_contra hn
  rw [hKe] at hn
  exact noLoss jz hlt B sB (by
    rw [Lost_def]
    exact ⟨hB, z, w, hz, hw, hjz, hn⟩)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan fgsa-s5-m5-d2d4 B `cause` (finality coverage first); blueprint
21:2689–2716 (IF.3(c)), 526–546 (W3). DC: INTENTIONAL global event-index
measure. At a loss read with no earlier loss, F of the reader is below the
lost high source B. If F conflicts with B or is above B: either the height of
B is above the certificate height of F, and R-XING (B is held by its source
node) puts F below B; or the target source of F is as high as B and conflicts
with B, which gives an earlier loss; or B is below F and the HEAD covers B. -/
theorem healing_loss_F_below [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hScopes : LossServiceScope p c E rho)
    (emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho)
    {k : Nat} (noLoss : ∀ k' < k, ∀ B sB, ¬ Lost p c E rho B sB k')
    {B : FGBlock (Fin p.n)} {sB : Slot} {x : V} {l : Slot}
    (hB : HighSrcN p c E rho B sB) (hx : x ∈ rho.honest) (hl : sB + 1 ≤ l)
    (hk : rho.events[k]? = some (.tick x (SA.voteTime p.toParams l)))
    (hn : ¬ Block.Preceq (eraseFG B) (headAtIdx p c E rho k l)) :
    FGBlock.Preceq (storeAt p c E rho k x).fg.F B := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hl0 : l ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.succ_pos sB) hl)
  have hBF : ¬ FGBlock.Preceq B (storeAt p c E rho k x).fg.F := fun h =>
    hn (healing_head_covers_root p c E rho hk hl0 (Or.inr h))
  by_cases hFg : (storeAt p c E rho k x).fg.F = .genesis
  · rw [hFg]
    exact KitFG.genesis_preceq B
  obtain ⟨D, hD, hDF, K, s, hK, hKh, hKT, -⟩ :=
    healing_finality_source (hroots := hrec.base.idealization) p c E rho hS origin hx hFg
  have hFK : FGBlock.Preceq (storeAt p c E rho k x).fg.F K := by
    have he := (fgCertificateLaws p).height.entry_preceq K
    rwa [hKT] at he
  by_cases hh : (finalityView p D).h_F < (heightView p B).h
  · -- B is held by its source node at an index after k.
    have hB' := hB
    rw [HighSrcN_def, SrcN_def] at hB'
    obtain ⟨⟨j, y, r, a, -, ha, hBs, -⟩, -⟩ := hB'
    have hj := ha.2.1
    have hBTF : B ∈ (storeAt p c E rho j y).fg.TF := by
      have hr := actionSourceFG_eq_round p c E rho hS hj
      rw [hr] at hBs
      have hsel := FGSA.pickPair_some_spec _ _ (Option.some.inj hBs)
      have hfull := (Finset.mem_filter.mp hsel.1).1
      have hT := ((KitFG.mem_filteredFromView _ _ _ _).mp hfull).1
      change B ∈ (FGSA.clock p (storeAt p c E rho j y) (p.actionTime r)).fg.TF at hT
      rwa [clock_fg] at hT
    have hheld : HeldAt p c E rho (k + j) y B :=
      ⟨ha.1, (fgsa_store_durable p c E rho (Nat.le_add_left j k) y).1 hBTF⟩
    exact xing k (k + j) x y D B hx (Nat.le_add_right k j) hD hDF hheld hh
  · have hhK : (heightView p B).h ≤ (heightView p K).h := by
      rw [hKh]
      exact Nat.le_of_not_lt hh
    by_cases hc : Block.Compatible (eraseFG B) (eraseFG K)
    · rcases cause_compat_of_erase p hc with hBK | hKB
      · rcases KitFG.preceq_total_of_common hFK hBK with h | h
        · exact h
        · exact absurd h hBF
      · exact KitFG.preceq_trans hFK hKB
    · exact (healing_loss_single_cause p c E rho hrec hScopes emittedNonempty emittedName
        noLoss hB hl
        hk hK hc hhK).elim

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Plan fgsa-s5-m5-d2d4 B `cause` (B ∈ X and the restricted B18 cover);
blueprint 21:673–689 (relay of each supporter head), 2689–2716.
DC: INTENTIONAL per-block relay, not TDel. A source of label s ≤ u, above the
finality of an honest node x that ticks at v_(u+1), is in the store of x before
z_u: a clean early supporter target of the source gate, stamped before e_s,
reaches x by the per-block relay on [v_u, v_(u+1)], with its ancestors. -/
theorem healing_source_receipt [Fintype V] {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (hScopes : LossServiceScope p c E rho)
    (_emittedNonempty : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n},
      HonestRowAt p c E rho j x r a → ∃ e, namedEntry a.payload.height_pair = some e)
    (_emittedName : ∀ {j : Nat} {x : V} {r : Nat} {a : RowWire p.n} {e : Height × BlockId},
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e.1 = (heightView p C).h ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {i : Nat} {K : FGBlock (Fin p.n)} {s : Slot} (hK : SourceBefore p c E rho i K s)
    {u : Slot} (hsu : s ≤ u) (hgst : E.t_GST ≤ SA.voteTime p.toParams u)
    {k : Nat} {x : V} (hx : x ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick x (SA.voteTime p.toParams (u + 1))))
    (hJoin : joinedAt p E rho x (u + 1) (SA.voteTime p.toParams (u + 1)))
    (hF : FGBlock.Preceq (storeAt p c E rho k x).fg.F K) :
    K ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams u)) x).fg.TF := by
  have hS := hrec.base.valid.toScheduleWellFormed
  have hb := fgsa_target_receipt_on E rho hS hrec.base.receiptIdealization (eraseFG K)
    (SA.freezeTime p.toParams u) x hx (hScopes.receipts i K s u k x hK hsu hgst hx hk hJoin hF)
  obtain ⟨Y, hY, heY⟩ := ((storeBundle_stateBeforeTime E rho _ x).cstore.baseTree _).mp hb
  have he : Y = K := eraseFG_injective heY
  subst Y
  change K ∈ (rho.stateBefore E (V2.D.Run.idxBefore rho _) x).st.fg.TF
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
  exact hY

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B `cause` (moving-frame keep: path, leases and scores
together); blueprint 21:673–715, 2689–2728. DC: INTENTIONAL moving frame.
At a loss read of label i + 1 with no earlier loss, let X be the store of the
reader before z_i. If B is in the domain of X, the HEAD covers B: by H.1 at
i = sB, by H.2 with the lease bound at i ≥ sB + 1. -/
theorem healing_loss_domain [Fintype V] {G ΔF : Time}
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
    {k : Nat} (noLoss : ∀ k' < k, ∀ B sB, ¬ Lost p c E rho B sB k')
    {B : FGBlock (Fin p.n)} {sB : Slot} {x : V} {i : Slot}
    (hB : HighSrcN p c E rho B sB) (hx : x ∈ rho.honest) (hl : sB ≤ i)
    (hk : rho.events[k]? = some (.tick x (SA.voteTime p.toParams (i + 1))))
    (hFB : FGBlock.Preceq (storeAt p c E rho k x).fg.F B)
    (hD : B ∈ D_at p c E rho k x
      (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams i)) x).fg.TF) :
    Block.Preceq (eraseFG B) (headAtIdx p c E rho k (i + 1)) := by
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  have hd := p.deltaPos
  let D := SA.freezeTime p.toParams i
  classical
  let X := (storeAt p c E rho (V2.D.Run.idxBefore rho D) x).fg.TF.filter
    (fun A => FGBlock.Preceq (storeAt p c E rho k x).fg.F A)
  have hDX : B ∈ D_at p c E rho k x X := by
    obtain ⟨hBmem, hFB', hZB, W, hW, hBW, hlo⟩ :=
      (KitFG.mem_filteredFromView _ _ _ _).mp hD
    exact (KitFG.mem_filteredFromView _ _ _ _).mpr
      ⟨Finset.mem_filter.mpr ⟨hBmem, hFB⟩, hFB', hZB, W,
        Finset.mem_filter.mpr ⟨hW, KitFG.preceq_trans hFB hBW⟩, hBW, hlo⟩
  have hread : postClock E rho x (SA.voteTime p.toParams (i + 1)) =
      some ((fgsa p c).clock (V2.D.Run.stateBefore E rho k x)
        (SA.voteTime p.toParams (i + 1))) := by
    rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hS hk]
    rfl
  have hdpos : 0 < D := by
    change 0 < 4 * p.Δ * (i : Int) + 3 * p.Δ
    positivity
  have hdvote : D ≤ SA.voteTime p.toParams (i + 1) := by
    change 4 * p.Δ * (i : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith
  have hdfreeze : D ≤ SA.freezeTime p.toParams (i + 1 - 1) := by
    rw [Nat.add_sub_cancel]
  have hBSource := ((HighSrcN_def p c E rho B sB) ▸ hB).1
  have hgst0 := healing_high_source_sync p c E rho emittedNonempty emittedName
    ((SrcN_def p c E rho B sB) ▸ hBSource) (((HighSrcN_def p c E rho B sB) ▸ hB).2)
  have hgsti0 : E.t_GST ≤ SA.voteTime p.toParams i := by
    refine hgst0.trans ?_
    have hsi : (sB : Int) ≤ (i : Int) := by exact_mod_cast hl
    change 4 * p.Δ * (sB : Int) + p.Δ ≤ 4 * p.Δ * (i : Int) + p.Δ
    nlinarith [p.deltaPos]
  have hEpoch := loss_freeze_epoch p c E rho hrec hx hgsti0 k
  have hXv : X ⊆ voterBlocks p (FGSA.clock p (storeAt p c E rho k x)
      (SA.voteTime p.toParams (i + 1))) (i + 1) := by
    intro W hW
    obtain ⟨hW, hFW⟩ := Finset.mem_filter.mp hW
    exact healing_frozen_path_on p c E rho hS hdpos hdvote hdfreeze hW hread (by
      intro j hj
      have he : j = k := Option.some.inj
        ((fgsa_tickIdx_of_event p c E rho hS hj).symm.trans
          (fgsa_tickIdx_of_event p c E rho hS hk))
      exact he.symm ▸ hEpoch) W
      (by change FGBlock.Preceq (FGSA.clock p _ _).fg.F W; rw [clock_fg]; exact hFW)
      (KitFG.preceq_refl W)
  have hXc : ∀ W ∈ X, ∀ A, FGBlock.Preceq (storeAt p c E rho k x).fg.F A →
      FGBlock.Preceq A W → A ∈ X := by
    intro W hW A hFA hAW
    obtain ⟨hW, -⟩ := Finset.mem_filter.mp hW
    have hinv := (storeBundle_stateBefore E rho (V2.D.Run.idxBefore rho D) x).cstore
    obtain ⟨A', hA', he⟩ := eraseFG_ancestor_mem hinv.fg.closed hW (eraseFG_preceq hAW)
    exact Finset.mem_filter.mpr ⟨(eraseFG_injective he) ▸ hA', hFA⟩
  have hsrc := hB
  rw [HighSrcN_def, SrcN_def] at hsrc
  have hCut := healing_high_source_window p c E rho emittedNonempty emittedName hsrc.1 hsrc.2
  have hci := hCut.cut_mono hl
  have hJoin := healing_recovery_joined_vote_next E rho hrec hci hx hk
  rcases Nat.eq_or_lt_of_le hl with rfl | hlt
  · exact healing_first_transfer_domain p c E rho hrec.toRecovery₂ emittedNonempty emittedName
      hB hx hk (hScopes.first B sB k x hB hx hk hJoin) hXv hXc hDX
  · have hB' := hB
    rw [HighSrcN_def] at hB'
    have hgst := healing_high_source_sync p c E rho emittedNonempty emittedName
      ((SrcN_def p c E rho B sB) ▸ hB'.1) hB'.2
    have hgsti : E.t_GST ≤ SA.voteTime p.toParams i := by
      refine hgst.trans ?_
      have hsi : (sB : Int) ≤ (i : Int) := by exact_mod_cast hl
      change 4 * p.Δ * (sB : Int) + p.Δ ≤ 4 * p.Δ * (i : Int) + p.Δ
      nlinarith
    have hcover := healing_noLoss_heads p c E rho hS noLoss hB hk (w := i) hlt (by
      change 4 * p.Δ * (i : Int) + p.Δ < 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
      push_cast
      linarith)
    have hlease := healing_loss_lease_late p c E rho hrec mono emittedNonempty emittedName
      writes noLoss hB hx (show sB + 2 ≤ i + 1 from Nat.succ_le_succ hlt) hk
      (hScopes.fast B sB (i + 1) k x hB (Nat.succ_le_succ hlt) hx hk)
      (eraseFG_preceq hFB)
    exact healing_next_transfer_domain p c E rho hrec mono hgsti hcover hx hk
      (hScopes.next B sB i k x hB hlt hx hk hJoin) hci hXv hXc hDX hlease

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B `cause`; blueprint 21:2677–2741, 2767–2813
(fj.descent.v3). DC: INTENTIONAL global event-index measure. The `cause`
input of `healing_high_source_first_failure` at c₀ = μ + 1: at a loss with no
earlier loss, two earlier incompatible high sources exist. The view is the
store of the reader before z_(l-1); F is below B (`healing_loss_F_below`); B
and every source above F are in the view (`healing_source_receipt`); the
descent then gives a cause (`healing_loss_cause_of_view`). The first transfer
l = sB + 1 needs no row of B before the loss (blocker B2). -/
theorem healing_loss_cause [Fintype V] {G ΔF : Time}
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
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho) :
    ∀ k K s, (∀ k' < k, ∀ B sB, ¬ Lost p c E rho B sB k') → Lost p c E rho K s k →
      ∃ K₁ K₂ s₁ s₂, SourceBefore p c E rho k K₁ s₁ ∧ SourceBefore p c E rho k K₂ s₂ ∧
        muOf p c E rho + 1 ≤ (heightView p K₁).h ∧ muOf p c E rho + 1 ≤ (heightView p K₂).h ∧
        ¬ Block.Compatible (eraseFG K₁) (eraseFG K₂) := by
  intro k B sB noLoss hL
  have hE := hrec.base.valid
  have hS := hE.toScheduleWellFormed
  rw [Lost_def] at hL
  obtain ⟨hB, x, l, hx, hl, hk, hn⟩ := hL
  obtain ⟨i, rfl⟩ : ∃ i, l = i + 1 :=
    ⟨l - 1, (Nat.sub_add_cancel (le_trans (Nat.succ_pos sB) hl)).symm⟩
  have hsi : sB ≤ i := Nat.le_of_succ_le_succ hl
  have hFB := healing_loss_F_below p c E rho hrec hScopes emittedNonempty emittedName xing origin
    noLoss hB hx hl hk hn
  have hB' := hB
  rw [HighSrcN_def] at hB'
  have hsrc := (SrcN_def p c E rho B sB) ▸ hB'.1
  have hgst := healing_high_source_sync p c E rho emittedNonempty emittedName hsrc hB'.2
  have hCut := healing_high_source_window p c E rho emittedNonempty emittedName hsrc hB'.2
  have hJoin := healing_recovery_joined_vote_next E rho hrec (hCut.cut_mono hsi) hx hk
  have hgsti : E.t_GST ≤ SA.voteTime p.toParams i := by
    refine hgst.trans ?_
    have hsi' : (sB : Int) ≤ (i : Int) := by exact_mod_cast hsi
    change 4 * p.Δ * (sB : Int) + p.Δ ≤ 4 * p.Δ * (i : Int) + p.Δ
    nlinarith [p.deltaPos]
  let D := SA.freezeTime p.toParams i
  have hDk : V2.D.Run.idxBefore rho D ≤ k := healing_support_idxBefore_le p c E rho hS hk (by
    change 4 * p.Δ * (i : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos])
  have hX : (storeAt p c E rho (V2.D.Run.idxBefore rho D) x).fg.TF ⊆
      (storeAt p c E rho k x).fg.TF := (fgsa_store_durable p c E rho hDk x).1
  have hBX := healing_source_receipt p c E rho hrec hScopes
    emittedNonempty emittedName hsrc hsi hgsti
    hx hk hJoin hFB
  refine healing_loss_cause_of_view p c E rho hrec hScopes emittedNonempty emittedName xing origin
    noLoss hB hx hl hk hn hX hBX ?_
    (healing_loss_domain p c E rho hrec hScopes mono emittedNonempty emittedName writes noLoss hB hx
      hsi hk hFB)
  intro K s hK hFK _ _
  left
  have hsl : s ≤ i := by
    have hg := healing_source_gate p c E rho hS hK hk
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((i + 1 : Nat) : Int) + p.Δ at hg
    push_cast at hg
    have hlt : (s : Int) ≤ i := by
      by_contra hn'
      have : (i : Int) + 1 ≤ s := by omega
      nlinarith [p.deltaPos]
    exact_mod_cast hlt
  exact healing_source_receipt p c E rho hrec hScopes
    emittedNonempty emittedName hK hsl hgsti hx hk hJoin hFK

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B; blueprint 21:2677–2741 (fj.descent.v3).
DC: INTENTIONAL global event-index measure. `healing_high_source_first_failure`
at c₀ = μ + 1 with the concrete `Lost`, `same` (IF.6), the corrected `support`
and `cause`: no high source is lost, and all high sources with rows before any
index are pairwise compatible. -/
theorem healing_high_source_compat [Fintype V] {G ΔF : Time}
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
    (xing : RXing p c E rho) (origin : RQCOrigin p c E rho) :
    (∀ k K s, ¬ Lost p c E rho K s k) ∧
      ∀ i K K' s s', SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s' →
        muOf p c E rho + 1 ≤ (heightView p K).h → muOf p c E rho + 1 ≤ (heightView p K').h →
        Block.Compatible (eraseFG K) (eraseFG K') :=
  healing_high_source_first_failure p c E rho (muOf p c E rho + 1) (Lost p c E rho)
    (healing_loss_same p c E rho hrec.toRecovery₂ emittedNonempty emittedName hScopes.same)
    (healing_loss_support p c E rho hrec.toRecovery₂ emittedNonempty emittedName)
    (healing_loss_cause p c E rho hrec hScopes mono emittedNonempty emittedName writes xing origin)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Plan fgsa-s5-m5-d2d4 B (the H0Reset.mu_le specialization); blueprint
21:3002–3004 (high), 1579–1582 (μ ≤ M). DC: SAME high threshold M + 1.
Sources of height at least M + 1 are pairwise compatible: μ ≤ M. -/
theorem healing_high_source_compat_reset [Fintype V] {G ΔF : Time}
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
    {w : HealingWitness} (h0 : H0Reset p c E rho w) :
    ∀ i K K' s s', SourceBefore p c E rho i K s → SourceBefore p c E rho i K' s' →
      high p w K → high p w K' → Block.Compatible (eraseFG K) (eraseFG K') := by
  intro i K K' s s' hK hK' hc hc'
  have hμ := h0.mu_le
  have hc0 : muOf p c E rho + 1 ≤ (heightView p K).h := le_trans (Nat.succ_le_succ hμ) hc
  have hc0' : muOf p c E rho + 1 ≤ (heightView p K').h := le_trans (Nat.succ_le_succ hμ) hc'
  exact (healing_high_source_compat p c E rho hrec hScopes mono
    emittedNonempty emittedName writes xing
    origin).2 i K K' s s' hK hK' hc0 hc0'

end AvailableChain.FGSA.Run
end

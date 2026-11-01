module
public import AvailableChainFGSAProofs.Proofs.Outage.ContinuationFrame
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Outage.ReceiverInputs -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceFrame

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- A received marker is durable across wakes. Only the actual HEAD reader is used.
No stamp or vote-pool persistence is requested across a restart. -/
theorem outage_received_marker_head_scoped
    (hmono : RMonoAll p c E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hstrat : RStrat p c E rho)
    {j i : Nat} {x : V} {B P : FGBlock (Fin p.n)} (s : Slot)
    (hx : x ∈ rho.honest) (hji : j ≤ i) (_hi : i ≤ rho.events.length)
    (hreceipt : Block.Preceq (eraseFG B) (F_at p c E rho j x) ∨
      P ∈ (storeAt p c E rho j x).fg.TF)
    (hBJ : FGBlock.Preceq B (heightView p P).J) (hnz : (heightView p P).h_j ≠ 0)
    (hnames : OutageNamedHistory p c E rho B i)
    (hlocks : ∀ row ∈ (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)).base.obligations,
      (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)).base.now < row.2.2 →
      Block.Compatible row.1 (eraseFG B)) :
    Block.Compatible (headVote p
      (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)) s) (eraseFG B) := by
  have _hcanonicalFrame := hframe
  let dst := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)
  have hinv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x) (SA.voteTime p.toParams s)
  by_cases hs : s = 0
  · rw [hs, headVote_zero]
    exact block_compatible_of_common (block_genesis_preceq _) (block_preceq_refl _)
  have hc := fgsa_cpCompat_of_scopedFrame p c E rho hstore hstrat i x B hx hnames.history
  have hctrl : controls p dst = controls p (storeAt p c E rho i x) := by
    change KitFG.treeStoreControlsView (heightView p) (clock p _ _).fg = _
    rw [clock_fg]
    rfl
  have hfg : dst.fg = (storeAt p c E rho i x).fg := clock_fg p _ _
  by_cases hBF : Block.Preceq (eraseFG B) (F_at p c E rho i x)
  · have hBroot : Block.Preceq (eraseFG B) (liveRoot p dst) := by
      apply block_preceq_trans (B := eraseFG dst.fg.F) ?_ (F_preceq_liveRoot p dst hinv)
      rw [hfg]
      exact hBF
    have hh : Block.Preceq (eraseFG B) (headVote p dst s) := by
      change Block.Preceq _ (if s = 0 then .genesis else headInTree p dst _ _ _)
      rw [ite_eq_right hs]
      exact block_preceq_trans hBroot (liveRoot_preceq_headInTree p dst _ _ _)
    exact Bool.or_eq_true_iff.mpr (Or.inr hh)
  have hFB : FGBlock.Preceq dst.fg.F B := by
    rw [hfg]
    rcases hc.2.1 with h | h
    · exact h
    · exact (hBF (eraseFG_preceq h)).elim
  have hP : P ∈ dst.fg.TF := by
    rw [hfg]
    rcases hreceipt with h | h
    · exact (hBF (block_preceq_trans h (eraseFG_preceq (hmono j i x hx hji).1))).elim
    · exact (fgsa_store_durable p c E rho hji x).1 h
  have hmark := outageV_received_height p dst hinv hP (preceq_trans hFB hBJ)
  have hZ : Block.Compatible (eraseFG (controls p dst).Z) (eraseFG B) := by
    rw [hctrl]
    have hz : FGBlock.Preceq (controls p (storeAt p c E rho i x)).Z B ∨
        FGBlock.Preceq B (controls p (storeAt p c E rho i x)).Z := by
      change FGBlock.Preceq (if (controls p _).rootIsJ then _ else _) B ∨
        FGBlock.Preceq B (if (controls p _).rootIsJ then _ else _)
      cases he : (controls p (storeAt p c E rho i x)).rootIsJ
      · exact hc.2.1
      · exact hc.2.2.1
    exact Bool.or_eq_true_iff.mpr (hz.imp eraseFG_preceq eraseFG_preceq)
  apply outageV_marker_head p dst hinv s
    (outageV_liveRoot_compatible p dst (eraseFG B) hZ hlocks) hBJ
    ((fgJustificationLaws p).J_entry P)
    (by rw [(fgJustificationLaws p).J_height P hnz]; exact hmark)
  · rw [hfg]
    exact hc.2.2.1
  · intro ht W hW hh
    rw [hctrl] at ht hh
    rw [hfg] at hW
    have htop := hc.2.2.2.2 ht
    exact outageV_contest_top p _ B htop.1 htop.2 W hW hh
  · intro W hW U hUW hh
    rw [hfg] at hW
    apply hc.1 W hW
    rw [certified_def]
    exact ⟨U, hUW, Or.inr (Or.inr ⟨rfl, hh⟩)⟩

/-- OUTPUT-DIRECT §§2–4. DC: INTENTIONAL; the event output and original
names supply live-root compatibility at the actual clocked HEAD read. -/
theorem outage_clocked_root_compatible_scoped
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hstrat : RStrat p c E rho) {i : Nat} {x : V} {s : Slot}
    (ht : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hx : x ∈ rho.honest) (B : FGBlock (Fin p.n))
    (hnames : OutageNamedHistory p c E rho B i)
    (hS : Block.Preceq (eraseFG B) (S_at p c E rho (i + 1) x)) :
    let dst := clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)
    Block.Compatible (liveRoot p dst) (eraseFG B) ∧
      ∀ row ∈ dst.base.obligations, dst.base.now < row.2.2 →
        Block.Compatible row.1 (eraseFG B) := by
  have _hcanonicalFrame := hframe
  intro dst
  have hpost : storeAt p c E rho (i + 1) x = dst := by
    change (V2.D.Run.stateBefore E rho (i + 1) x).st = _
    rw [(V2.D.Run.step_tick_eq E rho ht).1]
    exact tick_st (c := c) E rho _ x _
  have hlocks : ∀ row ∈ (storeAt p c E rho (i + 1) x).base.obligations,
      (storeAt p c E rho (i + 1) x).base.now < row.2.2 →
      Block.Compatible row.1 (eraseFG B) := by
    intro row hr hl
    exact block_compatible_of_common
      (leaseBelowOutput_stateBefore E rho (i + 1) x row hr hl) hS
  rw [hpost] at hlocks
  refine ⟨?_, hlocks⟩
  apply outageV_liveRoot_compatible p dst (eraseFG B) ?_ hlocks
  have hc := fgsa_cpCompat_of_scopedFrame p c E rho hstore hstrat i x B hx hnames.history
  have hctrl : controls p dst = controls p (storeAt p c E rho i x) := by
    change KitFG.treeStoreControlsView (heightView p) (clock p _ _).fg = _
    rw [clock_fg]
    rfl
  rw [hctrl]
  have hz : FGBlock.Preceq (controls p (storeAt p c E rho i x)).Z B ∨
      FGBlock.Preceq B (controls p (storeAt p c E rho i x)).Z := by
    change FGBlock.Preceq (if (controls p _).rootIsJ then _ else _) B ∨
      FGBlock.Preceq B (if (controls p _).rootIsJ then _ else _)
    cases he : (controls p (storeAt p c E rho i x)).rootIsJ
    · exact hc.2.1
    · exact hc.2.2.1
  exact Bool.or_eq_true_iff.mpr (hz.imp eraseFG_preceq eraseFG_preceq)

/-- OUTPUT-DIRECT §4. DC: INTENTIONAL; source names and post-tick S
protect a contested scheduled HEAD without a receipt or score premise. -/
theorem outage_clocked_contested_head_scoped
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hstrat : RStrat p c E rho) {i : Nat} {x : V} {s : Slot}
    (ht : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hx : x ∈ rho.honest) (B : FGBlock (Fin p.n))
    (hnames : OutageNamedHistory p c E rho B i)
    (hS : Block.Preceq (eraseFG B) (S_at p c E rho (i + 1) x))
    (hcontest : (controls p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams s))).contest = true) :
    Block.Compatible (headVote p (clock p (storeAt p c E rho i x)
      (SA.voteTime p.toParams s)) s) (eraseFG B) := by
  have hctrl : controls p (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s)) =
      controls p (storeAt p c E rho i x) := by
    change KitFG.treeStoreControlsView (heightView p) (clock p _ _).fg = _
    rw [clock_fg]
    rfl
  have hct : (R_at p c E rho i x).contest = true := by
    change (controls p (storeAt p c E rho i x)).contest = true
    rw [← hctrl]
    exact hcontest
  have hc := (fgsa_cpCompat_of_scopedFrame p c E rho hstore hstrat
    i x B hx hnames.history).2.2.2.2 hct
  apply outageV_contested_head p _ (cstoreInv_clock p _ (cstoreInv_stateBefore E rho i x) _)
    B s (outage_clocked_root_compatible_scoped hstore hframe hstrat ht hx B hnames hS).1 ?_ hcontest
  intro W hW hh
  rw [clock_fg] at hW
  change (heightView p W).h = (controls p (clock p (storeAt p c E rho i x)
    (SA.voteTime p.toParams s))).H at hh
  rw [hctrl] at hh
  exact outageV_contest_top p _ B hc.1 hc.2 W hW hh

/-- An earlier stored marker is served at the later joined HEAD read.
The public anchor is this slot start, after GST; the target floor is local. -/
theorem outage_later_marker_receipt {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hmono : RMonoAll p c E rho) {k i : Nat} {y x : V} {m s : Slot}
    {B P : FGBlock (Fin p.n)}
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams m)))
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hms : m ≤ s) (hGST : E.t_GST ≤ SA.voteTime p.toParams m)
    (hP : P ∈ (storeAt p c E rho k y).fg.TF)
    (hBP : FGBlock.Preceq B P)
    (hF : Block.Compatible (F_at p c E rho i x) (eraseFG B)) :
    Block.Preceq (eraseFG B) (F_at p c E rho i x) ∨
      P ∈ (storeAt p c E rho i x).fg.TF := by
  have hs := hBase.valid.toScheduleWellFormed
  by_cases hBF : Block.Preceq (eraseFG B) (F_at p c E rho i x)
  · exact Or.inl hBF
  have hFB : Block.Preceq (F_at p c E rho i x) (eraseFG B) := by
    rcases Bool.or_eq_true_iff.mp hF with h | h
    · exact h
    · exact (hBF h).elim
  have hFloor := block_preceq_trans hFB (eraseFG_preceq hBP)
  by_cases hgen : eraseFG P = .genesis
  · have hBG : Block.Preceq (eraseFG B) .genesis := by
      rw [← hgen]
      exact eraseFG_preceq hBP
    have he : B = .genesis := eraseFG_injective
      (block_preceq_antisymm hBG (block_genesis_preceq _))
    subst B
    exact (hBF (block_genesis_preceq _)).elim
  have hPm := ((cstoreInv_stateBefore E rho k y).baseTree _).mpr ⟨P, hP, rfl⟩
  obtain ⟨j, hjk, send, o, hb, ha⟩ :=
    fgsa_block_accepted_origin E rho k y (eraseFG P) hgen hPm
  have hsend : send ≤ SA.voteTime p.toParams m := by
    obtain ⟨parent, hj, _⟩ := ha.1
    by_contra hn
    have hkj := V2.D.Engine.tick_index_lt_delivery E rho hs hk hj (le_of_not_ge hn)
    omega
  let a := SA.proposalTime p.toParams (s + 1)
  have hva : SA.voteTime p.toParams m ≤ a := by
    change 4 * p.Δ * (m : Int) + p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int)
    have hcast := Int.ofNat_le.mpr hms
    push_cast
    nlinarith [p.deltaPos]
  have h0 : 0 ≤ a := by
    change 0 ≤ 4 * p.Δ * ((s + 1 : Nat) : Int)
    have := p.deltaPos
    positivity
  have hpa : SA.proposalTime p.toParams s < a := by
    change 4 * p.Δ * (s : Int) < 4 * p.Δ * ((s + 1 : Nat) : Int)
    push_cast
    linarith [p.deltaPos]
  have hpub : V2.PublicTime E a := by
    refine ⟨4 * (s + 1), ?_⟩
    rw [hBase.delta]
    change 4 * p.Δ * ((s + 1 : Nat) : Int) = ((4 * (s + 1) : Nat) : Int) * p.Δ
    push_cast
    ring
  have ht : a + p.Δ = SA.voteTime p.toParams (s + 1) := rfl
  have hservice := inclusion_service_accepted_target_service hBase.valid hBase.delta
    hSync hmono hx hy hi hJ hb ha (hsend.trans hva) h0 hpa hpub
    (hGST.trans hva) ht.le hFloor
  rw [ht] at hservice
  have hrec := fgsa_target_receipt_on E rho hs hBase.receiptIdealization _ _ x hx hservice
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hrec
  have hcut : rho.idxBefore (SA.voteTime p.toParams (s + 1)) ≤ i := by
    by_contra hn
    exact (lt_irrefl _) ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mp
      (Nat.lt_of_not_ge hn))
  have hkeep := (fgsa_store_durable p c E rho hcut x).2.1.subset hrec
  obtain ⟨P', hP', he⟩ := ((cstoreInv_stateBefore E rho i x).baseTree _).mp hkeep
  exact Or.inr (eraseFG_injective he ▸ hP')

/-- The marker transport producer and durable local frame prove this actual HEAD.
The joint induction supplies source names and compatible live rows at this read. -/
theorem outage_later_marker_head {ΔF : Time}
    (hBase : Base₂ p c E rho)
    (hSync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (hf : FGFoundation p c E rho) {k i : Nat} {y x : V} {m s : Slot}
    {B P : FGBlock (Fin p.n)}
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams m)))
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hy : y ∈ rho.honest) (hx : x ∈ rho.honest)
    (hJ : joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hms : m ≤ s) (hGST : E.t_GST ≤ SA.voteTime p.toParams m)
    (hP : P ∈ (storeAt p c E rho k y).fg.TF)
    (hBJ : FGBlock.Preceq B (heightView p P).J) (hnz : (heightView p P).h_j ≠ 0)
    (hnames : OutageNamedHistory p c E rho B i)
    (hlocks : ∀ row ∈
        (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams (s + 1))).base.obligations,
      SA.voteTime p.toParams (s + 1) < row.2.2 →
      Block.Compatible row.1 (eraseFG B)) :
    Block.Compatible (headVote p
      (clock p (storeAt p c E rho i x) (SA.voteTime p.toParams (s + 1))) (s + 1))
      (eraseFG B) := by
  have hF := (fgsa_cpCompat_of_scopedFrame p c E rho hf.store hf.strat
    i x B hx hnames.history).2.1
  have hBP := preceq_trans hBJ
    (preceq_trans ((fgCertificateLaws p).height.justified_preceq_entry P)
      ((fgCertificateLaws p).height.entry_preceq P))
  have hrec := outage_later_marker_receipt hBase hSync hf.mono hk hi hy hx hJ hms hGST
    hP hBP (Bool.or_eq_true_iff.mpr (hF.imp eraseFG_preceq eraseFG_preceq))
  exact outage_received_marker_head_scoped hf.mono hf.store hf.frame.1 hf.strat (s + 1)
    hx le_rfl (Nat.le_of_lt (List.getElem?_eq_some_iff.mp hi).1) hrec hBJ hnz hnames
    (by simpa only [(clock_vn _ _).2] using hlocks)

/-- A produced lease-or-F invariant gives a covering target at its actual emission.
Expiry and the named history refer to the emitter's post-tick store. -/
theorem outage_head_target_of_protection (hBase : Base₂ p c E rho)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    {i : Nat} {x : V} {s j : Slot} {q : Fin p.n} {B K : Block}
    {β : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hs : s ≠ 0) (hβ : eraseFG β = B)
    (hK : HeadTargetAtEmission p c E rho x (ofHead p ⟨.seat (.head s) q, K.root⟩)
      (SA.voteTime p.toParams s) K)
    (hnames : OutageNamedHistory p c E rho β (i + 1))
    (hp : OutageProtection p B j (storeAt p c E rho (i + 1) x))
    (ht : SA.voteTime p.toParams s < SA.gateTime p.toParams j + L p) :
    Block.Preceq B K := by
  let post := storeAt p c E rho (i + 1) x
  have hpost : post = clock p (storeAt p c E rho i x) (SA.voteTime p.toParams s) := by
    change (rho.stateBefore E (i + 1) x).st = _
    rw [(rho.step_tick_eq E hi).1]
    exact tick_st (c := c) E rho _ x _
  have hinv := cstoreInv_stateBefore E rho (i + 1) x
  have hret := (outage_frame_retains hf.store hf.frame.1 hsrc hx hβ hnames hp.1 hf.strat).2
  have hroot : Block.Preceq B (liveRoot p post) := by
    apply outage_liveRoot_covers p post hinv hp.1
      (leaseBelowOutput_stateBefore E rho (i + 1) x)
    rcases hret with hF | hdom
    · exact Or.inl hF
    · rcases hp.2 with hF | ⟨dl, hm, hd⟩
      · exact Or.inl hF
      · refine Or.inr ⟨dl, arming_leaseOf p post hinv hm, ?_, hdom⟩
        rw [hpost, (clock_vn _ _).2]
        exact ht.trans_le hd
  have he := headTargetAtEmission_at_tick E rho hBase.valid.toScheduleWellFormed hK hi rfl
  rw [he]
  rw [hpost] at hroot
  unfold headVote
  rw [ite_eq_right hs]
  exact block_preceq_trans hroot (liveRoot_preceq_headInTree p _ _ _ _)

/-- The low receiver-F branch requests only this protected emitted target.
The finalized receiver branch uses outage_finalized_gate_result instead. -/
theorem outage_conditional_target_of_protection (hBase : Base₂ p c E rho)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    {i k : Nat} {x y : V} {s j : Slot} {q : Fin p.n} {B K : Block}
    {β : FGBlock (Fin p.n)} (hy : y ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)))
    (hs : s ≠ 0) (hβ : eraseFG β = B)
    (hK : HeadTargetAtEmission p c E rho y (ofHead p ⟨.seat (.head s) q, K.root⟩)
      (SA.voteTime p.toParams s) K)
    (hnames : OutageNamedHistory p c E rho β (k + 1))
    (hp : OutageProtection p B j (storeAt p c E rho (k + 1) y))
    (ht : SA.voteTime p.toParams s < SA.gateTime p.toParams j + L p)
    (hlow : Block.Preceq (F_at p c E rho i x) B) :
    Block.Preceq B K ∧ Block.Preceq (F_at p c E rho i x) K := by
  have hBK := outage_head_target_of_protection hBase hf hsrc hy hk hs hβ hK hnames hp ht
  exact ⟨hBK, block_preceq_trans hlow hBK⟩

end AvailableChain.FGSA.Run
end

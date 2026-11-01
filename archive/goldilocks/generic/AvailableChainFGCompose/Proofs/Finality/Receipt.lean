module
public import AvailableChainFGCompose.Proofs.Finality.Carry
public import AvailableChainFGCompose.Proofs.Finality.Rows
public import AvailableChainGeneric.Proofs.V2.Duty.Reads
public import AvailableChainFGCompose.Proofs.Finality.MiddleSupport
public import AvailableChainKitFG.FrameGeometry

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (T : FGTiming) (E : Generic.Env V) (rho : V2.D.Run V P)
variable (I : V2.D.Interface P) (D : FGHistoryWireReads S)
variable (Ef : Electorate (Fin n)) (cfg : FGConfig) (K : Nat)
variable (carrier : P.Object → Slot → Block → List Wire → Prop)
variable (chainWireRows : P.State → Block → List Wire) (blockWireRows : P.State → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (validFor : P.State → Slot → FGBlock (Fin n) → Wire → Bool)

/-- Paper 22:1286–1305: the kernel supplies the deadline inside the run and the
independent honest quorum. DC: INTENTIONAL local W deadline; the aggregate execution and
fault inputs are split into these used fields. -/
theorem receipt_kernel_fields (deltaF horizon : Time) (sp : FGServicePoint) (pt : KernelPt)
    (honestSlot : Slot → Prop) (fgQuorum fgHonestWeight timeoutSlots capacity : Nat)
    (h : KernelPrem_W T deltaF horizon sp pt honestSlot fgQuorum fgHonestWeight
      timeoutSlots capacity) :
    kernelDeadlineW T deltaF (pt.r + 2) ≤ horizon ∧ fgQuorum ≤ fgHonestWeight :=
  ⟨h.hhor, h.honest_quorum⟩

/-- A covered parent key stays covered at the child (window monotonicity). -/
private theorem d7a5g_covered_parent (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K) (y : Nat)
    (U X : FGBlock (Fin n)) (h : KitFG.Window.CoveredW Ef cfg K X.parent y U) :
    KitFG.Window.CoveredW Ef cfg K X y U := by
  have path : FGBlock.Preceq X.parent X := by
    cases X with
    | genesis => exact KitFG.preceq_refl _
    | node B s root body rows => exact KitFG.preceq_parent_node B s root body rows
  exact ⟨h.1.trans (KitFG.Window.window_hF_mono Ef cfg K hne hK _ _ path),
    KitFG.preceq_trans h.2 (KitFG.Window.window_F_mono Ef cfg K hne hK _ _ path)⟩

/-- A real child whose rows complete one retained bit set finalizes that key. -/
private theorem d7a5g_child_consume (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K) (y : Nat)
    (U X : FGBlock (Fin n)) (child : X ≠ .genesis)
    (h : FinalityCoveredByChild_W Ef cfg K X U y) :
    FGBlock.Preceq U (SimplexFG.Window.derive Ef cfg K X).F ∧
      y ≤ (SimplexFG.Window.derive Ef cfg K X).h_F := by
  obtain ⟨e, he, hj, hX, Q, hQ, cover⟩ := h
  cases X with
  | genesis => exact (child rfl).elim
  | node B s root body rows =>
      have hc : ∀ i ∈ Q, i ∈ e.Q ∨ ∃ row ∈ rows,
          row.signer = i ∧ row.finality_pair = some ⟨e.j, e.X.root⟩ := by
        intro i hi
        rcases cover i hi with hb | ⟨row, hrow, hs, hf⟩
        · exact Or.inl hb
        · exact Or.inr ⟨row, hrow, hs, by rw [hj, hX]; exact hf⟩
      have r := KitFG.Window.window_finality_of_cover Ef cfg K hne hK B s root body rows e he
        Q hQ hc
      rw [hj, hX] at r
      exact r

/-- Paper 22:1286–1289: carriage gives a finalized descendant in both branches.
DC: INTENTIONAL greatest-ready W fold; prior coverage is a separate branch.
The fold proves only carrier finality. It does not prove receipt or guards. -/
theorem receipt_finalized_of_carriage
    (hsel : TRowsSelect R S E rho T I carrier chainWireRows blockWireRows parentFG validFor)
    (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (decode : ∀ a i, D.signer a = some i → ∃ u, S.decode a = some u)
    (occurrence : ∀ s (Q : Block) H nd a u,
      proposalStateAt E rho I s = some nd → parentFG nd Q.parent = some H →
      a ∈ chainWireRows nd Q.parent → S.decode a = some u →
      ∃ W, FGBlock.Preceq W H ∧ u ∈ W.rows)
    (O : FGObservationReads R) (height : FGHeightLaws Ef O.height)
    (height_eq : O.height = KitFG.Window.certificateHeight Ef cfg K)
    (parentHeight : P.State → Slot → FGBlock (Fin n) → Height × BlockId)
    (parentHeight_eq : ∀ nd s B, parentHeight nd s B = ((O.height B).h, (O.height B).T_h.root))
    (validFor_eq : ∀ nd s B a, validFor nd s B a =
      ((S.decode a).isSome && ((S.decode a).map
        (SimplexFG.Window.r6w (KitFG.Window.parentState Ef cfg K B s))).getD false))
    (validWire : Wire → Bool) (ΔF : Time) (q y : Nat) (A U X : FGBlock (Fin n))
    (hchild : X ≠ .genesis)
    (h : TerminalCarriagePrem_W R S O T E rho I D Ef cfg K validWire
      carrier blockWireRows parentFG ΔF q y A U X)
    (valid : ∀ B s root body rs, FGBlock.Preceq (.node B s root body rs) X.parent →
      ∀ a ∈ rs,
      (match a.height_pair with
        | .empty => false
        | .vote h _ _ => decide (1 ≤ h) &&
            (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true) = true ∧
        SimplexFG.Window.r6w (SimplexFG.Window.derive Ef cfg K B) a = true) :
    FGBlock.Preceq U (SimplexFG.Window.derive Ef cfg K X).F := by
  rcases terminalCarriage_W_of_tRowsSelect R S T E rho I D Ef cfg K carrier chainWireRows
      blockWireRows parentFG validFor hsel hne hK decode occurrence O height height_eq
      parentHeight parentHeight_eq validFor_eq validWire ΔF q y A U X h valid with
    hcovered | ⟨_hvalid, hcover⟩
  · exact (d7a5g_covered_parent Ef cfg K hne hK y U X hcovered).2
  · exact (d7a5g_child_consume Ef cfg K hne hK y U X hchild hcover).1

/-- Paper 22:1145–1146, 1296: I3 compares F before carrier admission.
DC: INTENTIONAL W certificate agreement. The block family, its agreement and the stored
block membership are the protocol's leaves. -/
theorem receipt_finCmp_of_block (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (O : FGObservationReads R)
    (finality_eq : O.finality = KitFG.Window.certificateFinality Ef cfg K)
    (finBlock : FGBlock (Fin n) → Prop)
    (hI3 : ∀ C W, finBlock C → finBlock W →
      FGBlock.compatible (O.finality C).F (O.finality W).F = true)
    (i : Nat) (x : V)
    (inv : KitFG.FGStoreInvariant O.height O.finality
      (R.core (V2.D.Run.stateBefore E rho i x)).fg)
    (stored : ∀ C ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF, C ≠ .genesis →
      finBlock C)
    (X U : FGBlock (Fin n))
    (hfinal : FGBlock.Preceq U (SimplexFG.Window.derive Ef cfg K X).F)
    (hblock : finBlock X) :
    FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho i x)).fg.F U ∨
      FGBlock.Preceq U (R.core (V2.D.Run.stateBefore E rho i x)).fg.F := by
  obtain ⟨C, hC, hCF⟩ := inv.Fcar
  by_cases hgen : C = .genesis
  · subst C
    have hF : (R.core (V2.D.Run.stateBefore E rho i x)).fg.F = .genesis := by
      rw [← hCF, finality_eq, (KitFG.Window.windowCertificateLaws Ef cfg K hne hK).initial]
    exact Or.inl (hF ▸ KitFG.genesis_preceq U)
  have hc := hI3 C X (stored C hC hgen) hblock
  rw [hCF] at hc
  have hXF : (O.finality X).F = (SimplexFG.Window.derive Ef cfg K X).F := by
    rw [finality_eq]
    rfl
  rw [hXF] at hc
  rcases Bool.or_eq_true_iff.mp hc with hbelow | habove
  · exact KitFG.preceq_total_of_common hbelow hfinal
  · exact Or.inr (KitFG.preceq_trans hfinal habove)

/-- Paper 22:1145–1146, 1296: I3 compares F at this same selected receipt.
DC: INTENTIONAL W certificate agreement; the selected receipt names a block of the family. -/
theorem receipt_finCmp (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (O : FGObservationReads R)
    (finality_eq : O.finality = KitFG.Window.certificateFinality Ef cfg K)
    (ready : Nat → V → FGBlock (Fin n) → Time → Prop)
    (finBlock : FGBlock (Fin n) → Prop)
    (hI3 : ∀ C W, finBlock C → finBlock W →
      FGBlock.compatible (O.finality C).F (O.finality W).F = true)
    (i : Nat) (x : V)
    (inv : KitFG.FGStoreInvariant O.height O.finality
      (R.core (V2.D.Run.stateBefore E rho i x)).fg)
    (stored : ∀ C ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF, C ≠ .genesis →
      finBlock C)
    (X U : FGBlock (Fin n)) (t : Time)
    (readyBlock : ready i x X t → finBlock X)
    (hfinal : FGBlock.Preceq U (SimplexFG.Window.derive Ef cfg K X).F)
    (hready : ready i x X t) :
    FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho i x)).fg.F U ∨
      FGBlock.Preceq U (R.core (V2.D.Run.stateBefore E rho i x)).fg.F :=
  receipt_finCmp_of_block R E rho Ef cfg K hne hK O finality_eq finBlock hI3 i x inv stored
    X U hfinal (readyBlock hready)

/-- The kernel deadline precedes the next action. -/
private theorem d7a5g_next_action (L : FGTimingLaws T) (ΔF : Time) (q : Nat)
    (hbound : LivenessBoundW T ΔF) : kernelDeadlineW T ΔF q < T.action (q + 1) := by
  have hd := L.delta_pos
  have hk : (kappaF T ΔF : Time) ≤ T.roundSlots := by exact_mod_cast hbound.kappa_le_R
  rw [kmid_actionTime_eq T L]
  unfold kernelDeadlineW betaF
  rw [kmid_period_eq]
  push_cast
  nlinarith

omit [DecidableEq V] in
/-- A selected event before the kernel deadline is before the next action. -/
private theorem d7a5g_index_before (L : FGTimingLaws T) (hs : V2.D.ScheduleWellFormed E rho)
    (ΔF : Time) (q i : Nat) (t : Time) (hbound : LivenessBoundW T ΔF)
    (ht : eventTime rho i = some t) (hbefore : t < kernelDeadlineW T ΔF q) :
    i < V2.D.Run.idxBefore rho (T.action (q + 1)) := by
  have hnext := d7a5g_next_action T L ΔF q hbound
  obtain ⟨e, he, htime⟩ := Option.map_eq_some_iff.mp ht
  exact (Gen.V2.Duty.index_lt_idxBefore_iff hs he (T.action (q + 1))).mpr
    (htime ▸ hbefore.trans hnext)

/-- Paper 22:1290–1302: the pre-next-action cap bounds the inserted h_max.
DC: INTENTIONAL W receipt insert, with height views and the shared causal cap.
The receiver and carrier use the same selected event index. -/
theorem receipt_cap (O : FGObservationReads R)
    (height_eq : O.height = KitFG.Window.certificateHeight Ef cfg K)
    (L : FGTimingLaws T) (hs : V2.D.ScheduleWellFormed E rho)
    (ΔF : Time) (q y i : Nat) (x : V) (X : FGBlock (Fin n))
    (t : Time) (hx : x ∈ rho.honest) (hbound : LivenessBoundW T ΔF)
    (ht : eventTime rho i = some t) (hbefore : t < kernelDeadlineW T ΔF q)
    (inv : KitFG.FGStoreInvariant O.height O.finality
      (R.core (V2.D.Run.stateBefore E rho i x)).fg)
    (hheight : y + 1 ≤ (O.height X).h)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt R E rho j z W →
      (∀ k u r a row h B timeout, HonestRowAt S E rho T k u r a →
        S.decode a = some row → row.height_pair = .vote h B timeout →
        T.action r < cut → h < b + 1) → (O.height W).h < b + 2)
    (hrows : ∀ j z r a row h B timeout, HonestRowAt S E rho T j z r a →
      S.decode a = some row → row.height_pair = .vote h B timeout →
      T.action r < T.action (q + 1) → h ≤ y + 1) :
    (receiptInsert_W R E rho Ef cfg K i x X).h_max ≤
      (SimplexFG.Window.derive Ef cfg K X).h + 1 := by
  have hi := Nat.le_of_lt (d7a5g_index_before T E rho L hs ΔF q i t hbound ht hbefore)
  have hcap : ∀ W ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF,
      (O.height W).h ≤ y + 2 := by
    intro W hW
    exact actual_anchor_cap R S O T E rho q y hcapBefore hrows i x W hi ⟨hx, hW⟩
  have hm : (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_max ≤ y + 2 := by
    rw [inv.hmax]
    exact max_le (Finset.sup_le hcap) (Nat.succ_le_succ (Nat.zero_le (y + 1)))
  have hX : (O.height X).h = (SimplexFG.Window.derive Ef cfg K X).h := by
    rw [height_eq]
    rfl
  change max (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_max
    (SimplexFG.Window.derive Ef cfg K X).h ≤ (SimplexFG.Window.derive Ef cfg K X).h + 1
  rw [← hX]
  exact max_le (hm.trans (Nat.add_le_add_right hheight 1)) (Nat.le_succ _)

/-- Paper 22:1294–1296: the separate finality lag excludes a higher receiver certificate.
DC: INTENTIONAL W F carrier at the pre-handler read; the lag is the protocol's input.
This height bound does not produce delivery or cached-J source provenance. -/
theorem receipt_receiver_finalityLag (O : FGObservationReads R)
    (L : FGTimingLaws T) (hs : V2.D.ScheduleWellFormed E rho)
    (ΔF : Time) (q y i : Nat) (x : V) (t : Time)
    (hx : x ∈ rho.honest) (hbound : LivenessBoundW T ΔF)
    (ht : eventTime rho i = some t) (hbefore : t < kernelDeadlineW T ΔF q)
    (inv : KitFG.FGStoreInvariant O.height O.finality
      (R.core (V2.D.Run.stateBefore E rho i x)).fg)
    (hfinalityLag : ∀ (r k j : Nat) (z : V) (W : FGBlock (Fin n)),
      0 < k → j ≤ V2.D.Run.idxBefore rho (T.action (r + 1)) →
      HeldAt R E rho j z W →
      (∀ l u s a row B timeout, HonestRowAt S E rho T l u s a →
        S.decode a = some row → row.height_pair = .vote k B timeout →
        ¬ T.action s < T.action r) → (O.finality W).h_F < k)
    (hrowsEarlier : ∀ j z r a row h B timeout, HonestRowAt S E rho T j z r a →
      S.decode a = some row → row.height_pair = .vote h B timeout →
      T.action r < T.action q → h < y + 1) :
    ∃ C, HeldAt R E rho i x C ∧
      (O.finality C).F = (R.core (V2.D.Run.stateBefore E rho i x)).fg.F ∧
      (O.finality C).h_F < y + 1 := by
  have hi := Nat.le_of_lt (d7a5g_index_before T E rho L hs ΔF q i t hbound ht hbefore)
  obtain ⟨C, hC, hCF⟩ := inv.Fcar
  have hheld : HeldAt R E rho i x C := ⟨hx, hC⟩
  refine ⟨C, hheld, hCF, hfinalityLag q (y + 1) i x C (Nat.zero_lt_succ _) hi hheld ?_⟩
  intro j z r a row B timeout ha hd hp hlt
  exact (Nat.lt_irrefl _) (hrowsEarlier j z r a row (y + 1) B timeout ha hd hp hlt)

/-- Paper 22:1297–1302: the h_j = y case has its cached anchor on the carrier path.
DC: INTENTIONAL W cached-J guard. This does not produce source provenance. -/
theorem receipt_jPath_of_cached_anchor (i : Nat) (x : V) (X U : FGBlock (Fin n))
    (hcached : (R.core (V2.D.Run.stateBefore E rho i x)).fg.J = U)
    (hpath : FGBlock.Preceq U X.parent) :
    FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho i x)).fg.J X ∨
      (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_j <
        (SimplexFG.Window.derive Ef cfg K X).h_j := by
  have hp : FGBlock.Preceq X.parent X := by
    cases X with
    | genesis => exact KitFG.preceq_refl _
    | node B s root body rows => exact KitFG.preceq_parent_node B s root body rows
  exact Or.inl (hcached ▸ KitFG.preceq_trans hpath hp)

/-- The window height view has the justified-entry laws (through the window bridge). -/
private theorem d7a5g_justification (O : FGObservationReads R)
    (height_eq : O.height = KitFG.Window.certificateHeight Ef cfg K) (hK : 2 ≤ K) :
    FGJustificationLaws O.height := by
  rw [height_eq]
  exact FGJustificationLaws.of_bridge (KitFG.Window.windowHeightBridge Ef cfg K hK)

/-- Paper 22:1297–1302: a high cached J is on the terminal carrier path.
DC: INTENTIONAL W cached pair and action-source ancestry. Stratification, emitted-name
provenance, the root-scope equation and the historical high-source transfer are the
protocol's inputs. -/
theorem receipt_jPath (O : FGObservationReads R)
    (height_eq : O.height = KitFG.Window.certificateHeight Ef cfg K)
    (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K) (L : FGTimingLaws T)
    (hs : V2.D.ScheduleWellFormed E rho) (entry : Wire → Option (Height × BlockId))
    (reflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (erase_parent : ∀ B, R.erase B.parent = (R.erase B).parent)
    (ΔF : Time) (q y i : Nat) (x : V) (A X : FGBlock (Fin n)) (t : Time)
    (deltaF : E.Δ ≤ ΔF) (path : FGBlock.Preceq A X.parent)
    (proposal : HonestProposal E rho I X.slot (R.erase X))
    (hXhor : T.proposal X.slot ≤ rho.horizon)
    (sp : FGServicePoint) (hM : 1 ≤ sp.reset.M)
    (transfer : FGHistoricalHighTransfer R O T E rho I sp rho.horizon)
    (hx : x ∈ rho.honest) (hbound : LivenessBoundW T ΔF)
    (ht : eventTime rho i = some t) (hbefore : t < kernelDeadlineW T ΔF q)
    (hslot : X.slot = q * T.roundSlots + kappaF T ΔF)
    (hanchor : (O.height A).h_j = y) (hfloor : sp.reset.M + 1 ≤ y)
    (inv : KitFG.FGStoreInvariant O.height O.finality
      (R.core (V2.D.Run.stateBefore E rho i x)).fg)
    (hStrat : ∀ j z W, z ∈ rho.honest →
      W ∈ (R.core (V2.D.Run.stateBefore E rho j z)).fg.TF →
      ∀ J ∈ certified R O W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore S E rho T j u r a ∧ entry a = some ((O.height J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt S E rho T j z r a →
      entry a = some e → ∃ C,
        actionSourceFG R E rho T z r = some (some C) ∧
        e = ((O.height C).h, (O.height C).T_h.root) ∧
        FGBlock.Preceq (O.height C).T_h C)
    (rootScope : ∀ C k u r a B, C ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF →
      HonestRowAt S E rho T k u r a → actionSourceFG R E rho T u r = some (some B) →
      (O.height C).J.root = (O.height B).T_h.root → (O.height C).J = (O.height B).T_h) :
    FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho i x)).fg.J X ∨
      (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_j <
        (SimplexFG.Window.derive Ef cfg K X).h_j := by
  by_cases hstrict : (R.core (V2.D.Run.stateBefore E rho i x)).fg.h_j <
      (SimplexFG.Window.derive Ef cfg K X).h_j
  · exact Or.inr hstrict
  have hpp : FGBlock.Preceq X.parent X := by
    cases X with
    | genesis => exact KitFG.preceq_refl _
    | node B s root body rows => exact KitFG.preceq_parent_node B s root body rows
  have hXj : y ≤ (SimplexFG.Window.derive Ef cfg K X).h_j := by
    have hm := KitFG.Window.window_hj_mono Ef cfg K hne hK A X (KitFG.preceq_trans path hpp)
    have ha : (SimplexFG.Window.derive Ef cfg K A).h_j = y := by
      rw [← hanchor, height_eq]
      rfl
    rw [ha] at hm
    exact hm
  obtain ⟨C, hC, _hFC, hCJ, hJ⟩ := inv.pair.1
  have hCpos : (O.height C).h_j ≠ 0 := by
    simp only [Height] at hCJ hXj hfloor hstrict ⊢
    omega
  have hJheight := (d7a5g_justification R Ef cfg K O height_eq hK).J_height C hCpos
  have hJne : (O.height C).J ≠ .genesis := by
    intro hg
    rw [hg] at hJheight
    have hgen : (O.height FGBlock.genesis).h = 1 := by
      rw [height_eq]
      rfl
    have hz : (O.height C).h_j = 1 := hJheight.symm.trans hgen
    simp only [Height] at hCJ hXj hfloor hstrict hz hM ⊢
    omega
  have hcert : (O.height C).J ∈ certified R O C :=
    ⟨C, KitFG.preceq_refl _, Or.inl rfl⟩
  obtain ⟨u, r, a, hrowBefore, hnames⟩ := hStrat i x C hx hC _ hcert hJne
  obtain ⟨j, hji, hrow⟩ := hrowBefore
  obtain ⟨B, hsource, hentry, hJB⟩ := hEmittedSource j u r a _ hrow hnames
  have hJeq : (O.height C).J = (O.height B).T_h :=
    rootScope C j u r a B hC hrow hsource (congrArg Prod.snd hentry)
  have hhigh : sp.reset.M + 1 ≤ (O.height B).h := by
    have hheight := congrArg Prod.fst hentry
    simp only [Height] at hCJ hXj hfloor hstrict hJheight hheight ⊢
    omega
  have hi := d7a5g_index_before T E rho L hs ΔF q i t hbound ht hbefore
  have hrtime := (Gen.V2.Duty.index_lt_idxBefore_iff hs hrow.2.1 _).mp (hji.trans hi)
  have hrq : r ≤ q :=
    Nat.le_of_lt_succ ((kmid_action_strictMono T L).lt_iff_lt.mp hrtime)
  have hFpos := E.Δ_pos.trans_le deltaF
  have hcover := kmid_kappa_cover T L ΔF (le_of_lt hFpos)
  have hk : 2 ≤ kappaF T ΔF := by
    have hd := L.delta_pos
    by_contra hn
    have hcast : (kappaF T ΔF : Time) ≤ 1 := by exact_mod_cast (show _ ≤ 1 by omega)
    nlinarith
  have hlabel : r * T.roundSlots + 2 ≤ X.slot := by
    rw [hslot]
    exact Nat.add_le_add (Nat.mul_le_mul_right T.roundSlots hrq) hk
  have hrhor : T.action r ≤ rho.horizon :=
    (hs.in_horizon _ (List.mem_of_getElem? hrow.2.1)).2
  have hbasepath := transfer u r B hrow.1 hsource hhigh hrhor X.slot (R.erase X) proposal
    hXhor hlabel
  rw [← erase_parent] at hbasepath
  have hpath : FGBlock.Preceq B X.parent := reflect _ _ hbasepath
  exact Or.inl (hJ.trans hJeq ▸ KitFG.preceq_trans hJB (KitFG.preceq_trans hpath hpp))

/-- Paper 22:1286–1305: the terminal carrier gives every acceptance field at the selected
receipts. DC: INTENTIONAL local W receipt and same-event guards. The selected delivery is
the concrete supplier's; the carrier finality is the carriage result. -/
theorem receipt_acceptPrem_W (O : FGObservationReads R)
    (height_eq : O.height = KitFG.Window.certificateHeight Ef cfg K)
    (finality_eq : O.finality = KitFG.Window.certificateFinality Ef cfg K)
    (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K) (L : FGTimingLaws T)
    (hs : V2.D.ScheduleWellFormed E rho) (entry : Wire → Option (Height × BlockId))
    (reflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (erase_parent : ∀ B, R.erase B.parent = (R.erase B).parent)
    (ready : Nat → V → FGBlock (Fin n) → Time → Prop)
    (finBlock : FGBlock (Fin n) → Prop)
    (hI3 : ∀ C W, finBlock C → finBlock W →
      FGBlock.compatible (O.finality C).F (O.finality W).F = true)
    (readyBlock : ∀ i x X t, ready i x X t → finBlock X)
    (stored : ∀ i x, ∀ C ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF,
      C ≠ .genesis → finBlock C)
    (inv : ∀ i x, x ∈ rho.honest → KitFG.FGStoreInvariant O.height O.finality
      (R.core (V2.D.Run.stateBefore E rho i x)).fg)
    (ΔF : Time) (q y : Nat) (A U X : FGBlock (Fin n))
    (deltaF : E.Δ ≤ ΔF) (path : FGBlock.Preceq A X.parent)
    (proposal : HonestProposal E rho I X.slot (R.erase X))
    (hXhor : T.proposal X.slot ≤ rho.horizon)
    (sp : FGServicePoint) (hM : 1 ≤ sp.reset.M)
    (transfer : FGHistoricalHighTransfer R O T E rho I sp rho.horizon)
    (hbound : LivenessBoundW T ΔF)
    (hslot : X.slot = q * T.roundSlots + kappaF T ΔF)
    (hanchor : (O.height A).h_j = y) (hfloor : sp.reset.M + 1 ≤ y)
    (hStrat : ∀ j z W, z ∈ rho.honest →
      W ∈ (R.core (V2.D.Run.stateBefore E rho j z)).fg.TF →
      ∀ J ∈ certified R O W, J ≠ .genesis → ∃ u r a,
        HonestRowBefore S E rho T j u r a ∧ entry a = some ((O.height J).h, J.root))
    (hEmittedSource : ∀ j z r a e, HonestRowAt S E rho T j z r a →
      entry a = some e → ∃ C,
        actionSourceFG R E rho T z r = some (some C) ∧
        e = ((O.height C).h, (O.height C).T_h.root) ∧
        FGBlock.Preceq (O.height C).T_h C)
    (rootScope : ∀ i x, x ∈ rho.honest → ∀ C k u r a B,
      C ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF →
      HonestRowAt S E rho T k u r a → actionSourceFG R E rho T u r = some (some B) →
      (O.height C).J.root = (O.height B).T_h.root → (O.height C).J = (O.height B).T_h)
    (hheight : y + 1 ≤ (O.height X).h)
    (hcapBefore : ∀ (cut : Time) (b j : Nat) (z : V) (W : FGBlock (Fin n)),
      j ≤ V2.D.Run.idxBefore rho cut → HeldAt R E rho j z W →
      (∀ k u r a row h B timeout, HonestRowAt S E rho T k u r a →
        S.decode a = some row → row.height_pair = .vote h B timeout →
        T.action r < cut → h < b + 1) → (O.height W).h < b + 2)
    (hrows : ∀ j z r a row h B timeout, HonestRowAt S E rho T j z r a →
      S.decode a = some row → row.height_pair = .vote h B timeout →
      T.action r < T.action (q + 1) → h ≤ y + 1)
    (hfinal : FGBlock.Preceq U (SimplexFG.Window.derive Ef cfg K X).F) (a₀ : Time)
    (delivery : BlockDelivery_W R E rho ready X U a₀ (kernelDeadlineW T ΔF q))
    (horizon : kernelDeadlineW T ΔF q ≤ rho.horizon) :
    Nonempty (AcceptPrem_W R E rho Ef cfg K ready X U a₀ (kernelDeadlineW T ΔF q)) := by
  refine ⟨{ schedule := hs
            finalized := hfinal
            deliver := delivery
            guards := { finCmp := ?_, jPath := ?_, cap := ?_ }
            horizon := horizon }⟩
  · intro x hx
    dsimp only
    intro hready
    exact receipt_finCmp R E rho Ef cfg K hne hK O finality_eq ready finBlock hI3
      (delivery.selected x hx).index x (inv _ x hx) (stored _ x) X U
      (delivery.selected x hx).time (readyBlock _ x X _) hfinal hready
  · intro x hx
    dsimp only
    intro _hready _hnotCovered
    have hw := delivery.witness x hx
    exact receipt_jPath R S T E rho I Ef cfg K O height_eq hne hK L hs entry
      reflect erase_parent ΔF q y (delivery.selected x hx).index x A X
      (delivery.selected x hx).time deltaF path proposal hXhor sp hM transfer hx hbound hw.1
      hw.2.1
      hslot hanchor hfloor (inv _ x hx) hStrat hEmittedSource (rootScope _ x hx)
  · intro x hx
    dsimp only
    intro _hready _hnotCovered
    have hw := delivery.witness x hx
    exact receipt_cap R S T E rho Ef cfg K O height_eq L hs ΔF q y
      (delivery.selected x hx).index x X (delivery.selected x hx).time hx hbound hw.1 hw.2.1
      (inv _ x hx) hheight hcapBefore hrows

end AvailableChain.FGCompose
end

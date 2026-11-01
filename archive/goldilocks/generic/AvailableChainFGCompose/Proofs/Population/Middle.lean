module
public import AvailableChainFGCompose.Statements.Population.FinalityKernel
public import AvailableChainFGCompose.Proofs.Population.MiddleSupport
public import AvailableChainFGCompose.Proofs.Population.HolderBaseMiddle

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (O : FGObservationReads R) (T : FGTiming) (L : FGTimingLaws T)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (I : V2.D.Interface P)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))

variable (decodeProposal : P.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)
variable (blockWireRows : P.State → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : P.State → Slot → FGBlock (Fin n) → Height × BlockId)
variable (validFor : P.State → Slot → FGBlock (Fin n) → Wire → Bool)
variable (makeFG : FGBlock (Fin n) → Block → List Wire → FGBlock (Fin n))
variable (valid : Wire → Bool) (ac : FGACServiceReads V)
variable (cfg : FGConfig) (K : Nat) (ΔF : Time) (sp : FGServicePoint) (pt : KernelPt) (A : Block)
variable {Jst : Time}

include L in
/-- Construct the middle from the same service point and actual signed history. -/
theorem kernel_opening_and_middle_holder
    (CL : FGCoreLaws R) (HL : FGHeadLaws R E rho)
    (keep : FGTreeKeepLaws R) (restore : FGTreeRestoreLaws R)
    (hs : V2.D.ScheduleWellFormed E rho)
    (hc : FGCertificateLaws Ef O.height O.finality)
    (heightBridge : HeightBridge Ef cfg O.height)
    (height_eq : O.height = KitFG.Window.certificateHeight Ef cfg K)
    (finality_eq : O.finality = KitFG.Window.certificateFinality Ef cfg K)
    (hne : ¬ Ef.IsQuorum ∅)
    (target : TargetJustification Ef O.height)
    (foldTarget : ∀ y U X, X ≠ .genesis → EntryAt O.height U y →
      FGBlock.Preceq U X.parent →
      ((O.height X.parent).h = y → TargetCoveredByChild Ef O.height X U y) →
      y + 1 ≤ (O.height X).h)
    (noMixed : ∀ y U X, SlotChain X → EntryAt O.height U y →
      FGBlock.Preceq U X.parent → X.slot < U.slot + cfg.timeoutDelay + 1 →
      NoMixedOnPath O.height X y)
    (honestSlot : Slot → Prop)
    (hK : KernelPrem_W T ΔF rho.horizon sp pt honestSlot Ef.q
      (Ef.weightOf (Finset.univ \ historyFaulty S rho)) cfg.timeoutDelay K)
    (hF0 : 0 ≤ ΔF) (deltaF : E.Δ ≤ ΔF)
    (hreset : T.proposal (sp.reset.sStar + 2) ≤ sp.serviceStart)
    (hGSTstart : E.t_GST ≤ sp.serviceStart)
    (reset : H0Reset R S E rho O T (fun a => namedEntry (D.heightPair a)) Jst sp.reset)
    (history : FGHistoricalHighTransfer R O T E rho I sp rho.horizon)
    (reflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (parent : ∀ B, R.erase B.parent = (R.erase B).parent)
    (hNames : HighRecordNames R S O T E rho D)
    (hOrigin : RawHistoryOrigin R S E rho T D)
    (emission : HighRecordEmission S T E rho Ef cfg)
    (decoded : ∀ j x r a, HonestRowAt S E rho T j x r a → ∃ u, S.decode a = some u)
    (hweight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    (linked : Function.Injective (safetyHolder S rho))
    (receipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (awake : ∀ x ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon → E.awake x t = true)
    (honest_slot : ∀ s, honestSlot s → ∃ x, x ∈ rho.honest)
    (proposal : ∀ s, honestSlot s → pt.r * T.roundSlots ≤ s →
      s ≤ (pt.r + 2) * T.roundSlots → ∃ Q, HonestProposal E rho I s Q)
    (carrier : ∀ s Q, HonestProposal E rho I s Q →
      ∃ X : FGBlock (Fin n), R.erase X = Q ∧
        OpeningCarrier_W decodeProposal bodyErase bodyRows (fun nd Q => parentFG nd Q.parent)
          makeFG E rho I s Q X ∧ X.slot = s ∧
        (∃ rows, HonestCarrier E rho I (kernelCarrier decodeProposal bodyErase bodyRows)
          s Q rows ∧ X.rows = rows.filterMap S.decode) ∧
        ∃ nd, proposalStateAt E rho I s = some nd ∧
          parentFG nd Q.parent = some X.parent ∧ X.parent ∈ (R.core nd).fg.TF)
    (exactService : ∀ s Q, HonestProposal E rho I s Q → pt.r * T.roundSlots ≤ s →
      KernelExactService ac rho.horizon s Q)
    (source_read : ∀ s Q r x, KernelExactService ac rho.horizon s Q →
      T.gate s ≤ rho.horizon → s = r * T.roundSlots → x ∈ rho.honest →
      pt.r * T.roundSlots ≤ s → ac.source x r = some (some Q))
    (source_eq : ∀ x r, ac.source x r =
      (actionSourceFG R E rho T x r).map (Option.map R.erase))
    (head_read : ∀ s Q x, KernelExactService ac rho.horizon s Q →
      pt.r * T.roundSlots ≤ s → s ≤ (pt.r + 2) * T.roundSlots → x ∈ rho.honest →
      headAtLabel R E rho T x s = some Q)
    (head_held : ∀ s X x, headAtLabel R E rho T x s = some (R.erase X) →
      ∃ i, rho.events[i]? = some (.tick x (T.vote s)) ∧
        X ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF)
    (slot_chain : ∀ i x X, X ∈ (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF → SlotChain X)
    (closed : ∀ s nd, proposalStateAt E rho I s = some nd →
      ∀ X ∈ (R.core nd).fg.TF, X.parent ∈ (R.core nd).fg.TF)
    (roots : ∀ s nd, proposalStateAt E rho I s = some nd → ViewRootInj (R.core nd).fg.TF)
    (validRows : ∀ s nd, proposalStateAt E rho I s = some nd →
      ∀ X ∈ (R.core nd).fg.TF, ∀ row ∈ X.rows,
        SimplexFG.Window.r6w (SimplexFG.Window.derive Ef cfg K X.parent) row = true)
    (parentEq : ∀ nd s X, parentHeight nd s X = ((O.height X).h, (O.height X).T_h.root))
    (matchValid : ∀ nd s X a, valid a = true →
      namedEntry (D.heightPair a) = some (parentHeight nd s X) → validFor nd s X a = true)
    (hBatch : ∀ q y U X,
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .target q y U X →
      (O.height X.parent).h = y → TargetCoveredByChild Ef O.height X U y)
    (hSOCOVTarget : ∀ i : Fin n, safetyHolder S rho i ∈ rho.honest → ∀ r C,
      actionSourceFG R E rho T (safetyHolder S rho i) r = some (some C) →
      sp.reset.M + 1 ≤ (O.height C).h →
      E.awake (safetyHolder S rho i) (T.action r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt S E rho T j (safetyHolder S rho i) rSent a ∧
        RowComplete S rho D.signer valid (safetyHolder S rho i) a ∧
        D.heightPair a = .vote (O.height C).h (O.height C).T_h.root false)
    (hA : HonestProposal E rho I (pt.r * T.roundSlots) A) :
    Nonempty (KernelMiddleWitnessFG_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A) := by
  classical
  obtain ⟨_hF0, hκ2, hκR, hR2, _hs2, hGST, hhorA⟩ :=
    kmid_kernel_bounds T L hK.bound hK.start hK.hhor hF0 hreset hGSTstart
  have hΔ := L.delta_pos
  have laws := hc.height
  have hseats : ∀ i ∈ Finset.univ \ historyFaulty S rho,
      safetyHolder S rho i ∈ rho.honest := by
    intro i hi
    exact kmid_honest_seat (S := S) (rho := rho) ⟨i, .empty, none⟩
      (Finset.mem_sdiff.mp hi).2
  have hwin := hK.window
  rw [Gen.Pure.FGoodE_W_def] at hwin
  obtain ⟨hwA, hwB, ⟨cD, hcD1, hcD2, hwD⟩, -⟩ := hwin
  have e1 : (pt.r + 1) * T.roundSlots = pt.r * T.roundSlots + T.roundSlots := Nat.succ_mul _ _
  have e2 : (pt.r + 2) * T.roundSlots = pt.r * T.roundSlots + 2 * T.roundSlots := by ring
  have hcD1' : (pt.r + 1) * T.roundSlots + kappaF T ΔF ≤ (cD : Nat) := hcD1
  have hcD2' : (cD : Nat) ≤ (pt.r + 2) * T.roundSlots := hcD2
  have n01 : pt.r * T.roundSlots ≤ (pt.r + 1) * T.roundSlots := by omega
  have n12 : (pt.r + 1) * T.roundSlots ≤ (pt.r + 2) * T.roundSlots := by omega
  have n02 : pt.r * T.roundSlots ≤ (pt.r + 2) * T.roundSlots := by omega
  have nA2 : pt.r * T.roundSlots + 2 ≤ (pt.r + 1) * T.roundSlots := by omega
  have nAκ : pt.r * T.roundSlots + kappaF T ΔF ≤ (pt.r + 1) * T.roundSlots := by omega
  have nD2 : (pt.r + 1) * T.roundSlots + 2 ≤ (cD : Nat) := by omega
  have n0D : pt.r * T.roundSlots ≤ (cD : Nat) := by omega
  obtain ⟨x₀, hx₀⟩ := honest_slot _ hwA
  obtain ⟨xB, hxB⟩ := honest_slot _ hwB
  obtain ⟨xD, hxD⟩ := honest_slot _ hwD
  have hGSTr : ∀ r, pt.r ≤ r → E.t_GST ≤ T.action r := fun r hr =>
    hGST.trans (kmid_proposal_le_action T L (Nat.mul_le_mul_right _ hr))
  have hawake : ∀ x ∈ rho.honest, ∀ r, pt.r ≤ r → r ≤ pt.r + 2 →
      E.awake x (T.action r) = true := fun x hx r hlo hhi =>
    awake x hx _ (hGSTr r hlo)
      (le_trans ((kmid_action_strictMono T L).monotone hhi) hhorA)
  -- Step group A: the opening, middle and early proposals.
  obtain ⟨A₀, heA, carrierA, slotA, -, -⟩ := carrier _ _ hA
  have hA' : HonestProposal E rho I (pt.r * T.roundSlots) (R.erase A₀) := heA ▸ hA
  have exA := exactService _ _ hA' le_rfl
  have hhA := kmid_slot_horizon T L hhorA (s := pt.r * T.roundSlots) n02
  have sourceA : ∀ x ∈ rho.honest,
      actionSourceFG R E rho T x pt.r = some (some A₀) := fun x hx =>
    kmid_source_of_exact R T E rho CL (by
      rw [← source_eq]; exact source_read _ _ _ _ exA hhA.2.2 rfl hx le_rfl)
  obtain ⟨b, hb⟩ := proposal _ hwB n01 n12
  obtain ⟨B, heB, carrierB, slotB, ⟨rowsB, hcarB, hrowsB⟩, stB, hstB, hlookB, hparTFB⟩ :=
    carrier _ _ hb
  subst heB
  have exB := exactService _ _ hb n01
  have hhB := kmid_slot_horizon T L hhorA (s := (pt.r + 1) * T.roundSlots) n12
  have sourceB : ∀ x ∈ rho.honest,
      actionSourceFG R E rho T x (pt.r + 1) = some (some B) := fun x hx =>
    kmid_source_of_exact R T E rho CL (by
      rw [← source_eq]; exact source_read _ _ _ _ exB hhB.2.2 rfl hx n01)
  obtain ⟨xd, hxd⟩ := proposal _ hwD n0D hcD2
  obtain ⟨X_D, heD, carrierD, slotD, ⟨rowsD, hcarD, hrowsD⟩, stD, hstD, hlookD, hparTFD⟩ :=
    carrier _ _ hxd
  subst heD
  have exD := exactService _ _ hxd n0D
  have hhD := kmid_slot_horizon T L hhorA hcD2
  have highA : sp.reset.M + 1 ≤ (O.height A₀).h :=
    middle_reset_opening_height_core R S O T L E rho I D Ef sp rho.horizon Jst
      reset history laws reflect parent pt.r A₀ hA' hhA.1 _hs2
  -- Step 6–8: rows through action q and the first raw cut.
  have rowsQ : ∀ j x r a h, r ≤ pt.r → HonestRowAt S E rho T j x r a →
      historyRowHeight S D a = some h → h ≤ (O.height A₀).h := by
    intro j x r a h hr ha hh
    rcases Nat.lt_or_ge r pt.r with hlt | hge
    · exact kmid_rows_below_opening R S O T L E rho I D Ef sp rho.horizon history hNames
        laws reflect parent pt.r A₀ hA'
        (((kmid_action_strictMono T L).monotone (by omega)).trans hhorA) hhA.1 highA
        j x r a h hlt ha hh
    · obtain rfl : r = pt.r := le_antisymm hr hge
      exact (kmid_rows_at_source R S O T E rho D hNames pt.r A₀ sourceA j x a h ha hh).le
  obtain ⟨noFirstHeight, rowsBeforeB⟩ :=
    kmid_rows_cut S T L E rho D (O.height A₀).h pt.r rowsQ
  have capB : ∀ i x W, i ≤ afterTicksIdx rho (T.action (pt.r + 1)) →
      HeldAt R E rho i x W → (O.height W).h ≤ (O.height A₀).h + 1 :=
    fun i x W hi hW => kmid_held_cap_afterTicks R S O T E rho D Ef hc hOrigin hs hweight _ _
      rowsBeforeB i x W hi hW
  -- Step 10: the middle height.
  obtain ⟨iB, hiB, hBTF⟩ := head_held _ B xB (head_read _ _ _ exB n01 n12 hxB)
  have hBup : (O.height B).h ≤ (O.height A₀).h + 1 :=
    capB iB _ B ((kmid_tick_lt_afterTicks E rho hs hiB
      (kmid_vote_lt_action T L (le_refl ((pt.r + 1) * T.roundSlots))).le).le) ⟨hxB, hBTF⟩
  have hpAB := history x₀ pt.r A₀ hx₀
    (sourceA _ hx₀) highA
    (((kmid_action_strictMono T L).monotone (by omega)).trans hhorA) _ _ hb hhB.1 nA2
  rw [← parent] at hpAB
  have parentAB := reflect _ _ hpAB
  have hBne : B ≠ .genesis := by
    intro h
    rw [h] at slotB
    have h0 : (0 : Nat) = (pt.r + 1) * T.roundSlots := slotB
    omega
  have hparLow : (O.height A₀).h ≤ (O.height B.parent).h := laws.h_mono parentAB
  have entryA : EntryAt O.height (O.height A₀).T_h (O.height A₀).h :=
    ⟨laws.entry_same_height A₀, laws.entry_idem A₀⟩
  have pathA : FGBlock.Preceq (O.height A₀).T_h B.parent :=
    preceq_trans (laws.entry_preceq A₀) parentAB
  have batchB : (O.height B.parent).h = (O.height A₀).h →
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .target pt.r (O.height A₀).h (O.height A₀).T_h B := by
    intro hpar
    refine kmid_batchPrem_holder R S O T E rho I D Ef cfg K laws height_eq
      decodeProposal bodyErase bodyRows blockWireRows parentFG parentHeight validFor valid
      ΔF hs hweight linked (Finset.univ \ historyFaulty S rho) hseats
      hK.honest_quorum deltaF receipt pt.r _ _ B ?_
      ⟨rowsB, by rw [slotB]; exact hcarB, hrowsB⟩ stB
      (by rw [slotB]; exact hstB) hlookB hparTFB
      (closed _ _ hstB) (roots _ _ hstB) (validRows _ _ hstB)
      (parentEq _ _ _) (matchValid _ _ _) (by rw [slotB]; exact nA2) entryA pathA hpar ?_
    · rw [slotB]
      exact kmid_batch_horizon T L hF0 hhorA (hGSTr _ le_rfl) nAκ n12
    · intro i hi
      have hx := hseats i hi
      obtain ⟨j, rS, a, hle, ha, hc, hp⟩ :=
        hSOCOVTarget i hx pt.r A₀ (sourceA _ hx) highA
          (hawake _ hx _ le_rfl (by omega))
      exact ⟨j, rS, a, hle, ha, hc, hp⟩
  have hBlow : (O.height A₀).h + 1 ≤ (O.height B).h := by
    rcases Nat.eq_or_lt_of_le hparLow with heq | hlt
    · exact foldTarget _ _ B hBne entryA pathA
        (fun h => hBatch pt.r _ _ B (batchB h) h)
    · exact hlt.trans_le (laws.h_mono (kmid_parent_preceq B))
  have heightB : (O.height B).h = (O.height A₀).h + 1 := le_antisymm hBup hBlow
  -- Step 11: the fresh entry.
  have entryU : EntryAt O.height (O.height B).T_h ((O.height A₀).h + 1) :=
    ⟨(laws.entry_same_height B).trans heightB, laws.entry_idem B⟩
  have pathUB : FGBlock.Preceq (O.height B).T_h B := laws.entry_preceq B
  have slotChainB := slot_chain iB _ B hBTF
  have hA₀B : FGBlock.Preceq A₀ B := preceq_trans parentAB (kmid_parent_preceq B)
  have strictAU : FGBlock.Preceq A₀ (O.height B).T_h ∧ A₀ ≠ (O.height B).T_h := by
    rcases preceq_total_of_common hA₀B pathUB with h | h
    · refine ⟨h, ?_⟩
      intro he
      have h1 := entryU.1
      rw [← he] at h1
      exact Nat.succ_ne_self _ h1.symm
    · exfalso
      have h1 := laws.h_mono h
      rw [entryU.1] at h1
      exact Nat.not_succ_le_self _ h1
  have freshSlot : pt.r * T.roundSlots < ((O.height B).T_h).slot ∧
      ((O.height B).T_h).slot ≤ (pt.r + 1) * T.roundSlots := by
    have hUc : SlotChain (O.height B).T_h := fun W hW hg =>
      slotChainB W (preceq_trans hW pathUB) hg
    exact ⟨slotA ▸ kmid_slot_lt_of_strict hUc strictAU.1 strictAU.2,
      slotB ▸ kmid_slot_le_of_preceq slotChainB pathUB⟩
  -- Step 12: fresh targets at action q+1.
  have highB : sp.reset.M + 1 ≤ (O.height B).h := by
    rw [heightB]
    exact highA.trans (Nat.le_succ _)
  have targetsB : ∀ i : Fin n, safetyHolder S rho i ∈ rho.honest → ∃ j a,
      HonestRowAt S E rho T j (safetyHolder S rho i) (pt.r + 1) a ∧
      RowComplete S rho D.signer valid (safetyHolder S rho i) a ∧
      NamesEntry (pair := D.heightPair) .target a ((O.height A₀).h + 1) (O.height B).T_h := by
    intro i hx
    obtain ⟨j, rS, a, hle, ha, hc, hp⟩ :=
      hSOCOVTarget i hx (pt.r + 1) B (sourceB _ hx) highB
        (hawake _ hx _ (by omega) (by omega))
    have hrS : rS = pt.r + 1 := by
      by_contra hne
      have hlt : rS < pt.r + 1 := lt_of_le_of_ne hle hne
      have hh : historyRowHeight S D a = some ((O.height A₀).h + 1) := by
        have hdef : historyRowHeight S D a = (match D.heightPair a with
            | .empty => none | .vote h _ _ => some h) := rfl
        rw [hdef, hp, heightB]
      have hlate := noFirstHeight j (safetyHolder S rho i) rS a _ _ ha hh le_rfl
        (kmid_event_time S T E rho ha)
      exact absurd ((kmid_action_strictMono T L).lt_iff_lt.mpr hlt) (not_lt.mpr hlate)
    subst hrS
    refine ⟨j, a, ha, hc, ?_⟩
    change D.heightPair a = .vote _ _ false
    rw [hp, heightB]
  -- Step 12: rows through action q+1 and the second raw cut.
  have rowsQ1 : ∀ j x r a h, r ≤ pt.r + 1 → HonestRowAt S E rho T j x r a →
      historyRowHeight S D a = some h → h ≤ (O.height A₀).h + 1 := by
    intro j x r a h hr ha hh
    rcases Nat.lt_or_ge r (pt.r + 1) with hlt | hge
    · exact (rowsQ j x r a h (Nat.le_of_lt_succ hlt) ha hh).trans (Nat.le_succ _)
    · obtain rfl : r = pt.r + 1 := le_antisymm hr hge
      rw [kmid_rows_at_source R S O T E rho D hNames _ B sourceB j x a h ha hh, heightB]
  obtain ⟨noSecondHeight, rowsBeforeD⟩ :=
    kmid_rows_cut S T L E rho D ((O.height A₀).h + 1) (pt.r + 1) rowsQ1
  obtain ⟨noEarlyFinality, finBeforeD⟩ :=
    kmid_fin_cut S T L E rho D Ef cfg emission decoded ((O.height A₀).h + 1) (pt.r + 1) rowsQ1
  -- Step 13: the early carrier is above B.
  have hpBD := history x₀ (pt.r + 1) B hx₀ (sourceB _ hx₀) highB
    (((kmid_action_strictMono T L).monotone (by omega)).trans hhorA) _ _ hxd hhD.1 nD2
  rw [← parent] at hpBD
  have parentBD := reflect _ _ hpBD
  have pathUD : FGBlock.Preceq (O.height B).T_h X_D.parent := preceq_trans pathUB parentBD
  obtain ⟨iD, _hiD, hDTF⟩ := head_held _ X_D xD (head_read _ _ _ exD n0D hcD2 hxD)
  have slotChainD := slot_chain iD _ X_D hDTF
  have hDne : X_D ≠ .genesis := by
    intro h
    rw [h] at slotD
    have h0 : (0 : Nat) = cD := slotD
    omega
  have hmat : X_D.slot < ((O.height B).T_h).slot + cfg.timeoutDelay + 1 := by
    have hU : pt.r * T.roundSlots < ((O.height B).T_h).slot := freshSlot.1
    rw [slotD, hK.timeout_eq]
    refine lt_of_le_of_lt hcD2' ?_
    rw [e2]
    exact Nat.lt_succ_of_lt (Nat.add_lt_add_right hU _)
  have noMixedD : NoMixedOnPath O.height X_D ((O.height A₀).h + 1) :=
    noMixed _ _ X_D slotChainD entryU pathUD hmat
  -- Step 17: raw chain rows through each carrier.
  have chainA : ChainRowsBefore R E rho A₀ (T.action pt.r) :=
    kmid_chainRows_of_head R T E rho CL HL hs restore x₀ hx₀
      (head_read _ _ _ exA le_rfl n02 hx₀) _ (kmid_vote_lt_action T L le_rfl)
  have chainB : ChainRowsBefore R E rho B (T.action (pt.r + 1)) :=
    kmid_chainRows_of_head R T E rho CL HL hs restore x₀ hx₀
      (head_read _ _ _ exB n01 n12 hx₀) _ (kmid_vote_lt_action T L le_rfl)
  have chainD : ChainRowsBefore R E rho X_D (T.action (pt.r + 2)) :=
    kmid_chainRows_of_head R T E rho CL HL hs restore x₀ hx₀
      (head_read _ _ _ exD n0D hcD2 hx₀) _ (kmid_vote_lt_action T L hcD2)
  -- Step 15: the early batch.
  have batchD : (O.height X_D.parent).h = (O.height A₀).h + 1 →
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .target (pt.r + 1) ((O.height A₀).h + 1)
        (O.height B).T_h X_D := by
    intro hpar
    refine kmid_batchPrem_holder R S O T E rho I D Ef cfg K laws height_eq
      decodeProposal bodyErase bodyRows blockWireRows parentFG parentHeight validFor valid
      ΔF hs hweight linked (Finset.univ \ historyFaulty S rho) hseats
      hK.honest_quorum deltaF receipt (pt.r + 1) _ _ X_D ?_
      ⟨rowsD, by rw [slotD]; exact hcarD, hrowsD⟩
      stD (by rw [slotD]; exact hstD) hlookD hparTFD
      (closed _ _ hstD) (roots _ _ hstD) (validRows _ _ hstD)
      (parentEq _ _ _) (matchValid _ _ _) (by rw [slotD]; exact nD2) entryU pathUD
      hpar ?_
    · rw [slotD]
      exact kmid_batch_horizon T L hF0 hhorA (hGSTr _ (by omega)) hcD1 hcD2
    · intro i hi
      obtain ⟨j, a, ha, hc, hn⟩ := targetsB i (hseats i hi)
      exact ⟨j, pt.r + 1, a, le_rfl, ha, hc, hn⟩
  -- Step 18: the fresh pending justification.
  let freshD : FreshPrem R S E rho T D Ef (pt.r + 1) ((O.height A₀).h + 1) X_D :=
    ⟨hs, hweight, T.action (pt.r + 2), le_rfl, chainD, noSecondHeight,
      noEarlyFinality⟩
  obtain ⟨heightD, justifiedD, justifiedHeightD, pendingD, retainedD⟩ :=
    justifyFresh_W R S E rho T D Ef cfg O.height O.finality heightBridge hc hOrigin
      K hne hK.capacity_ge height_eq finality_eq target (pt.r + 1) _ _ X_D hDne entryU pathUD
      (fun h => hBatch (pt.r + 1) _ _ X_D (batchD h) h) noMixedD freshD
  -- Step 19: the package.
  exact ⟨{
    A₀ := A₀
    B := B
    U := (O.height B).T_h
    X_D := X_D
    cD := cD
    d := (O.height A₀).h
    opening := hA
    eraseA := heA
    carrierA := carrierA
    carrierB := carrierB
    carrierD := carrierD
    honestB := hb
    honestD := hxd
    slotA := slotA
    slotB := slotB
    slotD := slotD
    earlySlot := ⟨hcD1, hcD2⟩
    heightA := rfl
    highA := highA
    heightB := heightB
    entryB := rfl
    freshEntry := entryU
    strictAU := strictAU
    pathUB := pathUB
    freshSlot := freshSlot
    parentAB := parentAB
    parentBD := parentBD
    sourceA := sourceA
    sourceB := sourceB
    serviceD := exD
    heightD := heightD
    justifiedD := justifiedD
    justifiedHeightD := justifiedHeightD
    pendingD := by
      rw [finality_eq] at pendingD
      exact pendingD
    retainedD := retainedD
    noFirstHeight := noFirstHeight
    noSecondHeight := noSecondHeight
    noEarlyFinality := noEarlyFinality
    chainA := chainA
    chainB := chainB
    chainD := chainD
    freshD := freshD
    noMixedD := noMixedD
    batchB := batchB
    batchD := batchD
    targetsB := targetsB
    actionsInRun := hhorA
    capThroughBAction := fun i x W _ hi hW => capB i x W hi hW
    capThroughFinalAction := fun i x W _ hi hW =>
      kmid_held_cap_afterTicks R S O T E rho D Ef hc hOrigin hs hweight _ _ rowsBeforeD i x W hi hW
    finalityThroughFinalAction := fun i x W _ hi hW =>
      kmid_held_finality_afterTicks R S O T E rho D Ef hc hOrigin hs hweight _ _ (Nat.succ_pos _)
        finBeforeD i x W hi hW
    heldDAtFinalAction := fun x hx =>
      kmid_head_held_from R T E rho CL HL hs keep x
        (head_read _ _ _ exD n0D hcD2 hx) _ _
        (kmid_vote_lt_action T L hcD2).le le_rfl
    heldAAtEnd := fun x hx =>
      kmid_head_held_from R T E rho CL HL hs keep x
        (head_read _ _ _ exA le_rfl n02 hx) _ _ le_rfl
        (List.length_filter_le _ _) }⟩

variable (m : KernelMiddleWitnessFG_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
  blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A)

/-- The witness retains the same fresh entry; this does not make a new selection. -/
theorem kernel_middle_fresh_U_holder :
    FGBlock.Preceq m.A₀ m.U ∧ m.A₀ ≠ m.U ∧
    (O.height m.U).h = (O.height m.A₀).h + 1 ∧ FGBlock.Preceq m.U m.B := by
  refine ⟨m.strictAU.1, m.strictAU.2, ?_, m.pathUB⟩
  rw [m.freshEntry.1, m.heightA]

/-- The selected early carrier retains the same pending justification. -/
theorem kernel_middle_early_justification_holder :
    (O.height m.X_D).h = m.d + 2 ∧ (O.height m.X_D).J = m.U ∧
    (O.height m.X_D).h_j = m.d + 1 ∧
    (SimplexFG.Window.derive Ef cfg K m.X_D).h_F < m.d + 1 ∧
    KitFG.Window.RetainedW Ef cfg K m.X_D (m.d + 1) m.U :=
  ⟨m.heightD, m.justifiedD, m.justifiedHeightD, m.pendingD, m.retainedD⟩

/-- The cap includes the actual source read at the final action. -/
theorem kernel_middle_source_cap_holder (CL : FGCoreLaws R) (hs : V2.D.ScheduleWellFormed E rho)
    {x : V} {C : FGBlock (Fin n)} (hx : x ∈ rho.honest)
    (hsrc : actionSourceFG R E rho T x (pt.r + 2) = some (some C)) :
    (O.height C).h ≤ m.d + 2 := by
  obtain ⟨i, hi, hcut, hheld⟩ := kmid_source_held_at_tick R T E rho CL hs hx hsrc
  exact m.capThroughFinalAction i x C (List.getElem?_eq_some_iff.mp hi).1.le hcut.le hheld

end AvailableChain.FGCompose
end

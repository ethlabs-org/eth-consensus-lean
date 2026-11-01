module
public import AvailableChainFGCompose.Proofs.Population.HolderBaseGap
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchAge
public import AvailableChainFGCompose.Proofs.Population.FrontierSearchRepair
public import AvailableChainFGCompose.Proofs.Population.HolderBaseTop

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (O : FGObservationReads R) (T : FGTiming)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot) (I : V2.D.Interface Prot)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))
variable (decodeProposal : Prot.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)
variable (blockWireRows : Prot.State → List Wire)
variable (parentFG : Prot.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : Prot.State → Slot → FGBlock (Fin n) → Height × BlockId)
variable (validFor : Prot.State → Slot → FGBlock (Fin n) → Wire → Bool)
variable (fold : Prot.State → Slot → FGBlock (Fin n) → Window.State (Fin n))
variable (Jst : Time) (leaseSlots : Nat)
variable (obs : FGObservationLaws R O) (cert : FGCertificateLaws Ef O.height O.finality)
variable (inv : ∀ i x, FGStoreInvariant O.height O.finality
  (R.core (rho.stateBefore E i x)).fg)
variable (justif : FGJustificationLaws O.height)
variable (keep : ∀ i j, i ≤ j → ∀ x, TFAt R E rho i x ⊆ TFAt R E rho j x)
variable (positive : 0 < T.delta) (coreLaws : FGCoreLaws R)
variable (erasePreceq : ∀ {A B}, FGBlock.Preceq A B → Block.Preceq (R.erase A) (R.erase B))
variable (joined : Prot.State → Bool) (receipt : Block → Time → V → Prop)

include obs cert inv in
/-- ROOT-DIGEST W2b. Blueprint 21 HG.3 top J. DC: SAME finish repair in a quiet settled
phase. The entry-age input is local to this helper; the public consumer proves it
from the actual start carrier. -/
private theorem p0d5c_top_phase_holder (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
    (schedule : V2.D.ScheduleWellFormed E rho)
    (faultWeight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    {G ΔF ρbar u Dl : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    (hJst : E.t_GST ≤ Jst) (hG : 4 * T.delta ≤ G)
    (slotProposal : PromotionSlotProposal R E rho T I)
    (read : PromotionProposalRead R S E rho O I decodeProposal bodyErase bodyRows parentFG
      parentHeight validFor fold)
    (order : PromotionRowOrder R E rho O I) (signer : PromotionRowSigner S E rho T D)
    (sourceParent : PromotionSourceParent R E rho O T I Jst)
    {deltaT : Nat} (hδ : deltaT = 2 * T.roundSlots) (hbound : LivenessBoundW T ΔF)
    (rowsReceipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin n)),
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .progress r height U X →
      (O.height X.parent).h = height → ProgressCoveredByChild Ef O.height X U height)
    (hfold : ProgressFoldAdvance Ef O.height deltaT)
    (honestQuorum : ∃ Q : Finset (Fin n),
      (∀ i ∈ Q, safetyHolder S rho i ∈ rho.honest) ∧ Ef.q ≤ Ef.weightOf Q)
    (entryAgreement : ∀ r x y K L, x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) →
      actionSourceFG R E rho T y r = some (some L) →
      (O.height K).T_h.root = (O.height L).T_h.root → (O.height K).T_h = (O.height L).T_h)
    (sourceSlot : ∀ r x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
    (ancestorSlot : ∀ r x K A, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot)
    (eraseInj : Function.Injective R.erase)
    (eraseReflect : ∀ A B : FGBlock (Fin n), Block.Preceq (R.erase A) (R.erase B) →
      FGBlock.Preceq A B)
    (floor : AttemptProposalFloor R E rho O T I Jst)
    (gateCopy : ∀ u v m J contested q Q, Jst ≤ u →
      PhaseInterval R E rho O u v m J contested →
      FrontierSeedQualification T leaseSlots E.t_GST u q → T.gate q ≤ v →
      HonestProposal E rho I q Q → ∃ i x Qfg, V2.D.Run.idxBefore rho u ≤ i ∧
        i ≤ timeIdx rho v ∧ x ∈ rho.honest ∧
        Qfg ∈ (R.core (rho.stateBefore E i x)).fg.TF ∧ R.erase Qfg = Q)
    (service : ∀ u v m J contested q Q Qfg, Jst ≤ u → HonestProposal E rho I q Q →
      R.erase Qfg = Q → (O.height Qfg).h = m → FrontierProposalService R E rho T q Q →
      FrontierSeedQualification T leaseSlots E.t_GST u q → u ≤ T.proposal q →
      PhaseInterval R E rho O u (T.gate q) m J contested → T.gate q ≤ v →
      v ≤ rho.horizon →
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
        (R.core (rho.stateBefore E i x)).fg.h_max ≤ m) →
      FrontierLocalServiceFG R S E rho O T I D.heightPair q Q Qfg m v)
    (common : ∀ u m J contested q Q Qfg r, Jst ≤ u → HonestProposal E rho I q Q →
      R.erase Qfg = Q → FrontierProposalService R E rho T q Q →
      FrontierSeedQualification T leaseSlots E.t_GST u q → u ≤ T.proposal q →
      q ≤ r * T.roundSlots → (∀ r', q ≤ r' * T.roundSlots → r ≤ r') →
      PhaseInterval R E rho O u (T.action r) m J contested →
      OpeningCoveredFG R S E rho O.height T D.heightPair (FGHonestSeats S rho) r Q ∧
      ((O.height Qfg).h = m - 1 → OpeningEntry R E rho O.height T r (m - 1) ∨
        ∃ x K, x ∈ rho.honest ∧ actionSourceFG R E rho T x r = some (some K) ∧
          (O.height K).h = m))
    {J : FGBlock (Fin n)} {m : Nat} {w : Time} (hready : Jst ≤ u)
    (hp : PhaseInterval R E rho O u Dl m (some J) false)
    (allowance : FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar u)
    (hrepairBudget : u + ρbar ≤ Dl)
    (hopeningBudget : u + ρbar + FGCompose.P T + Γ T G + epsF T ΔF ≤ Dl)
    (hentryBudget : w + 2 * FGCompose.P T + Γ T G - 4 * T.delta ≤ Dl)
    (hentryAge : ∀ q Q Qfg, HonestProposal E rho I q Q → R.erase Qfg = Q →
      u ≤ T.proposal q → T.gate q ≤ Dl → (O.height Qfg).h = m - 1 →
      T.proposal (O.height Qfg).T_h.slot ≤ w - 6 * T.delta) :
    ∃ t, u ≤ t ∧ t ≤ Dl ∧
      StrongServedFG R S E rho O T I D.heightPair Jst leaseSlots m t := by
  classical
  have p0d5c_top_eps_nonneg (T : FGTiming) (hT : FGTimingLaws T) {ΔF : Time} (hF : 0 ≤ ΔF) :
      0 ≤ epsF T ΔF := by
    clear * - hT hF
    have hd : 0 < 4 * T.delta := by linarith [hT.delta_pos]
    have hn : 0 ≤ 6 * T.delta + ΔF + 4 * T.delta - 1 := by
      have hd1 : (1 : Time) ≤ T.delta := hT.delta_pos
      linarith
    have hc : 6 * T.delta + ΔF ≤ (kappaF T ΔF : Time) * (4 * T.delta) := by
      delta kappaF
      rw [Int.toNat_of_nonneg (Int.ediv_nonneg hn hd.le)]
      have hhi := Int.lt_ediv_add_one_mul_self (6 * T.delta + ΔF + 4 * T.delta - 1) hd
      nlinarith
    have hnat : 2 ≤ kappaF T ΔF := by
      by_contra hk
      have hk' : (kappaF T ΔF : Time) ≤ 1 := by
        exact_mod_cast (show kappaF T ΔF ≤ 1 by omega)
      nlinarith [hT.delta_pos]
    have hk2 : (2 : Time) ≤ kappaF T ΔF := by exact_mod_cast hnat
    unfold epsF betaF
    nlinarith [hT.delta_pos]
  have p0d5c_top_first_time (T : FGTiming) (hT : FGTimingLaws T) {q r : Nat}
      (hqr : q ≤ r * T.roundSlots) (hfirst : ∀ r', q ≤ r' * T.roundSlots → r ≤ r') :
      T.gate q ≤ T.action r ∧ T.action r ≤ T.gate q + FGCompose.P T - 4 * T.delta := by
    clear * - hT hqr hfirst
    have hd := hT.delta_pos
    rw [hT.action_eq, hT.gate_eq, hT.gate_eq, hT.proposal_eq, hT.proposal_eq]
    have hqrI : (q : Time) ≤ ((r * T.roundSlots : Nat) : Time) := by exact_mod_cast hqr
    have hup : r * T.roundSlots + 1 ≤ q + T.roundSlots := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr
        have := hT.rounds
        omega
      · have hlt : ¬ q ≤ (r - 1) * T.roundSlots := fun h => by
          have := hfirst (r - 1) h
          omega
        have he : (r - 1) * T.roundSlots + T.roundSlots = r * T.roundSlots := by
          rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr]
        omega
    have hupI : ((r * T.roundSlots : Nat) : Time) + 1 ≤ (q : Time) + T.roundSlots := by
      exact_mod_cast hup
    unfold FGCompose.P
    constructor <;> nlinarith
  have p0d5c_top_action (T : FGTiming) (hT : FGTimingLaws T) (r : Nat) :
      T.action r = (r : Time) * FGCompose.P T + 6 * T.delta := by
    clear * - hT
    rw [hT.action_eq, hT.gate_eq, hT.proposal_eq]
    unfold FGCompose.P
    push_cast
    ring
  have p0d5c_top_slot_time (T : FGTiming) (hT : FGTimingLaws T) {a b : Slot} (h : a ≤ b) :
      T.proposal a ≤ T.proposal b := by
    clear * - hT h
    rw [hT.proposal_eq, hT.proposal_eq]
    have hI : (a : Time) ≤ b := by exact_mod_cast h
    nlinarith [hT.delta_pos]
  have p0d5c_top_beta (T : FGTiming) (hT : FGTimingLaws T) {ΔF : Time}
      (hbound : LivenessBoundW T ΔF) : betaF T ΔF ≤ FGCompose.P T := by
    clear * - hT hbound
    have hk : (kappaF T ΔF : Time) ≤ T.roundSlots := by exact_mod_cast hbound.kappa_le_R
    delta betaF FGCompose.P
    nlinarith [hT.delta_pos]
  have hGST : E.t_GST ≤ u := hJst.trans hready
  have hd := hT.delta_pos
  have hP := frontierSearch_period_bound_core T hT
  have hΓ := (healing_promotion_gap_remainder T hT G).1
  have hbudget0 : u + ρbar ≤ Dl := hrepairBudget
  have hF : 0 ≤ ΔF := by rw [hdelta] at deltaF; linarith
  have heps0 := p0d5c_top_eps_nonneg T hT hF
  obtain ⟨_, l, hl, hrep⟩ := allowance
  obtain ⟨hafter, hseedEx⟩ := hrep hG Dl m (some J) false hready hp
  obtain ⟨q, Q, hlq, hgate, hQ, hsvc⟩ := hseedEx hbudget0
  have hseed := frontierSearch_seed_of_start_core E T leaseSlots hl hlq
  have huq := frontierSearch_seed_after_core T leaseSlots hT hk hseed
  have hqg : T.proposal q ≤ T.gate q := by rw [hT.gate_eq]; linarith
  have hgateD : T.gate q ≤ Dl := hgate.trans hbudget0
  obtain ⟨iq, xq, Qfg, hiq0, hiq1, hxq, hQmem, hErase⟩ :=
    gateCopy u Dl m (some J) false q Q hready hp hseed hgateD hQ
  obtain ⟨hlo, hhi⟩ := frontierSearch_proposal_heights_core R E rho O T I Jst Ef obs cert inv
    floor hready hp huq hgateD hQ hErase ⟨iq, xq, hiq0, hiq1, hxq, hQmem⟩
  have finishAt {s : Slot} {X : FGBlock (Fin n)} (hls : T.proposal l < T.proposal s)
      (hnew : HonestProposal E rho I s (R.erase X)) (hut : u ≤ T.proposal s)
      (hsD : T.gate s ≤ Dl) (hh : m ≤ (O.height X).h) :
      ∃ t, u ≤ t ∧ t ≤ Dl ∧
      StrongServedFG R S E rho O T I D.heightPair Jst leaseSlots m t := by
    have hsg : u ≤ T.gate s := hut.trans (by rw [hT.gate_eq]; linarith)
    have hps := frontierSearch_phase_cut_core R E rho O hp hsg hsD
    have hss := (hrep hG (T.gate s) m (some J) false hready hps).1 s _ hls le_rfl hnew
    have hseedS := frontierSearch_seed_of_start_core E T leaseSlots hl hls
    obtain ⟨j, y, Y, hj0, hj1, hy, hYmem, hYe⟩ :=
      gateCopy u Dl m (some J) false s _ hready hp hseedS hsD hnew
    have hYX : Y = X := eraseInj hYe
    subst Y
    have hheights := frontierSearch_proposal_heights_core R E rho O T I Jst Ef obs cert inv
      floor hready hp hut hsD hnew rfl ⟨j, y, hj0, hj1, hy, hYmem⟩
    have hh' : (O.height X).h = m := Nat.le_antisymm hheights.2 hh
    exact ⟨_, hsg, hsD, frontierSearch_save_seed_holder R S E rho O T I D.heightPair Jst leaseSlots
      obs hT hk hready hp hseedS hnew rfl hh' hss hsD
      (service u (T.gate s) m (some J) false s _ X hready hnew rfl hh' hss hseedS hut hps le_rfl
        (hsD.trans hp.2.1) (frontierSearch_phase_cap_core R E rho O obs hp hsD))⟩
  by_cases hhigh : (O.height Qfg).h = m
  · exact finishAt hlq (hErase ▸ hQ) huq hgateD hhigh.ge
  have hlow : (O.height Qfg).h = m - 1 := by
    have hlo' : m - 1 ≤ (O.height Qfg).h := by simpa using hlo
    exact Nat.le_antisymm (Nat.le_sub_one_of_lt (lt_of_le_of_ne hhi hhigh)) hlo'
  have hex : ∃ r, q ≤ r * T.roundSlots := ⟨q, by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left q
      (show 1 ≤ T.roundSlots from (by decide : 1 ≤ 2).trans hT.rounds)⟩
  let r := Nat.find hex
  have hqr : q ≤ r * T.roundSlots := Nat.find_spec hex
  have hfirst : ∀ r', q ≤ r' * T.roundSlots → r ≤ r' := fun r' hr' => Nat.find_min' hex hr'
  obtain ⟨h0, h1⟩ := p0d5c_top_first_time T hT hqr hfirst
  have ha := p0d5c_top_action T hT r
  have har : T.action r ≤ u + ρbar + (FGCompose.P T - 4 * T.delta) := by linarith
  have harD : T.action r ≤ Dl := by linarith
  have hur : u ≤ T.action r := by linarith
  have hpr := frontierSearch_phase_cut_core R E rho O hp hur harD
  obtain ⟨hc, hlowOr⟩ := common u m (some J) false q Q Qfg r hready hQ hErase hsvc hseed huq hqr
    hfirst hpr
  have hqrT : T.proposal q ≤ (r : Time) * FGCompose.P T := by
    have hqrI : (q : Time) ≤ ((r * T.roundSlots : Nat) : Time) := by exact_mod_cast hqr
    rw [hT.proposal_eq]
    unfold FGCompose.P
    push_cast at hqrI
    nlinarith
  have huvote : u ≤ T.vote (r * T.roundSlots) := by
    rw [hT.vote_eq]
    have := p0d5c_top_slot_time T hT hqr
    linarith
  have hstart : E.t_GST ≤ (r : Time) * FGCompose.P T := hGST.trans (huq.trans hqrT)
  rcases hlowOr hlow with he | ⟨x, K, hx, hK, hKh⟩
  · obtain ⟨A, hAh, hAq⟩ := honestQuorum
    have hA : A ⊆ FGHonestSeats S rho := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hAh i hi⟩
    have hne : A.Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      change Ef.q ≤ ∑ i ∈ A, Ef.weight i at hAq
      rw [he, Finset.sum_empty] at hAq
      omega
    obtain ⟨seat, hseat⟩ := hne
    let xh := safetyHolder S rho seat
    have hxh : xh ∈ rho.honest := hAh seat hseat
    obtain ⟨K, nd, j, rSent, a, _, hK, _, hQK, _, _, _⟩ := hc seat (hA hseat)
    have hKheight := (he.choose_spec xh K hxh hK).1
    have hQKfg : FGBlock.Preceq Qfg K := eraseReflect _ _ (hErase ▸ hQK)
    have hKU : (O.height K).T_h = (O.height Qfg).T_h :=
      (cert.height.entry_plateau hQKfg (hlow.trans hKheight.symm)).symm
    let U := (O.height Qfg).T_h
    have hage : T.proposal U.slot ≤ w - 6 * T.delta :=
      hentryAge q Q Qfg hQ hErase huq hgateD hlow
    have heps : epsF T ΔF ≤ FGCompose.P T - 8 * T.delta := by
      have := p0d5c_top_beta T hT hbound
      unfold epsF
      linarith
    have hgateBudget : max (T.action r + Γ T G + 4 * T.delta + epsF T ΔF)
        (T.proposal U.slot + 2 * FGCompose.P T + Γ T G + 2 * T.delta) ≤ Dl := by
      apply max_le
      · linarith
      · linarith
    have hwindow : max ((r : Time) * FGCompose.P T + betaF T ΔF - 4 * T.delta)
        (T.proposal U.slot + 2 * FGCompose.P T - 4 * T.delta) + G ≤ rho.horizon := by
      have hb := p0d5c_top_beta T hT hbound
      apply le_trans _ hp.2.1
      rw [← max_add_add_right]
      apply max_le
      · have hg := (le_max_left _ _).trans hgateBudget
        unfold epsF at hg
        linarith
      · linarith
    obtain ⟨s, X, hnew, _, hlater, hsD, hh⟩ :=
      frontierSearch_age_service_holder R S O T E rho I D Ef
      decodeProposal bodyErase bodyRows blockWireRows parentFG parentHeight validFor fold
      cert.height hA ⟨seat, hseat⟩ hT schedule faultWeight deltaF hdelta gap hJst
      slotProposal read order signer
      sourceParent hδ hbound rowsReceipt progressCoverage hfold hAq he
      (fun i hi => hc i (hA hi))
      ⟨xh, K, hxh, hK, hKU⟩ (entryAgreement r) (sourceSlot r) (ancestorSlot r) hready hstart
      huvote hp hwindow hgateBudget
    have hls : T.proposal l < T.proposal s := by linarith
    exact finishAt hls hnew (hur.trans hlater.le) hsD
      (by simpa only [Nat.sub_add_cancel hp.2.2.1] using hh)
  · let b := (r : Time) * FGCompose.P T + 4 * T.delta
    have hbGST : E.t_GST ≤ b := by dsimp only [b]; linarith
    have hbhor : b + G ≤ rho.horizon := by
      apply le_trans _ hp.2.1
      dsimp only [b]
      linarith
    obtain ⟨s, hloS, hhiS, hslotS⟩ := gap b hbGST hbhor
    have hsD : T.gate s ≤ Dl := by
      rw [hT.gate_eq]
      dsimp only [b] at hhiS
      linarith
    have hsHor : T.proposal s ≤ rho.horizon := by
      rw [hT.gate_eq] at hsD
      linarith [hp.2.1]
    obtain ⟨X, hnew, _⟩ := slotProposal s hslotS (by dsimp only [b] at hloS; linarith) hsHor
    have hslabel : r * T.roundSlots + 2 ≤ s := by
      dsimp only [b] at hloS
      rw [hT.proposal_eq] at hloS
      unfold FGCompose.P at hloS
      have hz : ((r * T.roundSlots : Nat) : Time) + 1 < s := by push_cast; nlinarith
      exact_mod_cast Int.add_one_le_iff.mpr hz
    have hat : T.action r < T.proposal s := by
      have hz : ((r * T.roundSlots + 2 : Nat) : Time) ≤ s := by exact_mod_cast hslabel
      rw [ha, hT.proposal_eq]
      unfold FGCompose.P
      push_cast at hz
      have hm := mul_le_mul_of_nonneg_left hz (show (0 : Time) ≤ 4 * T.delta by linarith)
      have he : (r : Time) * (4 * (T.roundSlots : Time) * T.delta) =
          4 * T.delta * ((r : Time) * T.roundSlots) := by ring
      have he' : 4 * (s : Time) * T.delta = 4 * T.delta * s := by ring
      rw [he, he']
      linarith
    have hpts := frontierSearch_phase_cut_core R E rho O hp (hur.trans hat.le)
      (by rw [hT.gate_eq] at hsD; linarith)
    have hpath := sourceParent u m (some J) false r s X x K hready hpts huvote hat.le hslabel
      hnew hx hK
    have hPX : FGBlock.Preceq X.parent X := by
      cases X with
      | genesis => exact KitFG.preceq_refl _
      | node P s root body rows => exact KitFG.preceq_parent_node _ _ _ _ _
    have hh : m ≤ (O.height X).h :=
      (hKh ▸ cert.height.h_mono hpath).trans (cert.height.h_mono hPX)
    have hls : T.proposal l < T.proposal s := by linarith
    exact finishAt hls hnew (hur.trans hat.le) hsD hh

include obs cert inv justif keep positive coreLaws erasePreceq in
/-- ROOT-DIGEST W2b. Blueprint 21 HG.3 top J; run 2 R2-b.
DC: SAME keep both E_jF branches. The actual accepted J supplies its age;
no exact-service-to-seed reconstruction or E_jF collapse is used. -/
theorem frontier_hg3_topJ_holder (hT : FGTimingLaws T) (hk : 1 ≤ leaseSlots)
    (crossing : RXing R E rho O) (schedule : V2.D.ScheduleWellFormed E rho)
    (mono : FGRunOrderLaws E rho R)
    (awake : ∀ y ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon →
      E.awake y t = true)
    (joinedTick : ∀ iy y t, y ∈ rho.honest →
      rho.events[iy]? = some (.tick y t) → t ≤ rho.horizon →
      E.t_GST ≤ slotStartZ T (((slotAt T t : Slot) : Int) - 1) →
      joined (Prot.clock (rho.stateBefore E iy y) t) = true)
    (readyCut : ∀ t, Jst ≤ t → E.t_GST ≤ slotStartZ T (((slotAt T t : Slot) : Int) - 1))
    (hServices : ∀ i (ev : V2.Event V Prot.Object) m,
      rho.events[i]? = some ev → Jst ≤ ev.time → 1 ≤ m →
      frontierAtIdx R E rho (i + 1) = m → ev.time + T.delta ≤ rho.horizon →
      PhaseWitnessReceiptScope R E rho O joined receipt (i + 1) m (ev.time + T.delta))
    (receiptHeld : ∀ W d y, y ∈ rho.honest → receipt (R.erase W) d y →
      W ∈ (R.core (rho.stateBeforeTime E d y)).fg.TF)
    (faultWeight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    {G ΔF ρbar : Time} (deltaF : E.Δ ≤ ΔF) (hdelta : E.Δ = T.delta)
    (gap : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
      ∃ s, t < T.proposal s ∧ T.proposal s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s)
    (hJst : E.t_GST ≤ Jst) (hG : 4 * T.delta ≤ G)
    (slotProposal : PromotionSlotProposal R E rho T I)
    (read : PromotionProposalRead R S E rho O I decodeProposal bodyErase bodyRows parentFG
      parentHeight validFor fold)
    (order : PromotionRowOrder R E rho O I) (signer : PromotionRowSigner S E rho T D)
    (sourceParent : PromotionSourceParent R E rho O T I Jst)
    {deltaT : Nat} (hδ : deltaT = 2 * T.roundSlots) (hbound : LivenessBoundW T ΔF)
    (rowsReceipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (progressCoverage : ∀ (r height : Nat) (U X : FGBlock (Fin n)),
      BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
        parentFG parentHeight validFor ΔF .progress r height U X →
      (O.height X.parent).h = height → ProgressCoveredByChild Ef O.height X U height)
    (hfold : ProgressFoldAdvance Ef O.height deltaT)
    (honestQuorum : ∃ Q : Finset (Fin n),
      (∀ i ∈ Q, safetyHolder S rho i ∈ rho.honest) ∧ Ef.q ≤ Ef.weightOf Q)
    (entryAgreement : ∀ r x y K L, x ∈ rho.honest → y ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) →
      actionSourceFG R E rho T y r = some (some L) →
      (O.height K).T_h.root = (O.height L).T_h.root → (O.height K).T_h = (O.height L).T_h)
    (sourceSlot : ∀ r x K, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
    (ancestorSlot : ∀ r x K A, x ∈ rho.honest →
      actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
      A.slot ≤ K.slot)
    (eraseReflect : ∀ A B : FGBlock (Fin n), Block.Preceq (R.erase A) (R.erase B) →
      FGBlock.Preceq A B)
    (floor : AttemptProposalFloor R E rho O T I Jst)
    (gateCopy : ∀ u v m J contested q Q, Jst ≤ u →
      PhaseInterval R E rho O u v m J contested →
      FrontierSeedQualification T leaseSlots E.t_GST u q → T.gate q ≤ v →
      HonestProposal E rho I q Q → ∃ i x Qfg, V2.D.Run.idxBefore rho u ≤ i ∧
        i ≤ timeIdx rho v ∧ x ∈ rho.honest ∧
        Qfg ∈ (R.core (rho.stateBefore E i x)).fg.TF ∧ R.erase Qfg = Q)
    (service : ∀ u v m J contested q Q Qfg, Jst ≤ u → HonestProposal E rho I q Q →
      R.erase Qfg = Q → (O.height Qfg).h = m → FrontierProposalService R E rho T q Q →
      FrontierSeedQualification T leaseSlots E.t_GST u q → u ≤ T.proposal q →
      PhaseInterval R E rho O u (T.gate q) m J contested → T.gate q ≤ v →
      v ≤ rho.horizon →
      (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
        (R.core (rho.stateBefore E i x)).fg.h_max ≤ m) →
      FrontierLocalServiceFG R S E rho O T I D.heightPair q Q Qfg m v)
    (common : ∀ u m J contested q Q Qfg r, Jst ≤ u → HonestProposal E rho I q Q →
      R.erase Qfg = Q → FrontierProposalService R E rho T q Q →
      FrontierSeedQualification T leaseSlots E.t_GST u q → u ≤ T.proposal q →
      q ≤ r * T.roundSlots → (∀ r', q ≤ r' * T.roundSlots → r ≤ r') →
      PhaseInterval R E rho O u (T.action r) m J contested →
      OpeningCoveredFG R S E rho O.height T D.heightPair (FGHonestSeats S rho) r Q ∧
      ((O.height Qfg).h = m - 1 → OpeningEntry R E rho O.height T r (m - 1) ∨
        ∃ x K, x ∈ rho.honest ∧ actionSourceFG R E rho T x r = some (some K) ∧
          (O.height K).h = m))
    (justifiedSource : ∀ i x, x ∈ rho.honest →
      (R.core (rho.stateBefore E i x)).fg.h_j ≠ 0 →
      ∃ j y r a K, j < i ∧ HonestRowAt S E rho T j y r a ∧
        actionSourceFG R E rho T y r = some (some K) ∧
        (O.height K).T_h = (R.core (rho.stateBefore E i x)).fg.J)
    (parentFrame : ∀ q Q, HonestProposal E rho I q Q → ∃ j,
      rho.events[j]? = some (.tick (V2.D.proposerOf rho I q) (T.proposal q)) ∧
      ∀ Qfg, R.erase Qfg = Q → FGBlock.Preceq
        (O.controls (rho.stateBefore E j (V2.D.proposerOf rho I q))).Z Qfg.parent)
    {i m : Nat} {ev : V2.Event V Prot.Object}
    (hstart : FrontierSearchStart R E rho O T Jst i ev m .topJ)
    (allowance : FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar
      (ev.time + 3 * T.delta))
    (hhor : ev.time + E_jF T ΔF G ρbar ≤ rho.horizon) :
    FrontierHG3ResultFG R S E rho O T I D.heightPair Jst leaseSlots i m ev.time
      (ev.time + E_jF T ΔF G ρbar) := by
  have p0d5c_top_eps_nonneg (T : FGTiming) (hT : FGTimingLaws T) {ΔF : Time} (hF : 0 ≤ ΔF) :
      0 ≤ epsF T ΔF := by
    clear * - hT hF
    have hd : 0 < 4 * T.delta := by linarith [hT.delta_pos]
    have hn : 0 ≤ 6 * T.delta + ΔF + 4 * T.delta - 1 := by
      have hd1 : (1 : Time) ≤ T.delta := hT.delta_pos
      linarith
    have hc : 6 * T.delta + ΔF ≤ (kappaF T ΔF : Time) * (4 * T.delta) := by
      delta kappaF
      rw [Int.toNat_of_nonneg (Int.ediv_nonneg hn hd.le)]
      have hhi := Int.lt_ediv_add_one_mul_self (6 * T.delta + ΔF + 4 * T.delta - 1) hd
      nlinarith
    have hnat : 2 ≤ kappaF T ΔF := by
      by_contra hk
      have hk' : (kappaF T ΔF : Time) ≤ 1 := by
        exact_mod_cast (show kappaF T ΔF ≤ 1 by omega)
      nlinarith [hT.delta_pos]
    have hk2 : (2 : Time) ≤ kappaF T ΔF := by exact_mod_cast hnat
    unfold epsF betaF
    nlinarith [hT.delta_pos]
  obtain ⟨hi, hgst0, _, hfront, hm, hkind⟩ :=
    (FrontierSearchStart_def R E rho O T Jst i ev m .topJ).mp hstart
  have hρ : 0 ≤ ρbar := allowance.1
  have hd := hT.delta_pos
  have hP := frontierSearch_period_bound_core T hT
  have hΓ := (healing_promotion_gap_remainder T hT G).1
  have hF : 0 ≤ ΔF := by rw [hdelta] at deltaF; linarith
  have heps := p0d5c_top_eps_nonneg T hT hF
  have hleft : ev.time + 3 * T.delta + ρbar + FGCompose.P T + Γ T G + epsF T ΔF ≤
      ev.time + E_jF T ΔF G ρbar := by
    have hb := le_max_left (ρbar + FGCompose.P T + Γ T G + 3 * T.delta + epsF T ΔF)
      (2 * FGCompose.P T + Γ T G - 4 * T.delta)
    unfold E_jF
    linarith only [hb]
  have hright : ev.time + 2 * FGCompose.P T + Γ T G - 4 * T.delta ≤
      ev.time + E_jF T ΔF G ρbar := by
    have hb := le_max_right (ρbar + FGCompose.P T + Γ T G + 3 * T.delta + epsF T ΔF)
      (2 * FGCompose.P T + Γ T G - 4 * T.delta)
    unfold E_jF
    linarith only [hb]
  have hrepair : ev.time + 3 * T.delta + ρbar ≤ ev.time + E_jF T ΔF G ρbar := by linarith
  rcases frontierSearch_first_effective_split R E rho O schedule i
      (ev.time + E_jF T ΔF G ρbar) with hstop | hquiet
  · rcases frontierSearch_classify_stop R E rho O mono hfront hstop with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  obtain ⟨J, hp, _⟩ := healing_settle_start_on (R := R) (E := E) (rho := rho) (O := O)
    (Ef := Ef) (obs := obs) (cert := cert) (inv := inv) (justif := justif) (keep := keep)
    (Jst := Jst) (T := T) (positive := positive) (coreLaws := coreLaws)
    (erasePreceq := erasePreceq) (joined := joined) (receipt := receipt)
    crossing schedule mono hdelta hJst awake joinedTick readyCut hServices receiptHeld
    i ev _ m .topJ hi hgst0 (by linarith) hhor hm hfront hkind hquiet
  have hready : Jst ≤ ev.time + 3 * T.delta := by linarith
  have p0d5c_top_idx_le (hs : V2.D.ScheduleWellFormed E rho)
      {j : Nat} {e : V2.Event V Prot.Object} (hj : rho.events[j]? = some e) {u : Time}
      (hu : u ≤ e.time) : V2.D.Run.idxBefore rho u ≤ j := by
    by_contra hn
    have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs hj u).mp (Nat.lt_of_not_ge hn)
    exact (not_lt.mpr hu) hlt
  have p0d5c_top_lt_timeIdx (hs : V2.D.ScheduleWellFormed E rho)
      {k : Nat} {e : V2.Event V Prot.Object} (hk : rho.events[k]? = some e) {t : Time}
      (ht : e.time ≤ t) : k < timeIdx rho t := by
    have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hs hk (t + 1)).mpr (Int.lt_add_one_iff.mpr ht)
    refine hlt.trans_le ?_
    change (rho.events.filter (fun e => decide (e.time < t + 1))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ t))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he =>
      decide_eq_true (Int.lt_add_one_iff.mp (of_decide_eq_true he)))
  have p0d5c_top_low_entry (hs : V2.D.ScheduleWellFormed E rho)
      (parentFrame : ∀ q Q, HonestProposal E rho I q Q → ∃ j,
        rho.events[j]? = some (.tick (V2.D.proposerOf rho I q) (T.proposal q)) ∧
        ∀ Qfg, R.erase Qfg = Q → FGBlock.Preceq
          (O.controls (rho.stateBefore E j (V2.D.proposerOf rho I q))).Z Qfg.parent)
      {u Dl : Time} {m q : Nat} {J Qfg : FGBlock (Fin n)} {Q : Block}
      (hp : PhaseInterval R E rho O u Dl m (some J) false)
      (hQ : HonestProposal E rho I q Q) (he : R.erase Qfg = Q)
      (huq : u ≤ T.proposal q) (hqD : T.proposal q ≤ Dl)
      (hlow : (O.height Qfg).h = m - 1) : (O.height Qfg).T_h = J := by
    obtain ⟨j, hj, hframe⟩ := parentFrame q Q hQ
    let y := V2.D.proposerOf rho I q
    have hy : y ∈ rho.honest := hQ.1.2
    obtain ⟨hH, hc, hr⟩ := hp.2.2.2 j y (p0d5c_top_idx_le hs hj huq)
      (p0d5c_top_lt_timeIdx hs hj hqD).le hy
    have hZ : (O.controls (rho.stateBefore E j y)).Z = J := by
      unfold Controls.Z
      rw [hr.1]
      exact hr.2
    have hJQ : FGBlock.Preceq J Qfg := by
      have hPQ : FGBlock.Preceq Qfg.parent Qfg := by
        cases Qfg with
        | genesis => exact KitFG.preceq_refl _
        | node P s root body rows => exact KitFG.preceq_parent_node _ _ _ _ _
      exact KitFG.preceq_trans (hZ ▸ hframe Qfg he) hPQ
    have hroot := hr.1
    rw [obs.controls_eq] at hH hroot hr
    unfold Controls.rootIsJ at hroot
    have htop : (R.core (rho.stateBefore E j y)).fg.h_max =
        (R.core (rho.stateBefore E j y)).fg.h_j + 1 :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hroot).1
    obtain ⟨C, _, _, hjC, hJC⟩ := (inv j y).pair.1
    have hCJ : (O.height C).J = J := hJC.symm.trans hr.2
    have hpos := cert.height.one_le_h Qfg
    have hjC' : (O.height C).h_j = m - 1 := by
      change (R.core (rho.stateBefore E j y)).fg.h_max = m at hH
      simp only [Height] at *
      omega
    have hJheight : (O.height J).h = m - 1 := by
      rw [← hCJ, justif.J_height C (by simp only [Height] at *; omega)]
      exact hjC'
    have hJe : (O.height J).T_h = J := by
      rw [← hCJ]
      exact justif.J_entry C
    exact (cert.height.entry_plateau hJQ (hJheight.trans hlow.symm)).symm.trans hJe
  have p0d5c_top_seed_age (hT : FGTimingLaws T)
      (crossing : RXing R E rho O) (hs : V2.D.ScheduleWellFormed E rho)
      (mono : FGRunOrderLaws E rho R)
      (joinedTick : ∀ iy y t, y ∈ rho.honest →
        rho.events[iy]? = some (.tick y t) → t ≤ rho.horizon →
        E.t_GST ≤ slotStartZ T (((slotAt T t : Slot) : Int) - 1) →
        joined (Prot.clock (rho.stateBefore E iy y) t) = true)
      (readyCut : ∀ t, Jst ≤ t → E.t_GST ≤ slotStartZ T (((slotAt T t : Slot) : Int) - 1))
      (hServices : ∀ i (ev : V2.Event V Prot.Object) m,
        rho.events[i]? = some ev → Jst ≤ ev.time → 1 ≤ m →
        frontierAtIdx R E rho (i + 1) = m → ev.time + T.delta ≤ rho.horizon →
        PhaseWitnessReceiptScope R E rho O joined receipt (i + 1) m (ev.time + T.delta))
      (receiptHeld : ∀ W d y, y ∈ rho.honest → receipt (R.erase W) d y →
        W ∈ (R.core (rho.stateBeforeTime E d y)).fg.TF)
      (justifiedSource : ∀ i x, x ∈ rho.honest →
        (R.core (rho.stateBefore E i x)).fg.h_j ≠ 0 →
        ∃ j y r a K, j < i ∧ HonestRowAt S E rho T j y r a ∧
          actionSourceFG R E rho T y r = some (some K) ∧
          (O.height K).T_h = (R.core (rho.stateBefore E i x)).fg.J)
      (sourceSlot : ∀ r x K, x ∈ rho.honest →
        actionSourceFG R E rho T x r = some (some K) → K.slot ≤ r * T.roundSlots)
      (ancestorSlot : ∀ r x K A, x ∈ rho.honest →
        actionSourceFG R E rho T x r = some (some K) → FGBlock.Preceq A K →
        A.slot ≤ K.slot)
      (parentFrame : ∀ q Q, HonestProposal E rho I q Q → ∃ j,
        rho.events[j]? = some (.tick (V2.D.proposerOf rho I q) (T.proposal q)) ∧
        ∀ Qfg, R.erase Qfg = Q → FGBlock.Preceq
          (O.controls (rho.stateBefore E j (V2.D.proposerOf rho I q))).Z Qfg.parent)
      {Dl : Time} {i m : Nat} {ev : V2.Event V Prot.Object} {J : FGBlock (Fin n)}
      (hstart : FrontierSearchStart R E rho O T Jst i ev m .topJ)
      (hquiet : ∀ j, i < j → j < timeIdx rho Dl → ¬ EffectiveEvent R E rho O j)
      (hp : PhaseInterval R E rho O (ev.time + 3 * T.delta) Dl m (some J) false) :
      ∀ q Q Qfg, HonestProposal E rho I q Q → R.erase Qfg = Q →
        ev.time + 3 * T.delta ≤ T.proposal q → T.gate q ≤ Dl → (O.height Qfg).h = m - 1 →
        T.proposal (O.height Qfg).T_h.slot ≤ ev.time - 6 * T.delta := by
    intro q Q Qfg hQ he huq hgate hlow
    have hd := hT.delta_pos
    obtain ⟨hi, hgst, _, hfront, hm, ht, _⟩ :=
      (FrontierSearchStart_def R E rho O T Jst i ev m .topJ).mp hstart
    have hwin := healing_phase_window_all R E rho O mono hfront hquiet
    obtain ⟨j, hq, hframe⟩ := parentFrame q Q hQ
    let y := V2.D.proposerOf rho I q
    have hy : y ∈ rho.honest := hQ.1.2
    have hqg : T.proposal q ≤ T.gate q := by rw [hT.gate_eq]; linarith
    have hcut : V2.D.Run.idxBefore rho (ev.time + T.delta) ≤ j :=
      p0d5c_top_idx_le hs hq (show ev.time + T.delta ≤ T.proposal q by linarith)
    have hiCut : i + 1 ≤ V2.D.Run.idxBefore rho (ev.time + T.delta) :=
      Nat.succ_le_of_lt ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi _).mpr
        (lt_add_of_pos_right _ hd))
    have hjD : j ≤ timeIdx rho Dl := (p0d5c_top_lt_timeIdx hs hq (hqg.trans hgate)).le
    have hreceiptHor : ev.time + T.delta ≤ rho.horizon := by linarith [hp.1, hp.2.1]
    have hqHor : T.proposal q ≤ rho.horizon := (hqg.trans hgate).trans hp.2.1
    have hslotq : slotAt T (T.proposal q) = q := by
      unfold slotAt
      rw [hT.proposal_eq, show 4 * (q : Time) * T.delta = (q : Time) * (4 * T.delta) by ring,
        Int.mul_ediv_cancel _ (by linarith)]
      simp
    have hjoin := joinedTick j y (T.proposal q) hy hq hqHor
      (hslotq ▸ readyCut (T.proposal q) (hgst.trans (by linarith)))
    obtain ⟨x, C, ⟨hx, hC⟩, hh, hj, hJ, hReceipt⟩ :=
      (hServices i ev m hi hgst hm hfront hreceiptHor).top ht
    let k := V2.D.Run.idxBefore rho (ev.time + T.delta)
    have hkD : k ≤ timeIdx rho Dl := hcut.trans hjD
    have hCk : C ∈ (R.core (rho.stateBefore E k x)).fg.TF := keep _ _ hiCut x hC
    have hFcut : FGBlock.Preceq (R.core (rho.stateBefore E k y)).fg.F C := by
      obtain ⟨Kc, hKc, hKcF⟩ := (inv k y).Fcar
      have hf := (healing_phase_finality_le (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef)
        (cert := cert) (inv := inv) hKc hKcF).trans_lt
        (healing_phase_justified_lt (R := R) (E := E) (rho := rho) (O := O) (Ef := Ef)
          (cert := cert) (inv := inv) k y)
      have hloc := (healing_phase_local_le_frontier (R := R) (E := E) (rho := rho) hy
        (i := k)).trans_eq (hwin k hiCut hkD).1
      exact crossing k k y x Kc C hy le_rfl hKc hKcF ⟨hx, hCk⟩
        (hf.trans_le (hloc.trans hh.symm.le))
    have hservice := hReceipt.atRead j y (T.proposal q) hy hq hjoin (by linarith) (by
      rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs]
      exact erasePreceq hFcut)
    have hCcut := receiptHeld C (ev.time + T.delta) y hy hservice
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hCcut
    have hCj : C ∈ (R.core (rho.stateBefore E j y)).fg.TF := keep _ _ hcut y hCcut
    have hcapj : frontierAtIdx R E rho j ≤ m := (hwin j (hiCut.trans hcut) hjD).1.le
    obtain ⟨hHj, htopj, hJj⟩ := phase_top_carrier R E rho O Ef cert inv justif crossing hy hCj
      hh hj hcapj
    obtain ⟨_, hc, hr⟩ := hp.2.2.2 j y (p0d5c_top_idx_le hs hq huq) hjD hy
    rw [obs.controls_eq] at hc hr
    have hJC : FGBlock.Preceq (R.core (rho.stateBefore E j y)).fg.J C := by
      by_contra hn
      change (decide ((R.core (rho.stateBefore E j y)).fg.h_max =
        (R.core (rho.stateBefore E j y)).fg.h_j + 1) &&
        decide (∃ W ∈ (R.core (rho.stateBefore E j y)).fg.TF,
          FGBlock.Preceq (R.core (rho.stateBefore E j y)).fg.F W ∧
          (O.height W).h = (R.core (rho.stateBefore E j y)).fg.h_max ∧
          ¬ FGBlock.Preceq (R.core (rho.stateBefore E j y)).fg.J W)) = false at hc
      have hroot := (healing_phase_frontier_root (R := R) (E := E) (rho := rho) (O := O)
        (Ef := Ef) (obs := obs) (cert := cert) (inv := inv) crossing hy hCj (by
          rw [obs.controls_eq]; exact hh.trans hHj.symm)).1
      rcases Bool.and_eq_false_iff.mp hc with h | h
      · exact of_decide_eq_false h (hHj.trans htopj.symm)
      · exact of_decide_eq_false h ⟨C, hCj, hroot, hh.trans hHj.symm, hn⟩
    have hJJ : J = (R.core (rho.stateBefore E (i + 1) x)).fg.J :=
      hr.2.symm.trans ((hJj hJC).trans hJ)
    have hj0 : (R.core (rho.stateBefore E (i + 1) x)).fg.h_j ≠ 0 := by
      have hm2 := cert.height.one_le_h Qfg
      have hlocalTop := (phase_top_carrier R E rho O Ef cert inv justif crossing hx hC hh hj
        hfront.le).2.1
      simp only [Height] at *
      omega
    have hage := frontierSearch_initial_J_age_core R S O T E rho Ef cert hT hs justifiedSource
      sourceSlot ancestorSlot hi hx hj0
    have heJ := p0d5c_top_low_entry hs parentFrame hp hQ
      he huq (hqg.trans hgate) hlow
    rw [heJ, hJJ]
    exact hage
  have hage := p0d5c_top_seed_age hT crossing schedule mono joinedTick
    readyCut hServices receiptHeld justifiedSource sourceSlot ancestorSlot parentFrame hstart
    hquiet hp
  obtain ⟨t, hut, htD, hs⟩ := p0d5c_top_phase_holder (R := R) (S := S) (O := O) (T := T)
    (E := E) (rho := rho) (I := I) (D := D) (Ef := Ef) (decodeProposal := decodeProposal)
    (bodyErase := bodyErase) (bodyRows := bodyRows) (blockWireRows := blockWireRows)
    (parentFG := parentFG) (parentHeight := parentHeight) (validFor := validFor)
    (fold := fold) (Jst := Jst) (leaseSlots := leaseSlots) (obs := obs) (cert := cert)
    (inv := inv) hT hk schedule faultWeight deltaF hdelta gap hJst hG slotProposal read order
    signer sourceParent hδ hbound rowsReceipt progressCoverage hfold honestQuorum
    entryAgreement sourceSlot ancestorSlot coreLaws.erase_inj eraseReflect floor gateCopy
    service common hready hp allowance hrepair hleft hright hage
  exact Or.inr (Or.inr ⟨t, by linarith, htD, hs⟩)

end AvailableChain.FGCompose
end

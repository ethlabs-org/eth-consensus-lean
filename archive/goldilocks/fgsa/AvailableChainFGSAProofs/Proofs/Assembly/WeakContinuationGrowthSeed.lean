module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Export -- shake: keep (retained seed interface)
public import AvailableChainFGSAProofs.Proofs.Foundations.Export -- shake: keep (source discipline producers)

public import AvailableChainFGSAProofs.Proofs.Finality.Export -- shake: keep (source join scope)
public import AvailableChainFGSAProofs.Proofs.Shared.Claims -- shake: keep (H-time source interface)

public section

namespace AvailableChain.FGSA.Run

open SimplexFG KitFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Rebuild the finite seed's certificate origins in the continuation.
The selected signer is honest in rho. No source signer is transferred. -/
theorem wcg_certifiedOrigin (hb : Base₂ p c E rho)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (i : Nat) (x : V) (hx : x ∈ rho.honest)
    (W : FGBlock (Fin p.n)) (hW : W ∈ (storeAt p c E rho i x).fg.TF)
    (X : FGBlock (Fin p.n)) (hX : X ∈ certified p W) (hne : X ≠ .genesis) :
    WCTargetOrigin p c E rho i X (heightView p X).h := by
  have strat := sourceDiscipline_strat p c E rho
    (pt := ()) ⟨hb, hq⟩ (fgsa_rStore p c E rho)
  obtain ⟨y, r, wire, ⟨j, hj, hrow⟩, hname⟩ := strat i x W hx hW X hX hne
  obtain ⟨K, B, hK, hpair, hentry, hB, hKB, _⟩ :=
    sourceDiscipline_emittedName p c E rho hb.valid.toScheduleWellFormed hrow hname
  have hXK : X = (derive p.E p.cfg K).T_h :=
    rootScope_eq hb.idealization
      (rootScope_ancestor (rootScope_store hx hW) (certified_preceq hX))
      (rootScope_ancestor (rootScope_source hrow.1 hK) hentry)
      (congrArg Prod.snd hpair)
  exact ⟨j, y, r, wire, K, B, hj, hrow, hname, hK, hXK ▸ hentry, hB, hKB⟩

/-- A nonempty growth suffix supplies the one-quorum cap needed to rebuild
certificate origins at its own cut, including certificates from the prefix. -/
theorem wcg_seedCertified {E₀ : Generic.Env V}
    {source : V2.D.Run V (fgsa p c)} {ΔF : Time}
    (h : CleanGrowthContinuationSleep₂ p c E₀ source E rho ΔF)
    (hne : source.horizon < rho.horizon) (u : Slot)
    (x : V) (hx : x ∈ rho.honest)
    (W : FGBlock (Fin p.n))
    (hW : W ∈ (storeAt p c E rho (afterTicksIdx rho (SA.gateTime p.toParams u)) x).fg.TF)
    (X : FGBlock (Fin p.n)) (hX : X ∈ certified p W) (hXne : X ≠ .genesis) :
    WCTargetOrigin p c E rho (afterTicksIdx rho (SA.gateTime p.toParams u))
      X (heightView p X).h :=
  wcg_certifiedOrigin h.base (wcg_suffix_faultQ h hne) _ x hx W hW X hX hXne

/-- A covered strict suffix forces a nonempty retained honest set. -/
theorem wcg_retained_nonempty {E₀ : Generic.Env V}
    {source : V2.D.Run V (fgsa p c)} {ΔF : Time}
    (h : CleanGrowthContinuationSleep₂ p c E₀ source E rho ΔF)
    (hne : source.horizon < rho.horizon) : rho.honest.Nonempty := by
  classical
  have hp := h.joinedParticipation rho.horizon hne le_rfl
  have hcard : (joinedHonest p E rho rho.horizon).card ≤ rho.honest.card := by
    exact Finset.card_filter_le _ _
  exact Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) (hp.trans_le hcard))

omit [Fintype V] in
/-- The healing carrier enters continuation scope through a retained store.
Its original source signer need not remain honest. -/
theorem wcg_seedCarrier {E₀ : Generic.Env V}
    {source : V2.D.Run V (fgsa p c)} {w : HealingWitness} {iSource : Nat}
    (ha : RetainedAgreesThrough₂ p c E₀ source E rho)
    (hsource : V2.D.ScheduleWellFormed E₀ source)
    (hrho : V2.D.ScheduleWellFormed E rho)
    (hs : WCSeed p c E₀ source w iSource)
    (hend : SA.gateTime p.toParams w.u ≤ source.horizon)
    (hne : rho.honest.Nonempty) :
    let i := afterTicksIdx rho (SA.gateTime p.toParams w.u)
    ∃ WStar : FGBlock (Fin p.n), eraseFG WStar = w.CStar ∧
      (heightView p WStar).h = w.M + 1 ∧
      RootBlockInRun p c E rho (eraseFG WStar) ∧
      ∀ x ∈ rho.honest, WStar ∈ (storeAt p c E rho i x).fg.TF := by
  intro i
  obtain ⟨W, hW, hh, _, hstored⟩ := hs.carrier
  have hretained : ∀ x ∈ rho.honest, W ∈ (storeAt p c E rho i x).fg.TF := by
    intro x hx
    rw [wcg_cut_storeReplay ha hsource hrho x hx hend, ← hs.cut]
    exact hstored x (ha.honest hx)
  obtain ⟨x, hx⟩ := hne
  exact ⟨W, hW, hh, rootScope_store hx (hretained x hx), hretained⟩

/-- The source join cutoff supplies every time from the first covered vote.
The strict suffix uses its joined count; the source endpoint stays in the prefix. -/
theorem wcg_participation {E₀ : Generic.Env V}
    {source : V2.D.Run V (fgsa p c)} {G ΔF : Time} {w : HealingWitness}
    (hsource : StrongRecoverySearchPrefix₂ p c E₀ source G ΔF)
    (h : CleanGrowthContinuationSleep₂ p c E₀ source E rho ΔF)
    (hne : source.horizon < rho.horizon)
    (hjoin : E₀.t_GST ≤ slotStartZ p (w.u : Int))
    (t : Time) (hfirst : SA.voteTime p.toParams (w.u + 1) ≤ t)
    (ht : t ≤ rho.horizon) :
    (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card := by
  classical
  by_cases hp : source.horizon < t
  · exact h.joinedParticipation t hp ht
  have hprefix : t ≤ source.horizon := le_of_not_gt hp
  have hd := p.deltaPos
  have hden : 0 < 4 * p.Δ := by linarith
  have hnonneg : 0 ≤ t := by
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ t at hfirst
    nlinarith [Nat.cast_nonneg (α := Int) (w.u + 1)]
  have hslot : (w.u : Int) + 1 ≤ (slotAt p t : Int) := by
    change (w.u : Int) + 1 ≤ ((t / (4 * p.Δ)).toNat : Int)
    rw [Int.toNat_of_nonneg (Int.ediv_nonneg hnonneg hden.le)]
    have he := Int.mul_ediv_add_emod t (4 * p.Δ)
    have hr := Int.emod_lt_of_pos t hden
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ t at hfirst
    push_cast at hfirst
    nlinarith
  have hcut : E₀.t_GST ≤ slotStartZ p ((slotAt p t : Int) - 1) := by
    apply hjoin.trans
    change 4 * p.Δ * (w.u : Int) ≤ 4 * p.Δ * ((slotAt p t : Int) - 1)
    nlinarith
  have hgst : E₀.t_GST ≤ t := by
    apply hjoin.trans
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ t at hfirst
    change 4 * p.Δ * (w.u : Int) ≤ t
    push_cast at hfirst
    nlinarith
  have hall : joinedHonest p E rho t = rho.honest := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    have hj := finality_recovery_joined p c E₀ source hsource.toRecovery₂
      (h.agrees.honest hx) hcut hgst hprefix
    refine ⟨(h.agrees.awake x hx t hprefix).trans hj.1, ?_, ?_⟩
    · intro u hu hut hw
      apply hj.2.1 u hu hut
      change E₀.awake x u = true ∧ E₀.awake x (u - 1) = false
      change E.awake x u = true ∧ E.awake x (u - 1) = false at hw
      rw [← h.agrees.awake x hx u (hut.trans hprefix),
        ← h.agrees.awake x hx (u - 1)
          ((sub_le_self _ (by decide)).trans (hut.trans hprefix))]
      exact hw
    · intro u hu hut he
      exact hj.2.2 u hu hut
        ((wcg_eventReplay h.agrees (.restart x u) hx (hut.trans hprefix)).mp he)
  rw [hall]
  exact (h.joinedParticipation rho.horizon hne le_rfl).trans_le (Finset.card_filter_le _ _)

omit [Fintype V] in
/-- H0 keeps GST before the join window of the seed's first covered vote. -/
theorem wcg_sourceJoinCut {w : HealingWitness} (h : H0 p c E rho w) :
    E.t_GST ≤ slotStartZ p (w.u : Int) := by
  have hs := h.synchronous
  have hu : (w.sStar : Int) + 2 ≤ w.u := by exact_mod_cast h.proposal_lower
  change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hs
  change E.t_GST ≤ 4 * p.Δ * (w.u : Int)
  nlinarith [p.deltaPos]


/-- All finite seed fields come from continuation producers at its own index. -/
theorem wcg_finiteSeed (hb : Base₂ p c E rho)
    (hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (i : Nat) :
    WCFiniteFacts p c E rho i := by
  have hsch := hb.valid.toScheduleWellFormed
  exact wcg_finiteFacts hb.valid hb.receiptIdealization
    (sourceDiscipline_strat p c E rho (pt := ()) ⟨hb, hq⟩ (fgsa_rStore p c E rho))
    (fun x hx => fgsa_clientSafeAll p c E rho hb.linked x hx)
    (fun _ _ _ _ _ ha he => sourceDiscipline_emittedName p c E rho hsch ha he)
    (fun i x row hr => by
      obtain ⟨j, hj, r, B, hG, hpass, hB, hp, hkeys, hd, he, hlast⟩ :=
        fgsa_leaseOrigins_lastWrite p c E rho hsch i x row hr
      refine ⟨j, hj, r, B, hG, hpass, hB, hp, hkeys, hd, he, ?_⟩
      intro k w C hjk hki hEnabled
      exact hlast k w C hjk hki hEnabled.1
        (by rw [clockPre_joined]; exact fgsa_gate_joined_of_enabled E rho hEnabled))
    (fgsa_leaseOrigins_fastWrites_epoch p c E rho hsch)
    (fgsa_leaseOrigins_ancestorDeadlines p c E rho) i

private def seed_headAtIdx (p : Params) {In : Type} (c : AppCodec In)
    {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (k : Nat) (s : Slot) : Block :=
  match rho.events[k]? with
  | some (.tick y t) =>
      headVote p ((fgsa p c).clock (V2.D.Run.stateBefore E rho k y) t).st s
  | _ => .genesis
private theorem seed_headAtIdx_eq : @headAtIdx = @seed_headAtIdx := rfl

/-- WC J1; DC height seed: construct HS from the selected HealingInput and source regime.
The output cut alone is not used as a replacement for the source witness. -/
theorem wcg_heightSeed_of_finite {G ΔF : Time} {w : HealingWitness}
    (hS : StrongRecoverySearchPrefix₂ p c E rho G ΔF)
    (hinput : HealingInput p c E rho w ΔF) (hend : tstar p w < rho.horizon)
    (hfinite : ∀ i, WCFiniteFacts p c E rho i) :
    let i := afterTicksIdx rho (tstar p w)
    BoundedHealingCut₂ p c E rho w.u w.QStar i ΔF ∧ WCSeed p c E rho w i := by
  let i := afterTicksIdx rho (tstar p w)
  have hs := hS.base.valid.toScheduleWellFormed
  have hservice := hinput.ac.h3 w.u w.QStar hinput.wit.proposal hinput.wit.proposal_lower
  have hgate : SA.gateTime p.toParams w.u ≤ rho.horizon := le_of_lt hend
  have hGateReader (x : V) (hx : x ∈ rho.honest) :=
    fgsa_recovery_gate_readers hS.toRecoverySleep₂ hinput.wit hgate x hx
  have hcut : E.t_GST ≤ slotStartZ p ((w.u : Int) - 1) := by
    have ht := hinput.wit.synchronous
    have hu : (w.sStar : Int) + 2 ≤ w.u := by exact_mod_cast hinput.wit.proposal_lower
    change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at ht
    change E.t_GST ≤ 4 * p.Δ * ((w.u : Int) - 1)
    nlinarith [p.deltaPos]
  have hheadReader (x : V) (hx : x ∈ rho.honest) :
      headReader p E rho x w.u (SA.voteTime p.toParams w.u) := by
    refine ⟨hx, finality_recovery_joined p c E rho hS.toRecovery₂ hx hcut ?_ ?_⟩
    · apply hcut.trans
      change 4 * p.Δ * ((w.u : Int) - 1) ≤ 4 * p.Δ * (w.u : Int) + p.Δ
      linarith [p.deltaPos]
    · apply le_trans ?_ hgate
      change 4 * p.Δ * (w.u : Int) + p.Δ ≤ 4 * p.Δ * (w.u : Int) + 6 * p.Δ
      linarith [p.deltaPos]
  have href : ∀ x ∈ rho.honest, S_at p c E rho i x = w.QStar := by
    intro x hx
    have h := hinput.ac.h4.1 x hx
    rw [afterTicks_eq_stateBefore E rho hs] at h
    exact h
  have hnext : SA.voteTime p.toParams (w.u + 1) ≤ SA.gateTime p.toParams w.u := by
    change 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ ≤ 4 * p.Δ * (w.u : Int) + 6 * p.Δ
    push_cast
    have hd := p.deltaPos
    nlinarith
  have hfirst : E.t_GST ≤ SA.voteTime p.toParams (w.u + 1) := by
    have hstart := hinput.wit.synchronous
    have hslot : w.sStar + 2 ≤ w.u := hinput.wit.proposal_lower
    have hslot' : (w.sStar : Int) ≤ (w.u : Int) + 1 := by
      exact_mod_cast (Nat.le_trans (Nat.le_add_right w.sStar 2)
        (hslot.trans (Nat.le_succ w.u)))
    change E.t_GST ≤ 4 * p.Δ * (w.sStar : Int) + p.Δ at hstart
    change E.t_GST ≤ 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ
    push_cast
    have hd := p.deltaPos
    nlinarith
  obtain ⟨j₀, y₀, a₀, WStar, hrow₀, _, hsrc₀, herase, hheight⟩ := hinput.wit.fresh
  have hstored : ∀ x ∈ rho.honest, WStar ∈ (storeAt p c E rho i x).fg.TF := by
    intro x hx
    have hc := cstoreInv_stateBefore E rho i x
    have hQ : w.QStar ∈ (storeAt p c E rho i x).base.blocks := by
      rw [← href x hx]
      exact hc.Smem
    obtain ⟨Qfg, hQfg, heQ⟩ := hc.baseTree w.QStar |>.mp hQ
    apply KitFG.ancestor_closed_of_parent_closed _ hc.fg.closed Qfg hQfg
    apply eraseFG_preceq_iff.mp
    rw [herase, heQ]
    exact hinput.wit.source_prefix
  have hscope := rootScope_source hrow₀.1 hsrc₀
  refine ⟨⟨hinput.wit.after_gst, hend, rfl, hinput.wit.proposal, href⟩,
    ⟨rfl, List.length_filter_le _ _, hinput.wit.after_gst, hfirst,
      ⟨WStar, herase, hheight, hscope, hstored⟩, hinput.wit.source_prefix,
      ?_, href, ?_, ?_, ?_, ?_, ?_, hfinite i⟩⟩
  · intro x hx
    obtain ⟨hraw, ⟨j, hj, hpass⟩, _⟩ := hservice.2 hgate x hx (hGateReader x hx)
    refine ⟨j, wcg_tick_before_cut hs hj.1 le_rfl, hj.1, ?_, hpass⟩
    rw [gateResultAt_eq_gateResult p c E rho hs hj.1]
    exact hraw
  · intro x hx
    have heq : ((4 * (w.u + 1) + 1 : Nat) : Time) * p.Δ =
        SA.voteTime p.toParams (w.u + 1) := by
      change _ = 4 * p.Δ * ((w.u + 1 : Nat) : Int) + p.Δ
      push_cast
      ring
    obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hs hS.base.delta x hx
      (4 * (w.u + 1) + 1) (heq ▸ hnext.trans hgate)
      (heq ▸ hS.awake x hx _ hfirst (hnext.trans hgate))
    rw [heq] at hk
    let st := FGSA.clock p (storeAt p c E rho k x) (SA.voteTime p.toParams (w.u + 1))
    have hread : headAtLabel p c E rho x (w.u + 1) = some (headVote p st (w.u + 1)) := by
      change (postClock E rho x (SA.voteTime p.toParams (w.u + 1))).map
        (fun nd => headVote p nd.st (w.u + 1)) = _
      rw [postClock_def, preTick_def, fgsa_tickIdx_of_event p c E rho hs hk]
      rfl
    have hraw := (hservice.2 hgate x hx (hGateReader x hx)).1
    have hsu : w.sStar ≤ w.u := le_trans (Nat.le_add_right _ _) hinput.wit.proposal_lower
    have hle := (hinput.ac.h5 x w.u w.QStar hx hsu hraw).2.1
      x (w.u + 1) (headVote p st (w.u + 1))
        ⟨hx, finality_recovery_joined p c E rho hS.toRecovery₂ hx
          (by simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using
            wcg_sourceJoinCut hinput.wit) hfirst (hnext.trans hgate)⟩ le_rfl hread
    have hinv := cstoreInv_clock p _ (cstoreInv_stateBefore E rho k x)
      (SA.voteTime p.toParams (w.u + 1))
    refine ⟨k, wcg_tick_before_cut hs hk hnext, ⟨hk, ?_, ?_, ?_⟩⟩
    · rw [seed_headAtIdx_eq]
      unfold seed_headAtIdx
      rw [hk]
      exact hle
    · intro A hA
      obtain ⟨H, hH, hHread⟩ := hinv.baseTree _ |>.mp (headVote_stored p st hinv (w.u + 1))
      obtain ⟨Afg, hAfg, heA⟩ := eraseFG_ancestor_mem hinv.fg.closed hH
        (hHread ▸ Gen.Pure.block_preceq_trans hA hle)
      exact hinv.baseTree A |>.mpr ⟨Afg, hAfg, heA⟩
    · have hr := (hfinite k).receipts x hx
      constructor
      · simpa only [(clock_cumulative p _ _).2.2.1] using hr.blocks
      · simpa only [(clock_cumulative p _ _).2.2.2.1] using hr.votes
  · intro j x r a e hj ha he hhigh
    obtain ⟨K, B, hK, hpair, hentry, hB, hKB, _⟩ :=
      sourceDiscipline_emittedName p c E rho hs ha he
    refine ⟨K, B, hK, hpair, hentry, hB, hKB, ?_⟩
    have ht := wcg_time_before_cut hs ha.2.1 hj
    have hlabel : r * p.R ≤ w.u := by
      change 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ ≤
        4 * p.Δ * (w.u : Int) + 6 * p.Δ at ht
      have hd := p.deltaPos
      have hcast : ((r * p.R : Nat) : Int) ≤ (w.u : Int) := by nlinarith
      exact_mod_cast hcast
    rcases hlabel.lt_or_eq with hlt | heq
    · have hh : high p w K := by
        rw [high_def, heightView_eq_simplex]
        change w.M + 1 ≤ hOf p.E p.cfg K
        simpa only [hpair] using hhigh
      have hhead := hservice.1 (by
        change 4 * p.Δ * (w.u : Int) + p.Δ ≤ rho.horizon
        change 4 * p.Δ * (w.u : Int) + 6 * p.Δ ≤ rho.horizon at hgate
        have hd := p.deltaPos
        nlinarith) x ha.1 (hheadReader x ha.1).2
      exact (hinput.ac.h2A x r K ha.1 hK hh).1 x w.u w.QStar (hheadReader x ha.1)
        (Nat.succ_le_of_lt hlt) hhead
    · rw [heq] at hB
      have heB := Option.some.inj (Option.some.inj
        (hB.symm.trans (hservice.2 hgate x ha.1 (hGateReader x ha.1)).1))
      exact heB ▸ hKB
  · intro x hx
    have hc := (cstoreInv_stateBefore E rho i x).fg
    change w.M + 1 ≤ (rho.stateBefore E i x).st.fg.h_max
    rw [hc.hmax]
    rw [← hheight]
    have hw : WStar ∈ (rho.stateBefore E i x).st.fg.TF := hstored x hx
    exact le_sup_of_le_left (Finset.le_sup (f := fun B => (heightView p B).h) hw)
  · intro x hx
    have hn := nestOK_stateBefore E rho i x
    change Block.Preceq (F_at p c E rho i x) (S_at p c E rho i x) at hn
    rwa [href x hx] at hn
  · intro x hx row hr _
    have ht := storedTargetsBelowOutput_target p _ (fgsa_storedTargetsBelowOutput p c E rho i x)
      row hr
    change Block.Preceq row.1 (S_at p c E rho i x) at ht
    rwa [href x hx] at ht

/-- The source seed consumes the family's finite-facts producer. -/
theorem wcg_heightSeed {G ΔF : Time} {w : HealingWitness}
    (hS : StrongRecoverySearchPrefix₂ p c E rho G ΔF)
    (hinput : HealingInput p c E rho w ΔF) (hend : tstar p w < rho.horizon) :
    let i := afterTicksIdx rho (tstar p w)
    BoundedHealingCut₂ p c E rho w.u w.QStar i ΔF ∧ WCSeed p c E rho w i :=
  wcg_heightSeed_of_finite hS hinput hend
    (wcg_finiteSeed hS.base (fgsa_faultQ_of_count p hS.fault))

/-- Keep the selected source join cutoff with the seed before any continuation. -/
theorem wcg_sourceWitness_joined (hH : HTimeClaim p) {G ΔF : Time}
    (hδ : p.δt = 2 * p.R)
    (hS : StrongRecoverySearchPrefix₂ p c E rho G ΔF)
    (hfinite : ∀ i, WCFiniteFacts p c E rho i) :
    ∃ w : HealingWitness,
      BoundedHealingCut₂ p c E rho w.u w.QStar
        (afterTicksIdx rho (SA.gateTime p.toParams w.u)) ΔF ∧
      WCSeed p c E rho w (afterTicksIdx rho (SA.gateTime p.toParams w.u)) ∧
      E.t_GST ≤ slotStartZ p (w.u : Int) := by
  obtain ⟨w, input, start, bound⟩ := hH G ΔF hδ c E rho ()
    ⟨⟨hS.toRecoverySleep₂, hS.liveness⟩, hS.endpoint.ge⟩
  have hend : tstar p w < rho.horizon := by
    rw [hS.endpoint]
    exact start.trans_lt bound
  have hs := wcg_heightSeed_of_finite hS input hend hfinite
  exact ⟨w, hs.1, hs.2, wcg_sourceJoinCut input.wit⟩

/-- Choose the bounded source seed before any continuation is considered. -/
theorem wcg_sourceWitness (hH : HTimeClaim p) {G ΔF : Time}
    (hδ : p.δt = 2 * p.R)
    (hS : StrongRecoverySearchPrefix₂ p c E rho G ΔF)
 :
    ∃ w : HealingWitness,
      BoundedHealingCut₂ p c E rho w.u w.QStar
        (afterTicksIdx rho (SA.gateTime p.toParams w.u)) ΔF ∧
      WCSeed p c E rho w (afterTicksIdx rho (SA.gateTime p.toParams w.u)) := by
  obtain ⟨w, hcut, hseed, _⟩ := wcg_sourceWitness_joined hH hδ hS
    (wcg_finiteSeed hS.base (fgsa_faultQ_of_count p hS.fault))
  exact ⟨w, hcut, hseed⟩

/-- Replay all seed fields for a continuation with a nonempty suffix. -/
theorem wcg_retainedSeed_of_finite {E₀ : Generic.Env V}
    {source : V2.D.Run V (fgsa p c)} {G ΔF : Time} {w : HealingWitness} {iSource : Nat}
    (hS : StrongRecoverySearchPrefix₂ p c E₀ source G ΔF)
    (hc : CleanGrowthContinuationSleep₂ p c E₀ source E rho ΔF)
    (hne : source.horizon < rho.horizon)
    (hs : WCSeed p c E₀ source w iSource)
    (hend : SA.gateTime p.toParams w.u ≤ source.horizon)
    (hfinite : ∀ i, WCFiniteFacts p c E rho i) :
    WCSeed p c E rho w (afterTicksIdx rho (SA.gateTime p.toParams w.u)) := by
  have hss := hS.base.valid.toScheduleWellFormed
  have hrs := hc.base.valid.toScheduleWellFormed
  have states := wcg_seed_state hc.agrees hss hrs hs hend
  have hg : E.t_GST = E₀.t_GST := hc.agrees.gst
  refine ⟨rfl, List.length_filter_le _ _, hg ▸ hs.afterGST,
    hg ▸ hs.firstVoteAfterGST,
    wcg_seedCarrier hc.agrees hss hrs hs hend (wcg_retained_nonempty hc hne),
    hs.sourcePrefix, ?_, (fun x hx => (states x hx).1), ?_, ?_,
    (fun x hx => (states x hx).2.1), (fun x hx => (states x hx).2.2.1),
    (fun x hx => (states x hx).2.2.2), hfinite _⟩
  · intro x hx
    obtain ⟨j, _, hj, hv, hp⟩ := hs.gates x (hc.agrees.honest hx)
    obtain ⟨k, hk, he⟩ := wcg_tickEventReplay hc.agrees hss hrs
      hx hend hj
    exact ⟨k, wcg_tick_before_cut hrs hk le_rfl, hk,
      (wcg_tickReads hj hk he).1.trans hv, wcg_tickPassed hj hk he hp⟩
  · intro x hx
    obtain ⟨j, hjcut, hhead⟩ := hs.nextHeads x (hc.agrees.honest hx)
    have ht := wcg_time_before_cut hss hhead.event (hs.cut ▸ hjcut)
    obtain ⟨k, hk, he⟩ := wcg_tickEventReplay hc.agrees hss hrs
      hx (ht.trans hend) hhead.event
    have hstore : storeAt p c E rho k x = storeAt p c E₀ source j x :=
      congrArg (fun st => st.st) he
    refine ⟨k, wcg_tick_before_cut hrs hk ht, hk, ?_, ?_, ?_⟩
    · rw [(wcg_tickReads hhead.event hk he).2]
      exact hhead.covers
    · rw [hstore]
      exact hhead.path
    · have hr := (hfinite k).receipts x hx
      constructor
      · simpa only [(clock_cumulative p _ _).2.2.1] using hr.blocks
      · simpa only [(clock_cumulative p _ _).2.2.2.1] using hr.votes
  · intro k x r a e hk hrow hentry hhigh
    have ht := wcg_time_before_cut hrs hrow.2.1 hk
    obtain ⟨j, hj⟩ := wcg_rowSourceReplay hc.agrees hss hrs
      hrow (ht.trans hend)
    have hjcut : j < iSource := hs.cut ▸ wcg_tick_before_cut hss hj.2.1 ht
    obtain ⟨K, B, hK, he, hT, hB, hKB, hQ⟩ := hs.highSources j x r a e hjcut hj hentry hhigh
    have reads := wcg_actionReads hc.agrees hss hrs
      x hrow.1 (ht.trans hend)
    exact ⟨K, B, reads.1.trans hK, he, hT, reads.2.trans hB, hKB, hQ⟩


/-- Rebuild finite facts in the continuation, then apply occurrence replay. -/
theorem wcg_retainedSeed {E₀ : Generic.Env V}
    {source : V2.D.Run V (fgsa p c)} {G ΔF : Time} {w : HealingWitness} {iSource : Nat}
    (hS : StrongRecoverySearchPrefix₂ p c E₀ source G ΔF)
    (hc : CleanGrowthContinuationSleep₂ p c E₀ source E rho ΔF)
    (hne : source.horizon < rho.horizon) (hs : WCSeed p c E₀ source w iSource)
    (hend : SA.gateTime p.toParams w.u ≤ source.horizon) :
    WCSeed p c E rho w (afterTicksIdx rho (SA.gateTime p.toParams w.u)) :=
  wcg_retainedSeed_of_finite hS hc hne hs hend
    (wcg_finiteSeed hc.base (wcg_suffix_faultQ hc hne))

end AvailableChain.FGSA.Run
end

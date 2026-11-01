module
public import AvailableChainFGSAProofs.Proofs.Outage.ReceiverInputs
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceFrame
public import AvailableChainFGSAProofs.Proofs.Outage.PersistenceStep
public import AvailableChainFGSAProofs.Proofs.Outage.ArmingDutySleep
public import AvailableChainFGSAProofs.Proofs.Outage.ExactProposalRetained

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- Only covered receivers carry the local duty invariant before restoration. -/
structure OutageCoveredDutyHistory (fast : Bool) (b₀ : Time) (B : Block)
    (j : Slot) (i : Nat) : Prop where
  history : ∀ k y t o, k < i → y ∈ coveredNodes p E rho fast b₀ →
    SA.gateTime p.toParams j ≤ t → rho.events[k]? = some (.tick y t) →
    o ∈ rho.emitsAt E k →
    (∀ H, HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H) ∧
    (∀ N, o.payload = .proposal N → Block.Preceq B N.parent.erase)

/-- The actual good HEAD before restoration is covered, or is the in-flight seed.
The index bound is at the current release or source tick. -/
theorem outage_good_head_through_restored
    {fast : Bool} {b₀ : Time} {r j : Slot}
    (hcut : b₀ < SA.gateTime p.toParams j)
    {B : Block} {i : Nat}
    (hDuty : OutageCoveredDutyHistory (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ B j i)
    (hSeed : ∀ y o t (q : Fin p.n) H, y ∈ rho.honest → V2.D.Run.emits E rho y o t →
      o.auth = .seat (.base (.head (j + 1))) q →
      HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H)
    {s : Slot} (hjs : j < s) (hsr : s ≤ r)
    {q : Fin p.n} {K : Block}
    (hGood : rho.seatOf (.base (.head s)) q ∈
      outageH p E rho s \ outageW p E rho fast b₀ r)
    (hK : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K)
    (hBefore : ∀ k, rho.events[k]? = some
      (.tick (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s)) → k < i) :
    Block.Preceq B K := by
  classical
  have hh : rho.seatOf (.base (.head s)) q ∈ rho.honest :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hGood).1).1
  have hKkeep := hK
  obtain ⟨k, _, _, hk, hem, _, _⟩ := hK
  by_cases hsj : s = j + 1
  · subst s
    exact hSeed _ _ _ q K hh ⟨k, hk, hem⟩ rfl hKkeep
  have htime : SA.gateTime p.toParams j < SA.voteTime p.toParams s := by
    rw [arming_gate_eq, arming_vote_eq]
    have hcast : (j : Int) + 2 ≤ (s : Int) := by
      dsimp only [Slot] at hjs hsj ⊢
      omega
    nlinarith [p.deltaPos]
  have hyG := outage_good_covered E rho hGood (hcut.le.trans htime.le) hsr
  exact (hDuty.history k _ _ _ (hBefore k hk) hyG htime.le hk hem).1 K hKkeep

/-- The public restored cut supplies the label bound for the local good HEAD. -/
theorem outage_good_head_before_restored
    {fast : Bool} {b₀ b₁ : Time} {r j : Slot}
    (hr : FirstRestored p b₁ r) (hcut : b₀ < SA.gateTime p.toParams j)
    {B : Block} {i : Nat}
    (hDuty : OutageCoveredDutyHistory (p := p) (c := c) (E := E) (rho := rho)
      fast b₀ B j i)
    (hSeed : ∀ y o t (q : Fin p.n) H, y ∈ rho.honest → V2.D.Run.emits E rho y o t →
      o.auth = .seat (.base (.head (j + 1))) q →
      HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H)
    {s : Slot} (hjs : j < s) (hvb : SA.voteTime p.toParams s < b₁)
    {q : Fin p.n} {K : Block}
    (hGood : rho.seatOf (.base (.head s)) q ∈
      outageH p E rho s \ outageW p E rho fast b₀ r)
    (hK : HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K)
    (hBefore : ∀ k, rho.events[k]? = some
      (.tick (rho.seatOf (.base (.head s)) q) (SA.voteTime p.toParams s)) → k < i) :
    Block.Preceq B K := by
  have hsr : s ≤ r := by
    by_contra hn
    have hv := (hr s).mpr (by dsimp only [Slot] at hn ⊢; omega)
    exact (not_lt_of_ge hv) hvb
  exact outage_good_head_through_restored hcut hDuty hSeed hjs hsr hGood hK hBefore

/-- Named source history gives current F compatibility at every honest receiver.
No local protection or receiver join is required for this frame conclusion. -/
theorem outage_source_frame_compatible
    (hf : FGFoundation p c E rho) {B : Block} {β : FGBlock (Fin p.n)} {i : Nat}
    (hβ : eraseFG β = B) (hNames : OutageNamedHistory p c E rho β i)
    {x : V} (hx : x ∈ rho.honest) : Block.Compatible (F_at p c E rho i x) B := by
  have hF := (fgsa_cpCompat_of_scopedFrame p c E rho hf.store hf.strat
    i x β hx hNames.history).2.1
  rw [← hβ]
  exact Bool.or_eq_true_iff.mpr (hF.imp eraseFG_preceq eraseFG_preceq)

/-- The full pre-restoration joint induction includes restart events. Sources and
names are global; protection and new duties are limited to covered receivers.
Release uses the fixed A union W bound. The endpoint can equal lease expiry. -/
theorem outage_event_induction_before_vote_cut [Fintype V]
    (hBase : Base₂ p c E rho) (hf : FGFoundation p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {fast : Bool} {b₀ b₁ : Time} {r j : Slot} {B : Block} {β : FGBlock (Fin p.n)}
    (hVotes : ∀ s, SA.voteTime p.toParams s < b₁ → s ≤ r) (hcut : b₀ < SA.gateTime p.toParams j)
    (hBound : (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card <
      SA.releaseThreshold p.toParams)
    (hβ : eraseFG β = B) (hend : b₁ ≤ SA.gateTime p.toParams j + L p)
    (hSource : OutageSourceHistory p c E rho B (afterTicksIdx rho (SA.gateTime p.toParams j)))
    (hLocal : ∀ y ∈ coveredNodes p E rho fast b₀, OutageProtection p B j
      (storeAt p c E rho (afterTicksIdx rho (SA.gateTime p.toParams j)) y))
    (hSeed : ∀ y o t (q : Fin p.n) H, y ∈ rho.honest → V2.D.Run.emits E rho y o t →
      o.auth = .seat (.base (.head (j + 1))) q →
      HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H)
    {i : Nat} (hI : afterTicksIdx rho (SA.gateTime p.toParams j) ≤ i)
    (hK : i ≤ rho.idxBefore b₁) :
    OutageSourceHistory p c E rho B i ∧
      OutageCoveredDutyHistory (p := p) (c := c) (E := E) (rho := rho) fast b₀ B j i ∧
      OutageNamedHistory p c E rho β i ∧
      ∀ y ∈ coveredNodes p E rho fast b₀,
        OutageProtection p B j (storeAt p c E rho i y) := by
  classical
  have hs := hBase.valid.toScheduleWellFormed
  have named := fun {i} (h : OutageSourceHistory p c E rho B i) =>
    outage_named_of_source_history hBase.idealization hβ h hnamed
  induction i, hI using Nat.le_induction with
  | base =>
    refine ⟨hSource, ⟨?_⟩, named hSource, hLocal⟩
    intro k y t o hk hyG hj ht ho
    have hy := (Finset.mem_filter.mp hyG).1
    have htd := arming_tick_le hs ht
      (hk.trans_le (preIdx_le_afterTicksIdx E rho hs _).2)
    have heq := le_antisymm htd hj
    constructor
    · intro H hH
      obtain ⟨s, _, _, _, he, _, _⟩ := arming_emit_head hBase.valid hy ⟨k, ht, ho⟩ hH
      exact (arming_gate_ne_vote p j s (heq.symm.trans he)).elim
    · intro N hN
      obtain ⟨s, _, _, he, _, _⟩ := arming_emit_proposal hBase.valid hy ⟨k, ht, ho⟩ hN
      exact (arming_gate_ne_proposal p j s (heq.symm.trans he)).elim
  | succ i hI ih =>
    have hiK : i < rho.idxBefore b₁ := by omega
    obtain ⟨hsource, hduty, hnames, hlocal⟩ := ih hiK.le
    have hil := hiK.trans_le (arming_idxBefore_le_length rho b₁)
    have he : rho.events[i]? = some rho.events[i] := List.getElem?_eq_getElem hil
    have htend := (Gen.V2.Duty.index_lt_idxBefore_iff hs he b₁).mp hiK
    have hnames' (h : OutageSourceHistory p c E rho B (i + 1)) := named h
    have unchanged {y : V} {ev : V2.Event V (Obj p)} (he : rho.events[i]? = some ev)
        (h : ∀ t, ev ≠ .tick y t) :
        ∀ k u, k < i + 1 → rho.events[k]? = some (.tick y u) → k < i := by
      intro k u hk ht
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hki | rfl
      · exact hki
      · exact (h u (Option.some.inj (he.symm.trans ht))).elim
    cases hevent : rho.events[i] with
    | restart x t =>
      rw [hevent] at he
      have hs' : OutageSourceHistory p c E rho B (i + 1) := by
        constructor
        intro k y r C hk hy ht hC
        exact hsource.history k y r C
          (unchanged he (fun _ h => by cases h) k _ hk ht) hy ht hC
      refine ⟨hs', ⟨?_⟩, hnames' hs', ?_⟩
      · intro k y u a hk hy hj ht ho
        exact hduty.history k y u a
          (unchanged he (fun _ h => by cases h) k u hk ht) hy hj ht ho
      · intro y hy
        by_cases hxy : x = y
        · subst y
          exact outage_restart_protection_at he (hlocal x hy)
        · unfold storeAt
          rw [rho.stateBefore_succ E he]
          simp only [V2.D.World.step, Function.update_of_ne (Ne.symm hxy)]
          exact hlocal y hy
    | deliver x o t =>
      rw [hevent] at he
      have hs' := outage_source_history_delivery he hsource
      refine ⟨hs', ⟨?_⟩, hnames' hs', ?_⟩
      · intro k y u a hk hy hj ht ho
        exact hduty.history k y u a
          (unchanged he (fun _ h => by cases h) k u hk ht) hy hj ht ho
      · intro y hyG
        by_cases hxy : x = y
        · subst y
          exact outage_delivery_protection he (hlocal x hyG)
            (outage_source_frame_compatible hf hβ (hnames' hs')
              (Finset.mem_filter.mp hyG).1)
        · unfold storeAt
          rw [rho.stateBefore_succ E he]
          simp only [V2.D.World.step, Function.update_of_ne (Ne.symm hxy)]
          exact hlocal y hyG
    | tick x t =>
      rw [hevent] at he
      have hdt := outage_tick_after_cut hs he hI
      have htb : t < b₁ := by simpa only [hevent, V2.Event.time] using htend
      have hx := hs.honest_only _ (List.mem_of_getElem? he)
      let st := storeAt p c E rho i x
      let P := clockPre p st t
      let Q := clock p st t
      have hpost : storeAt p c E rho (i + 1) x = Q := by
        change (rho.stateBefore E (i + 1) x).st = _
        rw [(rho.step_tick_eq E he).1]
        exact tick_st (c := c) E rho _ x t
      have good {s : Slot} (hjs : j < s) (hvs : SA.voteTime p.toParams s < t) :
          ∀ q K, rho.seatOf (.base (.head s)) q ∈
            outageH p E rho s \ outageW p E rho fast b₀ r →
          HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
            (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
          Block.Preceq B K := by
        intro q K hGood hK
        exact outage_good_head_through_restored hcut hduty hSeed hjs
          (hVotes _ (hvs.trans htb)) hGood hK (fun k hk =>
            V2.D.Engine.eventIndex_lt_of_time_lt hs hk he hvs)
      have hsource' : OutageSourceHistory p c E rho B (i + 1) := by
        constructor
        intro k y a C hk hy ht hC
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hki | hki
        · exact hsource.history k y a C hki hy ht hC
        subst k
        have hyt := V2.Event.tick.inj (Option.some.inj (ht.symm.trans he))
        have hyx : y = x := hyt.1
        subst y
        have htime := hyt.2
        have hjs : j < a * p.R := by
          apply (arming_gate_lt_iff p j (a * p.R)).mp
          rw [← fgsa_action_gate_time, htime]
          exact hdt
        have hvs : SA.voteTime p.toParams (a * p.R) < t := by
          rw [← htime, fgsa_action_gate_time, arming_vote_eq, arming_gate_eq]
          linarith [p.deltaPos]
        exact outage_source_of_good_heads hBase htsrc hBound hy rfl hC
          (fun q K hGood hK => block_compatible_of_common (block_preceq_refl K)
            (good hjs hvs q K hGood hK))
      have hClock (hyG : x ∈ coveredNodes p E rho fast b₀) :
          OutageProtection p B j Q ∧ Block.Preceq B (liveRoot p Q) := by
        have hp := hlocal x hyG
        have hfB := outage_source_frame_compatible hf hβ hnames hx
        have hcounts : ∀ s, SA.releaseTime p.toParams s = t →
            GridCO.releaseCount p.toParams.engine (actView P) s B <
              SA.releaseThreshold p.toParams := by
          intro s hsT
          have hjs : j < s := by
            rw [arming_gate_eq, ← hsT, arming_release_eq] at hdt
            have := p.deltaPos
            by_contra hn
            have hc : (s : Int) ≤ (j : Int) := by
              dsimp only [Slot] at hn ⊢
              omega
            nlinarith
          have hvs : SA.voteTime p.toParams s < t := by
            rw [← hsT, arming_vote_eq, arming_release_eq]
            linarith [p.deltaPos]
          have hb := outage_good_release_bound E rho hBase.valid hBase.cstar
            hBase.idealization fast b₀ r s B (i + 1) x (by
              intro y hy o u hem q K ha hK
              have hp : o.payload = .head K.root := by
                obtain ⟨_, _, _, _, _, ho, _⟩ := hK
                exact congrArg (fun o : Obj p => o.payload) ho
              have ho : o = ofHead p ⟨.seat (.head s) q, K.root⟩ := by
                cases o; cases ha; cases hp; rfl
              obtain ⟨k, hk, hm⟩ := hem
              have hm' := hm
              rw [ho, (rho.step_tick_eq E hk).2] at hm'
              have hfields := (fgsa_emits_head E rho _ y u s q K.root).mp hm'
              have htime : u = SA.voteTime p.toParams s := hfields.2.1.symm
              have hyseat := hfields.2.2.1
              subst y
              subst u
              rw [ho] at hK
              exact block_compatible_of_common (block_preceq_refl K)
                (good hjs hvs q K hy hK))
          rw [hpost] at hb
          change GridCO.releaseCount p.toParams.engine (actView (clock p st t)) s B ≤ _ at hb
          rw [inclusion_clock_offGate p st t
            (fun s h => outage_gate_ne_release p s _ (h.trans hsT.symm))] at hb
          exact hb.trans_lt hBound
        have hpP : OutageProtection p B j P := by
          refine ⟨?_, ?_⟩
          · rw [clockPre_stable]; exact hp.1
          · rw [clockPre_fg]
            exact hp.2.imp id (fun ⟨dl, hm, hd⟩ => ⟨dl,
              outage_clockPre_row p st t hm (htb.trans_le (hend.trans hd)) hcounts, hd⟩)
        have hpQ : OutageProtection p B j Q := by
          by_cases hg : ∃ s, SA.gateTime p.toParams s = t
          · obtain ⟨s, hsT⟩ := hg
            dsimp only [Q]
            rw [← hsT, arming_clock_gate]
            apply outage_gateStep_protection p _
              (cstoreInv_clockPre p st (cstoreInv_stateBefore E rho i x) _)
            · exact hsT ▸ hpP
            · rw [clockPre_fg]; exact hfB
            · exact (arming_gate_le_iff p j s).mp (hdt.le.trans_eq hsT.symm)
          · dsimp only [Q]
            rw [inclusion_clock_offGate p st t (fun s h => hg ⟨s, h⟩)]
            exact hpP
        have hroot : Block.Preceq B (liveRoot p Q) := by
          have hret := (outage_frame_retains hf.store hf.frame.1 hsrc hx hβ hnames
            hp.1 hf.strat).2
          apply outage_liveRoot_covers p Q
            (cstoreInv_clock p st (cstoreInv_stateBefore E rho i x) t) hpQ.1
            (hpost ▸ leaseBelowOutput_stateBefore E rho (i + 1) x)
          have hfg : Q.fg = st.fg := clock_fg p st t
          rcases hret with hF | hdom
          · left; rwa [hfg]
          · rcases hpQ.2 with hF | ⟨dl, hm, hd⟩
            · exact Or.inl hF
            · right
              refine ⟨dl, arming_leaseOf p Q
                (cstoreInv_clock p st (cstoreInv_stateBefore E rho i x) t) hm, ?_, ?_⟩
              · change (clock p st t).base.now < dl
                rw [(clock_vn st t).2]
                exact htb.trans_le (hend.trans hd)
              · change (∃ X ∈ fullTree p st, eraseFG X = B) ∨
                  Block.Preceq B (eraseFG (controls p st).Z) at hdom
                change (∃ X ∈ KitFG.treeStoreFrameView (heightView p) Q.fg Q.fg.TF,
                  eraseFG X = B) ∨
                  Block.Preceq B (eraseFG (KitFG.treeStoreControlsView (heightView p) Q.fg).Z)
                rw [hfg]
                exact hdom
        exact ⟨hpQ, hroot⟩
      refine ⟨hsource', ⟨?_⟩, hnames' hsource', ?_⟩
      · intro k y u a hk hyG hdu ht ho
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hki | hki
        · exact hduty.history k y u a hki hyG hdu ht ho
        subst k
        have hyt := V2.Event.tick.inj (Option.some.inj (ht.symm.trans he))
        have hyx : y = x := hyt.1
        have hut : u = t := hyt.2
        subst y; subst u
        have hroot := (hClock hyG).2
        constructor
        · intro H hH
          obtain ⟨s, _, k, _, ht, hk, hh⟩ := arming_emit_head hBase.valid hx ⟨i, he, ho⟩ hH
          obtain rfl := fgsa_tick_unique E rho hs hk he
          have hs0 : s ≠ 0 := by
            intro hz
            subst s
            rw [arming_vote_eq] at ht
            rw [arming_gate_eq] at hdt
            have hj0 : 0 ≤ 4 * p.Δ * (j : Int) := by
              have := p.deltaPos
              positivity
            norm_num at ht
            linarith [p.deltaPos]
          rw [hh]
          exact outage_head_of_root p Q hroot hs0
        · intro N hN
          obtain ⟨s, k, _, _, hk, hp⟩ := arming_emit_proposal hBase.valid hx ⟨i, he, ho⟩ hN
          obtain rfl := fgsa_tick_unique E rho hs hk he
          rw [hp]
          exact block_preceq_trans hroot (liveRoot_preceq_headInTree p Q _ _ _)
      · intro y hyG
        by_cases hxy : x = y
        · subst y
          rw [hpost]
          exact (hClock hyG).1
        · unfold storeAt
          rw [rho.stateBefore_succ E he]
          simp only [V2.D.World.step, Function.update_of_ne (Ne.symm hxy)]
          exact hlocal y hyG

/-- The scoped outage induction is the vote-cut induction at the public restore cut. -/
theorem outage_event_induction_scoped [Fintype V]
    (hBase : Base₂ p c E rho) (hf : FGFoundation p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    {fast : Bool} {b₀ b₁ : Time} {r j : Slot} {B : Block} {β : FGBlock (Fin p.n)}
    (hr : FirstRestored p b₁ r) (hcut : b₀ < SA.gateTime p.toParams j)
    (hBound : (Gen.V2.Duty.faulty rho ∪ outageW p E rho fast b₀ r).card <
      SA.releaseThreshold p.toParams)
    (hβ : eraseFG β = B) (hend : b₁ ≤ SA.gateTime p.toParams j + L p)
    (hSource : OutageSourceHistory p c E rho B (afterTicksIdx rho (SA.gateTime p.toParams j)))
    (hLocal : ∀ y ∈ coveredNodes p E rho fast b₀, OutageProtection p B j
      (storeAt p c E rho (afterTicksIdx rho (SA.gateTime p.toParams j)) y))
    (hSeed : ∀ y o t (q : Fin p.n) H, y ∈ rho.honest → V2.D.Run.emits E rho y o t →
      o.auth = .seat (.base (.head (j + 1))) q →
      HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H)
    {i : Nat} (hI : afterTicksIdx rho (SA.gateTime p.toParams j) ≤ i)
    (hK : i ≤ rho.idxBefore b₁) :
    OutageSourceHistory p c E rho B i ∧
      OutageCoveredDutyHistory (p := p) (c := c) (E := E) (rho := rho) fast b₀ B j i ∧
      OutageNamedHistory p c E rho β i ∧
      ∀ y ∈ coveredNodes p E rho fast b₀,
        OutageProtection p B j (storeAt p c E rho i y) := by
  exact outage_event_induction_before_vote_cut hBase hf hsrc htsrc hnamed
    (fun s hv => by
      by_contra hn
      exact (not_lt_of_ge ((hr s).mpr (by dsimp only [Slot] at hn ⊢; omega))) hv)
    hcut hBound hβ hend hSource hLocal hSeed hI hK

/-- The sleep certificate, Clean duty producers, and P-Fd source discipline supply
all seeds of the scoped induction. No local seed or HEAD invariant is assumed. -/
theorem outage_armed_induction_scoped [Fintype V] {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block} {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    (hβ : eraseFG β = B) (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon) :
    ∀ i, afterTicksIdx rho (SA.gateTime p.toParams (l + 1)) ≤ i → i ≤ rho.idxBefore b₁ →
      OutageSourceHistory p c E rho B i ∧
      OutageCoveredDutyHistory (p := p) (c := c) (E := E) (rho := rho)
        fast b₀ B (l + 1) i ∧ OutageNamedHistory p c E rho β i ∧
      ∀ y ∈ coveredNodes p E rho fast b₀,
        OutageProtection p B (l + 1) (storeAt p c E rho i y) := by
  obtain ⟨r, hr, hBound⟩ := outage_e1_release_bound h.protection
  have hend : b₁ ≤ SA.gateTime p.toParams (l + 1) + L p := by
    have hb := h.budget.trans (min_le_right p.η (L p))
    linarith [hc.cut_lt_pending]
  intro i hI hK
  exact outage_event_induction_scoped h.pre.base hf hsrc htsrc hnamed hr
    hc.cut_lt_pending hBound hβ hend (outage_arming_sources_scoped h.sleepPre htsrc hc)
    (fun y hy => (outage_arming_protection_scoped h.sleepPre hf htsrc hne hc
      hnamed hgate y hy).1)
    (arming_inflight_heads_sleep h hf hsrc hState hprov hc hne) hI hK

/-- Read the scoped invariant at the inclusive event prefix. Every honest F is
compatible; only covered receivers obtain the pending lease-or-F conclusion. -/
theorem outage_armed_read_scoped [Fintype V] {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageSleep₂ p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
    (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block} {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh)
    (hβ : eraseFG β = B) (hgate : SA.gateTime p.toParams (l + 1) ≤ rho.horizon)
    {t : Time} (hdt : SA.gateTime p.toParams (l + 1) ≤ t) (htb : t < b₁) :
    (∀ y ∈ rho.honest, Block.Compatible (F_at p c E rho (timeIdx rho t) y) B) ∧
      ∀ y ∈ coveredNodes p E rho fast b₀,
        let st := storeAt p c E rho (timeIdx rho t) y
        Block.Preceq B (S_at p c E rho (timeIdx rho t) y) ∧
        (Block.Preceq B (eraseFG st.fg.F) ∨
          ∃ dl, FGSA.leaseOf st B = some dl ∧ t < dl ∧
            SA.gateTime p.toParams (l + 1) + L p ≤ dl ∧
            ((∃ X ∈ fullTree p st, eraseFG X = B) ∨
              Block.Preceq B (eraseFG (controls p st).Z))) := by
  classical
  have hs := h.pre.base.valid.toScheduleWellFormed
  obtain ⟨_, _, hnames, hlocal⟩ := outage_armed_induction_scoped h hf hsrc htsrc hnamed hState
    hprov hne hc hβ hgate (timeIdx rho t)
    ((afterTicksIdx_mono rho hdt).trans (preIdx_le_afterTicksIdx E rho hs t).2)
    (arming_timeIdx_le_idxBefore rho htb)
  refine ⟨fun y hy => outage_source_frame_compatible hf hβ hnames hy, ?_⟩
  intro y hyG st
  have hy := (Finset.mem_filter.mp hyG).1
  have hp := hlocal y hyG
  refine ⟨hp.1, ?_⟩
  rcases hp.2 with hF | ⟨dl, hm, hd⟩
  · exact Or.inl hF
  have hret := (outage_frame_retains hf.store hf.frame.1 hsrc hy hβ hnames hp.1 hf.strat).2
  rcases hret with hF | hdom
  · exact Or.inl hF
  · exact Or.inr ⟨dl, arming_leaseOf p st (cstoreInv_stateBefore E rho _ y) hm,
      by have hb := h.budget.trans (min_le_right p.η (L p)); linarith [hc.cut_lt_pending],
      hd, hdom⟩

end AvailableChain.FGSA.Run
end

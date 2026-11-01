module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.StepOutput
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.StepRestart
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.StepTransfer

public section

/-! WC plan §6.5; DC the joint event step preserves all bounded history and state fields. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.5; DC a completed result remains completed in an extended prefix. -/
private theorem extend_result {i n j : Nat} {x : V} {s : Slot} {B : Block}
    (h : WCResult p c E rho w iStar i j x s B) (hin : i ≤ n) :
    WCResult p c E rho w iStar n j x s B :=
  { h with completed := h.completed.trans_le hin }

/-- WC plan §6.5; DC prefix origins remain valid in an extended history. -/
private theorem extend_history {i n : Nat} {B : Block}
    (h : WCBelowHistory p c E rho w iStar i B) (hin : i ≤ n) :
    WCBelowHistory p c E rho w iStar n B := by
  rcases h.origin with h | ⟨j, x, s, C, hr, hb⟩
  · exact ⟨Or.inl h⟩
  · exact ⟨Or.inr ⟨j, x, s, C, extend_result hr hin, hb⟩⟩

/-- WC plan §6.5; DC an ancestor uses the same seed or result origin. -/
private theorem prefix_history {i : Nat} {A B : Block} (hab : Block.Preceq A B)
    (h : WCBelowHistory p c E rho w iStar i B) :
    WCBelowHistory p c E rho w iStar i A := by
  rcases h.origin with h | ⟨j, x, s, C, hr, hb⟩
  · exact ⟨Or.inl (block_preceq_trans hab h)⟩
  · exact ⟨Or.inr ⟨j, x, s, C, hr, block_preceq_trans hab hb⟩⟩

omit [DecidableEq V] in
/-- WC plan §6.5; DC the schedule orders completed gate labels. -/
private theorem gate_label_le (hsch : V2.D.ScheduleWellFormed E rho)
    {i j : Nat} {x y : V} {s r : Slot} (hij : i ≤ j)
    (hi : IsGateTick p c rho i x s) (hj : IsGateTick p c rho j y r) : s ≤ r := by
  have ht : SA.gateTime p.toParams s ≤ SA.gateTime p.toParams r := by
    rcases hij.lt_or_eq with hij | rfl
    · obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
      have hk := (List.pairwise_iff_getElem.mp hsch.sorted) i j hil hjl hij
      rw [hie, hje] at hk
      exact V2.D.Engine.time_le_of_key_le _ _ hk
    · exact (V2.Event.tick.inj (Option.some.inj (hi.symm.trans hj))).2.le
  change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * (r : Int) + 6 * p.Δ at ht
  have hc : (s : Int) ≤ r := by nlinarith [p.deltaPos]
  exact Int.ofNat_le.mp hc

variable [Fintype V] {ΔF : Time}

/-- WC plan §6.5; DC join the proved handler, origin, gate and retrospective conclusions. -/
private theorem step_core : WCStepStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX hpart
    hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs i hi hilen inv e he
  have hsch := hvalid.toScheduleWellFormed
  have hnext : i + 1 ≤ rho.events.length := Nat.succ_le_of_lt hilen
  have hfinite := wc_finiteStep ΔF w iStar hvalid hlinked hcstar hnr hdelta hroots hsync
    hdeltaF hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo
    hcert hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines
    hheldRows hscopeRows hfinalHead hs i hi hilen inv e he
  have gate : ∀ x s, x ∈ rho.honest → enabledGateAt p c E rho i x s → w.u < s →
      ∃ B, gateResultAt p c E rho i = some (some B) ∧ Block.Preceq w.QStar B ∧
        gatePassedAt p c E rho i ∧
        (∀ j y r C, WCResult p c E rho w iStar i j y r C → r < s → Block.Preceq C B) ∧
        (∀ j y r C, WCResult p c E rho w iStar i j y r C → Block.Compatible C B) ∧
        ∀ y ∈ rho.honest,
          joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
          ∃ k < i, WCHeadRead p c E rho k y (s + 1) B := by
    intro x s hx ht hslabel
    obtain ⟨B, hB, hp, hQB, ho, hc, _⟩ := wc_gateResult ΔF w iStar hvalid hlinked hcstar
      hnr hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX hpart hstore hcumul hmono
      hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat hnoslash hemitted
      htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead hs i x s hi hilen
      inv ht hslabel
    exact ⟨B, hB, hQB, hp, ho, hc, wc_retrospective hvalid hlinked hcstar hnr hdelta hroots
      hsync hdeltaF hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta
      hrec hgeo hcert hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast
      hdeadlines hheldRows hscopeRows hfinalHead hs i hi hilen inv x s B hx ht.1 hslabel hB⟩
  have nonempty : ∀ j x s, iStar ≤ j → j < i + 1 → x ∈ rho.honest →
      enabledGateAt p c E rho j x s → w.u < s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧
        Block.Preceq w.QStar B ∧ gatePassedAt p c E rho j := by
    intro j x s hj hji hx ht hl
    rcases (Nat.le_of_lt_succ hji).lt_or_eq with hlt | rfl
    · exact inv.nonempty j x s hj hlt hx ht hl
    · obtain ⟨B, hB, hQ, hp, _⟩ := gate x s hx ht hl
      exact ⟨B, hB, hQ, hp⟩
  have ordered : ∀ j k x y s r B C, WCResult p c E rho w iStar (i + 1) j x s B →
      WCResult p c E rho w iStar (i + 1) k y r C → s < r → Block.Preceq B C := by
    intro j k x y s r B C hb hc hsr
    by_cases hk : k < i
    · by_cases hj : j < i
      · exact inv.ordered j k x y s r B C { hb with completed := hj }
          { hc with completed := hk } hsr
      · have heq : j = i := by have := hb.completed; omega
        subst j
        exact (not_lt.mpr (gate_label_le hsch hk.le hc.event hb.event) hsr).elim
    · have heq : k = i := by have := hc.completed; omega
      subst k
      have hj : j < i := by
        by_contra hn
        have heq : j = i := by have := hb.completed; omega
        subst j
        exact (not_lt.mpr (gate_label_le hsch le_rfl hc.event hb.event)) hsr
      obtain ⟨D, hD, _, _, ho, _⟩ := gate y r hc.honest (hc.enabled hsch) hc.label
      have heq : C = D := Option.some.inj (Option.some.inj (hc.value.symm.trans hD))
      exact heq ▸ ho j x s B { hb with completed := hj } hsr
  have sameLabel : ∀ j k x y s B C, WCResult p c E rho w iStar (i + 1) j x s B →
      WCResult p c E rho w iStar (i + 1) k y s C → Block.Compatible B C := by
    intro j k x y s B C hb hc
    by_cases hj : j < i
    · by_cases hk : k < i
      · exact inv.sameLabel j k x y s B C { hb with completed := hj }
          { hc with completed := hk }
      · have heq : k = i := by have := hc.completed; omega
        subst k
        obtain ⟨D, hD, _, _, _, hcompat, _⟩ := gate y s hc.honest (hc.enabled hsch) hc.label
        have heq : C = D := Option.some.inj (Option.some.inj (hc.value.symm.trans hD))
        exact heq ▸ hcompat j x s B { hb with completed := hj }
    · have heq : j = i := by have := hb.completed; omega
      subst j
      by_cases hk : k < i
      · obtain ⟨D, hD, _, _, _, hcompat, _⟩ := gate x s hb.honest (hb.enabled hsch) hb.label
        have heq : B = D := Option.some.inj (Option.some.inj (hb.value.symm.trans hD))
        change Block.compatible B C = true
        rw [block_compatible_comm, heq]
        exact hcompat k y s C { hc with completed := hk }
      · have heq : k = i := by have := hc.completed; omega
        subst k
        have heq : B = C := Option.some.inj (Option.some.inj (hb.value.symm.trans hc.value))
        exact block_compatible_of_common (heq ▸ block_preceq_refl C) (block_preceq_refl C)
  have resultCompat : ∀ j k x y s r B C,
      WCResult p c E rho w iStar (i + 1) j x s B →
      WCResult p c E rho w iStar (i + 1) k y r C → Block.Compatible B C := by
    intro j k x y s r B C hb hc
    rcases lt_trichotomy s r with h | h | h
    · exact block_compatible_of_common (ordered j k x y s r B C hb hc h)
        (block_preceq_refl C)
    · subst r
      exact sameLabel j k x y s B C hb hc
    · exact block_compatible_of_common (block_preceq_refl B)
        (ordered k j y x r s C B hc hb h)
  have historyCompat : ∀ A j x s B, WCBelowHistory p c E rho w iStar (i + 1) A →
      WCResult p c E rho w iStar (i + 1) j x s B → Block.Compatible A B := by
    intro A j x s B ha hr
    rcases ha.origin with ha | ⟨k, y, r, C, hc, hAC⟩
    · obtain ⟨C, hC, hQC, _⟩ := nonempty j x s hr.afterCut hr.completed hr.honest
        (hr.enabled hsch) hr.label
      have heq : C = B := Option.some.inj (Option.some.inj (hC.symm.trans hr.value))
      exact block_compatible_of_common (block_preceq_trans ha (heq ▸ hQC))
        (block_preceq_refl B)
    · exact block_compatible_of_preceq_compatible hAC (resultCompat k j y x r s C B hc hr)
  have sources : ∀ j x r K, iStar ≤ j → j < i + 1 → x ∈ rho.honest →
      rho.events[j]? = some (.tick x (p.actionTime r)) →
      actionSourceFG p c E rho x r = some (some K) →
      ∃ B, WCResult p c E rho w iStar (i + 1) j x (r * p.R) B ∧
        Block.Preceq (eraseFG K) B := by
    intro j x r K hj hji hx ht hK
    have hread : actionSource p c E rho x r = some (some (eraseFG K)) := by
      change (actionSourceFG p c E rho x r).map (Option.map eraseFG) = _
      rw [hK]
      rfl
    obtain ⟨targets, B, _, hmem, hB, hbelow, _⟩ := hsrc x r _ hx hread
    have hgate : IsGateTick p c rho j x (r * p.R) := ht
    exact ⟨B, ⟨hx, hj, hji, (wc_gate_cut_iff hsch hs hgate).mp hj, hgate,
      (gateResultAt_eq_gateResult p c E rho hsch hgate).trans hB⟩, hbelow _ hmem⟩
  have finite : ∀ k, iStar ≤ k → k ≤ i + 1 → WCFiniteFacts p c E rho k := by
    intro k hk hkn
    by_cases hki : k ≤ i
    · exact inv.finite k hk hki
    · have heq : k = i + 1 := by omega
      exact heq ▸ hfinite
  have finalHistory : ∀ x ∈ rho.honest,
      WCBelowHistory p c E rho w iStar i (F_at p c E rho (i + 1) x) := by
    intro x hx
    obtain ⟨D, hD, hF⟩ := (hstore (i + 1) x hx).1.fg.Fcar
    by_cases hlo : (finalityView p D).h_F ≤ w.M
    · have hbelow := (wc_lowFinalized hlinked hfaultX
        (hroots.toNamedRootCollisionFree E rho) hscopeRows hnoslash hs
        D _ _ (wc_finalizedOccurrence hscopeRows hnoslash D _ _
          (rootScope_store hx hD) hF rfl) hlo).2
      exact ⟨Or.inl hbelow⟩
    have hpos : 0 < (finalityView p D).h_F := by simp only [Height] at hlo ⊢; omega
    have hhigh : w.M + 1 ≤ (finalityView p D).h_F := by simp only [Height] at hlo ⊢; omega
    obtain ⟨jf, z, rf, af, uf, H, jt, q, rt, aT, ut, K, B, hjf, haf, _, _, _, _,
      _, _, _, _, hjt, haT, hdecode, _, htarget, hK, hXK, _hgate, _hKB, hgap⟩ :=
      (wc_finalityTargetEarlier hvalid hlinked hfaultQ
        (hroots.toNamedRootCollisionFree E rho) hheldRows hfinalHead hqc
        hemitted (i + 1) x D _ _ ⟨hx, hD⟩ hpos hF rfl).finalityRow
    have hfields : aT.payload.height_pair = ut.height_pair := by
      rcases aT with ⟨auth, body⟩
      cases auth with
      | none => cases hdecode
      | proposer s => cases hdecode
      | seat label k =>
        cases label with
        | head s => cases hdecode
        | fg => exact congrArg Row.height_pair (Option.some.inj hdecode)
    have hname : namedEntry aT.payload.height_pair =
        some ((finalityView p D).h_F, (storeAt p c E rho (i + 1) x).fg.F.root) := by
      rw [hfields, htarget]
      rfl
    by_cases hbefore : jt < iStar
    · obtain ⟨K', B', hK', _, _, _, _, hbelow⟩ :=
        hs.highSources jt q rt aT _ hbefore haT hname hhigh
      have heq : K = K' := Option.some.inj (Option.some.inj (hK.symm.trans hK'))
      exact ⟨Or.inl (block_preceq_trans (eraseFG_preceq hXK) (heq ▸ hbelow))⟩
    obtain ⟨C, hr, hKC⟩ := inv.suffixSources jt q rt K (Nat.le_of_not_gt hbefore)
      (hjt.trans_le (Nat.le_of_lt_succ hjf)) haT.1 haT.2.1 hK
    exact ⟨Or.inr ⟨jt, q, rt * p.R, C, hr,
      block_preceq_trans (eraseFG_preceq hXK) hKC⟩⟩
  have historyCompatOld : ∀ A C, WCBelowHistory p c E rho w iStar i A →
      WCBelowHistory p c E rho w iStar i C → Block.Compatible A C := by
    have seedResult : ∀ j x s B, WCResult p c E rho w iStar i j x s B →
        Block.Preceq w.QStar B := by
      intro j x s B hr
      obtain ⟨C, hC, hQ, _⟩ := inv.nonempty j x s hr.afterCut hr.completed hr.honest
        (hr.enabled hsch) hr.label
      have heq : C = B := Option.some.inj (Option.some.inj (hC.symm.trans hr.value))
      exact heq ▸ hQ
    intro A C ha hc
    rcases ha.origin with ha | ⟨j, x, r, B, hb, hAB⟩
    · rcases hc.origin with hc | ⟨k, y, s, D, hd, hCD⟩
      · exact block_compatible_of_common ha hc
      · exact block_compatible_of_common
          (block_preceq_trans ha (seedResult k y s D hd)) hCD
    · rcases hc.origin with hc | ⟨k, y, s, D, hd, hCD⟩
      · exact block_compatible_of_common hAB
          (block_preceq_trans hc (seedResult j x r B hb))
      · have hBD := resultCompat j k x y r s B D
          (extend_result hb (Nat.le_succ i))
          (extend_result hd (Nat.le_succ i))
        apply block_compatible_of_preceq_compatible hAB
        change Block.compatible _ _ = true
        rw [block_compatible_comm]
        apply block_compatible_of_preceq_compatible hCD
        change Block.compatible _ _ = true
        rw [block_compatible_comm]
        exact hBD
  have hout := wc_outputStep hsch
    (fun x hx => historyCompatOld _ _
      (wc_outputHistoryAt hs inv hi le_rfl hx) (finalHistory x hx)) (by
      intro x s hx hG
      obtain ⟨B, hB, hQ, hp, _, _, _⟩ := gate x s hx hG
        ((wc_gate_cut_iff hsch hs hG.1).mp hi)
      have hcompat := historyCompat _ i x s B
        (extend_history (wc_outputHistoryAt hs inv hi le_rfl hx) (Nat.le_succ i))
        ⟨hx, hi, Nat.lt_succ_self i, ((wc_gate_cut_iff hsch hs hG.1).mp hi), hG.1, hB⟩
      exact ⟨B, hB, hp, ((wc_gate_cut_iff hsch hs hG.1).mp hi), hcompat⟩)
  have outputHistory : ∀ x ∈ rho.honest,
      WCBelowHistory p c E rho w iStar (i + 1) (S_at p c E rho (i + 1) x) := by
    intro x hx
    rcases (hout x hx).2 with hkeep | ⟨s, ht, hl, hraw⟩ | hfinal
    · rw [hkeep]
      exact extend_history (wc_outputHistoryAt hs inv hi le_rfl hx) (Nat.le_succ i)
    · exact ⟨Or.inr ⟨i, x, s, _,
        ⟨hx, hi, Nat.lt_succ_self i, hl, ht, hraw⟩, block_preceq_refl _⟩⟩
    · rw [hfinal]
      exact extend_history (finalHistory x hx) (Nat.le_succ i)
  have oldOrigin : ∀ k x, iStar ≤ k → k ≤ i → x ∈ rho.honest →
      S_at p c E rho k x = w.QStar ∨
      (∃ j y s, WCResult p c E rho w iStar k j y s (S_at p c E rho k x)) ∨
      (∃ l, iStar ≤ l ∧ l ≤ k ∧ S_at p c E rho k x = F_at p c E rho l x ∧
        ∀ j y s B, WCResult p c E rho w iStar (i + 1) j y s B →
          Block.Compatible (F_at p c E rho l x) B) := by
    intro k x hlo hki hx
    rcases inv.outputOrigin k x hlo hki hx with hq | hr | ⟨l, hl, hlk, heq, _⟩
    · exact Or.inl hq
    · exact Or.inr (Or.inl hr)
    · refine Or.inr (Or.inr ⟨l, hl, hlk, heq, ?_⟩)
      intro j y s B hr
      exact historyCompat _ j y s B
        (extend_history (wc_finalHistoryAt hs inv hl (hlk.trans hki) hx)
          (hlk.trans (hki.trans (Nat.le_succ i)))) hr
  refine {
    interval := ⟨hi.trans (Nat.le_succ i), hnext⟩
    nonempty := nonempty
    ordered := ordered
    sameLabel := sameLabel
    retrospective := ?_
    preCutHigh := inv.preCutHigh
    suffixSources := sources
    highCertificates := ?_
    lowFinalized := ?_
    liveTargets := ?_
    oldLiveTargets := ?_
    suffixSaved := ?_
    suffixFast := ?_
    outputOrigin := ?_
    served := ?_
    transitions := ?_
    finite := finite
    carrier := ?_ }
  · intro j x s B hr y hy hJ
    by_cases hj : j < i
    · exact inv.retrospective j x s B { hr with completed := hj } y hy hJ
    · have heq : j = i := by have := hr.completed; omega
      subst j
      obtain ⟨C, hC, _, _, _, _, hhead⟩ := gate x s hr.honest (hr.enabled hsch) hr.label
      have heq : B = C := Option.some.inj (Option.some.inj (hr.value.symm.trans hC))
      exact heq ▸ hhead y hy hJ
  · intro k x W X hlo hkn hx hW hX hn hh
    by_cases hki : k ≤ i
    · exact inv.highCertificates k x W X hlo hki hx hW hX hn hh
    · have heq : k = i + 1 := by omega
      subst k
      have ho := hfinite.certified x hx W hW X hX hn
      refine ⟨ho, ?_⟩
      obtain ⟨j, y, r, wire, K, B, hj, hrow, hname, hK, hXK, _⟩ := ho.origin
      by_cases hjcut : j < iStar
      · obtain ⟨K', B', hK', _, _, _, _, hbelow⟩ :=
          hs.highSources j y r wire _ hjcut hrow hname hh
        have heq : K = K' := Option.some.inj (Option.some.inj (hK.symm.trans hK'))
        exact ⟨Or.inl (block_preceq_trans (eraseFG_preceq hXK) (heq ▸ hbelow))⟩
      · obtain ⟨C, hr, hKC⟩ := sources j y r K (Nat.le_of_not_gt hjcut) hj hrow.1 hrow.2.1 hK
        exact ⟨Or.inr ⟨j, y, r * p.R, C, hr, block_preceq_trans (eraseFG_preceq hXK) hKC⟩⟩
  · intro k x D X h _ _ hD hF hh hlo
    exact (wc_lowFinalized hlinked hfaultX (hroots.toNamedRootCollisionFree E rho) hscopeRows
        hnoslash hs D X h
      (wc_finalizedOccurrence hscopeRows hnoslash D X h
        (rootScope_store hD.1 hD.2) hF hh) hlo).1
  · intro k x row hlo hkn hx hr ht
    by_cases hki : k ≤ i
    · exact inv.liveTargets k x row hlo hki hx hr ht
    · have heq : k = i + 1 := by omega
      subst k
      exact prefix_history (htargets (i + 1) x row hr) (outputHistory x hx)
  · intro k x row hlo _ hx hr _ ht
    have hnow := V2.D.Engine.stateBefore_now_mono_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hsch
      hlo x
    rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho iStar x),
      fgsa_clock_now p c (V2.D.Run.stateBefore E rho k x)] at hnow
    exact hs.liveTargets x hx row hr (hnow.trans_lt ht)
  · intro k x s B hlo hkn hx hslabel hB
    obtain ⟨j, hj, hRF, ht, hraw⟩ := (finite k hlo hkn).saved x hx s B hB
    exact ⟨j, hRF, hx, (wc_gate_cut_iff hsch hs ht.1).mpr hslabel, hj, hslabel, ht.1, hraw⟩
  · intro k x s X hlo hkn hx hslabel hX
    obtain ⟨j, hj, hRF, ht, _, B, hB, hXB, _⟩ := (finite k hlo hkn).fastWrites x hx s X hX
    exact ⟨j, B, hRF, ⟨hx, (wc_gate_cut_iff hsch hs ht.1).mpr hslabel, hj, hslabel, ht.1, hB⟩, hXB⟩
  · intro k x hlo hkn hx
    by_cases hki : k ≤ i
    · exact oldOrigin k x hlo hki hx
    · have heq : k = i + 1 := by omega
      subst k
      rcases (hout x hx).2 with hkeep | ⟨s, ht, hl, hB⟩ | hfinal
      · rcases oldOrigin i x hi le_rfl hx with hq | ⟨j, y, s, hr⟩ | ⟨l, hl, hli, hF, hc⟩
        · exact Or.inl (hkeep.trans hq)
        · right; left
          refine ⟨j, y, s, ?_⟩
          rw [hkeep]
          exact extend_result hr (Nat.le_succ i)
        · exact Or.inr (Or.inr ⟨l, hl, hli.trans (Nat.le_succ i), hkeep.trans hF, hc⟩)
      · exact Or.inr (Or.inl ⟨i, x, s, hx, hi, Nat.lt_succ_self i, hl, ht, hB⟩)
      · exact Or.inr (Or.inr ⟨i + 1, hi.trans (Nat.le_succ i), le_rfl, hfinal,
          fun j y s B hr => historyCompat _ j y s B
            (extend_history (finalHistory x hx) (Nat.le_succ i)) hr⟩)
  · intro k x hlo hkn hx
    by_cases hki : k ≤ i
    · exact inv.served k x hlo hki hx
    · have heq : k = i + 1 := by omega
      subst k
      apply block_preceq_trans _ (hout x hx.1.1).1
      rw [← hs.refreshed x hx.1.1]
      exact wc_output_mono_of_inv hsch hs inv iStar i x ⟨le_rfl, hi⟩
        ⟨hi, le_rfl⟩ hi hx.1.1
  · intro k x hlo hkn hx hxnext
    rcases (Nat.le_of_lt_succ hkn).lt_or_eq with hki | rfl
    · exact inv.transitions k x hlo hki hx hxnext
    · exact (hout x hx.1.1).1
  · obtain ⟨W, hW, hh, _, hmem⟩ := hs.carrier
    refine ⟨W, hW, hh, ?_⟩
    intro k x hlo hkn hx
    exact (hcumul.1 iStar k x hx hlo (hkn.trans hnext)).1 (hmem x hx)

/-- WC plan §6.5; DC delivery preserves the joint invariant after immediate reconciliation. -/
theorem wc_stepDelivery : WCStepDeliveryStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv x o t he
  exact step_core hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv (.deliver x o t) he

/-- WC plan §6.5; DC a tick without a gate preserves the joint invariant in handler order. -/
theorem wc_stepNoGateTick : WCStepNoGateTickStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv x t he _hgate
  exact step_core hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv (.tick x t) he

/-- WC plan §6.5; DC a suffix gate adds its ordered result and retrospective HEAD evidence. -/
theorem wc_stepGateTick : WCStepGateTickStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv x s he _hlabel
  exact step_core hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv (.tick x (SA.gateTime p.toParams s)) he

/-- WC plan §6.5; DC split the actual event into the proved delivery, tick and restart cases. -/
theorem wc_step : WCStepStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
    hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
    hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
    hscopeRows hfinalHead hs i hi hilen inv e he
  cases e with
  | deliver x o t =>
    exact wc_stepDelivery hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
        hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
        hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
        hscopeRows hfinalHead hs i hi hilen inv x o t he
  | restart x t =>
    exact (wc_stepRestart hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
        hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
        hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
        hscopeRows hfinalHead hs i hi hilen inv x t he)
  | tick x t =>
    by_cases hg : isGateTime p t = true
    · obtain ⟨s, rfl⟩ := (isGateTime_iff p t).mp hg
      exact wc_stepGateTick hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
        hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
        hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
        hscopeRows hfinalHead hs i hi hilen inv x s he
        ((wc_gate_cut_iff hvalid.toScheduleWellFormed hs he).mp hi)
    · exact wc_stepNoGateTick hvalid hlinked hcstar hnr hdelta hroots hsync hdeltaF
        hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert
        hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines hheldRows
        hscopeRows hfinalHead hs i hi hilen inv x t he (Bool.eq_false_iff.mpr hg)

end AvailableChain.FGSA.Run
end

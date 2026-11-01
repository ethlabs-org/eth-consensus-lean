module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Epoch
public import AvailableChainFGSARun.Proofs.AC
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthReads

public section

/-! WC plan §6.7; DC safety follows from the joint finite invariant. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

/-- WC plan §6.7; DC completed result evidence persists in a longer history. -/
private theorem result_mono {i k j : Nat} {x : V} {s : Slot} {B : Block}
    (h : WCResult p c E rho w iStar i j x s B) (hik : i ≤ k) :
    WCResult p c E rho w iStar k j x s B :=
  { h with completed := h.completed.trans_le hik }

/-- WC plan §6.7; DC prefix origins persist in a longer history. -/
private theorem history_mono {i k : Nat} {B : Block}
    (h : WCBelowHistory p c E rho w iStar i B) (hik : i ≤ k) :
    WCBelowHistory p c E rho w iStar k B := by
  rcases h.origin with h | ⟨j, x, s, C, hr, hb⟩
  · exact ⟨Or.inl h⟩
  · exact ⟨Or.inr ⟨j, x, s, C, result_mono hr hik, hb⟩⟩

/-- WC plan §6.7; DC cached finality has a low or a high historical origin. -/
theorem wcg_finalHistoryAt {i k : Nat} {x : V}
    (hs : WCSeed p c E rho w iStar) (hi : WCInv p c E rho w iStar i)
    (hlo : iStar ≤ k) (hki : k ≤ i) (hx : x ∈ rho.honest) :
    WCBelowHistory p c E rho w iStar k (F_at p c E rho k x) := by
  obtain ⟨D, hD, hF⟩ := ((hi.finite k hlo hki).store x hx).fg.Fcar
  by_cases hX : (finalityView p D).F = .genesis
  · have he : F_at p c E rho k x = .genesis := by
      change eraseFG (storeAt p c E rho k x).fg.F = _
      rw [← hF, hX]
      rfl
    rw [he]
    exact ⟨Or.inl (block_genesis_preceq _)⟩
  by_cases hlow : (finalityView p D).h_F ≤ w.M
  · exact ⟨Or.inl (block_preceq_trans
      (hi.lowFinalized k x D _ _ hlo hki ⟨hx, hD⟩ hF rfl hlow) hs.sourcePrefix)⟩
  · have hn : (finalityView p D).h_F ≠ 0 := by
      simp only [Height] at *
      omega
    obtain ⟨C, D₀, _, _, hbirth, _⟩ := (fgCertificateLaws p).finality_origin D hn
    have hheight : (heightView p (finalityView p D).F).h = (finalityView p D).h_F := by
      rw [← hbirth.2.2.1, (fgCertificateLaws p).height.entry_same_height, hbirth.2.1]
    have hcert : (finalityView p D).F ∈ certified p D :=
      ⟨D, preceq_refl D, Or.inr (Or.inl rfl)⟩
    have hh : w.M + 1 ≤ (heightView p (finalityView p D).F).h := by
      rw [hheight]
      simp only [Height] at *
      omega
    have ho := (hi.highCertificates k x D _ hlo hki hx hD hcert hX hh).2
    rw [hF] at ho
    exact ho

/-- WC plan §6.7; DC the output origin keeps its own finite history bound. -/
theorem wcg_outputHistoryAt {i k : Nat} {x : V}
    (hs : WCSeed p c E rho w iStar) (hi : WCInv p c E rho w iStar i)
    (hlo : iStar ≤ k) (hki : k ≤ i) (hx : x ∈ rho.honest) :
    WCBelowHistory p c E rho w iStar k (S_at p c E rho k x) := by
  rcases hi.outputOrigin k x hlo hki hx with hq | ⟨j, y, s, hr⟩ | ⟨l, hl, hlk, he, _⟩
  · exact ⟨Or.inl (hq ▸ block_preceq_refl w.QStar)⟩
  · exact ⟨Or.inr ⟨j, y, s, _, hr, block_preceq_refl _⟩⟩
  · rw [he]
    exact history_mono (wcg_finalHistoryAt hs hi hl (hlk.trans hki) hx) hlk

/-- WC plan §6.7; DC result and output origins are compatible within the proved history. -/
theorem wcg_result_output_compatible {i k j : Nat} {x y : V} {s : Slot} {B : Block}
    (hS : V2.D.ScheduleWellFormed E rho)
    (hi : WCInv p c E rho w iStar i) (hr : WCResult p c E rho w iStar i j y s B)
    (hlo : iStar ≤ k) (hki : k ≤ i) (hx : x ∈ rho.honest) :
    Block.Compatible (S_at p c E rho k x) B := by
  rcases hi.outputOrigin k x hlo hki hx with hq | ⟨l, z, r, ho⟩ | ⟨l, _, _, he, hc⟩
  · obtain ⟨C, hC, hqC, _⟩ :=
      hi.nonempty j y s hr.afterCut hr.completed hr.honest (wcg_result_enabled hr hS) hr.label
    have he : C = B := Option.some.inj (Option.some.inj (hC.symm.trans hr.value))
    rw [hq]
    exact block_compatible_of_common (he ▸ hqC) (block_preceq_refl B)
  · have ho' := result_mono ho hki
    rcases lt_trichotomy r s with h | h | h
    · exact block_compatible_of_common (hi.ordered l j z y r s _ B ho' hr h)
        (block_preceq_refl B)
    · subst r
      exact hi.sameLabel l j z y s _ B ho' hr
    · exact block_compatible_of_common (block_preceq_refl _)
        (hi.ordered j l y z s r B _ hr ho' h)
  · rw [he]
    exact hc j y s B hr

/-- Kept outputs are monotone through every event in the proved finite history. -/
theorem wcg_output_mono_of_inv {last : Nat}
    (hschedule : V2.D.ScheduleWellFormed E rho) (hs : WCSeed p c E rho w iStar)
    (hi : WCInv p c E rho w iStar last) :
    MonoOn (· ∈ rho.honest) (S_at p c E rho)
      (fun i => iStar ≤ i ∧ i ≤ last) := by
  have resultSeed : ∀ j x s B, WCResult p c E rho w iStar last j x s B →
      Block.Preceq w.QStar B := by
    intro j x s B hr
    obtain ⟨C, hc, hq, _⟩ :=
      hi.nonempty j x s hr.afterCut hr.completed hr.honest
        (wcg_result_enabled hr hschedule) hr.label
    have he : B = C := Option.some.inj (Option.some.inj (hr.value.symm.trans hc))
    exact he ▸ hq
  have resultsCompat : ∀ j k x y s r B C,
      WCResult p c E rho w iStar last j x s B →
      WCResult p c E rho w iStar last k y r C → Block.Compatible B C := by
    intro j k x y s r B C hb hc
    rcases lt_trichotomy s r with h | h | h
    · exact block_compatible_of_common (hi.ordered j k x y s r B C hb hc h)
        (block_preceq_refl C)
    · subst r
      exact hi.sameLabel j k x y s B C hb hc
    · exact block_compatible_of_common (block_preceq_refl B)
        (hi.ordered k j y x r s C B hc hb h)
  have historyCompat : ∀ B C, WCBelowHistory p c E rho w iStar last B →
      WCBelowHistory p c E rho w iStar last C → Block.Compatible B C := by
    intro B C hb hc
    rcases hb.origin with hb | ⟨j, x, s, B', hr, hb⟩
    · rcases hc.origin with hc | ⟨k, y, r, C', hr, hc⟩
      · exact block_compatible_of_common hb hc
      · exact block_compatible_of_common
          (block_preceq_trans hb (resultSeed k y r C' hr)) hc
    · rcases hc.origin with hc | ⟨k, y, r, C', hr', hc⟩
      · exact block_compatible_of_common hb
          (block_preceq_trans hc (resultSeed j x s B' hr))
      · apply block_compatible_of_preceq_compatible hb
        change Block.compatible _ _ = true
        rw [block_compatible_comm]
        apply block_compatible_of_preceq_compatible hc
        change Block.compatible _ _ = true
        rw [block_compatible_comm]
        exact resultsCompat j k x y s r B' C' hr hr'
  have outputHistory : ∀ k x, iStar ≤ k → k ≤ last → x ∈ rho.honest →
      WCBelowHistory p c E rho w iStar last (S_at p c E rho k x) := by
    intro k x hlo hki hx
    rcases hi.outputOrigin k x hlo hki hx with hq | ⟨j, y, s, hr⟩ | ⟨l, hl, hlk, he, _⟩
    · exact ⟨Or.inl (hq ▸ block_preceq_refl w.QStar)⟩
    · exact ⟨Or.inr ⟨j, y, s, _, result_mono hr hki, block_preceq_refl _⟩⟩
    · rw [he]
      exact history_mono (wcg_finalHistoryAt hs hi hl (hlk.trans hki) hx) (hlk.trans hki)
  have step (k : Nat) (x : V) (hk : iStar ≤ k) (hkn : k < last)
      (hx : x ∈ rho.honest) :
      Block.Preceq (S_at p c E rho k x) (S_at p c E rho (k + 1) x) := by
    rcases fgsaAC_output_step E rho k x with hsame | ⟨r, ht⟩ | hrc | ⟨t, hr, _⟩
    · change S_at p c E rho (k + 1) x = S_at p c E rho k x at hsame
      rw [hsame]; exact block_preceq_refl _
    · change IsGateTick p c rho k x r at ht
      let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams r)
      by_cases hjoin : joinedNow p pre = true
      · rcases (fgsaAC_gate_write E rho k r x hjoin ht).effects with hskip | hrun
        · have he := hskip.2.1
          change S_at p c E rho (k + 1) x = S_at p c E rho k x at he
          rw [he]; exact block_preceq_refl _
        · cases hb : (fgsaAC E rho).raw k r x with
          | none =>
            have he := (hrun.empty hb).1
            change S_at p c E rho (k + 1) x = S_at p c E rho k x at he
            rw [he]; exact block_preceq_refl _
          | some B =>
            by_cases hveto : ∃ lease ∈ ((fgsaAC E rho).gateView k x r).obligations,
                ¬ Block.Compatible (Gen.AC.Lease.target lease) B
            · have he := (hrun.veto B hb hveto).1
              change S_at p c E rho (k + 1) x = S_at p c E rho k x at he
              rw [he]; exact block_preceq_refl _
            · have hall : ∀ lease ∈ ((fgsaAC E rho).gateView k x r).obligations,
                  Block.Compatible (Gen.AC.Lease.target lease) B := by
                simpa only [not_exists, not_and, not_not] using hveto
              have hview := fgsa_clockPre_gateView p (storeAt p c E rho k x) r
              have hG : enabledGateAt p c E rho k x r := by
                refine ⟨ht, ?_⟩
                have hg : joinedAtTime p (storeAt p c E rho k x).restartTime
                    (SA.gateTime p.toParams r) = true := by
                  simpa only [pre, clockPre_joined] using hjoin
                have hslot : p.slotOf (SA.gateTime p.toParams r) = r + 1 :=
                  (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho k x) _).2.symm.trans
                    (fgsa_gate_slot (c := c) (V2.D.Run.stateBefore E rho k x) r)
                change (match (storeAt p c E rho k x).restartTime with
                  | none => True | some w => w ≤ slotStartZ p (r : Int))
                cases hw : (storeAt p c E rho k x).restartTime with
                | none => trivial
                | some w =>
                  rw [hw] at hg
                  change decide (w ≤ 4 * p.Δ *
                    ((p.slotOf (SA.gateTime p.toParams r) : Int) - 1)) = true at hg
                  change w ≤ 4 * p.Δ * (r : Int)
                  simpa only [hslot, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
                    decide_eq_true_eq] using hg
              have hrawAt := wcg_gate_raw_enabled hschedule hG
              have hrawView : SA.Root.confirmationFrom p.toParams
                  (eraseFG (storeAt p c E rho k x).fg.F) (actView pre) r =
                    (fgsaAC E rho).raw k r x := by
                have he := congrArg (fun v => SA.Root.confirmationFrom p.toParams
                  (eraseFG (storeAt p c E rho k x).fg.F) v r) hview
                exact he
              have hraw : gateResultAt p c E rho k = some (some B) := by
                change gateResultAt p c E rho k = some (SA.Root.confirmationFrom
                  p.toParams (eraseFG (storeAt p c E rho k x).fg.F) (actView pre) r) at hrawAt
                exact hrawAt.trans (congrArg some (hrawView.trans hb))
              have hrB : WCResult p c E rho w iStar last k x r B :=
                ⟨hx, hk, hkn, (wcg_gate_cut_iff hschedule hs ht).mp hk, ht, hraw⟩
              have hc := wcg_result_output_compatible hschedule hi hrB hk hkn.le hx
              have hadv : Block.Preceq (S_at p c E rho k x)
                  (GridCO.advance (S_at p c E rho k x) B) := by
                unfold GridCO.advance
                split
                · exact block_preceq_refl _
                · next hn =>
                  rcases Bool.or_eq_true_iff.mp hc with h | h
                  · exact h
                  · exact (hn h).elim
              have hout := (hrun.accept B hb hall).1
              have hf : Block.preceq (F_at p c E rho k x)
                  (GridCO.advance (S_at p c E rho k x) B) = true :=
                block_preceq_trans (nestOK_stateBefore E rho k x) hadv
              change S_at p c E rho (k + 1) x = Gen.AC.normalizeOutput
                (F_at p c E rho k x) (GridCO.advance (S_at p c E rho k x) B) at hout
              rwa [hout, Gen.AC.normalizeOutput_def, ite_eq_left hf]
      · have hj : joinedNow p pre = false := Bool.eq_false_iff.mpr hjoin
        have hfresh : GridCO.savedGenuine pre.base r = none := by
          rw [GridCO.savedGenuine, clockPre_genuine]
          exact fgsa_gate_fresh E rho hschedule ht
        have hn : NestOK pre := by
          change Block.Preceq (eraseFG pre.fg.F) pre.base.stableRecord
          dsimp only [pre]
          rw [clockPre_fg, clockPre_stable]
          exact nestOK_stateBefore E rho k x
        have hout := ((gateStep_unjoined p pre r hfresh hj).2.2 hn).2.2
        have hclock : clock p (storeAt p c E rho k x) (SA.gateTime p.toParams r) =
            gateStep p pre r := by
          have hl : ((SA.gateTime p.toParams r - 6 * p.Δ) / (4 * p.Δ)).toNat = r := by
            have hz : (4 * p.Δ : Int) ≠ 0 := by nlinarith [p.deltaPos]
            change ((4 * p.Δ * (r : Int) + 6 * p.Δ - 6 * p.Δ) / (4 * p.Δ)).toNat = r
            simp [hz]
          unfold clock
          rw [hl]
          dsimp only
          have h0 : 0 ≤ SA.gateTime p.toParams r - 6 * p.Δ := by
            change 0 ≤ 4 * p.Δ * (r : Int) + 6 * p.Δ - 6 * p.Δ
            nlinarith [p.deltaPos, Int.natCast_nonneg r]
          simp only [h0, decide_true, beq_self_eq_true, Bool.true_and, ite_true]
          rfl
        have hpost := V2.D.Run.stateBefore_succ E rho ht
        change (S_at p c E rho k x).Preceq
          (V2.D.Run.stateBefore E rho (k + 1) x).st.base.stableRecord
        rw [hpost]
        simp only [V2.D.World.step, Function.update_self]
        rw [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho k x) x _]
        change (S_at p c E rho k x).Preceq
          (clock p (storeAt p c E rho k x) _).base.stableRecord
        rw [hclock, hout, clockPre_stable]
        exact block_preceq_refl _
    · obtain ⟨o, t, B, _he, _hb, _hf, hout⟩ := hrc
      have hc := historyCompat _ _ (outputHistory k x hk hkn.le hx)
        (history_mono (wcg_finalHistoryAt hs hi (hk.trans (Nat.le_succ k))
          (Nat.succ_le_of_lt hkn) hx) (Nat.succ_le_of_lt hkn))
      change S_at p c E rho (k + 1) x = Gen.AC.normalizeOutput
        (F_at p c E rho (k + 1) x) (S_at p c E rho k x) at hout
      rw [hout, Gen.AC.normalizeOutput_def]
      exact stable_preceq_normal hc
    · change rho.events[k]? = some (.restart x t) at hr
      change Block.Preceq (storeAt p c E rho k x).base.stableRecord
        (V2.D.Run.stateBefore E rho (k + 1) x).st.base.stableRecord
      rw [V2.D.Run.stateBefore_succ E rho hr]
      simp only [V2.D.World.step, Function.update_self]
      change (storeAt p c E rho k x).base.stableRecord.Preceq
        (acRestart p (storeAt p c E rho k x) t).base.stableRecord
      rw [acRestart_stableRecord]
      exact block_preceq_refl _
  intro i j x hii hjj hij hx
  induction j, hij using Nat.le_induction with
  | base => exact block_preceq_refl _
  | succ k hik ih =>
    exact block_preceq_trans (ih ⟨hii.1.trans hik, by omega⟩)
      (step k x (hii.1.trans hik) (by omega) hx)

/-- WC plan §6.7; DC event safety and both public output reads follow the joint invariant. -/
theorem wcg_cachedSafety (hschedule : V2.D.ScheduleWellFormed E rho)
    (hs : WCSeed p c E rho w iStar)
    (hinv : ∀ i, iStar ≤ i ∧ i ≤ rho.events.length → WCInv p c E rho w iStar i) :
    WCCachedSafety p c E rho iStar w.QStar := by
  let last := rho.events.length
  have hi := hinv last ⟨hs.within, le_rfl⟩
  have resultSeed : ∀ j x s B, WCResult p c E rho w iStar last j x s B →
      Block.Preceq w.QStar B := by
    intro j x s B hr
    obtain ⟨C, hc, hq, _⟩ :=
      hi.nonempty j x s hr.afterCut hr.completed hr.honest
        (wcg_result_enabled hr hschedule) hr.label
    have he : B = C := Option.some.inj (Option.some.inj (hr.value.symm.trans hc))
    exact he ▸ hq
  have resultsCompat : ∀ j k x y s r B C,
      WCResult p c E rho w iStar last j x s B →
      WCResult p c E rho w iStar last k y r C → Block.Compatible B C := by
    intro j k x y s r B C hb hc
    rcases lt_trichotomy s r with h | h | h
    · exact block_compatible_of_common (hi.ordered j k x y s r B C hb hc h)
        (block_preceq_refl C)
    · subst r
      exact hi.sameLabel j k x y s B C hb hc
    · exact block_compatible_of_common (block_preceq_refl B)
        (hi.ordered k j y x r s C B hc hb h)
  have historyCompat : ∀ B C, WCBelowHistory p c E rho w iStar last B →
      WCBelowHistory p c E rho w iStar last C → Block.Compatible B C := by
    intro B C hb hc
    rcases hb.origin with hb | ⟨j, x, s, B', hr, hb⟩
    · rcases hc.origin with hc | ⟨k, y, r, C', hr, hc⟩
      · exact block_compatible_of_common hb hc
      · exact block_compatible_of_common
          (block_preceq_trans hb (resultSeed k y r C' hr)) hc
    · rcases hc.origin with hc | ⟨k, y, r, C', hr', hc⟩
      · exact block_compatible_of_common hb
          (block_preceq_trans hc (resultSeed j x s B' hr))
      · apply block_compatible_of_preceq_compatible hb
        change Block.compatible _ _ = true
        rw [block_compatible_comm]
        apply block_compatible_of_preceq_compatible hc
        change Block.compatible _ _ = true
        rw [block_compatible_comm]
        exact resultsCompat j k x y s r B' C' hr hr'
  have outputHistory : ∀ k x, iStar ≤ k → k ≤ last → x ∈ rho.honest →
      WCBelowHistory p c E rho w iStar last (S_at p c E rho k x) := by
    intro k x hlo hki hx
    rcases hi.outputOrigin k x hlo hki hx with hq | ⟨j, y, s, hr⟩ | ⟨l, hl, hlk, he, _⟩
    · exact ⟨Or.inl (hq ▸ block_preceq_refl w.QStar)⟩
    · exact ⟨Or.inr ⟨j, y, s, _, result_mono hr hki, block_preceq_refl _⟩⟩
    · rw [he]
      exact history_mono (wcg_finalHistoryAt hs hi hl (hlk.trans hki) hx) (hlk.trans hki)
  have hcompat : CompatOn (· ∈ rho.honest) (S_at p c E rho)
      (fun i => iStar ≤ i ∧ i ≤ last) := by
    intro i j x y hii hjj hx hy
    exact historyCompat _ _ (outputHistory i x hii.1 hii.2 hx)
      (outputHistory j y hjj.1 hjj.2 hy)
  have hmono := wcg_output_mono_of_inv hschedule hs hi
  refine ⟨hcompat, hmono, ?_, ?_⟩
  · intro i x hii hx
    rw [← hs.refreshed x hx]
    exact hmono iStar i x ⟨le_rfl, hs.within⟩ hii hii.1 hx
  · intro g hg
    constructor
    · intro t u x y ht hu hx hy
      change Block.Compatible (V2.D.outputAt E rho g x t) (V2.D.outputAt E rho g y u)
      rw [fgsa_outputAt_eq_S_at E rho hschedule g hg x t,
        fgsa_outputAt_eq_S_at E rho hschedule g hg y u]
      exact hcompat _ _ x y ⟨ht, List.length_filter_le _ _⟩
        ⟨hu, List.length_filter_le _ _⟩ hx hy
    · intro t u x ht hu htu hx
      change Block.Preceq (V2.D.outputAt E rho g x t) (V2.D.outputAt E rho g x u)
      rw [fgsa_outputAt_eq_S_at E rho hschedule g hg x t,
        fgsa_outputAt_eq_S_at E rho hschedule g hg x u]
      exact hmono _ _ x ⟨ht, List.length_filter_le _ _⟩
        ⟨hu, List.length_filter_le _ _⟩ (V2.D.Engine.read_length_mono _ _ htu) hx

/-- Reader scopes are projections of the cached output safety theorem. -/
theorem wcg_seededSafety : WCSeededSafetyStatement p c E rho w iStar := by
  intro hschedule hs hinv
  have hc := wcg_cachedSafety hschedule hs hinv
  refine ⟨fun i j x y hii hjj hx hy => hc.compatible i j x y hii hjj hx.1.1 hy.1.1,
    fun i j x hii hjj hij hx _ => hc.monotone i j x hii hjj hij hx.1.1,
    fun i x hii hx => hc.seed i x hii hx.1.1, ?_⟩
  intro g hg
  exact ⟨fun t u x y ht hu hx hy => (hc.outputs g hg).1 t u x y ht hu hx.1 hy.1,
    fun t u x ht hu htu hx _ => (hc.outputs g hg).2 t u x ht hu htu hx.1⟩

end AvailableChain.FGSA.Run
end

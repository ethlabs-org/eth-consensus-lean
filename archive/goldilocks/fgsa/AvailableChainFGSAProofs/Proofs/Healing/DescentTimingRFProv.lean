module
public import AvailableChainFGSAProofs.Proofs.Healing.DescentTiming
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun
public import AvailableChainKitV2.DutyExecution
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

/-! RFProv clause 1 (B19). Split at the selected carrier's certificate
height. T1 gives the high source and its full period clock bound.
The low arm uses the after-action lower cut. The reset release q_(sStar)
is before that action; T1 also applies at the earlier release.
Blueprint: W3 21:542–546, H.17 21:2946–3047, H.18 21:3049–3060. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

omit [DecidableEq V] in
private theorem timing_tick_cut (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {x : V} {t : Time} (hj : rho.events[j]? = some (.tick x t)) :
    j < afterTicksIdx rho t := by
  by_contra hn
  have hc : cutPred (P := fgsa p c) t (.tick x t) = true := by
    change decide (toLex (t, 1) ≤ toLex (t, 1)) = true
    exact decide_eq_true le_rfl
  have hf := V2.D.Engine.filter_false_of_index_ge hs (cutPred t)
    (fun e f h ef => decide_eq_true (h.trans (of_decide_eq_true ef)))
    (Nat.le_of_not_gt hn) hj
  rw [hc] at hf
  contradiction

/-- The actual action source is held at its pre-action store. -/
theorem healing_action_source_held (hs : V2.D.ScheduleWellFormed E rho)
    {j r : Nat} {x : V} {K : FGBlock (Fin p.n)}
    (hj : rho.events[j]? = some (.tick x (p.actionTime r)))
    (hK : actionSourceFG p c E rho x r = some (some K)) :
    K ∈ (storeAt p c E rho j x).fg.TF := by
  rw [actionSourceFG_def, postClock_def, preTick_def] at hK
  cases hi : V2.D.Run.tickIdx? rho x (p.actionTime r) with
  | none => simp only [hi, Option.map_none] at hK; contradiction
  | some i =>
    have hij : i = j := by
      obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp (V2.D.Run.tickIdx?_spec hi)
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
      exact (List.Nodup.getElem_inj_iff hs.nodup).mp (hie.trans hje.symm)
    simp only [hi, Option.map_some, Option.some.injEq, hij] at hK
    let st := FGSA.clock p (V2.D.Run.stateBefore E rho j x).st (p.actionTime r)
    have hm : K ∈ fullTree p st := by
      change deepest _ = some K at hK
      exact (Finset.mem_filter.mp (FGSA.pickPair_some_spec _ _ hK).1).1
    have hm' : K ∈ st.fg.TF := (Finset.mem_filter.mp hm).1
    change K ∈ (FGSA.clock p _ _).fg.TF at hm'
    rwa [FGSA.clock_fg] at hm'

/-- The low-certificate arm of T3. This uses the actual CStar source
from H0Reset.fresh and RXing, after RFProv's action cut. -/
theorem healing_low_finality_at_reset (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) (xing : RXing p c E rho)
    (w : HealingWitness) (h0 : H0 p c E rho w) {i : Nat} {x : V}
    {D : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hi : afterTicksIdx rho (p.actionTime w.rStar) ≤ i)
    (hD : D ∈ (storeAt p c E rho i x).fg.TF)
    (hDF : (finalityView p D).F = (storeAt p c E rho i x).fg.F)
    (hlow : (finalityView p D).h_F ≤ w.M) :
    Block.Preceq (F_at p c E rho i x) w.CStar := by
  obtain ⟨j, y, a, C, ha, _, hC, hCS, hCh⟩ := h0.fresh
  have hji : j ≤ i := (Nat.le_of_lt (timing_tick_cut p c E rho hs ha.2.1)).trans hi
  have hheld := healing_action_source_held p c E rho hs ha.2.1 hC
  have hheld' := (fgsa_store_cumulative p c E rho hnr hji y).1 hheld
  have hFC := xing i i x y D C hx le_rfl hD hDF ⟨ha.1, hheld'⟩
    (by rw [hCh]; exact Nat.lt_succ_of_le hlow)
  rw [← hCS]
  exact eraseFG_preceq hFC

/-- ROOT-DIGEST W2b. T3: the full F branch of RFProv clause 1. The high arm uses T1's
source at the selected certificate height; the low arm uses the reset.
Assembly supplies the INLINE facts and RXing. -/
theorem healing_rFProv_finality (hv : V2.D.ExecutionValid E rho)
    (hnr : V2.D.NoRestart rho) (origin : RQCOrigin p c E rho)
    (heldRows : ∀ e x W, HeldAt p c E rho e x W →
      ∀ u ∈ chainRows W, ∃ (a : RowWire p.n) (r : Nat),
        a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
        ∃ k o t, k < e ∧ rho.events[k]? = some (.deliver x o t) ∧
          ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
            HonestRowBefore p c E rho e z r a ∧ p.actionTime r ≤ t)
    (cap : ∀ (y i : Nat), 0 < y → ∀ x W, HeldAt p c E rho i x W →
      y ≤ (finalityView p W).h_F →
      ∃ z r a u, HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
        RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
        u.finality_pair = some ⟨(finalityView p W).h_F, (finalityView p W).F.root⟩)
    (hhead : ∀ {j r : Nat} {z : V} {a : RowWire p.n} {u : Row (Fin p.n)},
      HonestRowAt p c E rho j z r a → RowSigner p c rho a z →
      a.toRow? = some u → ∀ fp, u.finality_pair = some fp →
      ∃ H, HeldAt p c E rho j z H ∧ fp.height = (heightView p H).h_j ∧
        fp.target = (heightView p H).J.root ∧
        KitFG.TargetQCAt p.E H fp.height (heightView p H).J)
    (xing : RXing p c E rho) (w : HealingWitness)
    (hroots : NamedRootCollisionFree p c E rho) :
    H0 p c E rho w → ∀ i x, x ∈ rho.honest →
      afterTicksIdx rho (p.actionTime w.rStar) ≤ i →
      Block.Preceq (F_at p c E rho i x) w.CStar ∨
        ∃ K s, SourceBefore p c E rho i K s ∧ high p w K ∧
          SA.gateTime p.toParams s + P p ≤ (storeAt p c E rho i x).base.now ∧
          Block.Preceq (F_at p c E rho i x) (eraseFG K) := by
  intro h0 i x hx hi
  by_cases hgen : (storeAt p c E rho i x).fg.F = .genesis
  · left
    change Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) w.CStar
    rw [hgen]
    exact Gen.Pure.block_genesis_preceq w.CStar
  obtain ⟨D, hD, hDF, K, s, hsrc, hh, hT, htime⟩ :=
    healing_finality_source_clock (hroots := hroots) p c E rho hv hnr origin heldRows cap hhead hx
      hgen
  by_cases hlow : (finalityView p D).h_F ≤ w.M
  · exact Or.inl (healing_low_finality_at_reset p c E rho hv.toScheduleWellFormed
      hnr xing w h0 hx hi hD hDF hlow)
  · right
    have hhigh : high p w K := by
      change w.M + 1 ≤ (heightView p K).h
      rw [hh]
      exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hlow)
    refine ⟨K, s, hsrc, hhigh, htime, ?_⟩
    change Block.Preceq (eraseFG (storeAt p c E rho i x).fg.F) (eraseFG K)
    rw [← hT]
    exact eraseFG_preceq ((fgCertificateLaws p).height.entry_preceq K)

end AvailableChain.FGSA.Run
end

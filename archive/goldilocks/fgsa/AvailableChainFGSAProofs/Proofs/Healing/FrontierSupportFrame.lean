module
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseRelay
public import AvailableChainFGSAProofs.Proofs.Healing.FrameZero
public import AvailableChainFGSAProofs.Proofs.Shared.HeldReceipt
public import AvailableChainFGSAProofs.Proofs.Healing.SupportFrame

public section

/-! G-HG1 capped frame (plan fgsa-s5-frontier §3.1 step 2; blueprint 21 HG.1:1520–1534,
L4-R step 2:2245–2262). Under a global frontier cap m, a held block above the height-m
pivot Q has height m. It witnesses itself at every honest frame: F and Z are below it and
the floor is at most m. No settled frame and no fixed phase are used. -/

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- ROOT-DIGEST W2b. Blueprint 21 HG.1:1521–1534 (state height on a path, IF.1). DC: SAME state
height does
not decrease along an erased path. -/
theorem frontier_height_mono {D B : FGBlock (Fin p.n)}
    (h : Block.Preceq (eraseFG D) (eraseFG B)) : (heightView p D).h ≤ (heightView p B).h := by
  have hl : FGBlock.Preceq D B :=
    eraseFG_preceq_iff.mp h
  exact (fgCertificateLaws p).height.h_mono hl

/-- Blueprint 21 HG.1:1520–1523; plan §3.1 step 2. DC: INTENTIONAL the closed cap of
TFrontier on [timeIdx u, timeIdx v] bounds every earlier honest cache, because the cache
height does not decrease (RMono). -/
theorem frontier_cap_before (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (mono : RMono p c E rho) (hN : V2.D.NoRestart rho) {u v : Time} {m : Nat}
    (huv : u ≤ v)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m) :
    ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m := by
  have huv' : timeIdx rho u ≤ timeIdx rho v := by
    change (rho.events.filter (fun e => decide (e.time ≤ u))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ v))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he =>
      decide_eq_true ((of_decide_eq_true he).trans huv))
  intro i x hi hx
  exact ((mono hN i (timeIdx rho v) x hx hi).2.2).trans
    (hCap _ x huv' le_rfl hx)

/-- The closed cap also bounds earlier stores through kept-state restarts. -/
theorem frontier_cap_before_on (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (mono : RMonoAll p c E rho) {u v : Time} {m : Nat}
    (huv : u ≤ v)
    (hCap : ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      (storeAt p c E rho i x).fg.h_max ≤ m) :
    ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m := by
  have huv' : timeIdx rho u ≤ timeIdx rho v := by
    change (rho.events.filter (fun e => decide (e.time ≤ u))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ v))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he =>
      decide_eq_true ((of_decide_eq_true he).trans huv))
  intro i x hi hx
  exact ((mono i (timeIdx rho v) x hx hi).2.2).trans
    (hCap _ x huv' le_rfl hx)

/-- Blueprint 21 HG.1:1521–1528; plan §3.1 step 2. DC: INTENTIONAL a held block above the
height-m pivot has height m, and so does the holder's cache, under the cap. -/
theorem frontier_height_eq (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {i : Nat} {x : V} (hcap : (storeAt p c E rho i x).fg.h_max ≤ m)
    {K : FGBlock (Fin p.n)} (hK : K ∈ (storeAt p c E rho i x).fg.TF)
    (hQK : Block.Preceq (eraseFG Qfg) (eraseFG K)) :
    (heightView p K).h = m ∧ (storeAt p c E rho i x).fg.h_max = m := by
  have h1 := frontier_height_mono (p := p) hQK
  have h2 := healing_phase_height_le p c E rho hK
  rw [hQm] at h1
  constructor <;> (simp only [Height] at *; omega)

/-- Blueprint 21 HG.1:1521–1534, L4-R step 2:2245–2262; plan §3.1 step 2. DC: INTENTIONAL a
held block K above the height-m pivot witnesses itself at the holder's live frame under the
cap: F and Z are below K, and the floor is at most h(K) = m. The root may be F or an
uncontested top J; no settlement is used. Assembly supplies RXing. -/
theorem frontier_self_witness (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (crossing : RXing p c E rho)
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {i : Nat} {x : V} (hx : x ∈ rho.honest) (hcap : (storeAt p c E rho i x).fg.h_max ≤ m)
    {K : FGBlock (Fin p.n)} (hK : K ∈ (storeAt p c E rho i x).fg.TF)
    (hQK : Block.Preceq (eraseFG Qfg) (eraseFG K)) :
    (heightView p K).h = m ∧ FGBlock.Preceq (storeAt p c E rho i x).fg.F K ∧
      FGBlock.Preceq (R_at p c E rho i x).Z K ∧ (R_at p c E rho i x).lo ≤ (heightView p K).h := by
  obtain ⟨hKm, hHm⟩ := frontier_height_eq E rho hQm hcap hK hQK
  have hH : (heightView p K).h = (R_at p c E rho i x).H := by
    change (heightView p K).h = (storeAt p c E rho i x).fg.h_max
    rw [hKm, hHm]
  obtain ⟨hF, hZ⟩ := healing_phase_frontier_root p c E rho crossing hx hK hH
  refine ⟨hKm, hF, hZ, ?_⟩
  rw [hH]
  exact KitFG.Controls.lo_le_H _

/-- Blueprint 21 HG.1:1520–1528, L4-R step 1:2232–2244; plan §3.1 step 2. DC: INTENTIONAL
every honest finality at an index under the cap is below each honest-held block of height
at least m held at that index or earlier (IF.3(c) via RXing). -/
theorem frontier_F_below_all (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (crossing : RXing p c E rho) {m : Nat}
    {a : Nat} {y : V} (hy : y ∈ rho.honest) (hcap : (storeAt p c E rho a y).fg.h_max ≤ m)
    {b : Nat} {z : V} (hz : z ∈ rho.honest) (hba : b ≤ a)
    {K : FGBlock (Fin p.n)} (hK : K ∈ (storeAt p c E rho b z).fg.TF)
    (hKm : m ≤ (heightView p K).h) :
    FGBlock.Preceq (storeAt p c E rho a y).fg.F K := by
  obtain ⟨Kc, hKc, hKcF⟩ := (storeBundle_stateBefore E rho a y).cstore.fg.Fcar
  have hf := (healing_phase_finality_le p c E rho hKc hKcF).trans_lt
    (healing_phase_justified_lt p c E rho a y)
  have hKa := (fgsa_store_durable p c E rho hba z).1 hK
  exact crossing a a y z Kc K hy le_rfl hKc hKcF ⟨hz, hKa⟩
    (by simp only [Height] at *; omega)

/-- Legacy interface; durable content does not need NoRestart. -/
theorem frontier_F_below (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (crossing : RXing p c E rho) (_hN : V2.D.NoRestart rho) {m : Nat}
    {a : Nat} {y : V} (hy : y ∈ rho.honest) (hcap : (storeAt p c E rho a y).fg.h_max ≤ m)
    {b : Nat} {z : V} (hz : z ∈ rho.honest) (hba : b ≤ a)
    {K : FGBlock (Fin p.n)} (hK : K ∈ (storeAt p c E rho b z).fg.TF)
    (hKm : m ≤ (heightView p K).h) :
    FGBlock.Preceq (storeAt p c E rho a y).fg.F K :=
  frontier_F_below_all E rho crossing hy hcap hz hba hK hKm

/-- ROOT-DIGEST W2b. Blueprint 21 HG.1:1529–1534, IF.5; plan §3.1 step 2. DC: INTENTIONAL a block
above the
height-m pivot, held by an honest node after an event at or after GST, is held by every
honest node strictly before that time + Δ, when the cap covers the receipt cut
(`healing_phase_held_receipt`). -/
theorem frontier_relay (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (crossing : RXing p c E rho) (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho)
    (hDelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time}
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {i : Nat} {ev : V2.Event V (Obj p)} {z : V} (hi : rho.events[i]? = some ev)
    (hz : z ∈ rho.honest) (hgst : E.t_GST ≤ ev.time)
    {K : FGBlock (Fin p.n)} (hK : K ∈ (storeAt p c E rho (i + 1) z).fg.TF)
    (hQK : Block.Preceq (eraseFG Qfg) (eraseFG K)) (hhor : ev.time + p.Δ ≤ rho.horizon)
    (hcut : V2.D.Run.idxBefore rho (ev.time + p.Δ) ≤ timeIdx rho v)
    {y : V} (hy : y ∈ rho.honest)
    (hAwake : E.awake y (ev.time + p.Δ) = true)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    K ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho (ev.time + p.Δ)) y).fg.TF := by
  have hKm : m ≤ (heightView p K).h := hQm ▸ frontier_height_mono (p := p) hQK
  have hfront : frontierAtIdx p c E rho (V2.D.Run.idxBefore rho (ev.time + p.Δ)) ≤
      (heightView p K).h := by
    change rho.honest.sup (fun x => (storeAt p c E rho _ x).fg.h_max) ≤ _
    exact Finset.sup_le (fun x hx => (hcap _ x hcut hx).trans hKm)
  exact healing_phase_held_receipt (hroots := hroots)
    p c E rho crossing hE hN hDelta hsync hi hz hgst hK hhor
    hfront hy hAwake

/-- ROOT-DIGEST W2b. Blueprint 21 HG.1:1529–1534, H.2 S1 (709–715); plan §3.1 steps 2–3. DC:
INTENTIONAL the
HEAD of an honest node at label i that covers the pivot is a held block of height m in its
full tree; every honest node holds it strictly before v_i + Δ, when the cap covers that
cut. This replaces the fixed-phase HEAD witness relay (`healing_head_witness_relay`). -/
theorem frontier_head_relay (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (crossing : RXing p c E rho) (hE : V2.D.ExecutionValid E rho) (hN : V2.D.NoRestart rho)
    (hDelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time}
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {jz : Nat} {z : V} {i : Slot} (hz : z ∈ rho.honest)
    (hjz : rho.events[jz]? = some (.tick z (SA.voteTime p.toParams i)))
    (hgst : E.t_GST ≤ SA.voteTime p.toParams i)
    (hQK : Block.Preceq (eraseFG Qfg) (headVote p (FGSA.clock p
      (V2.D.Run.stateBefore E rho jz z).st (SA.voteTime p.toParams i)) i))
    (hhor : SA.voteTime p.toParams i + p.Δ ≤ rho.horizon)
    (hcut : V2.D.Run.idxBefore rho (SA.voteTime p.toParams i + p.Δ) ≤ timeIdx rho v)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∃ Kfg, Kfg ∈ (storeAt p c E rho jz z).fg.TF ∧
      eraseFG Kfg = headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st
        (SA.voteTime p.toParams i)) i ∧ (heightView p Kfg).h = m ∧
      ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams i + p.Δ) = true →
        Kfg ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams i + p.Δ))
          y).fg.TF := by
  have hS := hE.toScheduleWellFormed
  obtain ⟨Kfg, hKfull, hKe, _⟩ := healing_full_witness_all p c E rho hS crossing hz hjz
  have hKT : Kfg ∈ (storeAt p c E rho jz z).fg.TF := by
    have h := ((KitFG.mem_filteredFromView _ _ _ _).mp hKfull).1
    change Kfg ∈ (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st _).fg.TF at h
    rwa [clock_fg] at h
  have hKe' : eraseFG Kfg = headVote p (FGSA.clock p
      (V2.D.Run.stateBefore E rho jz z).st (SA.voteTime p.toParams i)) i := hKe
  have hQK' : Block.Preceq (eraseFG Qfg) (eraseFG Kfg) := hKe' ▸ hQK
  have hjzv : jz ≤ timeIdx rho v := by
    have h1 : jz < V2.D.Run.idxBefore rho (SA.voteTime p.toParams i + p.Δ) :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hS hjz _).mpr (lt_add_of_pos_right _ p.deltaPos)
    exact h1.le.trans hcut
  have hKm := (frontier_height_eq E rho hQm (hcap jz z hjzv hz) hKT hQK').1
  refine ⟨Kfg, hKT, hKe', hKm, ?_⟩
  intro y hy hAwake
  exact frontier_relay (hroots := hroots) E rho crossing hE hN hDelta hsync hQm hcap hjz hz hgst
    ((fgsa_store_cumulative p c E rho hN (Nat.le_succ jz) z).1 hKT) hQK' hhor hcut hy hAwake

/-- Capped HEAD relay uses exact per-object services and durable receiver membership. -/
theorem frontier_head_relay_on (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (crossing : RXing p c E rho) (hE : V2.D.ExecutionValid E rho)
    {m : Nat} {Qfg : FGBlock (Fin p.n)} (hQm : (heightView p Qfg).h = m)
    {v : Time}
    (hcap : ∀ i x, i ≤ timeIdx rho v → x ∈ rho.honest → (storeAt p c E rho i x).fg.h_max ≤ m)
    {jz : Nat} {z : V} {i : Slot} (hz : z ∈ rho.honest)
    (hjz : rho.events[jz]? = some (.tick z (SA.voteTime p.toParams i)))
    (hQK : Block.Preceq (eraseFG Qfg) (headVote p (FGSA.clock p
      (V2.D.Run.stateBefore E rho jz z).st (SA.voteTime p.toParams i)) i))
    (hcut : V2.D.Run.idxBefore rho (SA.voteTime p.toParams i + p.Δ) ≤ timeIdx rho v)
    {y : V} (hy : y ∈ rho.honest) (hServices : HeadCarrierServices E rho jz z i y)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∃ Kfg, Kfg ∈ (storeAt p c E rho jz z).fg.TF ∧
      eraseFG Kfg = headVote p (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st
        (SA.voteTime p.toParams i)) i ∧ (heightView p Kfg).h = m ∧
      Kfg ∈ (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams i + p.Δ))
        y).fg.TF := by
  have hS := hE.toScheduleWellFormed
  obtain ⟨Kfg, hKfull, hKe, _⟩ := healing_full_witness_all p c E rho hS crossing hz hjz
  have hKT : Kfg ∈ (storeAt p c E rho jz z).fg.TF := by
    have h := ((KitFG.mem_filteredFromView _ _ _ _).mp hKfull).1
    change Kfg ∈ (FGSA.clock p (V2.D.Run.stateBefore E rho jz z).st _).fg.TF at h
    rwa [clock_fg] at h
  have hKe' : eraseFG Kfg = headVote p (FGSA.clock p
      (V2.D.Run.stateBefore E rho jz z).st (SA.voteTime p.toParams i)) i := hKe
  have hQK' : Block.Preceq (eraseFG Qfg) (eraseFG Kfg) := hKe' ▸ hQK
  have hjzv : jz ≤ timeIdx rho v := by
    have h1 : jz < V2.D.Run.idxBefore rho (SA.voteTime p.toParams i + p.Δ) :=
      (Gen.V2.Duty.index_lt_idxBefore_iff hS hjz _).mpr (lt_add_of_pos_right _ p.deltaPos)
    exact h1.le.trans hcut
  have hKm := (frontier_height_eq E rho hQm (hcap jz z hjzv hz) hKT hQK').1
  refine ⟨Kfg, hKT, hKe', hKm, ?_⟩
  have hFK := frontier_F_below_all E rho crossing hy (hcap _ y hcut hy) hz (by
    exact ((Gen.V2.Duty.index_lt_idxBefore_iff hS hjz _).mpr
      (lt_add_of_pos_right _ p.deltaPos)).le)
    hKT hKm.symm.le
  have hFloor : Block.Preceq
      (eraseFG (rho.stateBeforeTime E (SA.voteTime p.toParams i + p.Δ) y).st.fg.F)
      (eraseFG Kfg) := by
    rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
    exact eraseFG_preceq hFK
  have held := healing_held_block_receipt_on p c E rho hE hroots Kfg
    (SA.voteTime p.toParams i + p.Δ) y hy (hServices.direct Kfg hKT hKe' hFloor)
  change Kfg ∈ (rho.stateBefore E (V2.D.Run.idxBefore rho _) y).st.fg.TF
  rw [Gen.V2.Duty.stateBefore_idxBefore E rho _ hS]
  exact held

end AvailableChain.FGSA.Run
end

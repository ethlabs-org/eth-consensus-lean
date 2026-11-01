module
public import AvailableChainPCSAProofs.Proofs.Shared.FormationWindow
public import AvailableChainPCSAProofs.Proofs.Clean.FormationRelay

public section

/-! Freeze retention for Formation. Shared CollectClosed makes a
repeated collection call leave the store unchanged. The freeze clock keeps
the full PC list. This closes hFreezeKeep without a PC acceptance input. -/

namespace AvailableChain.PCSA
variable {n : Nat}

private theorem formation_collectClosed_fixed (st : State n) (h : CollectClosed st) :
    collectPCs st = st := by
  rw [CollectClosed_def] at h
  let candidates := (st.ackPool.filterMap (fun a =>
    (AckWire.decode? a).map (fun x => (x.1, x.2.2)))).eraseDups
  suffices ∀ cs : List (Slot × BlockId), cs ⊆ candidates →
      cs.foldl (fun acc sr =>
        match acc.base.blocks.find? (fun b => b.root == sr.2) with
        | none => acc
        | some b => match assemblePC acc sr.1 b with
          | none => acc
          | some C => installPC acc C) st = st from this candidates (List.Subset.refl _)
  intro cs hc
  induction cs with
  | nil => rfl
  | cons sr cs ih =>
    have htail : cs ⊆ candidates := fun _ hm => hc (List.mem_cons_of_mem _ hm)
    rw [List.foldl_cons]
    cases hb : st.base.blocks.find? (fun b => b.root == sr.2) with
    | none => exact ih htail
    | some b =>
      dsimp only
      cases ha : assemblePC st sr.1 b with
      | none => exact ih htail
      | some C =>
        dsimp only
        have hid := h sr.1 b C (List.mem_of_find?_eq_some hb) ha
        rw [KeyHeld_def] at hid
        obtain ⟨A, hm, hs, ht⟩ := hid
        have he := ((assemblePC_some_iff st sr.1 b C).mp ha).1
        have hslot : C.slot = sr.1 := congrArg PC.slot he
        have htarget : C.target = b := congrArg PC.target he
        have hdup : st.pcs.any (fun D => D.slot == C.slot && D.target == C.target) = true := by
          exact List.any_eq_true.mpr ⟨A, hm,
            Bool.and_eq_true_iff.mpr ⟨beq_iff_eq.mpr (hs.trans hslot.symm),
              beq_iff_eq.mpr (ht.trans htarget.symm)⟩⟩
        rw [installPC_duplicate st C hdup]
        exact ih htail
end AvailableChain.PCSA

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- The freeze tick retains every PC from the strict pre-freeze collection. -/
theorem pcsa_formation_freeze_keep (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hBase : Base₂ p c E rho) (y : V) (hy : y ∈ rho.honest) (s : Slot)
    (hhor : SA.freezeTime p.toParams s ≤ rho.horizon) :
    (collectPCs (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st).pcs ⊆
      (storeAfterTicks p c E rho y (SA.freezeTime p.toParams s)).pcs := by
  have hz : 0 ≤ SA.freezeTime p.toParams s := by
    have hd : (0 : Int) < p.Δ := p.deltaPos
    change 0 ≤ 4 * p.Δ * (s : Int) + 3 * p.Δ
    positivity
  have hpub : V2.PublicTime E (SA.freezeTime p.toParams s) := by
    refine ⟨4 * s + 3, ?_⟩
    rw [hBase.delta]
    change 4 * p.Δ * (s : Int) + 3 * p.Δ = ((4 * s + 3 : Nat) : Int) * p.Δ
    push_cast
    ring
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hBase.valid.tick_total y hy _ hpub hz hhor)
  have hpre := V2.D.Engine.stateBefore_tick_eq_stateBeforeTime
    hBase.valid.toScheduleWellFormed hBase.noRestart hi
  have hClosed := pcsa_collectClosed_stateBefore E rho hBase y hy i
  rw [hpre] at hClosed
  rw [formation_collectClosed_fixed _ hClosed]
  have hread : storeAfterTicks p c E rho y (SA.freezeTime p.toParams s) =
      clock p (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st
        (SA.freezeTime p.toParams s) := by
    change (FGSA.Run.afterTicks E rho (SA.freezeTime p.toParams s) y).st = _
    rw [FGSA.Run.afterTicks_eq_tick_preTick E rho hBase.valid.toScheduleWellFormed
      hBase.noRestart hi]
    exact pcsa_tick_st E rho _ _ _
  rw [hread, pcsa_clock_pcs]

variable [Fintype V]

/-- Formation stamps the PC with only ack admission and collection inputs. -/
theorem pcsa_formation_pc_of_store_facts_retained (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hAck : ∀ y ∈ rho.honest, E.awake y (SA.earlyTime p.toParams s) = true →
      HonestAckAt p c E rho y s N.erase)
    (hAckAdmit : ∀ y ∈ rho.honest, ∀ (i : Fin p.n) j t,
      rho.seatOf (.base (.ack s)) i ∈ rho.honest →
      SA.earlyTime p.toParams s ≤ t → t < SA.freezeTime p.toParams s →
      V2.D.Run.handlesAt E rho j y (ackObj p s i N.erase.root) t →
      (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈
        (V2.D.Run.stateBefore E rho (j + 1) y).st.ackPool)
    (hPCCollect : ∀ y ∈ rho.honest, ∀ Q : Finset (Fin p.n),
      let st := (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st
      (∀ i ∈ Q, (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈ st.ackPool) →
      pcQuorum p.n ≤ Q.card →
      ∃ C ∈ (collectPCs st).pcs, C.slot = s ∧ C.target = N.erase) :
    ∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s N.erase := by
  exact pcsa_formation_pc_of_store_facts E rho s N ΔF h hAck hAckAdmit hPCCollect (by
    intro y hy
    exact pcsa_formation_freeze_keep E rho h.base y hy s
      h.horizon)

/-- Formation stamps the PC with only ack admission and collection inputs. -/
theorem pcsa_formation_pc_of_participating_acks_retained (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (s : Slot) (N : NamedProposal p.n) (ΔF : Time)
    (h : FormationPreFreezePrem p c E rho s N ΔF)
    (hAck : ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s) = true →
      E.awake y (SA.earlyTime p.toParams s) = true → HonestAckAt p c E rho y s N.erase)
    (hAckAdmit : ∀ y ∈ rho.honest, ∀ (i : Fin p.n) j t,
      rho.seatOf (.base (.ack s)) i ∈ rho.honest →
      SA.earlyTime p.toParams s ≤ t → t < SA.freezeTime p.toParams s →
      V2.D.Run.handlesAt E rho j y (ackObj p s i N.erase.root) t →
      (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈
        (V2.D.Run.stateBefore E rho (j + 1) y).st.ackPool)
    (hPCCollect : ∀ y ∈ rho.honest, ∀ Q : Finset (Fin p.n),
      let st := (V2.D.Run.stateBeforeTime E rho (SA.freezeTime p.toParams s) y).st
      (∀ i ∈ Q, (⟨.seat (.ack s) i, N.erase.root⟩ : AckWire p.n) ∈ st.ackPool) →
      pcQuorum p.n ≤ Q.card →
      ∃ C ∈ (collectPCs st).pcs, C.slot = s ∧ C.target = N.erase) :
    ∀ y ∈ rho.honest, PCStampedBefore p c E rho y (SA.freezeTime p.toParams s) s N.erase := by
  exact pcsa_formation_pc_of_participating_acks E rho s N ΔF h hAck hAckAdmit hPCCollect (by
    intro y hy
    exact pcsa_formation_freeze_keep E rho h.base y hy s
      h.horizon)

end AvailableChain.PCSA.Run
end

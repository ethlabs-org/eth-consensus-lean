module
public import AvailableChainFGSAClaims.Statements.ChannelProps
public import AvailableChainFGSAClaims.Statements.Packages.Safety
public import AvailableChainFGSAProofs.Proofs.Shared.StoreRun
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:449–490; plan S22, H-BASE/HB1.
DC: SAME strict finalized crossing; INTENTIONAL accepted W certificate height.
The existing `fgsa_apiFinalLockClaim_body` supplies `crossing` from
`fgsa_finalLock`. Pass this foundation fact across the lane boundary. -/
theorem healing_rXing [Fintype V] {G ΔF : Time}
    (h : HealingSet p c E rho G ΔF)
    (crossing : FinalizedSafetyPrem p c E rho () → RXing p c E rho) :
    RXing p c E rho :=
  crossing ⟨h.base, h.fault⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:449–477, 2637–2666; plan S22, H-BASE/HB2.
DC: SAME causal cap; INTENTIONAL exact FG wire membership in the held chain.
`fgsa_rCap` supplies `cap` after its foundation premises are discharged.
Its height premise is transported to `heightView` at the lane boundary. -/
theorem healing_rCap
    (cap : ∀ y i x W, HeldAt p c E rho i x W → y + 2 ≤ (heightView p W).h →
      ∃ (z : V) (r : Nat) (a : RowWire p.n) (u : Row (Fin p.n))
        (T : BlockId) (timeout : Bool),
        HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
        a.toRow? = some u ∧ u ∈ chainRows W ∧
        u.height_pair = .vote (y + 1) T timeout) :
    RCap p c E rho := by
  intro y i x W hW hh
  obtain ⟨z, r, a, u, T, timeout, hb, _hs, hd, hu, hp⟩ := cap y i x W hW hh
  obtain ⟨j, hji, hj⟩ := hb
  have encode (b : RowWire p.n) (v : Row (Fin p.n)) (hv : b.toRow? = some v) :
      b = ⟨.seat .fg v.signer, .vote ⟨v.height_pair, v.finality_pair⟩⟩ := by
    rcases b with ⟨auth, ⟨⟨bh, bf⟩⟩⟩
    cases auth with
    | none => cases hv
    | proposer s => cases hv
    | seat label k =>
      cases label with
      | head s => cases hv
      | fg =>
        have he : (⟨k, bh, bf⟩ : Row (Fin p.n)) = v := Option.some.inj hv
        subst v
        rfl
  have ha := encode a u hd
  refine ⟨j, z, r, a, T, hji, hj, ?_, ?_⟩
  · rw [ha]
    change namedEntry u.height_pair = some (y + 1, T)
    rw [namedEntry_def, hp]
  · let st := storeAt p c E rho i x
    have hs := storeBundle_stateBefore E rho i x
    have hmem : W ∈ st.fg.TF := hW.2
    clear hW hh
    induction W with
    | genesis => exact (Finset.notMem_empty u hu).elim
    | node P s root body rows ih =>
      change u ∈ rows.toFinset ∪ chainRows P at hu
      rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨slot, N, hw, heN, hr⟩ :=
          stored_wire_of_block p st hs.cstore hs.«meta» hmem (by intro h; cases h)
        change rows = N.rows.filterMap RowWire.toRow? at hr
        have hur : u ∈ rows := List.mem_toFinset.mp hu
        rw [hr] at hur
        obtain ⟨b, hbw, hbu⟩ := List.mem_filterMap.mp hur
        have he : b = a := (encode b u hbu).trans ha.symm
        subst b
        apply List.mem_flatten.mpr
        refine ⟨N.rows, List.mem_filterMap.mpr ⟨_, hw, ?_⟩, hbw⟩
        have hrefl : Block.preceq (eraseFG (.node P s root body rows))
            (eraseFG (.node P s root body rows)) = true := Gen.Pure.block_preceq_refl _
        simp only [Wire.decode, heN, hrefl, ↓reduceIte]
      · have hpar := ih hu (hs.cstore.fg.closed _ hmem)
        obtain ⟨wires, hw, haw⟩ := List.mem_flatten.mp hpar
        obtain ⟨b, hb, hdec⟩ := List.mem_filterMap.mp hw
        apply List.mem_flatten.mpr
        refine ⟨wires, List.mem_filterMap.mpr ⟨b, hb, ?_⟩, haw⟩
        cases hbd : b.decode with
        | none => rw [hbd] at hdec; cases hdec
        | some msg =>
          cases msg with
          | vote s k B => rw [hbd] at hdec; cases hdec
          | row k payload => rw [hbd] at hdec; cases hdec
          | block slot N =>
            simp only [hbd] at hdec ⊢
            split at hdec
            · rename_i hpre
              have hparent : FGBlock.Preceq P (.node P s root body rows) := by
                change (decide (P = .node P s root body rows) || FGBlock.preceq P P) = true
                rw [KitFG.preceq_refl P, Bool.or_true]
              have hle : N.erase.preceq (eraseFG (.node P s root body rows)) = true :=
                Gen.Pure.block_preceq_trans hpre (eraseFG_preceq hparent)
              rw [hle, ite_eq_left (rfl : true = true)]
              exact hdec
            · cases hdec

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:548–590, 1125–1132; plan S20, H-BASE/HB4 and H-PHASE.
DC: SAME strict receipt and cumulative retention; INTENTIONAL independent ΔF.
Every row sent by the phase cut is held before cut + ΔF, including old rows
and sleeping receivers. `fgsa_tRowsReceipt` supplies the foundation fact. -/
theorem healing_phase_receipt (ΔF : Time)
    (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    (receipt : TRowsReceipt p c E rho ΔF)
    {j r : Nat} {y x : V} {a : RowWire p.n} {t : Time}
    (ha : HonestRowAt p c E rho j y r a) (hat : p.actionTime r ≤ t)
    (hgst : E.t_GST ≤ t) (hhor : t + ΔF ≤ rho.horizon) (hx : x ∈ rho.honest) :
    HeldBefore p c E rho x a (t + ΔF) := by
  have hdt : max (p.actionTime r) E.t_GST + ΔF ≤ t + ΔF :=
    Int.add_le_add_right (max_le hat hgst) ΔF
  have hh := receipt j y r a ha (hdt.trans hhor) x hx
  change rowHeld p (V2.D.Run.stateBeforeTime E rho _ x).st a at hh ⊢
  rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hs] at hh ⊢
  have hi : V2.D.Run.idxBefore rho (max (p.actionTime r) E.t_GST + ΔF) ≤
      V2.D.Run.idxBefore rho (t + ΔF) := by
    rw [V2.D.Run.idxBefore_def, V2.D.Run.idxBefore_def]
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he => decide_eq_true
      (lt_of_lt_of_le (of_decide_eq_true he) hdt))
  have hc := fgsa_store_cumulative p c E rho hnr hi x
  rcases hh with hh | hh
  · exact Or.inl (hc.2.2.2.2.2.subset hh)
  · right
    change a ∈ allBlockRows _ at hh ⊢
    obtain ⟨rows, hr, ha⟩ := List.mem_flatten.mp hh
    obtain ⟨w, hw, hd⟩ := List.mem_filterMap.mp hr
    exact List.mem_flatten.mpr ⟨rows,
      List.mem_filterMap.mpr ⟨w, hc.2.2.2.2.1.subset hw, hd⟩, ha⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:526–546, 2637–2653; plan S27/S30, H-BASE/HB5.
DC: SAME earlier-action order; INTENTIONAL FG action offset of 6Δ.
H-FRAME and H-DESCENT use this bound at proposal and HEAD reads.
It requires no reset, positive-slot, awake-reader, or finality premise. -/
theorem healing_source_time (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {C : FGBlock (Fin p.n)} {s u : Slot} {t : Time}
    (hsource : SourceBefore p c E rho i C s)
    (hi : rho.events[i]? = some (.tick x t))
    (ht : t = SA.proposalTime p.toParams u ∨ t = SA.voteTime p.toParams u) :
    s + 2 ≤ u := by
  obtain ⟨j, y, r, a, hji, ha, _hc, rfl⟩ := hsource
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp ha.2.1
  have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
  rw [hie, hje] at hk
  have htime : p.actionTime r ≤ t := V2.D.Engine.time_le_of_key_le _ _ hk
  have hd := p.deltaPos
  have hlt : (r * p.R : Int) + 1 < (u : Int) := by
    rcases ht with rfl | rfl
    · change 4 * p.Δ * (r * p.R : Nat) + 6 * p.Δ ≤ 4 * p.Δ * (u : Int) at htime
      push_cast at htime
      nlinarith
    · change 4 * p.Δ * (r * p.R : Nat) + 6 * p.Δ ≤
        4 * p.Δ * (u : Int) + p.Δ at htime
      push_cast at htime
      nlinarith
  exact_mod_cast (show (r * p.R : Int) + 2 ≤ (u : Int) by omega)

end AvailableChain.FGSA.Run
end

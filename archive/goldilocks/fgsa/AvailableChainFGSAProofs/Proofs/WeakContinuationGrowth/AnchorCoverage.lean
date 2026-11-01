module
public import AvailableChainFGSAProofs.Proofs.Shared.AnchorService
public import AvailableChainFGSAProofs.Proofs.Shared.Count

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)} {ΔF : Time}

private theorem gate_source_path (hsch : V2.D.ScheduleWellFormed E rho)
  {k : Nat} {y : V} {s : Slot} {K : Block}
  (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)))
  (hK : K ∈ (storeAt p c E rho k y).base.blocks) :
    ∀ b, Block.Preceq b K → b ≠ .genesis →
      ∃ l < k, ∃ t o, blockOf? p o = some b ∧
        V2.D.Run.acceptsAt E rho l y o t ∧ 0 ≤ t ∧ t < SA.voteTime p.toParams s := by
  intro b hb hne
  have hc := (storeBundle_stateBefore E rho k y).cstore
  obtain ⟨Kfg, hKfg, he⟩ := (hc.baseTree K).mp hK
  rw [← he] at hb
  obtain ⟨Bfg, hBfg, heB⟩ := eraseFG_ancestor_mem hc.fg.closed hKfg hb
  have hbm := (hc.baseTree b).mpr ⟨Bfg, hBfg, heB⟩
  obtain ⟨l, hl, t, o, ho, ha⟩ := fgsa_block_accepted_origin E rho k y b hne hbm
  refine ⟨l, hl, t, o, ho, ha, ?_, ?_⟩
  · obtain ⟨parent, hd, _⟩ := ha.1
    exact (hsch.in_horizon _ (List.mem_of_getElem? hd)).1
  · obtain ⟨parent, hd, _⟩ := ha.1
    obtain ⟨hll, hle⟩ := List.getElem?_eq_some_iff.mp hd
    obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
    have hkey := (List.pairwise_iff_getElem.mp hsch.sorted) l k hll hkl hl
    rw [hle, hke] at hkey
    change toLex (t, (2 : Nat)) ≤
      toLex (SA.voteTime p.toParams s, 1) at hkey
    rcases Prod.Lex.toLex_le_toLex.mp hkey with hlt | ⟨_, hphase⟩
    · exact hlt
    · omega


/-- Gate coverage uses this receiver and the vote-time anchor. -/
theorem wcg_gate_path_coverage (hE : V2.D.ExecutionValid E rho)
    (hR : V2.D.RestartsAtWakes E rho) (hDelta : E.Δ = p.Δ)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i k : Nat} {x y : V} {s : Slot} {K : Block}
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hG : enabledGateAt p c E rho i x s) (hcut : SA.gateTime p.toParams s ≤ rho.horizon)
    (hy : y ∈ rho.honest)
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams s)))
    (hK : K ∈ (storeAt p c E rho k y).base.blocks)
    (hF : ∀ j, j ≤ i → Block.Preceq (F_at p c E rho j x) K) :
    ∃ required paths,
      ReceiptCoverageAnchorPremises E rho (fun t => max t E.t_GST + p.Δ) rho.horizon
        (SA.earlyTime p.toParams s) 0 x K required paths
        (fun _ _ => SA.voteTime p.toParams s) ∧
      paths K (SA.earlyTime p.toParams s) := by
  have ht := hG.1
  have hx : x ∈ rho.honest := hE.honest_only _ (List.mem_of_getElem? ht)
  let required := fun o t => ∃ l < k, V2.D.Run.acceptsAt E rho l y o t ∧
    ∃ b, blockOf? p o = some b ∧ Block.Preceq b K
  let paths := fun B d => B = K ∧ d = SA.earlyTime p.toParams s
  have hsch := hE.toScheduleWellFormed
  have hD : SA.earlyTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hd : (0 : Int) < p.Δ := p.deltaPos
    linarith
  have hidx : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ i := by
    by_contra hh
    have hlt := (Gen.V2.Duty.index_lt_idxBefore_iff hsch ht (SA.earlyTime p.toParams s)).mp
      (Nat.lt_of_not_ge hh)
    exact (not_lt.mpr hD) hlt
  have htime : ∀ o t, required o t → 0 ≤ t ∧ t < SA.voteTime p.toParams s := by
    rintro o t ⟨l, hl, ha, _⟩
    obtain ⟨parent, hd, _⟩ := ha.1
    refine ⟨(hsch.in_horizon _ (List.mem_of_getElem? hd)).1, ?_⟩
    obtain ⟨hll, hle⟩ := List.getElem?_eq_some_iff.mp hd
    obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
    have hkey := (List.pairwise_iff_getElem.mp hsch.sorted) l k hll hkl hl
    rw [hle, hke] at hkey
    change toLex (t, (2 : Nat)) ≤
      toLex (SA.voteTime p.toParams s, 1) at hkey
    rcases Prod.Lex.toLex_le_toLex.mp hkey with hh | ⟨_, hh⟩
    · exact hh
    · omega
  have hve : SA.voteTime p.toParams s + p.Δ = SA.earlyTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 2 * p.Δ
    ring
  have hmax : max (SA.voteTime p.toParams s) E.t_GST = SA.voteTime p.toParams s :=
    max_eq_left hGST
  have decode {o : Obj p} {b : Block} (hb : blockOf? p o = some b) :
      ∃ r N, (toWire p o).decode = some (.block r N) := by
    change (match (toWire p o).decode with
      | some (.block _ N) => some N.erase | _ => none) = _ at hb
    cases hd : (toWire p o).decode with
    | none => rw [hd] at hb; contradiction
    | some m => cases m <;> simp_all
  refine ⟨required, paths, ?_, rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hDelta] using Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
          (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _)
  · intro o t hr
    have htt := htime o t hr
    obtain ⟨l, _, ha, b, hb, _⟩ := hr
    obtain ⟨r, N, hd⟩ := decode hb
    obtain ⟨hT, hH, hRF, _⟩ := fgsa_gate_path_anchor_service hE hDelta hR hx hy hG hd ha
      htt.2
    have h0 : 0 ≤ SA.voteTime p.toParams s := by
      change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
      have := p.deltaPos
      positivity
    refine ⟨htt.1, htt.2.le, h0,
      (le_max_left _ _).trans_lt (lt_add_of_pos_right _ p.deltaPos), ?_, Nat.zero_le _, ?_, hH, hRF,
      (fgsa_proposal_acceptance_facts hE hd ha).2⟩
    · simp only [hmax, hve, le_refl]
    · simpa only [hmax, hve] using hT
  · rintro o t ⟨l, _, ha, b, hb, _⟩ r signer B hv
    obtain ⟨u, N, hd⟩ := decode hb
    rw [hd] at hv
    cases hv
  · intro o t hr
    have htt := htime o t hr
    obtain ⟨l, _, ha, b, hb, _⟩ := hr
    obtain ⟨r, N, hd⟩ := decode hb
    have hh := (fgsa_gate_path_anchor_service hE hDelta hR hx hy hG hd ha
      htt.2).2.2.2
    simpa only [hmax, hve] using hh
  · intro j _ hj
    exact block_compatible_of_common (block_preceq_refl K) (hF j (hj.trans hidx))
  · exact ⟨fun _ _ hab => add_le_add (max_le_max hab le_rfl) le_rfl,
      hD.trans hcut, le_rfl, Nat.zero_le _⟩
  · rintro B d ⟨hBK, hdD⟩
    subst B
    subst d
    refine ⟨block_preceq_refl K, le_rfl, ?_⟩
    intro b hb hne
    obtain ⟨l, hl, t, o, ho, ha, _, ht'⟩ := gate_source_path hsch hk hK b hb hne
    have hdecode : ∃ r N, N.erase = b ∧ (toWire p o).decode = some (.block r N) := by
      change (match (toWire p o).decode with
        | some (.block _ N) => some N.erase | _ => none) = _ at ho
      cases he : (toWire p o).decode with
      | none => rw [he] at ho; contradiction
      | some m =>
        cases m <;> simp only [he, reduceCtorEq, Option.some.injEq] at ho
        exact ⟨_, _, ho, rfl⟩
    obtain ⟨r, N, heN, hdec⟩ := hdecode
    refine ⟨o, t, r, N, heN, ⟨l, hl, ha, b, ho, hb⟩, hdec, ?_⟩
    simp only [hmax, hve, le_refl]
  · intro o t r N hr hdec
    obtain ⟨l, hl, ha, b', hb', hBK⟩ := hr
    have hb : blockOf? p o = some N.erase := by
      change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
      rw [hdec]
    have heq := Option.some.inj (hb'.symm.trans hb)
    subst b'
    exact ⟨K, SA.earlyTime p.toParams s, ⟨rfl, rfl⟩, hBK⟩


/-- Transfer coverage uses the joined next voter and the early-time anchor. -/
theorem wcg_transfer_path_coverage
    (hE : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i : Nat} {x y : V} {s : Slot} {B : Block}
    (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    (hhor : SA.voteTime p.toParams (s + 1) ≤ rho.horizon)
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hcut : SA.freezeTime p.toParams s ≤ rho.horizon)
    (hpath : ∀ b, Block.Preceq b B → b ≠ .genesis →
      ∃ l < i, ∃ t o u N, N.erase = b ∧
        (toWire p o).decode = some (.block u N) ∧
        V2.D.Run.acceptsAt E rho l x o t ∧ 0 ≤ t ∧ t < SA.earlyTime p.toParams s)
    (hF : ∀ j, j ≤ V2.D.Run.idxBefore rho (SA.freezeTime p.toParams s) →
      Block.Preceq (F_at p c E rho j y) B) :
    ∃ required,
      ReceiptCoverageAnchorPremises E rho (fun t => max t E.t_GST + p.Δ) rho.horizon
        (SA.freezeTime p.toParams s) 0 y B required
        (fun L d => L = B ∧ d = SA.freezeTime p.toParams s)
        (fun _ _ => SA.earlyTime p.toParams s) := by
  let required := fun o t => 0 ≤ t ∧ t < SA.earlyTime p.toParams s ∧
    ∃ l < i, V2.D.Run.acceptsAt E rho l x o t ∧
      ∃ b, blockOf? p o = some b ∧ Block.Preceq b B
  have hef : SA.earlyTime p.toParams s + p.Δ = SA.freezeTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 3 * p.Δ
    ring
  have hfv : SA.freezeTime p.toParams s ≤ SA.voteTime p.toParams (s + 1) := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * ((s + 1 : Nat) : Int) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hmax : max (SA.earlyTime p.toParams s) E.t_GST = SA.earlyTime p.toParams s := by
    apply max_eq_left
    apply hGST.trans
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    linarith [p.deltaPos]
  have decode {o : Obj p} {b : Block} (hb : blockOf? p o = some b) :
      ∃ r N, (toWire p o).decode = some (.block r N) := by
    change (match (toWire p o).decode with
      | some (.block _ N) => some N.erase | _ => none) = _ at hb
    cases hd : (toWire p o).decode with
    | none => rw [hd] at hb; contradiction
    | some m => cases m <;> simp_all
  refine ⟨required, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hDelta] using Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
          (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _)
  · rintro o t ⟨h0, ht, l, _, ha, b, hb, _⟩
    obtain ⟨r, N, hd⟩ := decode hb
    obtain ⟨hT, hH, hRF, _⟩ := fgsa_transfer_path_anchor_service hE hDelta hy hx hJ hhor hd ha ht
    have hA : 0 ≤ SA.earlyTime p.toParams s := by
      change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
      have := p.deltaPos
      positivity
    refine ⟨h0, ht.le, hA,
      (le_max_left _ _).trans_lt (lt_add_of_pos_right _ p.deltaPos), ?_, Nat.zero_le _, ?_, hH,
      hRF.mono le_rfl (fgsa_idxBefore_mono rho hfv), (fgsa_proposal_acceptance_facts hE hd ha).2⟩
    · rw [hmax, hef]
    · simpa only [hmax, hef] using hT
  · rintro o t ⟨_, _, l, _, ha, b, hb, _⟩ r signer K hv
    obtain ⟨u, N, hd⟩ := decode hb
    rw [hd] at hv
    cases hv
  · rintro o t ⟨_, ht, l, _, ha, b, hb, _⟩
    obtain ⟨r, N, hd⟩ := decode hb
    have hH := (fgsa_transfer_path_anchor_service hE hDelta hy hx hJ hhor hd ha ht).2.2.2
    simpa only [hmax, hef] using hH
  · intro j _ hj
    exact block_compatible_of_common (block_preceq_refl B) (hF j hj)
  · exact ⟨fun _ _ hab => add_le_add (max_le_max hab le_rfl) le_rfl,
      hcut, le_rfl, Nat.zero_le _⟩
  · rintro K d ⟨hKB, hdD⟩
    subst K d
    refine ⟨block_preceq_refl B, le_rfl, ?_⟩
    intro b hb hne
    obtain ⟨l, hl, t, o, u, N, heN, hd, ha, hz, ht⟩ := hpath b hb hne
    have ho : blockOf? p o = some b := by
      change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
      rw [hd]
      exact congrArg some heN
    refine ⟨o, t, u, N, heN, ⟨hz, ht, l, hl, ha, b, ho, hb⟩, hd, ?_⟩
    simp only [hmax, hef, le_refl]
  · intro o t u N hr hd
    obtain ⟨_, _, l, hl, ha, b', hb', hBK⟩ := hr
    have hb : blockOf? p o = some N.erase := by
      change (match (toWire p o).decode with | some (.block _ N) => some N.erase | _ => none) = _
      rw [hd]
    have heq := Option.some.inj (hb'.symm.trans hb)
    subst b'
    exact ⟨B, SA.freezeTime p.toParams s, ⟨rfl, rfl⟩, hBK⟩


/-- A HEAD handler after its label start has dependencies and is timely. -/
theorem wcg_head_handlers (hV : V2.D.ExecutionValid E rho) (hDelta : E.Δ = p.Δ)
    (s : Slot) (q : Fin p.n) (b : BlockId) (x : V) {a d : Time}
    (hpa : SA.proposalTime p.toParams s ≤ a) :
    ∀ j u, a ≤ u → u < d →
      V2.D.Run.handlesAt E rho j x (ofHead p ⟨.seat (.head s) q, b⟩) u →
      (fgsa p c).wellFormed (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
      (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x)
        (ofHead p ⟨.seat (.head s) q, b⟩) = true ∧
      fgsaTimely p (V2.D.Run.stateBefore E rho j x) (ofHead p ⟨.seat (.head s) q, b⟩) := by
  intro j u hau hud hh
  have hcall := hh
  obtain ⟨parent, he, _⟩ := hh
  have deps := fgsa_hReady_of_not_block
    (dl := fun _ => d) (t := a) (o := ofHead p ⟨.seat (.head s) q, b⟩) (by intro r N h; cases h)
    (fgsa_hWF_of_delivery (dl := fun _ => d) (t := a) hV.wire) j u
    ((Gen.V2.Duty.index_lt_idxBefore_iff hV.toScheduleWellFormed he d).mpr hud) hcall
  refine ⟨deps.1, deps.2, ?_⟩
  have hpub : V2.PublicTime E (SA.proposalTime p.toParams s) := by
    refine ⟨4 * s, ?_⟩
    rw [hDelta]
    change 4 * p.Δ * (s : Int) = _
    push_cast
    ring
  have h0 : 0 ≤ SA.proposalTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int)
    have := p.deltaPos
    positivity
  have hn := V2.D.Engine.delivery_now_ge_public_atRestart (fgsaClock p c)
    (fgsaRestoreTimeLaw p c) E rho hV he hpub h0 (hpa.trans hau)
  change 4 * p.Δ * (s : Int) ≤ (rho.stateBefore E j x).st.base.now
  rw [← fgsa_clock_now p c (rho.stateBefore E j x)]
  exact hn

/-- Enabled gates bound all prior receiver restarts by the label start. -/
theorem wcg_gate_restart_bound (hS : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot} (hG : enabledGateAt p c E rho i x s) :
    ∀ j w, j < i → rho.events[j]? = some (.restart x w) →
      w ≤ SA.proposalTime p.toParams s := by
  intro j w hji hj
  obtain ⟨u, hu, hwu⟩ := fgsa_restartTime_ge E rho hS hj hji
  have hb := hG.2
  change (match (storeAt p c E rho i x).restartTime with
    | none => True | some t => t ≤ 4 * p.Δ * (s : Int)) at hb
  change (match (rho.stateBefore E i x).st.restartTime with
    | none => True | some t => t ≤ 4 * p.Δ * (s : Int)) at hb
  rw [hu] at hb
  exact hwu.trans hb

/-- The enabled gate retains its receiver stamps after a strict read in this label. -/
theorem wcg_gate_read_epoch (hV : V2.D.ExecutionValid E rho)
    {i : Nat} {x : V} {s : Slot} (hG : enabledGateAt p c E rho i x s)
    {D : Time} (hpD : SA.proposalTime p.toParams s < D) :
    V2.D.restartFree rho x (V2.D.Run.idxBefore rho D) i := by
  intro j w hDj hji he
  have hb := wcg_gate_restart_bound hV.toScheduleWellFormed hG j w hji he
  have hjD := (Gen.V2.Duty.index_lt_idxBefore_iff hV.toScheduleWellFormed he D).mpr
    (hb.trans_lt hpD)
  omega

/-- A fresh honest HEAD reaches the strict early read of this enabled receiver. -/
theorem wcg_gate_head_receipt
    (hV : V2.D.ExecutionValid E rho) (hR : V2.D.RestartsAtWakes E rho)
    (hDelta : E.Δ = p.Δ)
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i : Nat} {x : V} {s : Slot}
    (hGST : E.t_GST ≤ SA.voteTime p.toParams s)
    (hx : x ∈ rho.honest) (hG : enabledGateAt p c E rho i x s)
    (hcut : SA.gateTime p.toParams s ≤ rho.horizon) (q : Fin p.n) (b : BlockId)
    (hv : rho.seatOf (.base (.head s)) q ∈ rho.honest)
    (hem : rho.emits E (rho.seatOf (.base (.head s)) q)
      (ofHead p ⟨.seat (.head s) q, b⟩) (SA.voteTime p.toParams s)) :
    baseVote (⟨.seat (.head s) q, b⟩ : HeadWire p.n) ∈
      (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x).st.base.votes ∧
    GridCO.stampVote (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x).st.base
      (baseVote (⟨.seat (.head s) q, b⟩ : HeadWire p.n)) < SA.earlyTime p.toParams s := by
  have hS := hV.toScheduleWellFormed
  have h0 : 0 ≤ SA.voteTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + p.Δ
    have := p.deltaPos
    positivity
  have hpv : slotStartZ p (s : Int) ≤ SA.voteTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + p.Δ
    linarith [p.deltaPos]
  have hve : SA.voteTime p.toParams s + p.Δ = SA.earlyTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ + p.Δ = 4 * p.Δ * (s : Int) + 2 * p.Δ
    ring
  have heg : SA.earlyTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 2 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have hid : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ i := by
    by_contra hn
    exact (not_lt_of_ge heg) ((Gen.V2.Duty.index_lt_idxBefore_iff hS hG.1 _).mp
      (Nat.lt_of_not_ge hn))
  have hwindow : (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x).st.slot p ≤ s + 1 := by
    have hm := V2.D.Engine.stateBefore_now_mono_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hS hid x
    rw [fgsa_clock_now p c (rho.stateBefore E _ x),
      fgsa_clock_now p c (rho.stateBefore E i x),
      Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hm
    exact (Internal.slotOf_mono (p := p)
      (hm.trans (fgsa_preTick_now_le E rho hS hG.1))).trans_eq
      ((fgsa_postClock_slot (c := c) (rho.stateBefore E i x) _).2.symm.trans
        (fgsa_gate_slot (c := c) _ s))
  have hNX : (fgsa p c).excludes (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x)
      (ofHead p ⟨.seat (.head s) q, b⟩) = false := by
    apply Bool.eq_false_iff.mpr
    intro he
    change excludesS p (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x).st
      (ofHead p ⟨.seat (.head s) q, b⟩) = true at he
    rw [excludesS_of_vote _ rfl] at he
    obtain ⟨_, hOld | hCap⟩ := (Internal.grid_excludes_head_iff _ s q b).mp he
    · exact (not_lt_of_ge hwindow) hOld
    · obtain ⟨u, hu, v, hvotes, hne, hku, hkv⟩ := (Gen.AC.Root.cap_pair _ q).mp hCap
      have unique (o : GridCO.Wire p.n .root) (ho : o ∈ GridCO.votesAt
          (rho.stateBeforeTime E (SA.earlyTime p.toParams s) x).st.base s)
          (hk : GridCO.headSeat? o = some q) :
          o = baseVote (⟨.seat (.head s) q, b⟩ : HeadWire p.n) := by
        obtain ⟨hm, hl⟩ := List.mem_filter.mp ho
        rw [← Gen.V2.Duty.stateBefore_idxBefore E rho _ hS] at hm
        exact fgsa_honest_head_eq_of_stored E rho hV _ x s q b _ hv hem o hm
          (beq_iff_eq.mp hl) hk
      exact hne ((unique u hu hku).trans (unique v hvotes hkv).symm)
  have hmax : max (SA.voteTime p.toParams s) E.t_GST = SA.voteTime p.toParams s :=
    max_eq_left hGST
  have hdeadline : max (SA.voteTime p.toParams s) E.t_GST + p.Δ =
      SA.earlyTime p.toParams s := by rw [hmax, hve]
  let service : FreshHeadService E rho s q b (SA.earlyTime p.toParams s) x := {
    dl := fun t => max t E.t_GST + p.Δ, cut := rho.horizon, within := by
      simpa only [hDelta] using
        Gen.V2.Duty.deliveryWithinOn_of_partialSynchronyBy E rho hsync
          (fun o => ¬ isRowObject o) E.Δ (fgsaDelay_nonrow E.Δ _)
    ready := ⟨_, hv, Or.inl hem, fun u hvu hue =>
      fgsa_enabledGate_awakeClosed hV hx hG u (h0.trans hvu)
        (hpv.trans hvu) (hue.le.trans (hdeadline.le.trans heg))⟩
    later := (le_max_left _ _).trans_lt (lt_add_of_pos_right _ p.deltaPos)
    cut_le := hdeadline.le.trans (heg.trans hcut)
    horizon := hdeadline.le.trans (heg.trans hcut), freeze_le := hdeadline.le
    epoch := fgsa_enabledGate_anchor_epoch hV hR hx hG hpv
      (by rw [← hve]; exact lt_add_of_pos_right _ p.deltaPos) heg
    handlers := wcg_head_handlers hV hDelta s q b x hpv
    not_excluded := by simpa only [hdeadline] using hNX }
  obtain ⟨k, hk, ho⟩ := hem
  exact service.receipt hV hx hk ho


omit [DecidableEq V] in
theorem wcg_vote_restart_bound (hS : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot}
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho x (s + 1) (SA.voteTime p.toParams (s + 1))) :
    ∀ j w, j < i → rho.events[j]? = some (.restart x w) →
      w ≤ SA.proposalTime p.toParams s := by
  intro j w hji hj
  have hw : w ≤ SA.voteTime p.toParams (s + 1) := by
    by_contra hn
    have hij := V2.D.Engine.eventIndex_lt_of_time_lt hS hi hj (lt_of_not_ge hn)
    omega
  have hb := hJ.2.2 w (hS.in_horizon _ (List.mem_of_getElem? hj)).1 hw
    (List.mem_of_getElem? hj)
  change w ≤ slotStartZ p (s : Int)
  simpa only [Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right] using hb

omit [DecidableEq V] in
/-- The next joined voter retains strict-read stamps through its action index. -/
theorem wcg_vote_read_epoch (hS : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {y : V} {s : Slot}
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1))))
    (hJ : joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)))
    {D : Time} (hD : SA.proposalTime p.toParams s < D) :
    V2.D.restartFree rho y (V2.D.Run.idxBefore rho D) k := by
  intro j w hDj hjk he
  have hb := wcg_vote_restart_bound hS hk hJ j w hjk he
  have hjD := (Gen.V2.Duty.index_lt_idxBefore_iff hS he D).mpr (hb.trans_lt hD)
  omega

end AvailableChain.FGSA.Run
end

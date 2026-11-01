module
public import AvailableChainFGSAProofs.Proofs.Outage.InclusionGateBody -- shake: keep (examples)
public import AvailableChainFGSAProofs.Proofs.Outage.GrowthConsumer -- shake: keep (examples)

public section

namespace AvailableChain.FGSA.Run.Tests.InclusionGate

open AvailableChain.SimplexFG
open Gen.Pure

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}

section Fields

variable
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hInputs : InclusionReceiverInputs E rho)
    (hHistory : InclusionHistoryBounds E rho)
    (hstore : RStore p c E rho) (hframe : RFrameExactNext p c E rho)
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hstrat : RStrat p c E rho)
    (hordered : ∀ x y r s B C, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams r ≤ rho.horizon → SA.gateTime p.toParams s ≤ rho.horizon →
      gateResult p c E rho x r = some (some B) →
      gateResult p c E rho y s = some (some C) →
      (r < s → Block.Preceq B C) ∧ (r = s → Block.Compatible B C))
    (hnonempty : ∀ j x s, j < timeIdx rho rho.horizon → x ∈ rho.honest →
      enabledGateAt p c E rho j x s →
      ∃ B, gateResultAt p c E rho j = some (some B) ∧ (s = 0 → B = .genesis))
    (htransfer : ∀ x y s B H, x ∈ rho.honest → y ∈ rho.honest →
      SA.gateTime p.toParams s ≤ rho.horizon → gateResult p c E rho x s = some (some B) →
      joinedAt p E rho y (s + 1) (SA.voteTime p.toParams (s + 1)) →
      vHead p c E rho y s = some H → Block.Preceq B H)
    (hleases : ∀ i v, i ≤ timeIdx rho rho.horizon → v ∈ rho.honest →
      ∀ row ∈ (storeAt p c E rho i v).base.obligations,
        BelowLabel p c E rho i (labelBoundAt p c rho i) row.1)
    (hrows : ∀ i j x r (a : RowWire p.n) e, i ≤ timeIdx rho rho.horizon → j < i →
      HonestRowAt p c E rho j x r a → namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧ EntryBelow p e C ∧
        BelowLabel p c E rho i (labelBoundAt p c rho j) (eraseFG C))
    (pt : PtSP) (hprop : HonestProposal E rho (fgsaInterface p c) pt.s pt.P)
    (hhor : SA.gateTime p.toParams pt.s ≤ rho.horizon)
    (hmono : ScopedMono (confirmedReaderIdx p c E rho) (S_at p c E rho)
      (· ≤ rho.events.length))
    (hOrigins : ∀ t x, SA.gateTime p.toParams pt.s ≤ t → t ≤ rho.horizon →
      confirmedReader p c E rho x t →
      ∃ q i B, pt.s ≤ q ∧ SA.gateTime p.toParams q ≤ t ∧
        enabledGateAt p c E rho i x q ∧ gateResultAt p c E rho i = some (some B) ∧
        Block.Preceq B (S_at p c E rho (timeIdx rho t) x))

-- G6 uses confirmed readers and the exact receiver service at the enabled gate.
example :
    ScopedServed (fun x i => confirmedReaderAtIdx p c E rho x i
      (SA.gateTime p.toParams pt.s)) (S_at p c E rho) pt.P
      (fun i => i = afterTicksIdx rho (SA.gateTime p.toParams pt.s)) ∧
    ScopedMono (confirmedReaderIdx p c E rho) (S_at p c E rho) (· ≤ rho.events.length) :=
  clean_inclusion_post_gate_body (hstrat :=
    hstrat) E rho ΔF hset hInputs hHistory hstore hframe hsrc hordered hnonempty
    htransfer hleases hrows pt hprop hhor hmono

-- G7 keeps both getters and every read in the closed interval.
example :
    ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ScopedServed (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t) pt.P
        (fun t => SA.gateTime p.toParams pt.s ≤ t ∧ t ≤ rho.horizon) :=
  clean_inclusion_body (hstrat :=
    hstrat) E rho ΔF hset hInputs hHistory hstore hframe hsrc hordered hnonempty
    htransfer hleases hrows pt hprop hhor hOrigins

-- T61: the last gate read uses the approved post-tick confirmed-reader scope.
example (hd : SA.gateTime p.toParams pt.s = rho.horizon) {x : V}
    (hx : confirmedReaderAtIdx p c E rho x
      (afterTicksIdx rho (SA.gateTime p.toParams pt.s)) (SA.gateTime p.toParams pt.s)) :
    ∃ i, IsGateTick p c rho i x pt.s ∧ gatePassedAt p c E rho i ∧
      S_at p c E rho (i + 1) x = pt.P := by
  have he : ((4 * pt.s + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams pt.s := by
    change ((4 * pt.s + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (pt.s : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨i, hi, _⟩ := fgsa_tick_total E rho hset.pre.base.valid.toScheduleWellFormed
    hset.pre.base.delta x hx.1 (4 * pt.s + 6) (he ▸ hd.le) (he ▸ hx.2.1)
  rw [he] at hi
  have hg := inclusion_gate_exact (hstrat :=
    hstrat) E rho ΔF hset hInputs hHistory hstore hframe hsrc hordered hnonempty
    htransfer hleases hrows pt hprop hd.le hx.1
    (inclusion_enabled_gate_of_after_reader E rho
      hset.pre.base.valid.toScheduleWellFormed hi hx)
  exact ⟨i, hi, hg.2.2.1, hg.2.2.2⟩

-- s = 1 uses transfer at label 0. Its older-label branch is empty.
example (hfirst : pt.s = 1) {x : V} (hx : x ∈ rho.honest) :
    ∀ B, (0, B) ∈ cleanResults p c E rho
      (V2.D.Run.idxBefore rho (SA.gateTime p.toParams pt.s)) → Block.Preceq B pt.P := by
  have hh := inclusion_headAtLabel (hstrat :=
    hstrat) E rho ΔF hset hInputs hstore hframe hsrc hordered hnonempty
    htransfer hleases hrows pt hprop hhor
  exact inclusion_prior_results_below E rho hset hordered hnonempty htransfer
    pt.s pt.P (hfirst ▸ Nat.one_pos)
    hhor hh hx 0

-- A sleeping receiver has no gate tick in a valid sleep execution.
example {x : V} (hd : E.awake x (SA.gateTime p.toParams pt.s) = false)
    {i : Nat} (hi : IsGateTick p c rho i x pt.s) : False := by
  have ha := hset.pre.base.valid.tick_awake x (SA.gateTime p.toParams pt.s)
    (List.mem_of_getElem? hi)
  rw [hd] at ha
  cases ha

-- At d, the inclusive read uses a confirmed-reader gate origin.
example {x y : V} (hx : confirmedReader p c E rho x
    (SA.gateTime p.toParams pt.s)) (o : Obj p) {j : Nat}
    (hd : rho.events[j]? = some (.deliver y o (SA.gateTime p.toParams pt.s))) :
    cutPred (P := fgsa p c) (SA.gateTime p.toParams pt.s)
      (.deliver y o (SA.gateTime p.toParams pt.s)) = false ∧
      (.deliver y o (SA.gateTime p.toParams pt.s) : V2.Event V (Obj p)) ∈
        rho.events.filter (fun e => decide (e.time ≤ SA.gateTime p.toParams pt.s)) ∧
      Block.Preceq pt.P (V2.D.outputAt E rho (fgsaInterface p c).confirmed x
        (SA.gateTime p.toParams pt.s)) := by
  refine ⟨?_, List.mem_filter.mpr ⟨List.mem_of_getElem? hd, by simp [V2.Event.time]⟩, ?_⟩
  · simp [cutPred, V2.Event.key, V2.Event.time, V2.Event.phase, Prod.Lex.toLex_le_toLex]
  · exact clean_inclusion_body (hstrat :=
    hstrat) E rho ΔF hset hInputs hHistory hstore hframe hsrc hordered hnonempty
      htransfer hleases hrows pt hprop hhor hOrigins (fgsaInterface p c).confirmed
      (by simp) _ x ⟨le_rfl, hhor⟩ hx

-- Both getters use the confirmed-reader scope at the last public read.
example {x : V} (hx : confirmedReader p c E rho x rho.horizon) :
    Block.Preceq pt.P (V2.D.outputAt E rho (fgsaInterface p c).stable x rho.horizon) ∧
      Block.Preceq pt.P (V2.D.outputAt E rho (fgsaInterface p c).confirmed x rho.horizon) := by
  have hi := clean_inclusion_body (hstrat :=
    hstrat) E rho ΔF hset hInputs hHistory hstore hframe hsrc hordered hnonempty
    htransfer hleases hrows pt hprop hhor hOrigins
  exact ⟨hi _ (by simp) _ x ⟨hhor, le_rfl⟩ hx, hi _ (by simp) _ x ⟨hhor, le_rfl⟩ hx⟩

-- The growth supplier uses the inclusive gate witness for an earlier reader.
example (hOutputs : ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
      ScopedCompat (confirmedReader p c E rho) (fun t x => V2.D.outputAt E rho g x t)
        (fun t => 0 ≤ t ∧ t ≤ rho.horizon))
    {u : Time} {x : V} {g : V2.D.Output (fgsa p c)}
    (hu : 0 ≤ u) (hus : u < V2.D.proposalTime (fgsaInterface p c) pt.s)
    (hx : confirmedReader p c E rho x u)
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed]) :
    Block.Compatible (V2.D.outputAt E rho g x u) pt.P := by
  have hWitness := clean_inclusion_gate_witness (hstrat := hstrat) E rho ΔF hset hInputs hHistory
    hstore hframe hsrc hordered hnonempty htransfer hleases hrows pt hprop hhor
  exact clean_growth_compatible_of_outputs E rho hset hOutputs hhor hWitness hu hus hx hg

-- T31/T37: the counted receiver executes its own enabled gate and earlier vote.
example (q : Slot) (hq : SA.gateTime p.toParams q ≤ rho.horizon) :
    ∃ z ∈ rho.honest, joinedAt p E rho z (q + 1) (SA.gateTime p.toParams q) ∧
      joinedAt p E rho z (q + 1) (SA.voteTime p.toParams (q + 1)) ∧
      ∃ i, enabledGateAt p c E rho i z q :=
  inclusion_joined_gate_witness E rho hset q hq

-- T35: the vote reader can be different from the proposal sender.
example (hv : SA.voteTime p.toParams pt.s ≤ rho.horizon) :
    ∃ z ∈ rho.honest, joinedAt p E rho z pt.s (SA.voteTime p.toParams pt.s) ∧
      ∃ i : Nat, rho.events[i]? = some (V2.Event.tick z (SA.voteTime p.toParams pt.s)) :=
  inclusion_joined_vote_witness E rho hset pt.s hv

end Fields

/- Full execution fixtures are not supplied here. The following tests need
such fixtures: n = 5, a = 1, h_v = 2 below the fast threshold; s = 1 with
both lease tests failing; Byzantine late-only votes and equivocation; several
honest gate ticks plus a delivery at d; later finalization, expiry and release;
a gate after the horizon; and a run with DeltaF greater than Delta.
The examples above check theorem instantiation and event-cut boundaries.
They do not claim these full execution tests. -/

end AvailableChain.FGSA.Run.Tests.InclusionGate
end

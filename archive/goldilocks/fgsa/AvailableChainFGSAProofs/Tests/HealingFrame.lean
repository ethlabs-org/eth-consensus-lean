module
public import AvailableChainFGSAProofs.Proofs.Healing.FramePaths -- shake: keep (H-FRAME tests)
public import AvailableChainFGSAProofs.Proofs.Healing.FrameZero -- shake: keep (zero-label HEAD)
public import AvailableChainFGSAProofs.Proofs.Healing.FrameRelay -- shake: keep (held witness relay)

set_option linter.privateModule false

/-! H-FRAME tests, plan S30. The frozen TGeom type needs only schedule order.
The relay test uses an old held witness and receiver ancestry at the deadline.
The path test permits equality at the freeze. The genesis frame has frontier one.
-/

section
namespace AvailableChain.FGSA.Run.Tests.HealingFrame
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedReceiptRootCollisionFree p c E rho)

-- This is the exact frozen conjunction. It has no source or phase hypothesis.
example (hs : V2.D.ScheduleWellFormed E rho) : TGeom p c E rho :=
  healing_tGeom p c E rho hs

-- The floor belongs to the same immutable FG parent as the membership witness.
example (hs : V2.D.ScheduleWellFormed E rho) {s : Slot} {Q : Block} {st : State p.n}
    (hp : HonestProposal E rho (fgsaInterface p c) s Q)
    (hst : proposalStateAt p c E rho s = some st) (hne : (fullTree p st).Nonempty) :
    ∃ B ∈ fullTree p st, eraseFG B = Q.parent ∧ (frameR p st).lo ≤ (heightView p B).h :=
  (healing_tGeom p c E rho hs).1 s Q st hp hst hne

-- A suppressed row does not remove the source-slot bound.
example {x : V} {r : Nat} {C : FGBlock (Fin p.n)} (hx : x ∈ rho.honest)
    (hc : actionSourceFG p c E rho x r = some (some C)) : C.slot ≤ r * p.R :=
  healing_source_slot p c E rho hx hc

-- Old witnesses need no new-acceptance event or frontier-height equality.
example (mono : RMono p c E rho) (hv : V2.D.ExecutionValid E rho)
    (hnr : V2.D.NoRestart rho) (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i : Nat} {x y : V} {t : Time} {W : FGBlock (Fin p.n)}
    (hi : rho.events[i]? = some (.tick x t)) (hx : x ∈ rho.honest) (hy : y ∈ rho.honest)
    (hW : W ∈ (storeAt p c E rho i x).fg.TF) (hgst : E.t_GST ≤ t)
    (hhor : t + p.Δ ≤ rho.horizon)
    (hF : FGBlock.Preceq
      (storeAt p c E rho (V2.D.Run.idxBefore rho (t + p.Δ)) y).fg.F W)
    (hAwake : E.awake y (t + p.Δ) = true) :
    Gen.V2.Duty.HoldsBefore E rho (fun nd => W ∈ nd.st.fg.TF) (t + p.Δ) y :=
  healing_held_block_receipt (hroots := hroots) p c E rho mono hv hnr hdelta hsync hi hx hy hW
      hgst hhor hF hAwake

-- The HEAD can be outside its frozen domain. The height bound is on W.
example (crossing : RXing p c E rho) {i : Nat} {x : V} {s : Slot}
    (hx : x ∈ rho.honest) (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hs : 0 < s) :
    let st := ((fgsa p c).clock (rho.stateBefore E i x) (SA.voteTime p.toParams s)).st
    ∃ K ∈ fullTree p st, eraseFG K = headVote p st s ∧
      ∃ W ∈ st.fg.TF, FGBlock.Preceq K W ∧ (controls p st).lo ≤ (heightView p W).h :=
  healing_full_witness p c E rho crossing hx hi hs

-- B26 permits the receipt deadline to equal the phase endpoint.
example (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (hv : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho) (hdelta : E.Δ = p.Δ)
    {ΔF : Time} (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (u : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hgst : E.t_GST ≤ u) (hhead : u ≤ SA.voteTime p.toParams s)
    (hphase : PhaseInterval p c E rho u (SA.voteTime p.toParams s + p.Δ) m J contested)
    (hhor : SA.voteTime p.toParams s + p.Δ ≤ rho.horizon)
    (W : FGBlock (Fin p.n)) (hW : W ∈ (storeAt p c E rho i x).fg.TF)
    (hsrc : SettledPhaseFrame p (storeAt p c E rho i x) m J contested)
    (hZW : FGBlock.Preceq (R_at p c E rho i x).Z W)
    (hlo : (R_at p c E rho i x).lo ≤ (heightView p W).h) :
    ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s + p.Δ) = true →
      Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∀ B, FGBlock.Preceq B W → B ∈ nd.st.fg.TF)
      (SA.voteTime p.toParams s + p.Δ) y :=
  healing_witness_relay_phase (hroots := hroots) p c E rho mono crossing hv hnr hdelta hsync
    u (SA.voteTime p.toParams s + p.Δ) m J contested hgst hphase hx hi hhead le_rfl
    hhor W hW hsrc hZW hlo

-- Receipt at the freeze itself cannot enter its strict prefix.
example (hs : V2.D.ScheduleWellFormed E rho) {i : Nat} {x : V} {o : Obj p} {d : Time}
    (hi : rho.events[i]? = some (.deliver x o d)) : ¬ i < V2.D.Run.idxBefore rho d := by
  intro hl
  exact (lt_irrefl d) ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi d).mp hl)

-- Slot zero uses the actual early run state, with a genesis witness.
example (hs : V2.D.ScheduleWellFormed E rho) (crossing : RXing p c E rho)
    {i : Nat} {x : V} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams 0))) :
    let st := ((fgsa p c).clock (rho.stateBefore E i x) (SA.voteTime p.toParams 0)).st
    ∃ K ∈ fullTree p st, eraseFG K = headVote p st 0 ∧
      ∃ W ∈ st.fg.TF, FGBlock.Preceq K W ∧ (controls p st).lo ≤ (heightView p W).h :=
  healing_full_witness_all p c E rho hs crossing hx hi

-- The deadline can equal the freeze: retained ancestor stamps are strict.
example (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    {y : V} {q : Slot} {nd : Node p} {W : FGBlock (Fin p.n)}
    (hdpos : 0 < SA.freezeTime p.toParams (q - 1))
    (hdt : SA.freezeTime p.toParams (q - 1) ≤ SA.voteTime p.toParams q)
    (hW : W ∈ (storeAt p c E rho
      (V2.D.Run.idxBefore rho (SA.freezeTime p.toParams (q - 1))) y).fg.TF)
    (hread : postClock E rho y (SA.voteTime p.toParams q) = some nd) :
    ∀ B, FGBlock.Preceq nd.st.fg.F B → FGBlock.Preceq B W →
      B ∈ voterBlocks p nd.st q :=
  healing_frozen_path p c E rho hs hnr hdpos hdt le_rfl hW hread

-- Frontier one is a valid full-tree witness; there is no height-two assumption.
example : (fullTree p (initial p.n)).Nonempty := by
  refine ⟨.genesis, ?_⟩
  apply (KitFG.mem_filteredFromView _ _ _ _).mpr
  refine ⟨by simp [initial, Store.init], KitFG.preceq_refl _, KitFG.preceq_refl _,
    .genesis, by simp [initial, Store.init], KitFG.preceq_refl _, ?_⟩
  change 0 ≤ _
  exact Nat.zero_le _

-- An admitted current-slot proposal supplies the carried arm without a freeze stamp.
example (src dst : State p.n) (hr : Reachable p dst) (s : Slot) (Q : Block)
    (B : FGBlock (Fin p.n)) (hQ : Q ∈ dst.base.blocks) (hslot : Q.slot = s)
    (hB : B ∈ src.fg.TF) (hparent : eraseFG B = Q.parent)
    (hlo : (controls p dst).lo ≤ (heightView p B).h) (C : Block)
    (hstart : Block.Preceq (liveRoot p dst) C) (hCQ : Block.Preceq C Q) :
    C ∈ RetainedWalk.T p dst s :=
  healing_carried_path p src dst hr s Q B hQ hslot hB hparent hlo C hstart hCQ

end AvailableChain.FGSA.Run.Tests.HealingFrame
end

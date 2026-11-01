module
public import AvailableChainFGSAProofs.Proofs.Shared.HeldReceipt
public import AvailableChainFGSAClaims.Statements.ComposeStmt
public import AvailableChainFGSARun.Proofs.Receipts -- shake: keep (receipt API)
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseFrame

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:749–783, 1148–1252; plan S30, H-FRAME/F2.
DC: INTENTIONAL receiver frames are required at the strict receipt cut.
RXing uses the accepted finality certificate and a witness held at that same cut.
Settlement only at the source HEAD does not supply the destination frames. -/
theorem healing_witness_relay (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    {i : Nat} {x : V} {s m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hgst : E.t_GST ≤ SA.voteTime p.toParams s)
    (hhor : SA.voteTime p.toParams s + p.Δ ≤ rho.horizon)
    (W : FGBlock (Fin p.n)) (hW : W ∈ (storeAt p c E rho i x).fg.TF)
    (hsrc : SettledPhaseFrame p (storeAt p c E rho i x) m J contested)
    (hZW : FGBlock.Preceq (R_at p c E rho i x).Z W)
    (hlo : (R_at p c E rho i x).lo ≤ (heightView p W).h)
    (hdst : ∀ y ∈ rho.honest, SettledPhaseFrame p
      (storeAt p c E rho (V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ)) y)
      m J contested)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s + p.Δ) = true →
      Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∀ B, FGBlock.Preceq B W → B ∈ nd.st.fg.TF)
      (SA.voteTime p.toParams s + p.Δ) y := by
  let j := V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ)
  have hij : i < j := (Gen.V2.Duty.index_lt_idxBefore_iff hvalid.toScheduleWellFormed hi _).mpr
    (lt_add_of_pos_right _ p.deltaPos)
  have hWj := (fgsa_store_cumulative p c E rho hnr hij.le x).1 hW
  intro y hy hAwake
  have hd := hdst y hy
  have hF : FGBlock.Preceq (storeAt p c E rho j y).fg.F W := by
    cases J with
    | some B =>
      have hJB : (R_at p c E rho i x).Z = B := hsrc.2.2.2.1.2.2.1
      exact KitFG.preceq_trans hd.2.2.2.1.2.2.2.2.2 (hJB ▸ hZW)
    | none =>
      obtain ⟨K, hK, hKF, hKh⟩ := hd.2.2.2.1.2.2.1
      have hfloor : (R_at p c E rho j y).lo = (R_at p c E rho i x).lo :=
        hd.2.2.1.trans hsrc.2.2.1.symm
      exact crossing j j y x K W hy le_rfl hK hKF ⟨hx, hWj⟩
        (hKh.trans_le (hfloor ▸ hlo))
  have hreceipt := healing_held_block_receipt (hroots := hroots)
    p c E rho mono hvalid hnr hdelta hsync
    hi hx hy hW hgst hhor hF hAwake
  change W ∈ (V2.D.Run.stateBeforeTime E rho _ y).st.fg.TF at hreceipt
  change ∀ B, FGBlock.Preceq B W → B ∈ (V2.D.Run.stateBeforeTime E rho _ y).st.fg.TF
  intro B hBW
  have hinv := (storeBundle_stateBeforeTime E rho (SA.voteTime p.toParams s + p.Δ) y).cstore
  obtain ⟨A, hA, he⟩ := eraseFG_ancestor_mem hinv.fg.closed hreceipt (eraseFG_preceq hBW)
  exact (eraseFG_injective he) ▸ hA

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 21:749–783, 1148–1252; plan S30, H-FRAME/F2; owner B25/B26.
DC: INTENTIONAL the phase must include the strict receipt deadline.
The receiver frames come from healing_settled_frame. The lower-cut bridge is
kept in one place; it uses B25's PhaseInterval cut at timeIdx rho u. -/
theorem healing_witness_relay_phase (mono : RMono p c E rho) (crossing : RXing p c E rho)
    (hvalid : V2.D.ExecutionValid E rho) (hnr : V2.D.NoRestart rho)
    (hdelta : E.Δ = p.Δ) {ΔF : Time}
    (hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
    (u v : Time) (m : Nat) (J : Option (FGBlock (Fin p.n))) (contested : Bool)
    (hgst : E.t_GST ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    {i : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick x (SA.voteTime p.toParams s)))
    (hhead : u ≤ SA.voteTime p.toParams s)
    (hreceipt : SA.voteTime p.toParams s + p.Δ ≤ v)
    (hhor : SA.voteTime p.toParams s + p.Δ ≤ rho.horizon)
    (W : FGBlock (Fin p.n)) (hW : W ∈ (storeAt p c E rho i x).fg.TF)
    (hsrc : SettledPhaseFrame p (storeAt p c E rho i x) m J contested)
    (hZW : FGBlock.Preceq (R_at p c E rho i x).Z W)
    (hlo : (R_at p c E rho i x).lo ≤ (heightView p W).h)
    (hroots : NamedReceiptRootCollisionFree p c E rho) :
    ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s + p.Δ) = true →
      Gen.V2.Duty.HoldsBefore E rho
      (fun nd => ∀ B, FGBlock.Preceq B W → B ∈ nd.st.fg.TF)
      (SA.voteTime p.toParams s + p.Δ) y := by
  have hstrict : u < SA.voteTime p.toParams s + p.Δ :=
    hhead.trans_lt (lt_add_of_pos_right _ p.deltaPos)
  have hlow : timeIdx rho u ≤ V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ) := by
    change (rho.events.filter (fun e => decide (e.time ≤ u))).length ≤
      (rho.events.filter (fun e => decide (e.time < SA.voteTime p.toParams s + p.Δ))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he =>
      decide_eq_true ((of_decide_eq_true he).trans_lt hstrict))
  have hhigh : V2.D.Run.idxBefore rho (SA.voteTime p.toParams s + p.Δ) ≤ timeIdx rho v := by
    change (rho.events.filter (fun e => decide (e.time < SA.voteTime p.toParams s + p.Δ))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ v))).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    exact List.countP_mono_left (fun e _ he =>
      decide_eq_true ((of_decide_eq_true he).le.trans hreceipt))
  intro y hy hAwake
  apply healing_witness_relay (hroots := hroots)
    p c E rho mono crossing hvalid hnr hdelta hsync hx hi
    (hgst.trans hhead) hhor W hW hsrc hZW hlo ?_ y hy hAwake
  intro z hz
  exact healing_settled_frame p c E rho crossing u v m J contested hgst hphase _ z hlow hhigh hz

end AvailableChain.FGSA.Run
end

module
public import AvailableChainFGCompose.Statements.CoreReads
public import AvailableChainPCSAClaims.Statements.Reads
public import AvailableChainFGSA.Proofs.Carrier -- shake: keep (PC erasure injectivity test)

public section
namespace AvailableChain.PCSA.Run
open AvailableChain.SimplexFG
def pcsaCoreReads (p : Params) {In : Type} (c : AppCodec In) :
  FGCompose.FGCoreReads (pcsa p c) p.n (GridCO.State p.n .root) (Wire p.n) (RowWire p.n) :=
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := PCSA.eraseFG
    source := fun nd => PCSA.fgSource p nd.st
    headVote := fun nd s => PCSA.headVote p nd.st s
    finalityHead := fun nd => PCSA.fgBlockOf nd.st (PCSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) =>
          (PCSA.parentFG nd.st N.erase).map (fun P => PCSA.fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | some (.ack _ _ _) => none
      | some (.pc _) => none
      | none => none }
theorem pcsaCoreReads_def (p : Params) {In : Type} (c : AppCodec In) : pcsaCoreReads p c =
  { core := fun nd => ⟨nd.st.base, nd.st.fg, nd.st.proposals, nd.st.rowPool⟩
    erase := PCSA.eraseFG
    source := fun nd => PCSA.fgSource p nd.st
    headVote := fun nd s => PCSA.headVote p nd.st s
    finalityHead := fun nd => PCSA.fgBlockOf nd.st (PCSA.fgHead p nd.st)
    proposalFG := fun nd o => match (toWire p o).decode with
      | some (.block _ N) =>
          (PCSA.parentFG nd.st N.erase).map (fun P => PCSA.fgBlock P N.erase N.rows)
      | some (.vote _ _ _) => none
      | some (.row _ _) => none
      | some (.ack _ _ _) => none
      | some (.pc _) => none
      | none => none } := by
  rfl
theorem pcsa_eraseFG_eq {n : Nat} :
    (PCSA.eraseFG : FGBlock (Fin n) → Block) = FGSA.eraseFG := by
  funext B
  induction B with
  | genesis => rfl
  | node p s r x rs ih =>
    change Block.node (PCSA.eraseFG p) s r (encFGBody x rs) =
      Block.node (FGSA.eraseFG p) s r (encFGBody x rs)
    rw [ih]
theorem pcsa_eventReads_eq_compose {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V P) (x : V) (t : Time) :
    (@cutPred V In P t = @FGCompose.cutPred V In P t) ∧
    afterTicksIdx rho t = FGCompose.afterTicksIdx rho t ∧
    afterTicks E rho t = FGCompose.afterTicks E rho t ∧
    pcsa_preTick E rho x t = FGCompose.preTick E rho x t ∧
    pcsa_postClock E rho x t = FGCompose.postClock E rho x t :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem pcsa_source_mem_TF (p : Params) {In : Type} (c : AppCodec In) {nd : Node p}
    {C : FGBlock (Fin p.n)} (h : (pcsaCoreReads p c).source nd = some C) : C ∈ nd.st.fg.TF := by
  change PCSA.fgSource p nd.st = some C at h
  let rR := p.round (nd.st.slot p) * p.R
  let cand := (pcSnapshotAt nd.st rR).filter (fun cert =>
    rR < cert.slot + p.R && cert.slot ≤ rR && frameActive p nd.st cert)
  change (match bestPC cand with
    | some cert => pickPair (fullTree p nd.st) (fun B => decide (PCSA.eraseFG B = cert.target))
    | none => none) = some C at h
  cases hb : bestPC cand with
  | none => rw [hb] at h; cases h
  | some cert =>
    rw [hb] at h
    change pickPair (fullTree p nd.st)
      (fun B => decide (PCSA.eraseFG B = cert.target)) = some C at h
    unfold pickPair at h
    split at h
    · next hu =>
      cases h
      have hm := (Finset.choose_spec _ _ hu).1
      unfold PCSA.fullTree KitFG.storeFrameView at hm
      exact (Finset.mem_filter.mp hm).1
    · cases h
end AvailableChain.PCSA.Run

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Reach

public section

/-! # Shadow node configurations and AC reachability

The event order and wire checks are unchanged. Only execution and its frame are
shadow execution. No stock node reachability is assumed.
-/

namespace Consensus.Goldilocks.Node

variable {P : Params} {A : NodeAC P}

def Step' (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n) (cfg : Config A)
    (e : Event A) (t' : Time) (cfg' : Config A) : Prop :=
  cfg.time ≤ t' ∧ EventOK t' (Phase.at cfg.time t' cfg.phase) e ∧ WireOK dg e ∧
    cfg'.st = (exec' proposer dg self cfg.st t' e).1 ∧ cfg'.time = t' ∧
      cfg'.phase = e.phaseAfter

def Reachable' (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n) (cfg : Config A)
    (a : A.State := A.initial) : Prop :=
  Relation.ReflTransGen (fun cfg cfg' => ∃ e t', Step' proposer dg self cfg e t' cfg')
    (Config.init A a) cfg

theorem step'_iff (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n) (cfg : Config A)
    (e : Event A) (t' : Time) (cfg' : Config A) :
    Step' proposer dg self cfg e t' cfg' ↔
      cfg.time ≤ t' ∧ EventOK t' (Phase.at cfg.time t' cfg.phase) e ∧ WireOK dg e ∧
        cfg'.st = (exec' proposer dg self cfg.st t' e).1 ∧ cfg'.time = t' ∧
          cfg'.phase = e.phaseAfter := by rfl

theorem reachable'_eq (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n) (a : A.State) :
    Reachable' proposer dg self (a := a) =
      Relation.ReflTransGen (fun cfg cfg' => ∃ e t', Step' proposer dg self cfg e t' cfg')
        (Config.init A a) := by rfl

end Consensus.Goldilocks.Node

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} (proposer : Nat → Fin P.n)
  (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)

/-- The AC part of the node invariant, with payload well-formedness and root provenance
needed to validate an own proposal. The client record is handled by the signed-run supplier. -/
private structure NInv' (v : Fin P.n) (s₀ : A.State) (st : NodeState A) (t : Time) : Prop where
  fg : st.fg.Reachable' A.genesisPayload
  ac : A.ReqPayloadFrom s₀ v →
    ∃ t₀ ≤ t, A.ReachableAtFrom s₀ v st.fg.tree st.ac (frame' st) t₀
  wf : ({ A with initial := s₀ } : NodeAC P).Requirements → ∀ a ∈ st.fg.atts, a.WellFormed
  roots : (P.genesisBlock A.genesisPayload).RootOk dg → ∀ X ∈ st.fg.tree, X.RootOk dg

variable {s₀ : A.State}

private theorem frameIn_store' {st : NodeState A} (hr : st.fg.Reachable' A.genesisPayload) :
    A.FrameIn st.fg.tree (frame' st) := by
  rw [Node.frame'_eq]
  exact ⟨Store.frameOK_toFrame' hr.puSnapshot, fun _ h => by
    rw [Store.toFrame'_tree] at h
    exact h.1⟩

private theorem reachableAt_mono' {U U' : Set A.Blk} (hUU : U ⊆ U')
    {s : A.State} {Φ : A.Frm} {t : Time}
    (h : A.ReachableAtFrom s₀ self U s Φ t) : A.ReachableAtFrom s₀ self U' s Φ t := by
  induction h with
  | init Φ hi hin => exact .init Φ hi ⟨hin.1, hin.2.trans hUU⟩
  | step c _ ht hok ih => exact .step c ih ht ⟨⟨hok.1.1, hok.1.2.trans hUU⟩, hok.2⟩

private theorem NInv'.mono {st : NodeState A} {t t' : Time} (h : NInv' dg self s₀ st t)
    (ht : t ≤ t') : NInv' dg self s₀ st t' :=
  ⟨h.fg, fun hq => (h.ac hq).imp fun _ h => ⟨h.1.trans ht, h.2⟩, h.wf, h.roots⟩

private theorem NInv'.ac' {st : NodeState A} {t : Time} (h : NInv' dg self s₀ st t)
    (s : A.State) (hs : A.ReqPayloadFrom s₀ self →
      ∃ t₀ ≤ t, A.ReachableAtFrom s₀ self st.fg.tree s (frame' st) t₀) :
    NInv' dg self s₀ { st with ac := s } t := by
  refine ⟨h.fg, ?_, h.wf, h.roots⟩
  simpa only [frame'_eq] using hs

private theorem NInv'.acCall {st : NodeState A} {t : Time} (h : NInv' dg self s₀ st t)
    (c : A.Call) (hc : A.CallOK st.fg.tree (frame' st) t c (frame' st)) :
    NInv' dg self s₀ (acCall' self st t c).1 t := by
  rw [acCall'_eq]
  exact h.ac' dg self _ fun hq => by
    obtain ⟨t₀, ht₀, hR⟩ := h.ac hq
    exact ⟨t, le_rfl, .step c hR ht₀ hc⟩

private theorem NInv'.acProposal {st : NodeState A} {t : Time} (h : NInv' dg self s₀ st t) :
    NInv' dg self s₀ (Node.acProposal' st t).1 t := by
  rw [acProposal'_eq]
  exact h.ac' dg self _ fun hq => by
    obtain ⟨t₀, ht₀, hR⟩ := h.ac hq
    exact ⟨t, le_rfl, .step .proposal hR ht₀ ⟨frameIn_store' h.fg, rfl⟩⟩

private theorem NInv'.acToFG {st : NodeState A} {t : Time} (h : NInv' dg self s₀ st t) :
    NInv' dg self s₀ (Node.acToFG' st t).1 t := by
  rw [acToFG'_eq]
  exact h.ac' dg self _ fun hq => by
    obtain ⟨t₀, ht₀, hR⟩ := h.ac hq
    exact ⟨t, le_rfl, .step .toFG hR ht₀ ⟨frameIn_store' h.fg, rfl⟩⟩

private theorem mem_init_tree' {a : A.State} {B : A.Blk}
    (hB : B ∈ (Node.initWith A a).fg.tree) : B = P.genesisBlock A.genesisPayload := by
  change (if B.root = P.genesisRoot then some (P.genesisBlock A.genesisPayload) else none) =
    some B at hB
  split_ifs at hB
  exact (Option.some.inj hB).symm

theorem init_initialFrame' {a : A.State} : A.InitialFrame (frame' (Node.initWith A a)) := by
  rw [frame'_eq]
  simp only [ACInterface.InitialFrame, Store.toFrame'_F]
  refine ⟨Set.ext fun B => ⟨fun hB => ?_, fun hB => ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [Store.toFrame'_tree] at hB
    exact mem_init_tree' hB.1
  · rw [Set.mem_singleton_iff.1 hB, Store.toFrame'_tree]
    refine ⟨?_, .refl⟩
    change (if P.genesisRoot = P.genesisRoot then some (P.genesisBlock A.genesisPayload)
      else none) = some (P.genesisBlock A.genesisPayload)
    simp
  · rfl
  · rfl
  · rfl
  · rfl

end Consensus.Goldilocks.Compose

end

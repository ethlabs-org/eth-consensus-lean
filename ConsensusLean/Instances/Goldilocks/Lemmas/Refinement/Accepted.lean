module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.AcceptanceDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealedSafety
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.OutageSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NonfinalEndpoints
import ConsensusLean.Lemmas.Model.Laws
public import ConsensusLean.Instances.Goldilocks.Refinement.Defs
public import ConsensusLean.Spec.Shape.Accepted
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Transport
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Outage
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Final
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served

public section

/-! # Acceptance assembly with finite guarantee witnesses

The assumptions are fixed before choosing guarantees. The three named coefficient
holes and named supplier leaves are joint obligations, not independent arbitrary
choices. Every endpoint adapter is assembled; this does not prove acceptance.
Do not import into Main/Solution.
The local pattern is a fixed function of Setup's timeout; no legacy consecutive-run
formula or dependence of timeout on the outer gap is imposed here.
-/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- R8, claims C0.1/C0.2/F.2, node outputs_valid. NO PAPER PROOF for
engine/read transport; replacement endpoint: engine_outputValid. -/
theorem accepted_outputValid : (Sys (family S) V).HoldsAlways fun r =>
    ∀ c g, schema.output c = some g → OutputValid r.2 g := by
  exact shape_outputValid V S

/-- R8, claims C0.1/C0.2/F.2, node outputs_nested. NO PAPER PROOF for
engine chain transport; replacement endpoint: engine_nested. -/
theorem accepted_nested : ∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank →
    schema.output c₁ = some g₁ → schema.output c₂ = some g₂ →
    (Sys (family S) V).HoldsAlways fun r => (chainTrace r.2).Nested g₁ g₂ := by
  exact shape_nested V S

/-- R8, claims F.2, node finalized_monotone. NO PAPER PROOF for engine
read transport; replacement endpoint: engine_finalMonotone. -/
theorem accepted_finalMonotone : ∀ g, schema.output .final = some g →
    (Sys (family S) V).HoldsAlways fun r => (chainTrace r.2).Monotone g 0 := by
  exact shape_finalMonotone V S

/-- R7, claims G0.5 and G1.1–G1.5, node final_accountable.
NO PAPER PROOF for held-tree evidence/view and collision transport. Raw
GenesisFresh is not a premise here: the encoding must discharge root separation. -/
theorem accepted_finalAccountable : ∀ g, schema.output .final = some g →
    (Sys (family S) V).Holds (fun _ => True) fun r =>
      (chainTrace r.2).AccountablySafe r.2.ViewIdx r.2.Slashable
        (K S A).params.α g 0 := by
  exact shape_finalAccountable V S (K S A) (by norm_num [Params.standard])

/-- A single reader-conditional final query, with the original engine-scaled latency.
No supplier conclusion is a new premise of Healthy. -/
structure FinalQuery where
  run : (Sys (family S) V).Run
  hn : 1 ≤ Fintype.card V
  index : (K S A).Idx
  gst : Time
  query : Time
  valid : (Sys (family S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  healthy : (Sys (family S) V).Healthy (K S A) gst run
  progress : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) .final index
    ((Sys (family S) V).ready (K S A) gst run) run.2.horizon run
  mature : (Sys (family S) V).heal (K S A) .final index gst run ≤ query
  bounded : query + ((K S A).params.latency .final index : Time) * run.1.Δ ≤ run.2.horizon
  reader : ∃ v, run.2.point.Ready ((Sys (family S) V).cDur (K S A) run) v
    (query + ((K S A).params.latency .final index : Time) * run.1.Δ)

namespace FinalQuery

variable {S A V}

abbrev params (Q : FinalQuery S A V) := S.params (Model.pubOf Q.run.1) Q.hn
noncomputable abbrev trace (Q : FinalQuery S A V) := simTrace S Q.run.2 Q.hn
noncomputable abbrev deadline (Q : FinalQuery S A V) : Time :=
  Q.query + ((K S A).params.latency .final Q.index : Time) * Q.run.1.Δ

end FinalQuery

/-- Operational window witnesses only. The processing field is an OPEN endpoint-specific
transport budget, not acceptance or a freely chosen output delay. Source: workbench b3ca078,
four-anchor-window.md and fixed-timeout-synthesis.md. -/
structure FinalWindowData (Q : FinalQuery S A V) where
  start : Nat
  block : Fin 4 → SA.Blk Q.params.n (List (FG.Att Q.params.n))
  cut : Fin 4 → Nat
  slots : ∀ a, (block a).slot = start + (![0, S.δt - 1, S.δt + 1, S.δt + 3] a)
  proposals : ∀ a, Q.trace.ProposesAt (block a).proposer (cut a) (block a)
  accepted : ∀ a, Q.trace.AcceptAt (block a).proposer (cut a) (block a)
  ready : ∀ a, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
    ((Sys (family S) V).cDur (K S A) Q.run) (block a).proposer (Q.trace.time (cut a))
  fresh : Q.query < Q.trace.time (cut 0)
  ordered : StrictMono cut
  bounded : ∀ a, Q.trace.time (cut a) ≤ Q.deadline
  chain : ∀ a b, a ≤ b → Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (block a) (block b)
  /-- Actual canonical processing before the exact query deadline; deriving sufficient slack
  from the jointly chosen accepted_latency remains OPEN. No acceptance is assumed here. -/
  carrierProcessed : ∀ y, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
    ((Sys (family S) V).cDur (K S A) Q.run) y Q.deadline →
    ∃ j, Q.trace.BlockCallAt y j (block 3) ∧ Q.trace.time j ≤ Q.deadline

namespace FinalWindowData

variable {S A V} {Q : FinalQuery S A V} (W : FinalWindowData S A V Q)

/-- Use the actual last anchor's store, not an independently chosen chain-state map. -/
noncomputable abbrev store := (Q.trace.post (W.cut 3)).fg
noncomputable abbrev state (B : SA.Blk Q.params.n (List (FG.Att Q.params.n))) := W.store.σ B.root
abbrev OnChain (B : SA.Blk Q.params.n (List (FG.Att Q.params.n))) : Prop :=
  Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) B (W.block 3)
abbrev Extends (_W : FinalWindowData S A V Q)
    (B C : SA.Blk Q.params.n (List (FG.Att Q.params.n))) : Prop :=
  Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) B C

/-- An actual entry-creating transition, whether justification or timeout. -/
def Entry (B : SA.Blk Q.params.n (List (FG.Att Q.params.n))) : Prop :=
  W.OnChain B ∧ (W.state B).Th = B.root ∧ (W.state B).ThSlot = B.slot

/-- The actual first crossing after A0, or A0's own newly created entry. -/
def Selected (B : SA.Blk Q.params.n (List (FG.Att Q.params.n))) : Prop :=
  W.Entry B ∧ W.Extends (W.block 0) B ∧
    (B = W.block 0 ∨
      (W.start + 1 ≤ B.slot ∧ B.slot ≤ W.start + (S.δt - 1) ∧
        ∀ D, W.OnChain D → W.Extends (W.block 0) D → W.Extends D B →
          W.start < D.slot → D.slot < B.slot → (W.state D).Th = (W.state (W.block 0)).Th))

/-- No crossing of the inherited entry on the serving parent's chain. -/
def Uncrossed (P : SA.Blk Q.params.n (List (FG.Att Q.params.n))) : Prop :=
  ∀ D, W.Extends (W.block 0) D → W.Extends D P →
    (W.state D).h = (W.state (W.block 0)).h ∧ (W.state D).Th = (W.state (W.block 0)).Th

/-- Quorum counts identities once, including previously credited rows. -/
def InheritedProgress : Prop :=
  ∀ P, (W.block 1).parent = some P.root → W.Extends (W.block 0) P →
    (W.state (W.block 0)).ThSlot < W.start → W.Uncrossed P →
    ∃ ids : Finset (Fin Q.params.n), Q.params.toParams.fg.q ≤ ids.card ∧
      ∀ x ∈ ids, x ∈ (W.state P).prog ∨
        ∃ a ∈ (Q.trace.state (W.block 1).proposer (W.cut 1)).fg.atts,
          a.val = x ∧ a.WellFormed ∧ (W.state P).validAtt a ∧
          a.h = (W.state P).h ∧ a.T = (W.state P).Th

/-- Only the selected first descendant has the d−2 exposure bound. -/
def FirstCrossing : Prop :=
  ∃ B, W.Selected B ∧
    (B = W.block 0 ∨
      (B.slot ≤ W.start + (S.δt - 1) ∧ W.start + (S.δt - 1) - B.slot ≤ S.δt - 2))

/-- A justification on the surviving chain is distinct from a timeout crossing. -/
def JustifiedBy (B : SA.Blk Q.params.n (List (FG.Att Q.params.n))) (v : Nat) : Prop :=
  ∃ D, W.OnChain D ∧ W.Extends B D ∧ D.slot ≤ v ∧
    (W.state D).J = B.root ∧ (W.state D).hj = (W.state B).h

open Classical in
/-- Selected entry or its actual bound successor, at the designated exposing anchor.
An arbitrary no-timeout entry is deliberately not admitted by this domain. -/
def Protected (B : SA.Blk Q.params.n (List (FG.Att Q.params.n))) (e : Nat) : Prop :=
  (W.Selected B ∧ e = if B = W.block 0 then W.start else W.start + (S.δt - 1)) ∨
  (∃ D, W.Selected D ∧ W.Entry B ∧ W.Extends D B ∧
    (W.state B).J = D.root ∧ (W.state B).bound ∧
    B.slot ≤ W.start + (S.δt + 1) ∧
    e = if B.slot ≤ W.start + (S.δt - 1) then W.start + (S.δt - 1)
      else W.start + (S.δt + 1))

/-- Exact target rows with actual signing provenance; prior matching reports count.
Timing is only in this quorum branch, never imposed on already-justified entries.
The pair is tested against the actual parent, and identities are not multiplied. -/
def TargetRows (B P : SA.Blk Q.params.n (List (FG.Att Q.params.n))) (e : Nat) (a : Fin 4) : Prop :=
  (W.state P).h = (W.state B).h ∧ (W.state P).Th = B.root ∧
  ∃ ids : Finset (Fin Q.params.n), Q.params.toParams.fg.q ≤ ids.card ∧
    ∀ x ∈ ids, x ∈ honestKeys S Q.run.2 ∧ ∃ row j,
      Q.trace.SignAt x j row ∧ row.val = x ∧ row.h = (W.state B).h ∧ row.T = B.root ∧
      row.timeout = false ∧ row.WellFormed ∧ (W.state P).validAtt row ∧
      Q.trace.time j ≤ Q.params.ts e + 6 * Q.params.Δ ∧
      Q.params.ts e + 7 * Q.params.Δ ≤ Q.deadline ∧
      ((x ∈ (W.state P).target ∧
          ((W.state B).bound → x ∈ (W.state P).fin (W.state B).hj ∨
            (W.state B).hj ≤ (W.state P).hF)) ∨
        (row ∈ (Q.trace.state (W.block a).proposer (W.cut a)).fg.atts ∧
          ∃ k, Q.trace.ProcessAttAt (W.block a).proposer k row ∧ k < W.cut a ∧
            Q.trace.time k < Q.params.ts e + 7 * Q.params.Δ)) ∧
      ((W.state B).bound →
        row.fin = some ((W.state B).hj, (W.state B).J) ∧
        (((W.state B).hj, (W.state B).J) ∈ (W.state P).pending ∨
          (W.state B).hj ≤ (W.state P).hF))

/-- OPEN stable-entry normalization, prior-report/dedup and mandatory pool validity supplier.
No-timeout is local and must be discharged by the bounded-crossing argument. -/
def RowSupply : Prop :=
  ∀ B e, W.Protected B e → ∀ a : Fin 4,
    (e + 2 = (W.block a).slot ∨ (B = W.block 0 ∧ a = 1)) →
    ∀ P, (W.block a).parent = some P.root → W.Extends B P →
      (∀ D, W.Extends B D → W.Extends D P →
        (W.state D).h = (W.state B).h ∨ W.JustifiedBy B D.slot) →
      W.JustifiedBy B P.slot ∨ W.TargetRows B P e a

open Classical in
/-- Justification creates the actual bound successor. The birth-s branch permits w=1;
only the strictly post-A0 crossing has w≥2. Earlier successor justification finalizes B. -/
def BoundedCrossings : Prop :=
  ∃ B C, W.Selected B ∧ W.JustifiedBy B (W.start + (S.δt + 1)) ∧
    W.Entry C ∧ W.Extends B C ∧ (W.state C).J = B.root ∧ (W.state C).bound ∧
    W.start + (if B = W.block 0 then 1 else 2) ≤ C.slot ∧
    C.slot ≤ W.start + (S.δt + 1) ∧
    (let v := if C.slot ≤ W.start + (S.δt - 1) then W.start + (S.δt + 1)
      else W.start + (S.δt + 3)
     ∀ D, W.OnChain D → W.Extends C D → D.slot < v →
       (W.state D).h = (W.state C).h ∨ (W.state B).h ≤ (W.state D).hF) ∧
    ∃ F, W.store.blocks (W.state (W.block 3)).F = some F ∧ W.Extends B F

/-- Actual cache acceptance and persistence at the original endpoint, not mere delivery. -/
def CacheCoverage : Prop :=
  ∀ y t j, Q.deadline ≤ t → t ≤ Q.run.2.horizon →
    Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
      ((Sys (family S) V).cDur (K S A) Q.run) y t → Regimes.CutAfter Q.trace j t →
    W.Extends (W.block 0) (Q.trace.state y j).fg.F

end FinalWindowData

private theorem final_node_requirements (Q : FinalQuery S A V) :
    (goldilocksNode Q.params (S.ro _)).Requirements := by
  have h := SA.interface_requirements Q.params (List (FG.Att Q.params.n)) (S.ro _)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid _ _ _⟩

private theorem final_fg_run (Q : FinalQuery S A V) :
    FGLocalRun (goldilocksNode Q.params (S.ro _)).genesisPayload (honestKeys S Q.run.2)
      (Q.trace.HonestBlocks (honestKeys S Q.run.2)) Q.trace.projFG := by
  have hr := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  exact Compose.fg_projection _ _ _ _ _ _ _ (final_node_requirements S A V Q)
    hr.genesis_root_ok hr.toLocalRun
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)

private theorem final_anchor_post (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    (a : Fin 4) :
    Q.trace.post (W.cut a) = Q.trace.state (W.block a).proposer (W.cut a + 1) := by
  exact (Q.trace.state_succ_of_call (W.accepted a)).symm

private theorem final_store_reachable (Q : FinalQuery S A V) (W : FinalWindowData S A V Q) :
    W.store.Reachable (goldilocksNode Q.params (S.ro _)).genesisPayload := by
  have hr := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  change (Q.trace.post (W.cut 3)).fg.Reachable _
  rw [final_anchor_post S A V Q W 3]
  exact Compose.fg_reachable hr.toLocalRun (W.ready 3).1 _

private theorem final_anchor_held (Q : FinalQuery S A V) (W : FinalWindowData S A V Q) :
    W.block 3 ∈ W.store.tree := by
  have hr := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hon := (hr.cutLaw _ (W.ready 3).1 _ _ (W.accepted 3)).2.1
  change W.block 3 ∈ (Q.trace.post (W.cut 3)).fg.tree
  rw [(Store.tree_grows _ _ _ _ (Compose.fg_reachable hr.toLocalRun (W.ready 3).1 _)).1 _ _ hon]
  exact Set.mem_insert _ _

private theorem final_ancestry_local (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    {B C : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (h : W.Extends B C) (hC : C ∈ W.store.tree) : W.store.Anc B C := by
  have hr := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hnc := noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision
  have coh := Compose.honest_blocks_coherent hr.toLocalRun hnc
  have hs : W.store.tree ⊆ Q.trace.HonestBlocks (honestKeys S Q.run.2) := by
    intro X hX
    refine ⟨(W.block 3).proposer, (W.ready 3).1, W.cut 3 + 1, ?_⟩
    change X ∈ (Q.trace.post (W.cut 3)).fg.tree at hX
    rwa [final_anchor_post S A V Q W 3] at hX
  have hg := (Store.accepted_tree _ _ _ _ (final_store_reachable S A V Q W)).2.2.2
  induction h with
  | refl => exact .refl
  | @tail Y C hBY hYC ih =>
    rcases (hg C hC).cases_tail with he | ⟨Z, _, hZC⟩
    · cases he
      cases hYC.2.2
    · have he : Z = Y := coh.1 (hs hZC.1) hYC.1
        (Option.some.inj (hZC.2.2.symm.trans hYC.2.2))
      subst he
      exact (ih hZC.1).tail hZC

private theorem final_chain_held (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    {B : SA.Blk Q.params.n (List (FG.Att Q.params.n))} (hB : W.OnChain B) :
    B ∈ W.store.tree := by
  by_cases he : B = W.block 3
  · exact he ▸ final_anchor_held S A V Q W
  · exact (Anc.mem (final_ancestry_local S A V Q W hB (final_anchor_held S A V Q W)) he).1

private theorem final_chain_step (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    {B C : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hC : W.OnChain C) (hp : C.parent = some B.root) :
    Q.params.toParams.fg.stateTransition (W.state B) C.fgView = some (W.state C) := by
  have hC := final_chain_held S A V Q W hC
  have hr := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hfg := final_fg_run S A V Q
  have he : W.store = Q.trace.projFG.store (W.block 3).proposer (W.cut 3 + 1) := by
    change (Q.trace.post (W.cut 3)).fg = _
    rw [final_anchor_post S A V Q W 3]
    exact (congrArg Prod.fst (Compose.projFG_state hr.toLocalRun (W.ready 3).1 _)).symm
  change Q.params.toParams.fg.stateTransition (W.store.σ B.root) C.fgView = some (W.store.σ C.root)
  rw [he] at hC ⊢
  exact Store.step_σ hfg (W.ready 3).1 hC hp

private theorem final_fold_progress {n : Nat} {σ : FG.ChainState n} {atts : List (FG.Att n)}
    {v : Fin n} (h : v ∈ σ.prog ∨ ∃ a ∈ atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th) :
    v ∈ (atts.foldl FG.ChainState.processAtt σ).prog := by
  induction atts generalizing σ with
  | nil => exact h.resolve_right (by simp)
  | cons a as ih =>
    obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq σ [a]
    have hh : (σ.processAtt a).h = σ.h := by simpa using congrArg FG.ChainState.h he
    have hT : (σ.processAtt a).Th = σ.Th := by simpa using congrArg FG.ChainState.Th he
    have key : σ.prog ⊆ (σ.processAtt a).prog ∧
        (a.h = σ.h ∧ a.T = σ.Th → a.val ∈ (σ.processAtt a).prog) := by
      unfold FG.ChainState.processAtt
      rcases hf : a.fin with _ | q <;> dsimp only <;> split_ifs <;> simp_all
    rw [List.foldl_cons]
    refine ih ?_
    rw [hh, hT]
    rcases h with h | ⟨b, hb, hbv, hbh, hbT⟩
    · exact Or.inl (key.1 h)
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact Or.inl (hbv ▸ key.2 ⟨hbh, hbT⟩)
      · exact Or.inr ⟨b, hb, hbv, hbh, hbT⟩

private theorem final_step_entry {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
    {B : FG.FGBlock gp.n} (h : gp.stateTransition σ B = some σ') :
    (σ'.h = σ.h ∧ σ'.Th = σ.Th ∧ σ'.ThSlot = σ.ThSlot ∧
      (∀ v, (v ∈ σ.prog ∨ ∃ a ∈ B.atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th) →
        v ∈ σ'.prog) ∧ ¬ (gp.q ≤ σ'.prog.card ∧ σ.ThSlot + gp.δt ≤ B.slot)) ∨
    (σ'.h = σ.h + 1 ∧ σ'.Th = B.root ∧ σ'.ThSlot = B.slot) := by
  obtain ⟨_, rfl⟩ := gp.stateTransition_eq_some.1 h
  have hP := fun v (hv : v ∈ σ.prog ∨ ∃ a ∈ B.atts, a.val = v ∧ a.h = σ.h ∧ a.T = σ.Th) =>
    final_fold_progress (σ := { σ with s := B.slot }) hv
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he] at hP ⊢
  obtain ⟨F, hF, σ₁, rfl, _, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨_, he'⟩ | ⟨_, _, he'⟩ | ⟨_, hto, he'⟩ <;> rw [he']
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl, hP, hto⟩

private theorem final_entry_origin (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    {B : SA.Blk Q.params.n (List (FG.Att Q.params.n))} (hB : B ∈ W.store.tree) :
    ∃ E ∈ W.store.tree, E.root = (W.state B).Th ∧ E.slot = (W.state B).ThSlot ∧
      W.store.Anc E B := by
  have hreach := final_store_reachable S A V Q W
  have hg := (Store.accepted_tree _ _ _ _ hreach).2.2.2 B hB
  have hr := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have he : W.store = Q.trace.projFG.store (W.block 3).proposer (W.cut 3 + 1) := by
    change (Q.trace.post (W.cut 3)).fg = _
    rw [final_anchor_post S A V Q W 3]
    exact (congrArg Prod.fst (Compose.projFG_state hr.toLocalRun (W.ready 3).1 _)).symm
  have hstep {Y Z} (hYZ : ParentIn W.store.tree Y Z) :=
    Store.step_σ (final_fg_run S A V Q) (W.ready 3).1 (he ▸ hYZ.2.1) hYZ.2.2
  induction hg with
  | refl =>
    have hz := Store.σ_genesis (final_fg_run S A V Q) (W.ready 3).1 (W.cut 3 + 1)
    rw [← he] at hz
    refine ⟨_, (Store.accepted_tree _ _ _ _ hreach).2.2.1, ?_, ?_, .refl⟩
    · exact congrArg FG.ChainState.Th hz.symm
    · exact congrArg FG.ChainState.ThSlot hz.symm
  | @tail Y Z hGY hYZ ih =>
    have ht := hstep hYZ
    rw [← he] at ht
    rcases final_step_entry ht with ⟨_, hT, hs, _⟩ | ⟨_, hT, hs⟩
    · obtain ⟨E, hE, heT, hes, hEY⟩ := ih hYZ.1
      exact ⟨E, hE, heT.trans hT.symm, hes.trans hs.symm, hEY.tail hYZ⟩
    · exact ⟨Z, hYZ.2.1, hT.symm, hs.symm, .refl⟩

private theorem final_chain_height (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    {B C : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (h : W.Extends B C) (hC : W.OnChain C) :
    (W.state B).h ≤ (W.state C).h ∧
      ((W.state C).h = (W.state B).h → (W.state C).Th = (W.state B).Th) := by
  induction h with
  | refl => exact ⟨le_rfl, fun _ => rfl⟩
  | @tail Y C hBY hYC ih =>
    have hy := ih ((Relation.ReflTransGen.single hYC).trans hC)
    rcases final_step_entry (final_chain_step S A V Q W hC hYC.2.2) with
      ⟨hh, ht, _⟩ | ⟨hh, _, _⟩
    · exact ⟨hh ▸ hy.1, fun he => ht.trans (hy.2 (hh.symm.trans he))⟩
    · exact ⟨by omega, fun _ => by omega⟩

private theorem final_chain_stable (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    {B C : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (h : W.Extends B C) (hC : W.OnChain C) (hh : (W.state C).h = (W.state B).h) :
    (W.state C).ThSlot = (W.state B).ThSlot ∧ (W.state B).prog ⊆ (W.state C).prog := by
  induction h with
  | refl => exact ⟨rfl, subset_rfl⟩
  | @tail Y C hBY hYC ih =>
    have hY3 := (Relation.ReflTransGen.single hYC).trans hC
    have hy := (final_chain_height S A V Q W hBY hY3).1
    rcases final_step_entry (final_chain_step S A V Q W hC hYC.2.2) with
      ⟨he, _, hs, hp, _⟩ | ⟨he, _, _⟩
    · obtain ⟨hs', hp'⟩ := ih hY3 (by omega)
      exact ⟨hs.trans hs', fun v hv => hp v (Or.inl (hp' hv))⟩
    · omega

private theorem final_chain_row (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    {X P : SA.Blk Q.params.n (List (FG.Att Q.params.n))} {row : FG.Att Q.params.n}
    (hXP : W.Extends X P) (hP : W.OnChain P) (hx : row ∈ X.fgPayload)
    (hh : row.h = (W.state P).h) (hT : row.T = (W.state P).Th) :
    row.val ∈ (W.state P).prog := by
  have hr := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have coh := Compose.honest_blocks_coherent hr.toLocalRun
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
  have hX3 := hXP.trans hP
  have hXt := final_chain_held S A V Q W hX3
  have hreach := final_store_reachable S A V Q W
  rcases ((Store.accepted_tree _ _ _ _ hreach).2.2.2 X hXt).cases_tail with
    he | ⟨Y, _, hYX⟩
  · cases he
    simp [Params.genesisBlock] at hx
  · have hs : W.store.tree ⊆ Q.trace.HonestBlocks (honestKeys S Q.run.2) := by
      intro Z hZ
      refine ⟨(W.block 3).proposer, (W.ready 3).1, W.cut 3 + 1, ?_⟩
      change Z ∈ (Q.trace.post (W.cut 3)).fg.tree at hZ
      rwa [final_anchor_post S A V Q W 3] at hZ
    have hYX' : W.Extends Y X := .single ⟨hs hYX.1, hs hYX.2.1, hYX.2.2⟩
    have ht := final_chain_step S A V Q W hX3 hYX.2.2
    obtain ⟨⟨_, hv⟩, _⟩ := Q.params.toParams.fg.stateTransition_eq_some.1 ht
    have hrow : row.h ≤ (W.state Y).h := by
      rcases (hv row hx).2 with ⟨h, _⟩ | ⟨_, _, _, _, h⟩ <;> exact h.le
    have hYXh := (final_chain_height S A V Q W hYX' hX3).1
    have hXPh := (final_chain_height S A V Q W hXP hP).1
    have hXeq : (W.state X).h = (W.state P).h := by omega
    have hYeq : (W.state Y).h = (W.state P).h := by omega
    have hYT := (final_chain_height S A V Q W (hYX'.trans hXP) hP).2 hYeq.symm
    have hcredit : row.val ∈ (W.state X).prog := by
      rcases final_step_entry ht with ⟨_, _, _, hp, _⟩ | ⟨he, _⟩
      · exact hp _ (Or.inr ⟨row, hx, rfl, hh.trans hYeq.symm, hT.trans hYT⟩)
      · omega
    exact (final_chain_stable S A V Q W hXP hP hXeq.symm).2 hcredit

private theorem final_first_change (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    (hchange : (W.state (W.block 1)).h ≠ (W.state (W.block 0)).h) : W.FirstCrossing := by
  classical
  let pred (n : Nat) := ∃ B, W.Extends (W.block 0) B ∧ W.Extends B (W.block 1) ∧
    B.slot = n ∧ (W.state B).h ≠ (W.state (W.block 0)).h
  have hex : ∃ n, pred n := ⟨_, W.block 1, W.chain 0 1 (by decide), .refl, rfl, hchange⟩
  obtain ⟨B, hAB, hB1, hslot, hBh⟩ := Nat.find_spec hex
  have hB3 : W.OnChain B := hB1.trans (W.chain 1 3 (by decide))
  have hr := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have coh := Compose.honest_blocks_coherent hr.toLocalRun
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
  have hne : W.block 0 ≠ B := by rintro rfl; exact hBh rfl
  obtain ⟨P, hAP, hPB⟩ := hAB.cases_tail.resolve_left (Ne.symm hne)
  have hPlt : P.slot < B.slot := coh.2 _ hPB.1 _ hPB.2.1 hPB.2.2
  have hPh : (W.state P).h = (W.state (W.block 0)).h := by
    by_contra hn
    have hp : pred P.slot := ⟨P, hAP, (Relation.ReflTransGen.single hPB).trans hB1, rfl, hn⟩
    have := Nat.find_min' hex hp
    omega
  have hentry : (W.state B).Th = B.root ∧ (W.state B).ThSlot = B.slot := by
    rcases final_step_entry (final_chain_step S A V Q W hB3 hPB.2.2) with h | h
    · exact False.elim (hBh (h.1.trans hPh))
    · exact h.2
  have hs0 : (W.block 0).slot = W.start := by simpa using W.slots 0
  have hs1 : (W.block 1).slot = W.start + (S.δt - 1) := by simpa using W.slots 1
  have hlo := (hAB.slot_le coh).2 hne
  have hhi := (hB1.slot_le coh).1
  refine ⟨B, ⟨⟨hB3, hentry⟩, hAB, Or.inr ⟨by omega, by omega, ?_⟩⟩,
    Or.inr ⟨by omega, by omega⟩⟩
  intro D hD3 hAD hDB _ hDBslot
  have hDh : (W.state D).h = (W.state (W.block 0)).h := by
    by_contra hn
    have hd : pred D.slot := ⟨D, hAD, hDB.trans hB1, rfl, hn⟩
    have := Nat.find_min' hex hd
    omega
  exact (final_chain_height S A V Q W hAD hD3).2 hDh

private theorem final_own_rows (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    (a : Fin 4) : ∃ P,
      (W.block a).parent = some P.root ∧
      P ∈ (Q.trace.state (W.block a).proposer (W.cut a)).fg.tree ∧
      (W.block a).fgPayload =
        (Q.trace.state (W.block a).proposer (W.cut a)).fg.proposalAttestations P := by
  have hr := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have hc := W.accepted a
  rcases Compose.blockCall_cases hr.toLocalRun (W.ready a).1 hc with hg |
    ⟨j, x, hi, hg, hpr, d, p, hdp, hB, _, _, _, hfg⟩
  · have hp := (W.proposals a).1.2
    have hz := (hg.2.1 0 (List.length_pos_iff.mpr hg.1)).2.2.2.1
    simp only [Nat.add_zero] at hz
    exact False.elim (hp hz)
  · have hp : (W.block a).parent = some d.head.root := by rw [hB]; rfl
    have hpay : (W.block a).fgPayload =
        (Q.trace.state (W.block a).proposer (W.cut a)).fg.proposalAttestations d.head := by
      rw [hfg, hB]; rfl
    obtain ⟨cfg, hreach, hst, hstep⟩ := Compose.group_step hr.toLocalRun (W.ready a).1 hg
    have hhead := Compose.honest_block_accepted _ _ _ (final_node_requirements S A V Q)
      hr.genesis_root_ok cfg _ _ x hreach hstep hpr d p (by rw [hst]; exact hdp)
    refine ⟨d.head, hp, ?_, hpay⟩
    rw [hfg]
    simpa only [hst, Node.acProposal, Node.tickStep, Node.acCall] using hhead.1

private theorem final_pool_row (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    (a : Fin 4) {P : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hP : W.OnChain P)
    (hPt : P ∈ (Q.trace.state (W.block a).proposer (W.cut a)).fg.tree)
    (hpay : (W.block a).fgPayload =
      (Q.trace.state (W.block a).proposer (W.cut a)).fg.proposalAttestations P)
    {row : FG.Att Q.params.n}
    (hr : row ∈ (Q.trace.state (W.block a).proposer (W.cut a)).fg.atts)
    (hv : (W.state P).validAtt row) (hh : row.h = (W.state P).h)
    (hT : row.T = (W.state P).Th) :
    row.val ∈ (W.state P).prog ∨ row ∈ (W.block a).fgPayload := by
  classical
  have run := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have he a i : Q.trace.projFG.store (W.block a).proposer i =
      (Q.trace.state (W.block a).proposer i).fg :=
    congrArg Prod.fst (Compose.projFG_state run.toLocalRun (W.ready a).1 i)
  have hlast : Q.trace.projFG.store (W.block 3).proposer (W.cut 3 + 1) = W.store := by
    rw [he, ← final_anchor_post S A V Q W 3]
  have hσ := Store.σ_eq_of_held (final_fg_run S A V Q) (W.ready a).1 (W.ready 3).1
    (he a (W.cut a) ▸ hPt) (hlast ▸ final_chain_held S A V Q W hP)
  rw [he, hlast] at hσ
  by_cases hon : (Q.trace.state (W.block a).proposer (W.cut a)).fg.OnChain P row
  · obtain ⟨X, _, hXP, hx⟩ := hon
    have hs : (Q.trace.state (W.block a).proposer (W.cut a)).fg.tree ⊆
        Q.trace.HonestBlocks (honestKeys S Q.run.2) := fun X hX =>
      ⟨_, (W.ready a).1, W.cut a, hX⟩
    exact Or.inl (final_chain_row S A V Q W (Anc.mono hs hXP) hP hx hh hT)
  · right
    rw [hpay]
    exact List.mem_filter.mpr ⟨hr, by simpa only [decide_eq_true_eq, hσ] using And.intro hv hon⟩

/-- Assemble independently produced finite anchors and carrier processing.
Every budget and actual event remains explicit; eligible duties alone do not suffice. -/
theorem final_window_of_production (Q : FinalQuery S A V) (start : Nat)
    (block : Fin 4 → SA.Blk Q.params.n (List (FG.Att Q.params.n))) (cut : Fin 4 → Nat)
    (slots : ∀ a, (block a).slot = start + (![0, S.δt - 1, S.δt + 1, S.δt + 3] a))
    (proposals : ∀ a, Q.trace.ProposesAt (block a).proposer (cut a) (block a))
    (accepted : ∀ a, Q.trace.AcceptAt (block a).proposer (cut a) (block a))
    (ready : ∀ a, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
      ((Sys (family S) V).cDur (K S A) Q.run) (block a).proposer (Q.trace.time (cut a)))
    (fresh : Q.query < Q.trace.time (cut 0)) (ordered : StrictMono cut)
    (bounded : ∀ a, Q.trace.time (cut a) ≤ Q.deadline)
    (chain : ∀ a b, a ≤ b → Anc (Q.trace.HonestBlocks (honestKeys S Q.run.2)) (block a) (block b))
    (carrier : ∀ y, Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
      ((Sys (family S) V).cDur (K S A) Q.run) y Q.deadline →
      ∃ j, Q.trace.BlockCallAt y j (block 3) ∧ Q.trace.time j ≤ Q.deadline) :
    Nonempty (FinalWindowData S A V Q) :=
  ⟨⟨start, block, cut, slots, proposals, accepted, ready, fresh, ordered, bounded, chain, carrier⟩⟩

/-- OPEN extraction and endpoint budget; four-anchor-window.md / fixed-timeout-synthesis.md
at workbench b3ca078. Synthesizing accepted_latency must leave enough time for actual carrier
processing by the exact engine-scaled endpoint. No numeric output delay is invented. -/
theorem final_window_extract (Q : FinalQuery S A V) : Nonempty (FinalWindowData S A V Q) := by
  sorry

/-- OPEN inherited progress, with no lower bound on inherited birth. Paper: workbench b3ca078,
four-anchor-window.md and fixed-timeout-synthesis.md, inherited-entry bootstrap. -/
theorem final_inherited_progress (Q : FinalQuery S A V) (W : FinalWindowData S A V Q) :
    W.InheritedProgress := by
  sorry

/-- Conditional first crossing, justification OR timeout; exposure d−2 applies only to the
first post-A0 descendant. Paper: workbench 501e66f, fixed-timeout-synthesis.md, supplier 1.
InheritedProgress remains an explicit local input, not a new Healthy premise. -/
theorem final_first_crossing (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    (progress : W.InheritedProgress) : W.FirstCrossing := by
  classical
  have h03 := W.chain 0 3 (by decide)
  have h13 := W.chain 1 3 (by decide)
  have h01 := W.chain 0 1 (by decide)
  have hs0 : (W.block 0).slot = W.start := by simpa using W.slots 0
  have hs1 : (W.block 1).slot = W.start + (S.δt - 1) := by simpa using W.slots 1
  have run := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have coh := Compose.honest_blocks_coherent run.toLocalRun
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
  have reach := final_store_reachable S A V Q W
  obtain ⟨E, hE, hEr, hEs, hE0⟩ :=
    final_entry_origin S A V Q W (final_chain_held S A V Q W h03)
  by_cases he : E = W.block 0
  · subst E
    exact ⟨W.block 0, ⟨⟨h03, hEr.symm, hEs.symm⟩, .refl, Or.inl rfl⟩, Or.inl rfl⟩
  have hbirth : (W.state (W.block 0)).ThSlot < W.start := by
    have hc := (Store.accepted_tree _ _ _ _ reach).2.1
    have := (hE0.slot_le hc).2 he
    omega
  apply final_first_change S A V Q W
  intro hsame
  have hne : W.block 1 ≠ W.block 0 := by
    intro he
    have hd := A.timeout
    rw [he] at hs1
    omega
  obtain ⟨P, h0P, hP1⟩ := h01.cases_tail.resolve_left hne
  have hP3 : W.OnChain P := (Relation.ReflTransGen.single hP1).trans h13
  have hlo := (final_chain_height S A V Q W h0P hP3).1
  have hhi := (final_chain_height S A V Q W (.single hP1) h13).1
  have hPh : (W.state P).h = (W.state (W.block 0)).h := by omega
  have huncrossed : W.Uncrossed P := by
    intro D h0D hDP
    have hD3 := hDP.trans hP3
    have hlo := (final_chain_height S A V Q W h0D hD3).1
    have hhi := (final_chain_height S A V Q W hDP hP3).1
    have hh : (W.state D).h = (W.state (W.block 0)).h := by omega
    exact ⟨hh, (final_chain_height S A V Q W h0D hD3).2 hh⟩
  obtain ⟨ids, hq, hid⟩ := progress P hP1.2.2 h0P hbirth huncrossed
  obtain ⟨P', hp', hPt, hpay⟩ := final_own_rows S A V Q W 1
  have heP : P' = P := coh.1
    ⟨_, (W.ready 1).1, W.cut 1, hPt⟩ hP1.1
    (Option.some.inj (hp'.symm.trans hP1.2.2))
  subst P'
  rcases final_step_entry (final_chain_step S A V Q W h13 hP1.2.2) with
    ⟨_, _, _, hcredit, hnot⟩ | ⟨he, _⟩
  · apply hnot
    refine ⟨hq.trans (Finset.card_le_card ?_), ?_⟩
    · intro x hx
      apply hcredit
      rcases hid x hx with hx | ⟨row, hr, hv, _, hvalid, hh, hT⟩
      · exact Or.inl hx
      · rcases final_pool_row S A V Q W 1 hP3 hPt hpay hr hvalid hh hT with hc | hi
        · exact Or.inl (hv ▸ hc)
        · exact Or.inr ⟨row, hi, hv, hh, hT⟩
    · have hb := (final_chain_stable S A V Q W h0P hP3 hPh).1
      change (W.state P).ThSlot + S.δt ≤ (W.block 1).slot
      omega
  · omega

/-- OPEN exact-entry rows, including coherent prior reports and dedup; paper workbench b3ca078,
four-anchor-window.md / fixed-timeout-synthesis.md. Only designated protected entries qualify.
Deriving normalization and prior-report history from Healthy and the finite canonical simulation
remains OPEN; these conclusions are not assumed in the window context. -/
theorem final_row_supply (Q : FinalQuery S A V) (W : FinalWindowData S A V Q) :
    W.RowSupply := by
  sorry

private theorem final_chain_final_height (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    {B C : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hBC : W.Extends B C) (hC : W.OnChain C) : (W.state B).hF ≤ (W.state C).hF := by
  induction hBC with
  | refl => exact le_rfl
  | @tail P C hBP hPC ih =>
    have hP3 := (Relation.ReflTransGen.single hPC).trans hC
    obtain ⟨c, _, _, _, hc⟩ := Store.chain_state_of_chain _ _ _ _
      (final_store_reachable S A V Q W) P (final_chain_held S A V Q W hP3)
    exact (ih hP3).trans
      (FG.height_step _ _ _ _ _ hc (final_chain_step S A V Q W hC hPC.2.2)).2.2.1

private theorem final_root_heights (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    {D : SA.Blk Q.params.n (List (FG.Att Q.params.n))} (hD : D ∈ W.store.tree) :
    (W.state ((W.store.blocks (W.state D).F).getD D)).h ≥ (W.state D).hF ∧
    ∀ p ∈ (W.state D).pending, ∃ E ∈ W.store.tree,
      E.root = p.2 ∧ (W.state E).h = p.1 := by
  have reach := final_store_reachable S A V Q W
  have hg := (Store.accepted_tree _ _ _ _ reach).2.2.2 D hD
  have run := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have he : Q.trace.projFG.store (W.block 3).proposer (W.cut 3 + 1) = W.store := by
    change (Q.trace.projFG.state _ _).1 = _
    rw [Compose.projFG_state run.toLocalRun (W.ready 3).1,
      ← final_anchor_post S A V Q W 3]
  induction hg with
  | refl =>
    have hz := Store.σ_genesis (final_fg_run S A V Q) (W.ready 3).1 (W.cut 3 + 1)
    rw [he] at hz
    change _ ≥ (W.store.σ Q.params.genesisRoot).hF ∧
      ∀ p ∈ (W.store.σ Q.params.genesisRoot).pending, _
    rw [hz]
    exact ⟨Nat.zero_le _, by simp [FG.ChainState.init]⟩
  | @tail P D hGP hPD ih =>
    obtain ⟨ihF, ihp⟩ := ih hPD.1
    have ht := Store.step_σ (final_fg_run S A V Q) (W.ready 3).1
      (he ▸ hPD.2.1) hPD.2.2
    rw [he] at ht
    obtain ⟨_, ht⟩ := Q.params.toParams.fg.stateTransition_eq_some.1 ht
    obtain ⟨f, p, t, hf⟩ := FG.ChainState.foldl_processAtt_eq
      { W.state P with s := D.slot } D.fgPayload
    change Q.params.toParams.fg.heightEvents
      { D.fgPayload.foldl FG.ChainState.processAtt { W.state P with s := D.slot }
        with L := D.root } = W.state D at ht
    rw [hf] at ht
    obtain ⟨F, hF, σ₁, rfl, hchoice, hcases⟩ := Q.params.toParams.fg.heightEvents_cases
      { W.state P with s := D.slot, L := D.root, fin := f, prog := p, target := t }
    have hFbound : ∀ X, (W.state ((W.store.blocks F).getD X)).h ≥ hF := by
      intro X
      rcases hchoice with ⟨rfl, rfl⟩ | ⟨hm, _⟩
      · obtain ⟨E, hE, hEr, _⟩ := (Store.entry_state_of_source _ _ _ _ reach P hPD.1).2.1
        have hlookup : W.store.blocks (W.state P).F = some E := by
          rw [← hEr]; exact hE
        change (W.state ((W.store.blocks (W.state P).F).getD X)).h ≥ _
        rw [hlookup] at ihF ⊢
        exact ihF
      · obtain ⟨E, hE, hEr, hEh⟩ := ihp _ hm
        change E.root = F at hEr
        change (W.state E).h = hF at hEh
        have hlookup : W.store.blocks F = some E := by rw [← hEr]; exact hE
        simpa only [hlookup, Option.getD_some, hEh] using (le_rfl : hF ≤ hF)
    have hold : ∀ q ∈ (W.state P).pending.filter (fun q => hF < q.1),
        ∃ E ∈ W.store.tree, E.root = q.2 ∧ (W.state E).h = q.1 :=
      fun q hq => ihp q (List.mem_of_mem_filter hq)
    rcases hcases with ⟨_, hevent⟩ | ⟨_, _, hevent⟩ | ⟨_, _, hevent⟩
    all_goals rw [hevent] at ht
    · have hTh : ∃ E ∈ W.store.tree, E.root = (W.state P).Th ∧
          (W.state E).h = (W.state P).h := by
        obtain ⟨E, hE, hr, _, hh, _⟩ :=
          (Store.entry_state_of_source _ _ _ _ reach P hPD.1).1
        exact ⟨E, hE, hr, hh⟩
      rw [← ht]
      refine ⟨hFbound D, fun q hq => ?_⟩
      rcases List.mem_append.mp (List.mem_of_mem_drop hq) with hq | hq
      · exact hold q hq
      · have heq := List.mem_singleton.mp hq
        subst q
        exact hTh
    · rw [← ht]; exact ⟨hFbound D, hold⟩
    · rw [← ht]; exact ⟨hFbound D, hold⟩

private theorem final_coverage_of_height (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    {B D : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hB : W.Entry B) (hBD : W.Extends B D) (hD : W.OnChain D)
    (hh : (W.state B).h ≤ (W.state D).hF) :
    ∃ F, W.store.blocks (W.state D).F = some F ∧ W.Extends B F := by
  have reach := final_store_reachable S A V Q W
  have hs : W.store.tree ⊆ Q.trace.HonestBlocks (honestKeys S Q.run.2) := by
    intro X hX
    refine ⟨_, (W.ready 3).1, W.cut 3 + 1, ?_⟩
    change X ∈ (Q.trace.post (W.cut 3)).fg.tree at hX
    rwa [final_anchor_post S A V Q W 3] at hX
  have run := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have coh := Compose.honest_blocks_coherent run.toLocalRun
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
  have hDt := final_chain_held S A V Q W hD
  obtain ⟨F, hF, hFr, hFD⟩ := (Store.entry_state_of_source _ _ _ _ reach D hDt).2.1
  have hlookup : W.store.blocks (W.state D).F = some F := by rw [← hFr]; exact hF
  refine ⟨F, hlookup, ?_⟩
  have hFD' := Anc.mono hs hFD
  rcases Anc.total coh hBD hFD' with h | h
  · exact h
  · have hheight := (final_root_heights S A V Q W hDt).1
    rw [hlookup] at hheight
    have hle := (final_chain_height S A V Q W h hB.1).1
    have heq : (W.state B).h = (W.state F).h := by dsimp only [Option.getD] at hheight; omega
    have hTh := (final_chain_height S A V Q W h hB.1).2 heq
    obtain ⟨E, hE, hEr, _, hEF⟩ := final_entry_origin S A V Q W hF
    have he : E = B := coh.1 (hs hE) (hs (final_chain_held S A V Q W hB.1))
      (hEr.trans (hTh.symm.trans hB.2.1))
    exact he ▸ Anc.mono hs hEF

private theorem final_target_counted (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    {B P : SA.Blk Q.params.n (List (FG.Att Q.params.n))} {e : Nat} {a : Fin 4}
    (hP : W.OnChain P)
    (hPt : P ∈ (Q.trace.state (W.block a).proposer (W.cut a)).fg.tree)
    (hpay : (W.block a).fgPayload =
      (Q.trace.state (W.block a).proposer (W.cut a)).fg.proposalAttestations P)
    (rows : W.TargetRows B P e a) :
    let counted := (W.block a).fgPayload.foldl FG.ChainState.processAtt
      { W.state P with s := (W.block a).slot }
    Q.params.toParams.fg.q ≤ counted.target.card ∧
      ((W.state B).bound → ((W.state B).hj, (W.state B).J) ∈ (W.state P).pending →
        Q.params.toParams.fg.q ≤ (counted.fin (W.state B).hj).card) := by
  classical
  obtain ⟨hh, hT, ids, hq, hrows⟩ := rows
  have run := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have he a i : Q.trace.projFG.store (W.block a).proposer i =
      (Q.trace.state (W.block a).proposer i).fg :=
    congrArg Prod.fst (Compose.projFG_state run.toLocalRun (W.ready a).1 i)
  have hlast : Q.trace.projFG.store (W.block 3).proposer (W.cut 3 + 1) = W.store := by
    rw [he, ← final_anchor_post S A V Q W 3]
  have hσ := Store.σ_eq_of_held (final_fg_run S A V Q) (W.ready a).1 (W.ready 3).1
    (he a (W.cut a) ▸ hPt) (hlast ▸ final_chain_held S A V Q W hP)
  rw [he, hlast] at hσ
  obtain ⟨bf, bt, brow⟩ := Store.foldl_bits
    { W.state P with s := (W.block a).slot } (W.block a).fgPayload
  have credit x (hx : x ∈ ids) :
      x ∈ ((W.block a).fgPayload.foldl FG.ChainState.processAtt
        { W.state P with s := (W.block a).slot }).target ∧
      ((W.state B).bound → ((W.state B).hj, (W.state B).J) ∈ (W.state P).pending →
        x ∈ ((W.block a).fgPayload.foldl FG.ChainState.processAtt
          { W.state P with s := (W.block a).slot }).fin (W.state B).hj) := by
    obtain ⟨_, row, j, _, hv, hrh, hrT, hto, _, hvalid, _, _, hc, hpair⟩ := hrows x hx
    have rh : row.h = (W.state P).h := hrh.trans hh.symm
    have rT : row.T = (W.state P).Th := hrT.trans hT.symm
    rcases hc with ⟨ht, hf⟩ | ⟨hp, _⟩
    · refine ⟨bt ht, fun hb hm => ?_⟩
      rcases hf hb with hf | hf
      · exact bf _ hf
      · obtain ⟨c, _, _, _, hchain⟩ := Store.chain_state_of_chain _ _ _ _
          (final_store_reachable S A V Q W) P (final_chain_held S A V Q W hP)
        have hmem := (FG.chain_invariants _ _ _ hchain).2.2.2.2.2.2.2.1 _ hm
        change (W.state P).hF < (W.state B).hj ∧ _ at hmem
        omega
    · by_cases hon : (Q.trace.state (W.block a).proposer (W.cut a)).fg.OnChain P row
      · obtain ⟨X, _, hXP, hrX⟩ := hon
        have hs : (Q.trace.state (W.block a).proposer (W.cut a)).fg.tree ⊆
            Q.trace.HonestBlocks (honestKeys S Q.run.2) := fun X hX =>
          ⟨_, (W.ready a).1, W.cut a, hX⟩
        have hlocal := final_ancestry_local S A V Q W (Anc.mono hs hXP)
          (final_chain_held S A V Q W hP)
        have hbits := Store.rows_counted (final_fg_run S A V Q) (W.ready 3).1 (W.cut 3 + 1)
          (hlast ▸ final_chain_held S A V Q W hP) X (hlast ▸ hlocal) row hrX
        rw [hlast] at hbits
        obtain ⟨ht, hf⟩ := hbits.2 rh rT
        refine ⟨hv ▸ bt (ht hto), fun hb hm => ?_⟩
        exact hv ▸ bf _ (hf _ (hpair hb).1 hm)
      · have hin : row ∈ (W.block a).fgPayload := by
          rw [hpay]
          exact List.mem_filter.mpr ⟨hp, by
            simpa only [decide_eq_true_eq, hσ] using And.intro hvalid hon⟩
        obtain ⟨ht, hf⟩ := brow row hin rh rT
        exact ⟨hv ▸ ht hto, fun hb hm => hv ▸ hf _ (hpair hb).1 hm⟩
  exact ⟨hq.trans (Finset.card_le_card fun x hx => (credit x hx).1),
    fun hb hm => hq.trans (Finset.card_le_card fun x hx => (credit x hx).2 hb hm)⟩

private theorem final_before_timeout (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    {B D : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hB : W.Entry B) (hBD : W.Extends B D) (hD : W.OnChain D)
    (hage : D.slot < B.slot + S.δt) :
    ((W.state D).h = (W.state B).h ∧ (W.state D).Th = B.root ∧
      (W.state D).ThSlot = B.slot ∧ (W.state D).hj = (W.state B).hj ∧
      (W.state D).J = (W.state B).J ∧
      ((W.state B).bound → ((W.state B).hj, (W.state B).J) ∈ (W.state D).pending ∨
        (W.state D).hF = (W.state B).hj ∧ (W.state D).F = (W.state B).J)) ∨
    ∃ C, W.OnChain C ∧ W.Extends B C ∧ W.Extends C D ∧ B.slot < C.slot ∧
      (W.state C).h = (W.state B).h + 1 ∧ (W.state C).Th = C.root ∧
      (W.state C).ThSlot = C.slot ∧ (W.state C).hj = (W.state B).h ∧
      (W.state C).J = B.root ∧
      ((W.state B).bound → (W.state C).F = (W.state B).J ∧
        (W.state C).hF = (W.state B).hj) := by
  have run := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have coh := Compose.honest_blocks_coherent run.toLocalRun
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
  have reach := final_store_reachable S A V Q W
  induction hBD with
  | refl =>
    have he : Q.trace.projFG.store (W.block 3).proposer (W.cut 3 + 1) = W.store := by
      change (Q.trace.projFG.state _ _).1 = _
      rw [Compose.projFG_state run.toLocalRun (W.ready 3).1,
        ← final_anchor_post S A V Q W 3]
    have hf := Store.entry_facts (final_fg_run S A V Q) (W.ready 3).1
      (he ▸ final_chain_held S A V Q W hB.1) (he ▸ hB.2.1)
    rw [he] at hf
    exact Or.inl ⟨rfl, hB.2.1, hB.2.2, rfl, rfl, fun hb => Or.inl (hf.2 hb)⟩
  | @tail P D hBP hPD ih =>
    have hP3 := (Relation.ReflTransGen.single hPD).trans hD
    have hPDslot := coh.2 _ hPD.1 _ hPD.2.1 hPD.2.2
    rcases ih hP3 (by omega) with ⟨hh, hT, hu, hj, hJ, hp⟩ | ⟨C, hC, hBC, hCP, rest⟩
    · obtain ⟨c, _, _, _, hc⟩ := Store.chain_state_of_chain _ _ _ _ reach P
        (final_chain_held S A V Q W hP3)
      have ht := final_chain_step S A V Q W hD hPD.2.2
      rcases (Store.step_current hc ht hh hT hu hj hJ hp).1 hage with hkeep | hcross
      · exact Or.inl hkeep
      · obtain ⟨hheight, hentry, hjust, hroot, _, hfin⟩ := hcross
        have hslot : (W.state D).ThSlot = D.slot := by
          rcases final_step_entry ht with ⟨he, _⟩ | ⟨_, _, hs⟩
          · omega
          · exact hs
        have hBPs := (Anc.slot_le coh hBP).1
        exact Or.inr ⟨D, hD, hBP.tail hPD, .refl, by omega,
          hheight, hentry, hslot, hjust, hroot, hfin⟩
    · exact Or.inr ⟨C, hC, hBC, hCP.tail hPD, rest⟩

private theorem final_justified_crossing (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    {B D : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    (hB : W.Entry B) (hBD : W.Extends B D) (hD : W.OnChain D)
    (hage : D.slot < B.slot + S.δt)
    (hj : (W.state D).hj = (W.state B).h) :
    ∃ C, W.OnChain C ∧ W.Extends B C ∧ W.Extends C D ∧ B.slot < C.slot ∧
      (W.state C).h = (W.state B).h + 1 ∧ (W.state C).Th = C.root ∧
      (W.state C).ThSlot = C.slot ∧ (W.state C).hj = (W.state B).h ∧
      (W.state C).J = B.root ∧
      ((W.state B).bound → (W.state C).F = (W.state B).J ∧
        (W.state C).hF = (W.state B).hj) := by
  rcases final_before_timeout S A V Q W hB hBD hD hage with hkeep | hc
  · obtain ⟨c, _, _, _, hchain⟩ := Store.chain_state_of_chain _ _ _ _
      (final_store_reachable S A V Q W) B (final_chain_held S A V Q W hB.1)
    have hlt := (FG.chain_invariants _ _ _ hchain).2.2.1
    change (W.state B).hj < (W.state B).h at hlt
    have he := hkeep.2.2.2.1
    omega
  · exact hc

private theorem final_entry_service (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    (rows : W.RowSupply) {B : SA.Blk Q.params.n (List (FG.Att Q.params.n))}
    {e : Nat} {a : Fin 4} (hB : W.Entry B) (hprot : W.Protected B e)
    (hserve : e + 2 = (W.block a).slot ∨ (B = W.block 0 ∧ a = 1))
    (hBA : W.Extends B (W.block a)) (hstrict : B.slot < (W.block a).slot)
    (hage : (W.block a).slot ≤ B.slot + S.δt) :
    ∃ C, W.OnChain C ∧ W.Extends B C ∧ W.Extends C (W.block a) ∧ B.slot < C.slot ∧
      (W.state C).h = (W.state B).h + 1 ∧ (W.state C).Th = C.root ∧
      (W.state C).ThSlot = C.slot ∧ (W.state C).hj = (W.state B).h ∧
      (W.state C).J = B.root ∧
      ((W.state B).bound → (W.state C).F = (W.state B).J ∧
        (W.state C).hF = (W.state B).hj) := by
  have run := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have coh := Compose.honest_blocks_coherent run.toLocalRun
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
  have hA3 := W.chain a 3 (by omega)
  have hne : W.block a ≠ B := by rintro rfl; omega
  obtain ⟨P, hBP, hPA⟩ := hBA.cases_tail.resolve_left hne
  have hP3 := (Relation.ReflTransGen.single hPA).trans hA3
  have hPslot := coh.2 _ hPA.1 _ hPA.2.1 hPA.2.2
  rcases final_before_timeout S A V Q W hB hBP hP3 (by omega) with
    ⟨hh, hT, hu, hj, hJ, hp⟩ | ⟨C, hC, hBC, hCP, rest⟩
  swap
  · exact ⟨C, hC, hBC, hCP.tail hPA, rest⟩
  have hinterval : ∀ D, W.Extends B D → W.Extends D P →
      (W.state D).h = (W.state B).h ∨ W.JustifiedBy B D.slot := by
    intro D hBD hDP
    have hlo := (final_chain_height S A V Q W hBD (hDP.trans hP3)).1
    have hhi := (final_chain_height S A V Q W hDP hP3).1
    exact Or.inl (by omega)
  rcases rows B e hprot a hserve P hPA.2.2 hBP hinterval with
    ⟨D, hD, hBD, hDs, _, hDh⟩ | hrows
  · have hPD : W.Extends D P := by
      rcases Anc.total coh hD hP3 with h | h
      · exact h
      · by_cases he : P = D
        · exact he ▸ Relation.ReflTransGen.refl
        · have := (Anc.slot_le coh h).2 he
          omega
    obtain ⟨C, hC, hBC, hCD, rest⟩ :=
      final_justified_crossing S A V Q W hB hBD hD (by omega) hDh
    exact ⟨C, hC, hBC, (hCD.trans hPD).tail hPA, rest⟩
  · obtain ⟨P', hp', hPt, hpay⟩ := final_own_rows S A V Q W a
    have heP : P' = P := coh.1 ⟨_, (W.ready a).1, W.cut a, hPt⟩ hPA.1
      (Option.some.inj (hp'.symm.trans hPA.2.2))
    subst P'
    have hcount := final_target_counted S A V Q W hP3 hPt hpay hrows
    obtain ⟨c, _, _, _, hc⟩ := Store.chain_state_of_chain _ _ _ _
      (final_store_reachable S A V Q W) P (final_chain_held S A V Q W hP3)
    have ht := final_chain_step S A V Q W hA3 hPA.2.2
    obtain ⟨hheight, hentry, hjust, hroot, _, hfin⟩ :=
      (Store.step_current hc ht hh hT hu hj hJ hp).2 hcount.1 hcount.2
    have hslot : (W.state (W.block a)).ThSlot = (W.block a).slot := by
      rcases final_step_entry ht with ⟨he, _⟩ | ⟨_, _, hs⟩
      · omega
      · exact hs
    exact ⟨W.block a, hA3, hBA, .refl, hstrict,
      hheight, hentry, hslot, hjust, hroot, hfin⟩

/-- Conditional bounded crossing assembly; paper workbench 501e66f,
fixed-timeout-synthesis.md, supplier 1. Consumes FirstCrossing and RowSupply without
discharging them. Handles birth-s separately and counts targets before the timeout tie. -/
theorem final_bounded_crossings (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    (crossing : W.FirstCrossing) (rows : W.RowSupply) : W.BoundedCrossings := by
  classical
  obtain ⟨B, hB, _⟩ := crossing
  have hd := A.timeout
  have hs0 : (W.block 0).slot = W.start := by simpa using W.slots 0
  have hs1 : (W.block 1).slot = W.start + (S.δt - 1) := by simpa using W.slots 1
  have hs2 : (W.block 2).slot = W.start + (S.δt + 1) := by simpa using W.slots 2
  have hs3 : (W.block 3).slot = W.start + (S.δt + 3) := by simpa using W.slots 3
  have run := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  have coh := Compose.honest_blocks_coherent run.toLocalRun
    (noCollTransport V S Q.run.1 Q.run.2 Q.hn Q.valid Q.noCollision)
  have below {X} (hX : W.OnChain X) (a : Fin 4) (hlt : X.slot < (W.block a).slot) :
      W.Extends X (W.block a) := by
    rcases Anc.total coh hX (W.chain a 3 (by omega)) with h | h
    · exact h
    · have := (Anc.slot_le coh h).1
      omega
  have first : ∃ C, W.OnChain C ∧ W.Extends B C ∧
      B.slot < C.slot ∧ C.slot ≤ W.start + (S.δt + 1) ∧
      (W.state C).h = (W.state B).h + 1 ∧ (W.state C).Th = C.root ∧
      (W.state C).ThSlot = C.slot ∧ (W.state C).hj = (W.state B).h ∧
      (W.state C).J = B.root := by
    by_cases he : B = W.block 0
    · have hp : W.Protected B W.start := Or.inl ⟨hB, by simp [he]⟩
      have hBA : W.Extends B (W.block 1) := he ▸ W.chain 0 1 (by decide)
      obtain ⟨C, hC, hBC, hC1, hlt, hh, hT, hu, hj, hJ, _⟩ :=
        final_entry_service S A V Q W rows hB.1 hp (Or.inr ⟨he, rfl⟩) hBA
          (by rw [he]; omega) (by rw [he]; omega)
      have hCs := (Anc.slot_le coh hC1).1
      exact ⟨C, hC, hBC, hlt, by omega, hh, hT, hu, hj, hJ⟩
    · obtain ⟨hlo, hhi, _⟩ := hB.2.2.resolve_left he
      have hp : W.Protected B (W.start + (S.δt - 1)) := Or.inl ⟨hB, by simp [he]⟩
      obtain ⟨C, hC, hBC, hC2, hlt, hh, hT, hu, hj, hJ, _⟩ :=
        final_entry_service S A V Q W rows hB.1 hp (Or.inl (by omega))
          (below hB.1.1 2 (by omega)) (by omega) (by omega)
      have hCs := (Anc.slot_le coh hC2).1
      exact ⟨C, hC, hBC, hlt, by omega, hh, hT, hu, hj, hJ⟩
  obtain ⟨C, hC, hBC, hBCslot, hCs, hCh, hCT, hCu, hCj, hCJ⟩ := first
  have hCE : W.Entry C := ⟨hC, hCT, hCu⟩
  have hbound : (W.state C).bound := by
    obtain ⟨c, _, _, _, hc⟩ := Store.chain_state_of_chain _ _ _ _
      (final_store_reachable S A V Q W) B (final_chain_held S A V Q W hB.1.1)
    have hpos := (FG.chain_invariants _ _ _ hc).1
    change 1 ≤ (W.state B).h at hpos
    change 0 < (W.state C).hj ∧ (W.state C).hj + 1 = (W.state C).h
    omega
  have hClo : W.start + (if B = W.block 0 then 1 else 2) ≤ C.slot := by
    split_ifs with he
    · rw [he] at hBCslot; omega
    · have := (hB.2.2.resolve_left he).1; omega
  let v := if C.slot ≤ W.start + (S.δt - 1) then W.start + (S.δt + 1)
    else W.start + (S.δt + 3)
  have hv : v ≤ C.slot + S.δt := by
    dsimp only [v]
    split_ifs <;> split_ifs at hClo <;> omega
  have hprotected : ∀ D, W.OnChain D → W.Extends C D → D.slot < v →
      (W.state D).h = (W.state C).h ∨ (W.state B).h ≤ (W.state D).hF := by
    intro D hD hCD hDs
    rcases final_before_timeout S A V Q W hCE hCD hD (by omega) with hkeep |
      ⟨Z, hZ, _, hZD, _, _, _, _, _, _, hfin⟩
    · exact Or.inl hkeep.1
    · have hz := (hfin hbound).2
      have hmono := final_chain_final_height S A V Q W hZD hD
      exact Or.inr (by omega)
  have hfinal : (W.state B).h ≤ (W.state (W.block 3)).hF := by
    let e := if C.slot ≤ W.start + (S.δt - 1) then W.start + (S.δt - 1)
      else W.start + (S.δt + 1)
    have hp : W.Protected C e := Or.inr ⟨B, hB, hCE, hBC, hCJ, hbound, hCs, rfl⟩
    by_cases hsmall : C.slot ≤ W.start + (S.δt - 1)
    · have he : e = W.start + (S.δt - 1) := by simp [e, hsmall]
      obtain ⟨Z, _, _, hZ2, _, _, _, _, _, _, hfin⟩ :=
        final_entry_service S A V Q W rows hCE hp (Or.inl (by omega))
          (below hC 2 (by omega)) (by omega) (by simpa [v, hsmall, hs2] using hv)
      have hZ3 := hZ2.trans (W.chain 2 3 (by decide))
      have hz := (hfin hbound).2
      have hm := final_chain_final_height S A V Q W hZ3 (W.chain 3 3 (by decide))
      omega
    · have he : e = W.start + (S.δt + 1) := by simp [e, hsmall]
      obtain ⟨Z, _, _, hZ3, _, _, _, _, _, _, hfin⟩ :=
        final_entry_service S A V Q W rows hCE hp (Or.inl (by omega)) hC
          (by omega) (by simpa [v, hsmall, hs3] using hv)
      have hz := (hfin hbound).2
      have hm := final_chain_final_height S A V Q W hZ3 (W.chain 3 3 (by decide))
      omega
  exact ⟨B, C, hB, ⟨C, hC, hBC, hCs, hCJ, hCj⟩, hCE, hBC, hCJ, hbound,
    hClo, hCs, hprotected,
    final_coverage_of_height S A V Q W hB.1 (hBC.trans hC) (W.chain 3 3 (by decide)) hfinal⟩

/-- Transport an acceptance-or-coverage certificate from its actual historical
cut to the reader endpoint. The acceptance branch must already transfer immutable
carrier finality to the recipient cache; a BlockCallAt or compatibility is insufficient. -/
theorem final_cache_coverage_of_prior_cache (Q : FinalQuery S A V)
    (W : FinalWindowData S A V Q)
    (coverage : ∃ F, W.store.blocks (W.state (W.block 3)).F = some F ∧
      W.Extends (W.block 0) F)
    (producer : ∀ F, W.store.blocks (W.state (W.block 3)).F = some F →
      ∀ y t j, Q.deadline ≤ t → t ≤ Q.run.2.horizon →
      Regimes.ReadyAt Q.trace (honestKeys S Q.run.2)
        ((Sys (family S) V).cDur (K S A) Q.run) y t → Regimes.CutAfter Q.trace j t →
      ∃ k ≤ j, W.Extends F (Q.trace.state y k).fg.F ∨
        W.Extends (W.block 0) (Q.trace.state y k).fg.F) : W.CacheCoverage := by
  obtain ⟨F, hF, hAF⟩ := coverage
  intro y t j hdt hth hy hj
  obtain ⟨k, hkj, hk⟩ := producer F hF y t j hdt hth hy hj
  have hmono := (Compose.fg_grows
    (simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid) hy.1 hkj).2
  rcases hk with h | h
  · exact (hAF.trans h).trans hmono
  · exact h.trans hmono

/-- OPEN acceptance, not receipt. Paper workbench b3ca078, four-anchor-window.md /
fixed-timeout-synthesis.md. The latency budget and cache timing are jointly OPEN. -/
theorem final_cache_acceptance (Q : FinalQuery S A V) (W : FinalWindowData S A V Q)
    (coverage : ∃ F, W.store.blocks (W.state (W.block 3)).F = some F ∧
      W.Extends (W.block 0) F) : W.CacheCoverage := by
  sorry

/-- Conditional payload/read projection of the finite supplier package. Uses the engine's
existing catch-up duration, raw own-block release, and final cache membership at endCut.
Window extraction and CacheCoverage remain explicit inputs; no coefficient is synthesized. -/
theorem final_payload_projection
    (windows : ∀ Q : FinalQuery S A V, Nonempty (FinalWindowData S A V Q))
    (coverage : ∀ (Q : FinalQuery S A V) (W : FinalWindowData S A V Q), W.CacheCoverage) :
    ∀ g, schema.output .final = some g →
    ∀ (i : (K S A).Idx) (gst : Time), (Sys (family S) V).Holds
      (fun r => (Sys (family S) V).Healthy (K S A) gst r ∧
        (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) .final i
          ((Sys (family S) V).ready (K S A) gst r) ((Sys (family S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (family S) V).cDur (K S A) r)
        g ((Sys (family S) V).heal (K S A) .final i gst r) ((K S A).params.latency .final i) := by
  intro g hg i gst r hv ⟨hhealthy, hprog⟩
  have hg' : g = Out.finalized := Option.some.inj hg.symm
  subst g
  by_cases hcollision : r.2.HashCollision
  · exact Or.inr hcollision
  left
  intro t hm hb hr
  obtain ⟨v, hvr⟩ := hr
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  let Q : FinalQuery S A V := ⟨r, hn, i, gst, t, hv, hcollision, hhealthy,
    hprog, hm, hb, v, hvr⟩
  obtain ⟨W⟩ := windows Q
  have ht : 0 ≤ t := by
    have hd := r.1.Δ_pos
    have hg0 : (0 : Time) ≤ max gst 0 := le_max_right _ _
    have hp : 0 ≤ ((K S A).params.heal .final i : Time) * r.1.Δ :=
      mul_nonneg (Int.natCast_nonneg _) hd.le
    exact (add_nonneg hg0 hp).trans hm
  have hτ : 0 ≤ Q.trace.time (W.cut 0) := ht.trans W.fresh.le
  have hτh : Q.trace.time (W.cut 0) ≤ r.2.horizon := (W.bounded 0).trans hb
  have hproposal : Regimes.ReadyProposalAt Q.trace (honestKeys S r.2)
      ((Sys (family S) V).cDur (K S A) r) (Q.trace.time (W.cut 0)) (W.block 0) :=
    ⟨_, W.cut 0, W.ready 0, W.proposals 0, rfl⟩
  obtain ⟨k, hk, hrel⟩ := ready_proposal S r.2 hn hv hτ hτh hproposal
  refine ⟨Q.trace.time (W.cut 0), k, headerOf Q.params (W.block 0), W.fresh, hk, hrel, ?_⟩
  have hc : 0 ≤ (Sys (family S) V).cDur (K S A) r := by
    exact mul_nonneg (Int.natCast_nonneg _) r.1.Δ_pos.le
  have hdeadline : 0 ≤ Q.deadline := ht.trans (by
    change t ≤ t + _
    exact le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg _) r.1.Δ_pos.le))
  have hroot : (W.block 0).root ≠ Q.params.genesisRoot := by
    have run := simTrace_goldilocksRun S r.2 hn hv
    rcases Compose.blockCall_cases run.toLocalRun (W.ready 0).1 (W.accepted 0) with hg | hg
    · have hz := (hg.2.1 0 (List.length_pos_iff.mpr hg.1)).2.2.2.1
      exact False.elim ((W.proposals 0).1.2 (by simpa using hz))
    · obtain ⟨j, x, _, _, _, d, p, _, hB, _⟩ := hg
      rw [hB]
      exact taggedRoot_ne _ _
  exact finalized_inBy S r.2 hn hv
    (noCollTransport V S r.1 r.2 hn hv hcollision) hc hdeadline hb hroot
    (fun y j hy hj => coverage Q W y Q.deadline j le_rfl hb hy hj)

/-- Statement-only assembly of the OPEN four-anchor suppliers; not a completed liveness proof.
Paper: workbench b3ca078, four-anchor-window.md and fixed-timeout-synthesis.md. -/
theorem accepted_healthyLive_final : ∀ g, schema.output .final = some g →
    ∀ (i : (K S A).Idx) (gst : Time), (Sys (family S) V).Holds
      (fun r => (Sys (family S) V).Healthy (K S A) gst r ∧
        (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) .final i
          ((Sys (family S) V).ready (K S A) gst r) ((Sys (family S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (family S) V).cDur (K S A) r)
        g ((Sys (family S) V).heal (K S A) .final i gst r) ((K S A).params.latency .final i) := by
  apply final_payload_projection S A V (final_window_extract S A V)
  intro Q W
  have crossings := final_bounded_crossings S A V Q W
      (final_first_crossing S A V Q W (final_inherited_progress S A V Q W))
      (final_row_supply S A V Q W)
  obtain ⟨B, C, hB, _, _, _, _, _, _, _, _, F, hF, hBF⟩ := crossings
  exact final_cache_acceptance S A V Q W ⟨F, hF, hB.2.1.trans hBF⟩

/-- R3 available/stable inclusion; R4 FinalInclude for final.
NO PAPER PROOF for exact contract gHeal, bounded recurrence→node progress,
or repaired engine timing transport. See generic-r3-bridge-audit.md.
This field must not acquire whole-run progress before ready as a premise. -/
theorem accepted_healthyLive : ∀ cap g, schema.output cap = some g →
    ∀ (i : (K S A).Idx) (gst : Time), (Sys (family S) V).Holds
      (fun r => (Sys (family S) V).Healthy (K S A) gst r ∧
        (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) cap i
          ((Sys (family S) V).ready (K S A) gst r)
          ((Sys (family S) V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys (family S) V).cDur (K S A) r)
        g ((Sys (family S) V).heal (K S A) cap i gst r) ((K S A).params.latency cap i) := by
  intro cap g hg idx gst r hv ⟨hh, hp⟩
  by_cases hf : cap = .final
  · subst cap
    exact accepted_healthyLive_final S A V g hg idx gst r hv ⟨hh, hp⟩
  have hcap : cap = .available ∨ cap = .stable := by cases cap <;> simp_all
  have hg' : g = Out.confirmed := by
    rcases hcap with rfl | rfl <;> exact Option.some.inj hg.symm
  subst g
  by_cases hc : r.2.HashCollision
  · exact Or.inr hc
  left
  intro t ht hb hr
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨hr.choose⟩
  let Q : ConfirmedQuery S A V := ⟨r, hn, cap, hcap, idx, gst, t, hv, hc,
    Or.inr ⟨hh, hp, ht⟩, hb, hr⟩
  obtain ⟨P, cover⟩ := healthy_confirmed_supply S A V Q hh hp ht
  have h0 : 0 ≤ t :=
    (add_nonneg (le_max_right gst 0)
      (mul_nonneg (Int.natCast_nonneg _) r.1.Δ_pos.le)).trans ht
  exact confirmed_payload_projection S A V Q h0 P cover

/-- R1, sleepy-record-invariant.md §§2–5.1 and sleepy-proposal-adoption.md
§§2–4 (conditional S1–S4 package). NO PAPER PROOF for engine network,
readiness and read-cut transport. Node route: sleepy_invariant and ready reads. -/
theorem accepted_sleepySafe : ∀ cap g, (cap = .available ∨ cap = .stable) →
    schema.output cap = some g → (Sys (family S) V).Holds
      ((Sys (family S) V).Sleepy (K S A)) fun r =>
        (chainTrace r.2).ReadySafe ((Sys (family S) V).cDur (K S A) r) g 0 := by
  intro cap g hcap hg r hv hs
  have hg' : g = Out.confirmed := by
    rcases hcap with rfl | rfl <;> exact Option.some.inj hg.symm
  subst g
  by_cases hc : r.2.HashCollision
  · exact Or.inr hc
  left
  by_cases hn : 1 ≤ Fintype.card V
  · let Q : SleepySafetyQuery S A V := ⟨r, hn, hv, hc, hs⟩
    obtain ⟨hd, hsync, hf⟩ := sleepy_safety_inputs S A V Q
    have safe := sleepy_safe_engine S r.2 hn hv
      (noCollTransport V S r.1 r.2 hn hv hc) hsync hf
    have ready : ∀ v t, r.2.point.Ready ((Sys (family S) V).cDur (K S A) r) v t →
        r.2.point.Ready (Regimes.catchUp (S.params (Model.pubOf r.1) hn) + 1) v t := by
      intro v t h
      refine ⟨h.1, fun τ hlo hhi => h.2 τ ?_ hhi⟩
      exact (max_le_max_left 0 (sub_le_sub_right (sub_le_sub_left hd t) 1)).trans hlo
    exact ⟨fun u v i j hi hj hu hv => safe.1 u v i j hi hj (ready _ _ hu) (ready _ _ hv),
      fun v i j hi hij hj hvi hvj => safe.2 v i j hi hij hj (ready _ _ hvi) (ready _ _ hvj)⟩
  · have hempty : IsEmpty V := Fintype.card_eq_zero_iff.mp (by omega)
    exact ⟨fun u => (hempty.false u).elim, fun v => (hempty.false v).elim⟩

/-- R2 inclusion/growth, node sleepy_statements. NO PAPER PROOF yet pinned
for the exact recurrence/readiness/deadline transport; keep this gap explicit. -/
theorem accepted_sleepyLive : ∀ cap g, (cap = .available ∨ cap = .stable) →
    schema.output cap = some g → ∀ i : (K S A).Idx,
      (Sys (family S) V).Holds
        (fun r => (Sys (family S) V).Sleepy (K S A) r ∧
          (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) cap i
            0 ((Sys (family S) V).pt r).horizon r)
        fun r => ProposalLiveReady r.2 ((Sys (family S) V).cDur (K S A) r)
          g 0 ((K S A).params.latency cap i) := by
  intro cap g hcap hg idx r hv ⟨hs, hp⟩
  have hg' : g = Out.confirmed := by
    rcases hcap with rfl | rfl <;> exact Option.some.inj hg.symm
  subst g
  by_cases hc : r.2.HashCollision
  · exact Or.inr hc
  left
  intro t ht hb hr
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨hr.choose⟩
  let Q : ConfirmedQuery S A V := ⟨r, hn, cap, hcap, idx, 0, t, hv, hc,
    Or.inl ⟨hs, hp, ht⟩, hb, hr⟩
  obtain ⟨P, service⟩ := sleepy_serviced_proposal_supply S A V Q hs hp ht
  exact confirmed_payload_projection S A V Q ht P
    (sleepy_serviced_proposal_coverage S A V Q P service)

/-- R3 healed safety. NO PAPER PROOF for bounded [ready,heal] recurrence
to current whole-run HealedPremises or the target gHeal bound. RecRet also
has no completed proof (rc-recret-induction.md §6). -/
theorem accepted_healedSafe : ∀ cap g, (cap = .available ∨ cap = .stable) →
    schema.output cap = some g → ∀ (i : (K S A).Idx) (gst : Time),
      (Sys (family S) V).Holds
        (fun r => (Sys (family S) V).Healthy (K S A) gst r ∧
          (Sys (family S) V).prog (shapeProgress (family S) V) (K S A) cap i
            ((Sys (family S) V).ready (K S A) gst r)
            ((Sys (family S) V).heal (K S A) cap i gst r) r)
        fun r => (chainTrace r.2).ReadySafe ((Sys (family S) V).cDur (K S A) r)
          g ((Sys (family S) V).heal (K S A) cap i gst r) := by
  intro cap g hcap hg idx gst r hv ⟨hh, hp⟩
  have hg' : g = Out.confirmed := by
    rcases hcap with rfl | rfl <;> exact Option.some.inj hg.symm
  subst g
  by_cases hcollision : r.2.HashCollision
  · exact Or.inr hcollision
  left
  have htime : ∀ k, k ≤ (chainTrace r.2).cuts →
      (chainTrace r.2).cutTime k ≤ r.2.horizon :=
    (Model.sysOf_laws schema (compiled (family S)) V).trace r hv |>.cutTime_le_horizon
  let heal := (Sys (family S) V).heal (K S A) cap idx gst r
  by_cases hb : heal ≤ r.2.horizon
  · by_cases hn : 1 ≤ Fintype.card V
    · let Q : HealthyPreparationQuery S A V := ⟨r, hn, cap, hcap, idx, gst, hv,
        hcollision, hh⟩
      have h0 : 0 ≤ Q.heal :=
        add_nonneg (le_max_right gst 0)
          (mul_nonneg (Int.natCast_nonneg _) r.1.Δ_pos.le)
      exact healthy_ready_safety S A V Q h0 hb hp
    · have hempty : IsEmpty V := Fintype.card_eq_zero_iff.mp (by omega)
      exact ⟨fun u => (hempty.false u).elim, fun v => (hempty.false v).elim⟩
  · have hnone : ∀ k, ¬ (chainTrace r.2).InCuts heal k :=
      fun k hk => hb (hk.2.trans (htime k hk.1))
    exact ⟨fun _ _ i _ hi => (hnone i hi).elim,
      fun _ i _ hi => (hnone i hi).elim⟩

/-- R5 OC1–OC4: NO PAPER PROOF for composed-node outage continuation.
Blocked by lifetime (4k−1 versus 4k−2) and finite pre-outage network scope:
SyncUntil b₀ does not give unrestricted late-wake SyncRun calls. Do not
insert that false implication as an intermediate lemma. -/
theorem accepted_persists : ∀ g, schema.output .stable = some g → ∀ T b₀ b₁,
    (Sys (family S) V).Holds ((Sys (family S) V).Outage (K S A) T b₀ b₁)
      fun r => (chainTrace r.2).ProtectedThrough
        ((Sys (family S) V).cDur (K S A) r) g (resilienceTarget schema g) T b₀ b₁ := by
  intro g hg T b₀ b₁ r hv ho
  have hg' : g = Out.confirmed := Option.some.inj hg.symm
  subst g
  by_cases hcollision : r.2.HashCollision
  · exact Or.inr hcollision
  left
  intro v hvr t ht hth w hw hr
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  let Q : OutageQuery S A V := ⟨r, hn, T, b₀, b₁, hv, hcollision, ho⟩
  exact outage_protected S A V Q v hvr t ht hth w hw hr

/-- Exact nine-field assembly; the named gaps above are not a blanket claims assumption. -/
theorem accepted_claims : ShapeClaims (family S) (K S A) := by
  intro V _ _
  exact {
    outputValid := accepted_outputValid S V
    nested := accepted_nested S V
    finalMonotone := accepted_finalMonotone S V
    finalAccountable := accepted_finalAccountable S A V
    healthyLive := accepted_healthyLive S A V
    sleepySafe := accepted_sleepySafe S A V
    sleepyLive := accepted_sleepyLive S A V
    healedSafe := accepted_healedSafe S A V
    persists := accepted_persists S A V }

/-- Selection-aware singleton duties make every recurrence fit. -/
theorem accepted_progressFits : ProgressFits (K S A) (family S) := by
  intro cap i pub s
  rfl

/-- At an outer gap beyond the local span there is room for a bad slot. -/
theorem accepted_progressTolerant : ProgressTolerant schema (K S A) := by
  intro cap _ N
  let P := if cap = .final then finalWindow S else Pattern.single
  exact ⟨⟨P.span + 2, by omega⟩, Nat.le_refl _⟩

/-- Fixed thresholds and positive finite catch-up/budget are admissible. -/
theorem accepted_admissible : (K S A).params.Admissible := by
  rw [acceptanceContract_params_eq]
  exact {
    catchUp_pos := (accepted_coefficients S A).catchUp.pos
    θ_range := by norm_num [Params.standard]
    β_range := by norm_num [Params.standard]
    cover_range := by norm_num [Params.standard]
    α_range := by norm_num [Params.standard]
    budget_pos := by have := A.lookback.pos; have := S.two_le_k; dsimp [Params.standard]; omega }

/-- Concrete existential endpoint. Every gap is a named numeric or adapter
leaf; no simulation, GenesisFresh, or desired safety premise is added. -/
theorem accepted : ∃ C : AcceptanceCoefficients,
    Accepted (family S) (acceptanceContract A C) := by
  refine ⟨accepted_coefficients S A, ?_⟩
  exact {
    claims := accepted_claims S A
    admissible := accepted_admissible S A
    serves := by simp [OutputSchema.Serves, schema]
    progressFits := accepted_progressFits S A
    progressTolerant := accepted_progressTolerant S A }

end Consensus.Goldilocks.Refinement

module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.SleepyLayer1
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameGeometry

public section

/-! # Conditional sleepy read safety

Source provenance anchors frames; event safety and output provenance give read
agreement. Same-reader extension is retained as an independent premise.
-/

namespace Consensus.Goldilocks.Generic.SleepyLayer1

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n}

theorem frames_from_sources (C : ACCorrectLocal A sg) (D : Data A) :
    FramesFromSources C D := by
  intro hcache hrow hviable hsource cm proposer dg H tr b hrun hnc hpop y i t hr
  have hlocal := C.run.run_local hrun
  have hs : SourcedRows D tr H b t := by
    intro x k a hx ha _ hkb
    obtain ⟨j, src, E, _, _, _, _, hE, hroot, _, _, hanchor⟩ :=
      hrow hsource cm proposer dg H tr b hrun hnc x k a hx ha hkb
    exact ⟨E, ⟨x, k, tr.time k, hlocal.time_nonneg k,
      fun q hq => hlocal.time_mono hq.le, hx, hE⟩, hroot, hanchor⟩
  obtain ⟨hF, hJ⟩ := hcache cm proposer dg H tr b hrun hnc y i t hr (hpop y i t hr) hs
  refine ⟨hF, hJ, ?_, hviable cm proposer dg H tr b hrun hnc y i t hr (hpop y i t hr) hs⟩
  change Anchored D tr H b t (tr.state y i).fg.fcRoot
  unfold Store.fcRoot
  split <;> assumption

open Shape Blocks

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

theorem read_agreement (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) (D : Data A) :
    ReadAgreement M C D := by
  intro hevents houtputs ΔF b p hb hrun hnc hbind hpre hK hpop hframes
    y z i j t u hy hz hby hbz
  let tr := M.trace
  let H := M.honest
  have hl := C.run.run_local hrun
  have hcoh := Compose.Growing.honest_blocks_coherent_local hl hnc
  have genesis {B : A.Blk} (hB : B ∈ tr.HonestBlocksAt H) :
      P.genesisBlock A.genesisPayload ∈ tr.HonestBlocksAt H ∧
        Anc (tr.HonestBlocksAt H) (P.genesisBlock A.genesisPayload) B := by
    obtain ⟨v, k, d, hd, hkd, hv, hB⟩ := hB
    rw [← Trace.upTo_state tr v hkd] at hB
    obtain ⟨hg, ha⟩ := Compose.FrameGeometry.honest_genesis_anc (hl.upTo hd) ⟨v, hv, k, hB⟩
    exact ⟨RunTrace.honestBlocks_upTo_subset hl.time_mono hd hg,
      ha.mono (RunTrace.honestBlocks_upTo_subset hl.time_mono hd)⟩
  have down {B W : A.Blk} (hW : W ∈ tr.HonestBlocksAt H)
      (hBW : Anc (tr.HonestBlocksAt H) B W) (hw : Anchored D tr H b b W) :
      Anchored D tr H b b B := by
    rcases hw with hg | ⟨E, he, ha⟩
    · have hWG : W = P.genesisBlock A.genesisPayload :=
        hcoh.1 hW (genesis hW).1 hg
      subst W
      rcases Relation.ReflTransGen.cases_tail hBW with rfl | ⟨X, _, hx⟩
      · exact Or.inl rfl
      · cases hx.2.2
    · exact Or.inr ⟨E, he, hBW.trans ha⟩
  have lift {B : A.Blk} {v : Time} (hv : v ≤ b) (h : Anchored D tr H b v B) :
      Anchored D tr H b b B := by
    rcases h with h | ⟨E, ⟨x, k, s, hx, hk, hkb, he⟩, ha⟩
    · exact Or.inl h
    · exact Or.inr ⟨E, ⟨x, k, s, hx, hk.trans hv, hkb, he⟩, ha⟩
  have reader {v k d} (hr : HonestReadPoint tr H b v k d) (hb : ReadBoundary tr v k) :
      confirmedRead tr v k d ∈ tr.HonestBlocksAt H ∧
        Anchored D tr H b b (confirmedRead tr v k d) := by
    obtain ⟨hheld, ha⟩ :=
      houtputs M.committee M.proposer M.digest H tr b hrun hnc v k d hr hb
    have hsub : (tr.state v k).fg.tree ⊆ tr.HonestBlocksAt H :=
      fun _ h => ⟨v, k, d, hr.2.2.1, hr.2.1.1, hr.1, h⟩
    refine ⟨hsub hheld, ?_⟩
    rcases ha with ha | ha
    · exact lift hr.2.2.2 ha
    · have hF := (hframes v k d hr).1
      have hFm := (Store.cache_invariants _ _ _ _
        (Compose.fg_reachable (hl.upTo hr.2.2.1) hr.1 k)).1
      rw [Trace.upTo_state tr v hr.2.1.1] at hFm
      exact down (hsub hFm) ha (lift hr.2.2.2 hF)
  obtain ⟨hY, hYa⟩ := reader hy.1 hby
  obtain ⟨hZ, hZa⟩ := reader hz.1 hbz
  rcases hYa with hg | ⟨E, hE, ha⟩
  · have heq := hcoh.1 hY (genesis hY).1 hg
    rw [heq]
    exact Or.inl (genesis hZ).2
  rcases hZa with hg | ⟨E', hE', ha'⟩
  · have heq := hcoh.1 hZ (genesis hZ).1 hg
    rw [heq]
    exact Or.inr (genesis hY).2
  rcases hevents ΔF b p hb hrun hnc hbind hpre hK hpop hframes
      E E' hE hE' with he | he
  · exact Anc.total hcoh (ha.trans he) ha'
  · exact Anc.total hcoh ha (ha'.trans he)

theorem ready_read_safety (M : RunMap rho payload) (C : ACCorrectLocal A M.signer)
    (D : Data A) : ReadyReadSafety M C D := by
  intro hagree hevents houtputs hext ΔF b p hb hrun hnc hbind hpre hK hpop hf
  exact ⟨hagree hevents houtputs ΔF b p hb hrun hnc hbind hpre hK hpop hf,
    hext ΔF b p hb hrun hnc hbind hpre hK hpop hf⟩

end Consensus.Goldilocks.Generic.SleepyLayer1

end

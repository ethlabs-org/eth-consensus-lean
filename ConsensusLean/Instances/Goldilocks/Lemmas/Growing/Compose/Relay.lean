module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Retention
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle

public section

namespace Consensus.Goldilocks.Growing.LocalRun

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-- Finalization advances along the chain on a prefix through all cuts before the read. -/
theorem finalized_mono_on_prefix (h : LocalRun proposer dg H sg tr ini) {d : Time}
    (hd : 0 ≤ d) {y : Fin P.n} {i j : Nat} (hy : y ∈ H d) (hij : i ≤ j)
    (hj : ∀ k < j, tr.time k ≤ d) :
    Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F (tr.state y j).fg.F := by
  have ha := Healing.run_F_mono (h.upTo hd) hy hij
  rw [Trace.upTo_state tr y (fun k hk => hj k (hk.trans_le hij)), Trace.upTo_state tr y hj] at ha
  exact ha.mono (RunTrace.honestBlocks_upTo_subset h.time_mono hd)

/-- An honest reader's finalized block only advances along its chain. -/
theorem finalized_mono (h : LocalRun proposer dg H sg tr ini)
    {y : Fin P.n} {i j : Nat} (hy : y ∈ H (tr.time j)) (hij : i ≤ j) :
    Anc (tr.HonestBlocksAt H) (tr.state y i).fg.F (tr.state y j).fg.F :=
  h.finalized_mono_on_prefix (h.time_nonneg j) hy hij (fun _ hk => h.time_mono hk.le)

/-- An honest AC block call follows its FG acceptance at the same time. -/
theorem acBlock_prev (h : LocalRun proposer dg H sg tr ini) {y : Fin P.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {ℓ : ACLabel A} {B : A.Blk}
    (hc : tr.CallAt y i (.ac ℓ)) (hb : ℓ.call = .block B) :
    ∃ i', i = i' + 1 ∧ tr.CallAt y i' (.fg (.block B true)) ∧ tr.time i' = tr.time i := by
  obtain ⟨i', rfl, hc', ht⟩ := Compose.acBlock_prev (h.upTo (h.time_nonneg i)) hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc) hb
  exact ⟨i', rfl, ((Trace.upTo_callAt _).mp hc').2, ht⟩

/-- An honest FG acceptance is followed immediately by its AC block call. -/
theorem accept_next (h : LocalRun proposer dg H sg tr ini) {y : Fin P.n} {i : Nat}
    (hy : y ∈ H (tr.time i)) {B : A.Blk} (hc : tr.AcceptAt y i B) :
    ∃ ℓ : ACLabel A, tr.CallAt y (i + 1) (.ac ℓ) ∧ ℓ.call = .block B ∧
      tr.time (i + 1) = tr.time i := by
  obtain ⟨ℓ, hc', hb, ht⟩ := Compose.accept_next (h.upTo (h.time_nonneg i)) hy
    ((Trace.upTo_callAt_of_le _ le_rfl).mpr hc)
  exact ⟨ℓ, ((Trace.upTo_callAt _).mp hc').2, hb, ht⟩

/-- Lift an FG acceptance relay to AC. The relay gets the original send time via the
same-time source cut; `σ` is the effective time used for both deadlines. -/
theorem acRelayAt (hrun : LocalRun proposer dg H sg tr ini)
    {x y : Fin P.n} {i j : Nat} {B : A.Blk} {ℓ : ACLabel A} {σ : Time}
    (hx : x ∈ H (tr.time i)) (hacc : tr.projAC.AcceptAt x i B)
    (hy : y ∈ H (tr.time j)) (hc : tr.projAC.CallAt y j ℓ)
    (hanc : Anc (tr.HonestBlocksAt H) ℓ.frame.F B)
    (relay : ∀ k, tr.time k = tr.time i → x ∈ H (tr.time k) → tr.AcceptAt x k B →
      tr.IsCall y j → Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B →
      tr.BlockAcceptedBy y j σ B) :
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < tr.projAC.deadline y k σ := by
  obtain ⟨ℓ₀, hc₀, hb⟩ := hacc
  have hc := Compose.projAC_callAt.mp hc
  obtain ⟨i', rfl, hi', hti⟩ := hrun.acBlock_prev hx (Compose.projAC_callAt.mp hc₀) hb
  have hfr : ℓ.frame.F = (tr.state y j).fg.F := by rw [(hrun.cutLaw y j _ hc hy).1]; rfl
  exact Compose.acRelay_of_acceptNext (Compose.projAC_callAt.mpr hc)
    (relay i' hti (hti ▸ hx) hi' ⟨_, hc⟩ (hfr ▸ hanc))
    (fun _ hkj => hrun.accept_next (hrun.antitone (hrun.time_mono hkj) hy))

/-- Read a pre-GST FG catch-up witness from an honest observation at or after the snapshot. -/
theorem fgCatchAt (hrun : LocalRun proposer dg H sg tr ini) {g κ : Time}
    (hcatch : Healing.Growing.CatchRun tr H g κ)
    {x y : Fin P.n} {i j : Nat} {B : A.Blk}
    (hx : x ∈ H (tr.time i)) (ha : tr.AcceptAt x i B) (hi : tr.time i < SA.gbar g)
    (hy : y ∈ H (tr.time j)) (hj : SA.gbar g + κ ≤ tr.time j)
    (hanc : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B) :
    ∃ k < j, tr.AcceptAt y k B ∧ tr.time k < SA.gbar g + κ :=
  Healing.accept_before_snapshot hj fun q hq hfirst =>
    hcatch x i B hx ha hi y q (hrun.antitone hj hy) hfirst ((hrun.finalized_mono hy hq).trans hanc)

/-- Project a pre-GST catch-up to AC without changing the snapshot or its strict bound. -/
theorem acCatchAt (hrun : LocalRun proposer dg H sg tr ini) {g κ : Time}
    (hcatch : Healing.Growing.CatchRun tr H g κ)
    {x y : Fin P.n} {i j : Nat} {B : A.Blk} {ℓ : ACLabel A}
    (hx : x ∈ H (tr.time i)) (ha : tr.projAC.AcceptAt x i B) (hi : tr.time i < SA.gbar g)
    (hy : y ∈ H (tr.time j)) (hc : tr.projAC.CallAt y j ℓ) (hj : SA.gbar g + κ ≤ tr.time j)
    (hanc : Anc (tr.HonestBlocksAt H) ℓ.frame.F B) :
    ∃ k ≤ j, tr.projAC.AcceptAt y k B ∧ tr.time k < SA.gbar g + κ := by
  obtain ⟨ℓ₀, hc₀, hb⟩ := ha
  obtain ⟨q, _, hq, ht⟩ := hrun.acBlock_prev hx (Compose.projAC_callAt.mp hc₀) hb
  have hF : ℓ.frame.F = (tr.state y j).fg.F := by
    rw [(hrun.cutLaw y j _ (Compose.projAC_callAt.mp hc) hy).1]
    rfl
  obtain ⟨k, hk, hak, hkt⟩ := hrun.fgCatchAt hcatch (ht ▸ hx) hq (ht ▸ hi) hy hj (hF ▸ hanc)
  obtain ⟨ℓ', hc', hb', ht'⟩ := hrun.accept_next (hrun.antitone (hrun.time_mono hk.le) hy) hak
  exact ⟨k + 1, hk, ⟨ℓ', Compose.projAC_callAt.mpr hc', hb'⟩, ht'.symm ▸ hkt⟩

end Consensus.Goldilocks.Growing.LocalRun

end

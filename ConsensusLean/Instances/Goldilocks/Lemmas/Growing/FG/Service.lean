module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Entries
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.State
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Cut

public section

/-! # FG good-window service under growing faults

Retain each window through its own proposal, without requiring its proposer to remain honest.
-/

namespace Consensus.Goldilocks.Store.Growing

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Time → Set (Fin P.n)}
  {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}

/-- Retention preserves a good window. When its deadline follows the proposal, pool provenance
supplies a signature already present before the proposal. -/
theorem GoodWindow.upTo (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {cF a kF i : Nat} {p : Fin P.n} {T Bs Pr : NodeBlock P ACP} {R : Finset (FG.Att P.n)}
    (hw : GoodWindow P ACP H tr cF T a kF p i Bs Pr R) :
    Store.GoodWindow P ACP (H (tr.time i)) (tr.upTo (tr.time i)) cF T a kF p i Bs Pr R := by
  have hs := Trace.upTo_state tr p (i := i) (fun k hk => hr.time_mono hk.le)
  have hrun := hr.upTo (hr.time_nonneg i)
  refine ⟨?_, ?_, ?_, hw.window, hw.quorum, ?_, ?_, ?_, hw.params⟩
  · obtain ⟨hp, hc, hprop, htime, hPr, hpar, hincl⟩ := hw.proposal
    refine ⟨hp, (Trace.upTo_callAt tr).mpr ⟨le_rfl, hc⟩, hprop, htime, ?_⟩
    simpa only [FGTrace.store, hs] using And.intro hPr (And.intro hpar hincl)
  · simpa only [FGTrace.store, hs] using hw.entry
  · simpa only [FGTrace.store, hs] using hw.extends_entry
  · simpa only [FGTrace.store, hs] using hw.fgAtts
  · intro r hrR
    by_cases hon : (tr.store p i).OnChain Pr r
    · exact Or.inl (by simpa only [FGTrace.store, hs] using hon)
    · right
      intro hv
      by_cases hdi : P.slotTime (T.slot + a) + 6 * P.Δ ≤ tr.time i
      · obtain ⟨j, ⟨src, hc⟩, hjT⟩ :=
          (hw.emitted r hrR).resolve_left hon (hr.antitone hdi hv)
        exact ⟨j, ⟨src, (Trace.upTo_callAt tr).mpr ⟨hjT.trans hdi, hc⟩⟩, hjT⟩
      · have hp' : r ∈ (FGTrace.store (tr.upTo (tr.time i)) p i).atts := by
          simpa only [FGTrace.store, hs] using (hw.pooled r hrR).resolve_left hon
        obtain ⟨k, hk, hproc⟩ := Store.pool_processed hrun hw.proposal.1 i r hp'
        obtain ⟨l, hl, hsign⟩ := hrun.unforgeable p hw.proposal.1 k r hproc hv
        exact ⟨l, hsign, (hr.time_mono (hl.trans hk).le).trans (le_of_not_ge hdi)⟩
  · simpa only [FGTrace.store, hs] using hw.pooled

/-- The single-window core, retained through the serving proposal. -/
theorem window_justifies (hr : Consensus.Goldilocks.Growing.FGLocalRun acp₀ H U tr)
    {cF a kF i : Nat} {p : Fin P.n} {T Bs Pr : NodeBlock P ACP} {R : Finset (FG.Att P.n)}
    (hw : GoodWindow P ACP H tr cF T a kF p i Bs Pr R) :
    ∃ X, JustifiesEntry P ACP (tr.store p (i + 1)) T ((tr.store p i).σ T.root).h X ∧
      (tr.store p (i + 1)).Anc X Bs ∧
      ((tr.store p (i + 1)).σ X.root).h = ((tr.store p i).σ T.root).h + 1 ∧
      ((tr.store p (i + 1)).σ X.root).Th = X.root ∧
      (((tr.store p i).σ T.root).h, T.root) ∈ ((tr.store p (i + 1)).σ X.root).pending ∧
      (((tr.store p i).σ T.root).previousHeightJustified →
        ((tr.store p (i + 1)).σ X.root).F = ((tr.store p i).σ T.root).J ∧
        ((tr.store p (i + 1)).σ X.root).hF = ((tr.store p i).σ T.root).hj) := by
  have hs : ∀ k, k ≤ i + 1 → (tr.upTo (tr.time i)).state p k = tr.state p k := by
    intro k hk
    exact Trace.upTo_state tr p fun l hl => hr.time_mono (by omega)
  have h := Store.window_justifies (hr.upTo (hr.time_nonneg i)) (hw.upTo hr)
  simpa only [FGTrace.store, hs i (by omega), hs (i + 1) le_rfl] using h

/-- G1.6 at the proposal's own honest cut. -/
theorem previousHeightJustified_entry (P : Params) (ACP : Type) :
    PreviousHeightJustifiedEntry P ACP := by
  intro acp₀ H U tr hr cF T a kF p i Bs Pr R hw hb
  obtain ⟨X, hJ, hXB, -, -, -, hfin⟩ := window_justifies hr hw
  exact ⟨X, hJ, hXB, (hfin hb).1, (hfin hb).2⟩

/-- G1.7 uses each serving node's own honest cut, even across compromise between windows. -/
theorem previousHeightNotJustified_entry (P : Params) (ACP : Type) :
    PreviousHeightNotJustifiedEntry P ACP := by
  intro acp₀ H U tr hr cF T a₀ kF p i Bs Pr R hw _
  obtain ⟨X, hJ, hXB, hh, hTh, hpend, -⟩ := window_justifies hr hw
  have hs := Trace.upTo_state tr p (i := i) (fun k hk => hr.time_mono hk.le)
  have hT : T ∈ (FGTrace.store (tr.upTo (tr.time i)) p i).tree := by
    simpa only [FGTrace.store, hs] using hw.entry.1
  have h1 := (Store.one_le_h (hr.upTo (hr.time_nonneg i)) hw.proposal.1 hT).1
  simp only [FGTrace.store, hs] at h1
  change 1 ≤ ((tr.store p i).σ T.root).h at h1
  have hb : ((tr.store p (i + 1)).σ X.root).previousHeightJustified :=
    ⟨by rw [hJ.2.2.1]; omega, by rw [hJ.2.2.1, hh]⟩
  refine ⟨X, hJ, hXB, hpend, hh, hTh, hb, ?_⟩
  intro a₁ p₁ i₁ Bs₁ Pr₁ R₁ hw₁
  obtain ⟨Z, hJZ, hZB, -, -, -, hfin⟩ := window_justifies hr hw₁
  rw [σ_eq_of_held hr (hr.time_nonneg i₁) (hr.time_nonneg i)
    hw₁.proposal.1 hw.proposal.1 (fun k hk => hr.time_mono hk.le)
    (fun k hk => hr.time_mono (by omega)) hw₁.entry.1 hJ.1] at hfin
  obtain ⟨hF, hhF⟩ := hfin hb
  exact ⟨Z, hJZ.1, hZB, hF.trans hJ.2.2.2.1, hhF.trans hJ.2.2.1⟩

/-- G1.8(b), transferring the finalized entry between independently honest windows. -/
theorem coverage (P : Params) (ACP : Type) : Coverage P ACP := by
  intro acp₀ H U tr hr cF T₁ T a₀ kF p i Bs Pr R hw hnb _ hT₁T _ _ X hJX hXB
    a₁ p₁ i₁ Bs₁ Pr₁ R₁ hw₁
  obtain ⟨X', hJ', hX'B, -, hh', -, -, hZ⟩ :=
    previousHeightNotJustified_entry P ACP acp₀ H U tr hr cF T a₀ kF p i Bs Pr R hw hnb
  have r₀ := hr.upTo (hr.time_nonneg i)
  have r₁ := hr.upTo (hr.time_nonneg i₁)
  have hs₀ : ∀ k, k ≤ i + 1 → (tr.upTo (tr.time i)).state p k = tr.state p k := by
    intro k hk
    exact Trace.upTo_state tr p fun l hl => hr.time_mono (by omega)
  have hs₁ : ∀ k, k ≤ i₁ + 1 → (tr.upTo (tr.time i₁)).state p₁ k = tr.state p₁ k := by
    intro k hk
    exact Trace.upTo_state tr p₁ fun l hl => hr.time_mono (by omega)
  have coh₀ : Coherent (tr.store p (i + 1)).tree := by
    have h := r₀.coherent.mono (r₀.tree_subset p hw.proposal.1 (i + 1))
    simpa only [FGTrace.store, hs₀ (i + 1) le_rfl] using h
  have coh₁ : Coherent (tr.store p₁ (i₁ + 1)).tree := by
    have h := r₁.coherent.mono (r₁.tree_subset p₁ hw₁.proposal.1 (i₁ + 1))
    simpa only [FGTrace.store, hs₁ (i₁ + 1) le_rfl] using h
  have hjlt : ∀ B ∈ (tr.store p (i + 1)).tree,
      ((tr.store p (i + 1)).σ B.root).hj < ((tr.store p (i + 1)).σ B.root).h := by
    intro B hB
    have hB' : B ∈ (FGTrace.store (tr.upTo (tr.time i)) p (i + 1)).tree := by
      simpa only [FGTrace.store, hs₀ (i + 1) le_rfl] using hB
    simpa only [FGTrace.store, hs₀ (i + 1) le_rfl] using
      (Store.one_le_h r₀ hw.proposal.1 hB').2
  have hXX : X = X' := by
    rcases Goldilocks.Anc.total coh₀ hXB hX'B with h | h
    · by_contra hne
      have := (hJ'.2.2.2.2 X hJX.1 hJX.2.1 h hne).1
      have := hjlt X hJX.1
      have := hJX.2.2.1
      omega
    · by_contra hne
      have := (hJX.2.2.2.2 X' hJ'.1 hJ'.2.1 h (Ne.symm hne)).1
      have := hjlt X' hJ'.1
      have := hJ'.2.2.1
      omega
  rw [← hXX] at hZ
  obtain ⟨Z, hZt, hZB, hF, -⟩ := hZ a₁ p₁ i₁ Bs₁ Pr₁ R₁ hw₁
  have hX₁ : X ∈ (tr.store p₁ (i₁ + 1)).tree := by
    have hw' := hw₁.upTo hr
    simpa only [FGTrace.store, Store.tree, Set.mem_ofPred_eq, hs₁ (i₁ + 1) le_rfl] using
      (Store.held_mono r₁ hw₁.proposal.1 (Nat.le_succ i₁) hw'.entry.1).1
  have transfer := fun {A B} (h : (tr.store p (i + 1)).Anc A B)
      (hB : B ∈ (tr.store p₁ (i₁ + 1)).tree) =>
    anc_transfer hr (hr.time_nonneg i) (hr.time_nonneg i₁) hw.proposal.1 hw₁.proposal.1
      (fun k hk => hr.time_mono (by omega)) (fun k hk => hr.time_mono (by omega)) h hB
  have hTX := transfer hJX.2.1 hX₁
  have hTt : T ∈ (tr.store p₁ (i₁ + 1)).tree := by
    by_cases hTe : T = X
    exacts [hTe ▸ hX₁, (Goldilocks.Anc.mem hTX hTe).1]
  have hT₁T' : (tr.store p (i + 1)).Anc T₁ T := by
    apply hT₁T.mono
    intro B hB
    have hB' : B ∈ (FGTrace.store (tr.upTo (tr.time i)) p i).tree := by
      simpa only [FGTrace.store, hs₀ i (by omega)] using hB
    simpa only [FGTrace.store, Store.tree, Set.mem_ofPred_eq, hs₀ (i + 1) le_rfl] using
      (Store.held_mono r₀ hw.proposal.1 (Nat.le_succ i) hB').1
  refine ⟨Z, hZt, hZB, ?_, T, hTt, hF.symm, transfer hT₁T' hTt⟩
  have := (Goldilocks.Anc.slot_le coh₁ hZB).1
  have := (Goldilocks.Anc.slot_le coh₀ hXB).1
  have := (Goldilocks.Anc.slot_le coh₀ hT₁T').1
  have := hw.window.2
  have := hw₁.window.2
  omega

end Consensus.Goldilocks.Store.Growing

end

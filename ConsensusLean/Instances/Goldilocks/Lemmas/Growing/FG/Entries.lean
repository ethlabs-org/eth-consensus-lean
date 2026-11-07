module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGStore.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries

public section

/-! # Quorum-free entries with faults charged at consumption

Retain only through the receiving cut, not through the possibly later consumption budget.
Every namer of that retained run is a faulty-at-`d` or genuine early-signing namer.
-/

namespace Consensus.Goldilocks.Store.Growing

variable (P : Params) (ACP : Type)

/-- G1.10, using the consumption-horizon namer count. -/
theorem quorum_free_entries : QuorumFreeEntries P ACP := by
  intro acp₀ H U tr 𝓔 T₀ T d y hr hT₀ hT hTd hK hquiet i X hy hX ht
  have hid : tr.time i ≤ d := (ht.elim (fun h => h.le) (fun h => h.1.le)).trans hTd
  have hs : ∀ k, k ≤ i + 1 → (tr.upTo (tr.time i)).state y k = tr.state y k := by
    intro k hk
    exact Trace.upTo_state tr y fun l hl => hr.time_mono (by omega)
  have hnamers : ∀ E, Store.namers P ACP (H (tr.time i)) (tr.upTo (tr.time i)) T₀ E ⊆
      namers P ACP H tr T₀ d E := by
    intro E v hv
    rcases hv with hv | ⟨j, a, ⟨src, hc⟩, hj, ha⟩
    · exact Or.inl fun h => hv (hr.antitone hid h)
    · exact Or.inr ⟨j, a, ⟨src, ((Trace.upTo_callAt tr).mp hc).2⟩, hj, ha⟩
  have hcount : ∀ E ∈ 𝓔,
      (Store.namers P ACP (H (tr.time i)) (tr.upTo (tr.time i)) T₀ E).ncard < P.fg.q := by
    intro E hE
    exact (Set.ncard_le_ncard (hnamers E) (Set.toFinite _)).trans_lt (hK E hE)
  have hq := Store.quorum_free_entries P ACP acp₀ (H (tr.time i)) U
    (tr.upTo (tr.time i)) 𝓔 T₀ T y (hr.upTo (hr.time_nonneg i)) hT₀ hT hy hcount
    (fun v hv j a ha hjT₀ hjT E hE => by
      obtain ⟨src, hc⟩ := ha
      obtain ⟨hji, hc⟩ := (Trace.upTo_callAt tr).mp hc
      exact hquiet v j a (hr.antitone hji hv) ⟨src, hc⟩ hjT₀ hjT E hE)
    i X ((Trace.upTo_callAt tr).mpr ⟨le_rfl, hX⟩) ht
  simpa only [FGTrace.store, hs (i + 1) le_rfl] using hq

end Consensus.Goldilocks.Store.Growing

end

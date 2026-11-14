module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Same
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks SA: source compatibility after the cut (A1.9)

The block `C` that `ac_to_fg` returns at `x` at `t` is at or below the block of a live fast lock
of a slot `s' ≥ slot(t) − 2 ≥ s − 1` that `x` holds, which sits below the block of a fast lock of
slot `s'` that `x` wrote before the call (`fast_lock_provenance`), so `s' ≤ slot(t) ≤ m`:
* `s' > s`: the honest votes of slot `s'` extend `B` (`fastLock_compatible_of_votes`);
* `s' = s`: two fast locks of slot `s` (`fastLock_same_slot`);
* `s' = s − 1`, so `slot(t) = s + 1`: in case (ii) `x` restarted after `t_s = t_{slot(t)−1}` and is
  not joined, so it returns nothing; in case (i) its slot-`(s+1)` unlocking moved the lock to a
  block compatible with `B` (`locks_after_unlock`).

The fast lock enters only through its counted heads and the same-slot case, both of which pass
from its block `D` down to any `B ⪯ D`, so the proof is for a lock on `D` and a block `B ⪯ D`
(`source_compatible_stored`, the form C1.1 reads, with the stored block `Φ.viableAncestor D`);
A1.9 is `B = D`. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- A block that `ac_to_fg` returns is a candidate, from a joined node, which the call keeps. -/
private theorem toFG_some {FGP : Type} {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {C : Blk sp.n FGP} (h : (acToFG sp A Φ t).2 = some C) :
    C ∈ toFGCandidates sp A Φ t ∧ joined sp A t ∧
      (acToFG sp A Φ t).1.restartTime = A.restartTime := by
  unfold acToFG at h ⊢
  split_ifs at h ⊢ with hj
  split at h
  · cases h
  · rename_i C' hC'
    split_ifs at h ⊢
    cases h
    exact ⟨(deepest_mem hC').1, hj, rfl⟩

/-- **A1.9 for the stored block**: `SourceCompatible` for a fast lock on `D`, with every
hypothesis and the conclusion about a block `B ⪯ D` (the block the lock stores,
`Φ.viableAncestor D`). Only for population-sized committees (`committeeSize = n`). -/
theorem source_compatible_stored :
    ∀ (FGP : Type) (ro : ReplayOrder sp FGP)
    (proposer : Nat → Fin sp.n) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro),
    sp.committeeSize = sp.n →
    ACRun proposer tr H U → ∀ (s m : Nat) (w x : Fin sp.n) (i₀ i : Nat) (B D : Blk sp.n FGP)
      (CV : Set (Vote sp.n)) (ℓ : ACLabel (goldilocksSA sp FGP ro)) (C : Blk sp.n FGP),
    w ∈ H → FastLockAt tr w i₀ s D CV → Anc U B D →
    SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ) tr →
    Carry tr H U s CV → 2 * Hᶜ.ncard < sp.n →
    x ∈ H → ToFGAt tr x i ℓ C →
    sp.ts (s + 1 : Nat) + sp.Δ < tr.time i → tr.time i ≤ sp.ts m + sp.Δ →
    (∀ z ∈ H, ∀ j < i, ∀ e, VoteAt tr z j e → s < e.msg.slot → e.msg.slot ≤ m →
      VoteExtends U e.msg B) →
    ((∃ j < i, ∃ ℓ' e, CastAt tr x j ℓ' e ∧ e.msg.slot = s + 1 ∧ Compatible U ℓ'.frame.F B) ∨
      (∃ k < i, tr.RestartAt x k ∧ sp.ts s < tr.time k)) →
    Compatible U C B := by
  intro FGP ro proposer H U tr hstk hrun s m w x i₀ i B D CV ℓ C hw hfl hBD hsync hcarry hf hx hto
    hlo hhi hvotes hcase
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hc, hcall, hC⟩ := hto
  obtain ⟨⟨hCv, l, hl, hlb, hlf, hls⟩, hjoin, hrt⟩ := toFG_some sp hC
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  simp only at hlb hlf hls
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hr.frameLaw x hx i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  -- `C` is the viable ancestor of the lock's block: compatibility passes down to it
  have hCe : C = ℓ.frame.viableAncestor B₀ :=
    hU.1 (hΦU hCv.1) (hΦU (viableAncestor_anc hΦ hB₀).1) hlb.symm
  subst hCe
  have down : ∀ {X Y}, Anc U X Y → Compatible U Y B → Compatible U X B := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact anc_total hU hXY h
  refine down (Anc.mono hΦU (anc_viableAncestor _ B₀)) ?_
  -- the slots: `s + 1 ≤ slot(t) ≤ m`
  have hΔ := sp.toParams.hΔ
  have ht0 := hr.time_nonneg i
  have hσlo : s + 1 ≤ sp.slot (tr.time i) := by
    have := ((ts_le_iff_le_slot sp ht0) (s + 1 : Nat)).1 (by linarith)
    exact_mod_cast this
  have hσhi : sp.slot (tr.time i) ≤ m := by
    by_contra h
    have := ((ts_le_iff_le_slot sp ht0) (m + 1 : Nat)).2 (by push_cast; omega)
    simp only [SAParams.ts] at this hhi
    push_cast at this
    linarith
  -- the lock's origin: a fast lock of its slot that `x` wrote before the call
  obtain ⟨j, hj, B', CV', hfl', L, hL, hLr, hLB'⟩ := fast_lock_provenance hr hx i l₀ hl₀ hlf
  obtain rfl : B₀ = L := hU.1 (hΦU hB₀) hL (hB₀r.trans hLr.symm)
  have hs'σ : l₀.slot ≤ sp.slot (tr.time i) := by
    have hmono := slot_mono sp (hr.time_nonneg j) (hr.time_mono hj.le)
    rcases hfl' with ⟨ℓ', C', ⟨-, -, ht, -⟩, -⟩ | ⟨ℓ', A', -, hsl, -⟩
    · have : sp.ts (l₀.slot + 1 : Nat) ≤ tr.time j := by
        rw [ht]; simp only [SAParams.ts]; push_cast; linarith
      have := ((ts_le_iff_le_slot sp (hr.time_nonneg j)) _).1 this
      push_cast at this
      omega
    · omega
  -- a population-sized committee: every validator, `committeeSize = n`
  rcases lt_trichotomy s l₀.slot with hlt | heq | hgt
  · -- a later slot: its honest votes extend `B`
    refine down hLB' (fastLock_compatible_of_votes hrun _ CommitteeP.full hx hj hfl'
      (cs2_full hstk hf) fun z hz j' hj' e hv hes =>
        hvotes z hz j' hj' e hv (hes ▸ hlt) (by omega))
  · -- slot `s`: two fast locks of one slot
    subst heq
    refine down hLB' ?_
    rcases fastLock_same_slot hrun _ CommitteeP.full (size_binding_full hstk) hw hfl hx hfl'
      hsync (cs2_full hstk hf) with h | h
    exacts [Or.inr (hBD.trans h), anc_total hU h hBD]
  · -- slot `s − 1`, so `slot(t) = s + 1`
    have hσ : sp.slot (tr.time i) = s + 1 := by omega
    rcases hcase with ⟨j₁, hj₁, ℓ₁, e₁, hc₁, hs₁, hF₁⟩ | ⟨k, hk, hrk, htk⟩
    · exact locks_after_unlock hrun (by rw [hstk]; exact Fin.pos x) hw hfl hBD hcarry hx hc₁ hs₁
        hF₁ hj₁ l₀ hl₀ hgt B₀ (hΦU hB₀) hB₀r
    · -- a restart after `t_s` leaves `x` unjoined in slot `s + 1`
      exfalso
      have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
      rw [hc.1, hcall] at he
      have hpost : joined sp (tr.post i) (tr.time i) := by
        have : tr.post i = (acToFG sp (tr.state x i) ℓ.frame (tr.time i)).1 :=
          (congrArg Prod.fst he).symm
        unfold joined at hjoin ⊢
        rw [this, hrt]
        exact hjoin
      have := ((joined_awake sp) FGP ro H U tr hr x hx i ℓ hc hpost).2 k hk.le hrk
      rw [hσ] at this
      have hc' : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
      rw [hc'] at this
      linarith

/-- **A1.9.** -/
theorem source_compatible : SourceCompatible sp :=
  fun FGP ro H U tr proposer hstk hrun s m w x i₀ i B CV ℓ C hw hfl =>
    source_compatible_stored sp FGP ro proposer H U tr hstk hrun s m w x i₀ i B B CV ℓ C hw hfl
      Relation.ReflTransGen.refl

end Consensus.Goldilocks.SA

end

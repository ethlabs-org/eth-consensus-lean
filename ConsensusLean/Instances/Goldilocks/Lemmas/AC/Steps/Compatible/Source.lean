module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Same
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Unlocked

public section

/-! # Goldilocks SA: source compatibility after the cut (A1.9)

The block `C` that `ac_to_fg` returns at `x` at `t` is at or below the block of a live fast lock
of a slot `s' ≥ slot(t) − 2 ≥ s − 1` that `x` holds, which sits below the block of a fast lock of
slot `s'` that `x` wrote before the call (`fast_lock_provenance`), so `s' ≤ slot(t) ≤ m`:
* `s' > s`: the honest votes of slot `s'` extend `B` (`fastLock_compatible_of_votes`);
* `s' = s`: two fast locks of slot `s` (`fastLock_same_slot`);
* `s' = s − 1`, so `slot(t) = s + 1`: in case (ii) `x` restarted after `t_s = t_{slot(t)−1}` and is
  not joined, so it returns nothing; in case (i) its slot-`(s+1)` unlocking moved the lock to a
  block compatible with `B` (`locks_after_unlock`). -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- A block that `ac_to_fg` returns is a candidate, from a joined node, which the call keeps. -/
private theorem toFG_some {FGP : Type} {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {C : Blk sp.n FGP} (h : (acToFG sp A Φ t).2.1 = some C) :
    C ∈ toFGCandidates sp A Φ t ∧ joined sp A t ∧
      (acToFG sp A Φ t).1.restartTime = A.restartTime := by
  unfold acToFG at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hj
  split at h
  · cases h
  · rename_i C' hC'
    split_ifs at h ⊢
    cases h
    exact ⟨(deepest_mem hC').1, hj, rfl⟩

/-- **A1.9.** -/
theorem source_compatible : SourceCompatible sp := by
  intro FGP ro H U tr hrun s m w x i₀ i B CV ℓ C hw hfl hsync hcarry hf hx hto _ hlo hhi hvotes
    hcase _ _
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
    nlinarith
  -- the lock's origin: a fast lock of its slot that `x` wrote before the call
  obtain ⟨j, hj, B', CV', hfl', L, hL, hLr, hLB'⟩ := fast_lock_provenance hr hx i l₀ hl₀ hlf
  obtain rfl : B₀ = L := hU.1 (hΦU hB₀) hL (hB₀r.trans hLr.symm)
  have hs'σ : l₀.slot ≤ sp.slot (tr.time i) := by
    have hmono := slot_mono sp (hr.time_nonneg j) (hr.time_mono hj.le)
    rcases hfl' with ⟨ℓ', C', ⟨-, -, ht, -⟩, -⟩ | ⟨ℓ', A', -, hsl, -⟩
    · have : sp.ts (l₀.slot + 1 : Nat) ≤ tr.time j := by
        rw [ht]; simp only [SAParams.ts]; push_cast; nlinarith
      have := ((ts_le_iff_le_slot sp (hr.time_nonneg j)) _).1 this
      push_cast at this
      omega
    · omega
  rcases lt_trichotomy s l₀.slot with hlt | heq | hgt
  · -- a later slot: its honest votes extend `B`
    refine down hLB' (fastLock_compatible_of_votes hrun hx hj hfl' hf fun z hz j' hj' e hv hes =>
      hvotes z hz j' hj' e hv (hes ▸ hlt) (by omega))
  · -- slot `s`: two fast locks of one slot
    subst heq
    exact down hLB' ((fastLock_same_slot hrun hw hfl hx hfl' hsync hf).symm)
  · -- slot `s − 1`, so `slot(t) = s + 1`
    have hσ : sp.slot (tr.time i) = s + 1 := by omega
    rcases hcase with ⟨j₁, hj₁, ℓ₁, e₁, hc₁, hs₁, hF₁, -⟩ | ⟨k, hk, hrk, htk⟩
    · exact locks_after_unlock hrun hw hfl hcarry hx hc₁ hs₁ hF₁ hj₁ l₀ hl₀ hgt B₀ (hΦU hB₀) hB₀r
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

end Consensus.Goldilocks.SA

end

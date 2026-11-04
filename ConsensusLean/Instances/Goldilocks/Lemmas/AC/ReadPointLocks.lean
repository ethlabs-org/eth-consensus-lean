module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Events

public section

/-! # Goldilocks SA: the live locks at a vote's read point lie on one chain

consensus-lean#135 (WI-15/16). At every honest vote the read point has the lock invariant
(`castAt_readPoint_lockInv`): the state before the call has it (`lockInv_of_reachable`, moved
to the call's frame by `LockInv.callOK`), and the receipt's optimistic check and `try_vote`'s
unlocking keep it (`LockInv.step_readPoint`). So the live lock blocks of the read point lie on
one chain (`castAt_liveLockBlocks_chain`), and every live lock block of the read point or
`fc_root` is compatible with every live lock block (`castAt_compatible_of_live`). No regime is
assumed: the invariant holds at every reachable state. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

/-- **The read point of an honest vote has the lock invariant** at the call's frame. -/
theorem castAt_readPoint_lockInv (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) : LockInv U e.readPoint ℓ.frame := by
  have hU := hr.coherent
  obtain ⟨hcall, he⟩ := hc
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hr.frameLaw y hy i ℓ hcall with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  obtain ⟨Φp, tp, hR, hok⟩ : ∃ Φp tp,
      (goldilocksSA sp FGP ro).ReachableAt y U (tr.state y i) Φp tp ∧
        (goldilocksSA sp FGP ro).CallOK U Φp (tr.time i) ℓ.call ℓ.frame := by
    rcases hr.frameLaw y hy i ℓ hcall with ⟨hn, Φ₀, hi, hf, hok⟩ | ⟨j, ℓ', hj, hc', hnb, hok⟩
    · refine ⟨Φ₀, 0, ?_, hok⟩
      rw [tr.state_of_noCall hn, hr.init y hy]
      exact .init Φ₀ hi hf
    · refine ⟨ℓ'.frame, tr.time j, ?_, hok⟩
      rw [tr.state_of_lastCall hc' hj hnb]
      exact localRun_reachable _ _ _ _ _ tr hr y hy j ℓ' hc'
  obtain ⟨hin, -, hinv⟩ := lockInv_of_reachable hU hR
  have hx := hr.exec i ℓ hcall.2 (hcall.1 ▸ hy)
  rw [hcall.1] at hx
  have he' : e ∈ ((goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i)
      ℓ.call).2 := by
    rw [hx]
    exact he
  exact (hinv.callOK hU hin hok).step_readPoint hU hΦ hΦU y _ (hr.time_nonneg i) _ e he'

/-- **The live lock blocks of an honest vote's read point lie on one chain**, at every time. -/
theorem castAt_liveLockBlocks_chain (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) (t : Time) :
    ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame t,
      ∀ D ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame t, Compatible ℓ.frame.tree L D := by
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  exact (castAt_readPoint_lockInv hr hy hc).liveBlocks_chain hr.coherent hΦ hΦU

/-- **A read live lock is compatible with every live lock.** At an honest vote, a live lock
block of the read point, or `fc_root`, is compatible with every live lock block of the read
point. -/
theorem castAt_compatible_of_live (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) {t : Time} {C : Blk sp.n FGP}
    (hC : C ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame t ∪ {ℓ.frame.fcRoot}) :
    ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame t, Compatible ℓ.frame.tree L C := by
  have hΦ : FrameOK ℓ.frame := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.1
  obtain ⟨-, hanc⟩ := anc_getAnchor hΦ (castAt_liveLockBlocks_chain hr hy hc t)
  intro L hL
  exact anc_total hΦ.coherent (hanc L (Or.inl hL)) (hanc C hC)

end Consensus.Goldilocks.SA

end

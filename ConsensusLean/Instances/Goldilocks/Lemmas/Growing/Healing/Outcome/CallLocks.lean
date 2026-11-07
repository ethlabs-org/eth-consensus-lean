module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.CallLocksPending
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.SameSlot
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockProvenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Live locks at a call compare with the unanimous head, under growing faults

`call_locks_compatible_of_unanimous_at`, the growing form of
`Healing.ResetPremisesUpTo.call_locks_compatible_of_unanimous`: through the update deadline, the
normalized live locks of a call of a node honest at it compare with the head `P` of a unanimous
slot `u`. Each live lock comes from an earlier write of the caller (honest then, as it is honest at
the later call):

* of a label below `u`, clean after the drain: its block is below the head of an actual slot-`u`
  cast (`clean_source_below_cast_at`, by clean-source vote retention);
* of label `u`: below `P` (`same_slot_source_below_unanimous_at`);
* of label `u + 1`: an optimistic selection before the call, compatible with `P` by `hnext`
  (a later label cannot be written by the update deadline). -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A bounded clean source, written by a node honest at its write, is below the head of an actual
later-label cast of a node honest at it. The cast's head is supplied explicitly. -/
theorem clean_source_below_cast_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s i : Nat} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    {B P : SA.Blk sp.n (List (FG.Att sp.n))}
    (horig : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hcast : SA.CastAt tr.projAC y i ell e) (hib : tr.time i ≤ b)
    (hsi : s < e.msg.slot) (hPU : P ∈ tr.HonestBlocksAt H) (heP : e.msg.head = P.root) :
    Anc (tr.HonestBlocksAt H) B P := by
  have hext : SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
    rcases horig with ⟨CV, hf⟩ | hslo
    · exact hp.fast_source_votes_before_at hc hx hf hs hrb i hib y hy ell e hcast hsi
    · exact hp.slow_source_votes_before_at hc hx hslo hs hrb i hib y hy ell e hcast hsi
  obtain ⟨D, hD, hDr, hBD⟩ := hext
  obtain rfl : D = P := (Compose.Growing.honest_blocks_coherent hp.run hp.noColl).1 hD hPU
    (hDr.trans heP)
  exact hBD

/-- **Through the update deadline, normalized live locks compare with the unanimous head**, at a
call of a node honest at it. Older and same-label source ancestry are derived from actual bounded
votes. -/
theorem call_locks_compatible_of_unanimous_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hPU : P ∈ tr.HonestBlocksAt H) (hts : cutZ sp.toParams g ≤ sp.ts u)
    (hun : ∀ z q e, z ∈ H (tr.time q) → SA.VoteAt tr.projAC z q e → tr.time q ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hvote : ∃ z q ell e, z ∈ H (tr.time q) ∧ SA.CastAt tr.projAC z q ell e ∧
      tr.time q ≤ b ∧ e.msg.slot = u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hcall : tr.projAC.CallAt y j ell) (hjb : tr.time j ≤ b)
    (hafter : drainTime sp a ≤ tr.time j) (hbefore : tr.time j ≤ sp.ts u + 6 * sp.Δ)
    (hnext : ∀ r < j, ∀ B CV, SA.OptimisticLockAt tr.projAC y r (u + 1) B CV →
      Compatible (tr.HonestBlocksAt H) B P) :
    ∀ L ∈ SA.liveLockBlocks sp (tr.projAC.state y j).locks ell.frame (tr.time j),
      Compatible (tr.HonestBlocksAt H) L P := by
  have hm := hp.run.time_mono
  have hmA : Monotone tr.projAC.time := hm
  have ht := hp.run.time_nonneg j
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hm ht
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time j))
    (tr.upTo (tr.time j)) proposer (hp.run.upTo ht) (hp.noColl.upTo _)).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc' : (tr.projAC.upTo (tr.time j)).CallAt y j ell :=
    (Trace.upTo_callAt_of_le _ le_rfl).mpr hcall
  have hst : (tr.projAC.upTo (tr.time j)).state y j = tr.projAC.state y j :=
    Trace.upTo_state tr.projAC y (fun _ hk => hm hk.le)
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc'
  have hDelta := sp.toParams.hΔ
  rintro L ⟨hLt, l', ⟨l, hl, B, hB, hBr, hlive, rfl⟩, hLr⟩
  obtain rfl : L = ell.frame.viableAncestor B := hPhi.coherent.1 hLt
    (SA.viableAncestor_anc hPhi hB).1 hLr.symm
  have hl' : l ∈ ((tr.projAC.upTo (tr.time j)).state y j).locks := by rw [hst]; exact hl
  -- the lock's earlier write, on the prefix through the call
  obtain ⟨r, hrj, D, hraw, X, hX, hXr, hXD⟩ :
      ∃ r < j, ∃ D,
        ((∃ CV, SA.FastLockAt (tr.projAC.upTo (tr.time j)) y r l.slot D CV) ∨
          SA.SlowLockAt (tr.projAC.upTo (tr.time j)) y r l.slot D) ∧
        ∃ X ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)),
          X.root = l.block ∧ Anc ((tr.upTo (tr.time j)).HonestBlocks (H (tr.time j))) X D := by
    cases hf : l.fast with
    | false =>
      obtain ⟨r, hrj, D, hslow, hX⟩ := SA.slow_lock_provenance hr hy j l hl' hf
      exact ⟨r, hrj, D, Or.inr hslow, hX⟩
    | true =>
      obtain ⟨r, hrj, D, CV, hfast, hX⟩ := SA.fast_lock_provenance hr hy j l hl' hf
      exact ⟨r, hrj, D, Or.inl ⟨CV, hfast⟩, hX⟩
  obtain rfl : B = X := (hr.coherent.1 hX (hPhiU hB) (hXr.trans hBr.symm)).symm
  have hrtime := hm hrj.le
  have hyr : y ∈ H (tr.time r) := hp.run.antitone hrtime hy
  have horig : (∃ CV, SA.FastLockAt tr.projAC y r l.slot D CV) ∨
      SA.SlowLockAt tr.projAC y r l.slot D := by
    rcases hraw with ⟨CV, hf⟩ | hs
    · exact Or.inl ⟨CV, (SA.upTo_fastLockAt hmA).mp hf |>.2⟩
    · rcases hs with ⟨ell', C, hu, hC, hslow⟩
      rw [Trace.upTo_time,
        Trace.upTo_state tr.projAC y (fun _ hq => (hm hq.le).trans hrtime)] at hslow
      refine Or.inr ⟨ell', C, (SA.upTo_updateAt hmA).mp hu |>.2, ?_, hslow⟩
      rwa [Trace.upTo_state tr.projAC y (fun _ hq => (hm hq.le).trans hrtime)] at hC
  have hLD : Anc (tr.HonestBlocksAt H) (ell.frame.viableAncestor B) D :=
    Anc.mono hsub (((SA.anc_viableAncestor ell.frame B).mono hPhiU).trans hXD)
  have hrb := hrtime.trans hjb
  have hrt := hrtime.trans hbefore
  have hDP : Compatible (tr.HonestBlocksAt H) D P := by
    by_cases hlu : l.slot < u
    · have hwf : SA.LocksWF sp ((tr.projAC.upTo (tr.time j)).state y j).locks :=
        SA.locksWF_state hr hy j
      rw [hst] at hwf
      have hs := drain_live_locks hwf hafter _ ⟨l, hl, B, hB, hBr, hlive, rfl⟩
      obtain ⟨z, q, ellq, e, hz, hcast, hqb, hes⟩ := hvote
      exact Or.inl (clean_source_below_cast_at hp hc hyr hz horig hs hrb hcast hqb
        (hes ▸ hlu) hPU (hun z q e hz ⟨ellq, hcast⟩ hqb hes))
    by_cases heq : l.slot = u
    · exact Or.inl (hp.same_slot_source_below_unanimous_at hc hyr (heq ▸ horig) hrb hts hPU hun)
    have hgt : u < l.slot := by omega
    rcases horig with ⟨CV, ⟨ellr, C, hupd, _⟩ | hop⟩ | ⟨ellr, C, hupd, _⟩
    · have htr : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
      have hlt := (SA.ts_lt_iff sp).2 (show (u : Int) < l.slot by omega)
      exfalso; linarith only [hrt, htr, hlt]
    · have hsl : sp.slot (tr.time r) = l.slot := hop.choose_spec.choose_spec.2.1
      have hmono := SA.slot_mono sp (hp.run.time_nonneg r) hrt
      change sp.slot (tr.time r) ≤ sp.slot (sp.ts u + 6 * sp.Δ) at hmono
      have hs : sp.slot (sp.ts u + 6 * sp.Δ) = u + 1 :=
        SA.slot_of_mem sp (u + 1) (by simp only [SAParams.ts]; push_cast; linarith only [hDelta])
          (by simp only [SAParams.ts]; push_cast; linarith only [hDelta])
      rw [hsl, hs] at hmono
      exact hnext r hrj D CV (show l.slot = u + 1 by omega ▸ hop)
    · have htr : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
      have hlt := (SA.ts_lt_iff sp).2 (show (u : Int) < l.slot by omega)
      exfalso; linarith only [hrt, htr, hlt]
  rcases hDP with hDP | hPD
  · exact Or.inl (hLD.trans hDP)
  · exact SA.anc_total hU hLD hPD

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end

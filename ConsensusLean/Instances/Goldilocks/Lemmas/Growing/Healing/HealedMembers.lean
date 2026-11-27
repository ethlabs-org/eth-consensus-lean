module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LocksWF
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Deep FG sources: membership of the healed family

With deep FG sources on, the source of an honest `ac_to_fg` call need not sit below a *fast* lock:
without a fast candidate it is a deep candidate at or below the *deepest live lock block* (the
deep anchor), fast or slow. After the drain of the reset `a`, every live lock has label
`≥ cleanLabel a + k + 2` (`drain_live_locks`), and a live lock block is below its holder's own lock
write of the lock's slot (`lock_write_at`). So the lock write is a member of the healed family from
the lock floor `rL = cleanLabel a + k + 2`, and any source, fast or deep, is on the healed chain
(`deep_source_on_healed_chain_at`).

The two frontier facts then give compatibility and votes for a source: S1 (members are pairwise
compatible) makes a source compatible with every member, a high origin included
(`healed_source_compatible_highOrigin_at`, `healed_sources_compatible_at`); S2 (honest votes of a
slot after a member's label extend it) makes such a vote extend every block below the member
(`healed_source_votes_at`). S1 and S2 are hypotheses here, in the forms of
`SeededInvariant.origins_compatible` and `SeededInvariant.vote_extends`. -/

namespace Consensus.Goldilocks.Compose.Growing

open AC (ACParams ReplayOrder Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State} {g : Time}

/-- **After the drain, a source is on the healed chain, fast or deep.** For the reset `a`, an
honest `ac_to_fg` source `C` at a cut `i` at or after the drain `t_{clean(a)+k+3}` (`drainTime`),
written at a time `≤ b`, is on the healed chain with the lock floor `cleanLabel a + k + 2` (any
origin floor `rO`). A fast source is the block of a live lock; a deep source is below the deep
anchor, the deepest live lock block. Either way it is below its holder's own lock write of a label
past the drain, a `LockWithin` member of the healed family. -/
theorem deep_source_on_healed_chain_at (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) {a : Time} {rO : Nat} {b : Time}
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) (hdt : Healing.drainTime sp a ≤ tr.time i)
    (hib : tr.time i ≤ b) {ℓ : ACLabel (goldilocksNode sp ro)}
    {C : AC.Blk sp.n (List (FG.Att sp.n))} (h : AC.ToFGAt tr.projAC y i ℓ C) :
    OnHealedChain tr H g (Healing.cleanLabel sp a + sp.k + 2) rO C b := by
  have hd := hrun.time_nonneg i
  have hU := honestBlocksAt_coherent hrun hnc
  obtain ⟨hpc, -, hC⟩ := h
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun hnc hy hpc
  rw [projAC_state_at hrun hy] at hC
  have hwf : AC.LocksWF sp (tr.state y i).ac.locks := by
    have h := Compose.locksWF_state (hrun.upTo hd) (hnc.upTo _) hy i
    rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h
  -- a live lock block is below its holder's own lock write of a label past the drain
  have hlock : ∀ L ∈ AC.liveLockBlocks sp (tr.state y i).ac.locks ℓ.frame (tr.time i),
      ∃ D s, HealedOrigin tr H g (Healing.cleanLabel sp a + sp.k + 2) rO D s b ∧
        Anc (tr.HonestBlocksAt H) L D := by
    rintro L ⟨hL, l, hlm, hlL⟩
    have hlab : Healing.cleanLabel sp a + sp.k + 2 ≤ l.slot :=
      Healing.drain_live_locks (a := a) hwf hdt l hlm
    obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hlm
    obtain rfl : L = ℓ.frame.viableAncestor B₀ :=
      hΦ.coherent.1 hL (AC.viableAncestor_anc hΦ hB₀).1 hlL.symm
    obtain ⟨L₀, hL₀, hL₀r, D, hD, hL₀D⟩ :=
      lock_write_at hrun hnc hd (fun _ hk => hrun.time_mono hk.le) hy l₀ hl₀
    obtain rfl : B₀ = L₀ := hU.1 (hΦU hB₀) (mem_honestBlocksAt hrun hy hL₀) (hB₀r.trans hL₀r.symm)
    exact ⟨D, l₀.slot, .of_lock hlab (hD.mono hib),
      ((AC.anc_viableAncestor _ B₀).mono hΦU).trans hL₀D⟩
  obtain ⟨hCv, hs⟩ := AC.toFG_source hC
  rcases hs with ⟨-, l, hlm, hlC, -⟩ | ⟨_, anchor, -, hanc, -, hdeep⟩
  · obtain ⟨D, s, hD, hCD⟩ := hlock C ⟨hCv.1, l, hlm, hlC⟩
    exact onHealedChain_iff.2 ⟨D, s, hD, hCD⟩
  · obtain ⟨D, s, hD, hAD⟩ := hlock anchor (AC.deepest_mem hanc).1
    exact onHealedChain_iff.2 ⟨D, s, hD, (hdeep.2.1.mono hΦU).trans hAD⟩

/-- **A lock write within `t` has a label at most `slot t`**: a fast update or a slow lock of
label `s` is written at `t_s + 6Δ`, an optimistic selection in slot `s`. -/
theorem LockWithin.label_le_slot (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat} {t : Time} (h : LockWithin tr H C s t) :
    s ≤ sp.slot t := by
  obtain ⟨x, i, -, hit, hl⟩ := lockWithin_iff.1 h
  have hi0 := hrun.time_nonneg i
  have hm := AC.slot_mono sp hi0 hit
  have hupd : ∀ ℓ, AC.UpdateAt tr.projAC x i s ℓ → s ≤ sp.slot (tr.time i) := fun ℓ hu => by
    have htime : tr.time i = sp.ts s + 6 * sp.Δ := hu.2.2.1
    have hts : sp.ts s ≤ tr.time i := by linarith [sp.toParams.hΔ]
    have := (AC.ts_le_iff_le_slot sp hi0 (s : Int)).1 hts
    omega
  rcases hl with ⟨-, ⟨ℓ, -, hu, -⟩ | ⟨-, -, -, hsl, -⟩⟩ | ⟨ℓ, -, hu, -⟩
  · exact (hupd ℓ hu).trans hm
  · have hs : sp.slot (tr.time i) = s := hsl
    omega
  · exact (hupd ℓ hu).trans hm

/-- **S1 for a source and a high origin.** On the healed chain with S1 (members of the healed
family within `b` are pairwise compatible), a source is compatible with every high origin written
at a time `≤ b`. -/
theorem healed_source_compatible_highOrigin_at
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    {rL rO : Nat} {b : Time}
    (hS1 : ∀ C s C' s', HealedOrigin tr H g rL rO C s b → HealedOrigin tr H g rL rO C' s' b →
      Compatible (tr.HonestBlocksAt H) C C')
    {C : AC.Blk sp.n (List (FG.Att sp.n))} (hC : OnHealedChain tr H g rL rO C b)
    {x : Fin sp.n} {i j : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))} (hib : tr.time i ≤ b)
    (hO : Healing.Growing.HighOrigin tr H g x i j O) :
    Compatible (tr.HonestBlocksAt H) C O :=
  OnHealedChain.compatible hrun hnc hS1 hC (HealedOrigin.of_high hib hO)

/-- **S1 for two sources.** Two blocks on the healed chain are compatible, given S1. -/
theorem healed_sources_compatible_at
    (hrun : Growing.GoldilocksRun proposer dg H tr ini) (hnc : NoCollRun dg tr)
    {rL rO : Nat} {b : Time}
    (hS1 : ∀ C s C' s', HealedOrigin tr H g rL rO C s b → HealedOrigin tr H g rL rO C' s' b →
      Compatible (tr.HonestBlocksAt H) C C')
    {C C' : AC.Blk sp.n (List (FG.Att sp.n))} (hC : OnHealedChain tr H g rL rO C b)
    (hC' : OnHealedChain tr H g rL rO C' b) : Compatible (tr.HonestBlocksAt H) C C' := by
  obtain ⟨D', s', hD', hC'D'⟩ := onHealedChain_iff.1 hC'
  exact (compatible_of_anc_left (honestBlocksAt_coherent hrun hnc) hC'D'
    (OnHealedChain.compatible hrun hnc hS1 hC hD').symm).symm

/-- **S2 for a block below a member.** A block `B` below a member `C` of the healed family of
label `s` is extended by every honest vote at a time `≤ b` of a slot after `s`, given S2. -/
theorem healed_source_votes_at {rL rO : Nat} {b : Time}
    (hS2 : ∀ C s, HealedOrigin tr H g rL rO C s b → ∀ y i e, HVoteAt tr H y i e →
      tr.time i ≤ b → s < e.msg.slot → AC.VoteExtends (tr.HonestBlocksAt H) e.msg C)
    {B C : AC.Blk sp.n (List (FG.Att sp.n))} {s : Nat} (hC : HealedOrigin tr H g rL rO C s b)
    (hBC : Anc (tr.HonestBlocksAt H) B C) {y : Fin sp.n} {i : Nat}
    {e : AC.Em sp (List (FG.Att sp.n))}
    (hv : HVoteAt tr H y i e) (hib : tr.time i ≤ b) (hs : s < e.msg.slot) :
    AC.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  obtain ⟨W, hWU, hWr, hCW⟩ := hS2 C s hC y i e hv hib hs
  exact ⟨W, hWU, hWr, hBC.trans hCW⟩

end Consensus.Goldilocks.Compose.Growing

end

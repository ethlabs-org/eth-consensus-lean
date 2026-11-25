module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesPrefix
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowCast
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.CurrentPassage
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Causal read-lock and anchor bounds for warm votes -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
variable {hold : Time}

/-- The current optimistic residue uses only casts strictly before this cast. -/
theorem FrameWindow.read_locks_below_of_earlier_heads_at
    {g ΔF b : Time} {s₀ p floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts p + sp.Δ) floor kindJ J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hsp : s₀ ≤ p) (hp0 : 0 < p)
    (hpb : sp.ts p + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts p + sp.Δ)) (hdes : z = proposer p)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = p)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = p)
    (hmargin : s₀ + 2 * sp.k ≤ p)
    (hIH : ∀ x j ev, j < i → x ∈ H (tr.time j) → AC.VoteAt tr.projAC x j ev →
      ev.msg.slot = p → ev.msg.head = P.root)
    {l : AC.Lock} (hl : l ∈ e.readPoint.locks) (hlive : p ≤ l.slot + sp.k)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ell.frame.tree)
    (hBr : B.root = l.block) (hK : CommitteeHalfUpTo tr H K g b) :
    Anc (tr.HonestBlocksAt H) B P := by
  obtain ⟨_, hdom, hpass⟩ := KernelProof.current_lock_passage_of_regular_base_at hframe hrun
    hnc hsvc hawake hf hcatch hnr hm hsp hp0 hpb hz hdes hP hPs hy hc hes hmargin hl hlive hB hBr
    hK
  rcases hpass with h | ⟨hs, _⟩
  · exact h
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hri := hac.upTo (hrun.time_nonneg i)
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hcast : AC.CastAt (tr.projAC.upTo (tr.time i)) y i ell e := ⟨hci, hc.2⟩
  have hPhi := AC.frameIn_of_callAt hri.localRun hy hci
  have hslot := (AC.castAt_spec hri.localRun hy hcast).2.1.symm.trans hes
  have ht := AC.vote_time_le hri.localRun hy ⟨ell, hcast⟩
  change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
  change sp.slot (tr.time i) = p at hslot
  rw [hslot] at ht
  have hcs := hK.cs2 p
    (by
      have ht : sp.ts s₀ ≤ sp.ts p := (AC.ts_le_iff sp).2 (by exact_mod_cast hsp)
      linarith [sp.toParams.hΔ])
    (by linarith [sp.toParams.hΔ]) (tr.time i) (hrun.time_nonneg i) (ht.trans hpb)
  exact AC.current_read_lock_below_of_earlier_heads hri hy hcast hl (hs.trans hes.symm)
    K (AC.CommitteePAt.upTo hrun.time_mono hrun.antitone hK.facts.hP _)
    (by rw [hes]; omega)
    (hPhi.2 hdom.1.1)
    (fun x hx j hji ev hv hs' => by
      obtain ⟨ellx, hcx, hex⟩ := hv
      obtain ⟨hjd, hcx⟩ := (Trace.upTo_callAt _).mp hcx
      exact hIH x j ev hji (hrun.antitone hjd hx) ⟨ellx, hcx, hex⟩ (hs'.trans hes))
    (hPhi.2 hB) hBr

/-- All live read-lock images, hence the deepest actual anchor, lie below the proposal. -/
theorem FrameWindow.vote_anchor_below_of_earlier_heads_at
    {g ΔF b : Time} {s₀ p floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts p + sp.Δ) floor kindJ J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hsp : s₀ ≤ p) (hp0 : 0 < p)
    (hpb : sp.ts p + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts p + sp.Δ)) (hdes : z = proposer p)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = p)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = p)
    (hmargin : s₀ + 2 * sp.k ≤ p)
    (hIH : ∀ x j ev, j < i → x ∈ H (tr.time j) → AC.VoteAt tr.projAC x j ev →
      ev.msg.slot = p → ev.msg.head = P.root) (hK : CommitteeHalfUpTo tr H K g b) :
    Anc (tr.HonestBlocksAt H) (AC.getAnchor sp e.readPoint ell.frame (tr.time i)) P := by
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hri := hac.upTo (hrun.time_nonneg i)
  have hci : (tr.projAC.upTo (tr.time i)).CallAt y i ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hcast : AC.CastAt (tr.projAC.upTo (tr.time i)) y i ell e := ⟨hci, hc.2⟩
  have hPhi := AC.frameIn_of_callAt hri.localRun hy hci
  have hPv := (KernelProof.proposal_viable_at_cast_at hframe hrun hnc hsvc hf hnr
    (by linarith [sp.toParams.hΔ]) hsp hp0 hpb hz hdes hP hPs hy hc hes).1
  have hfP : Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P :=
    Anc.mono hPhi.2 (hPhi.1.fcRoot_anc_viableHeads P hPv)
  have hlk : ∀ B ∈ AC.liveLockBlocks sp e.readPoint.locks ell.frame (tr.time i),
      Anc (tr.HonestBlocksAt H) B P := by
    intro B hB
    obtain ⟨l, hl, B₀, hB₀, hB₀r, hlive, rfl⟩ := AC.mem_liveLockBlocks_of_wf hPhi.1
      (AC.castAt_readPoint_locksWF hri.localRun hrun.vstart hy hcast) hB
    have hslot := (AC.castAt_spec hri.localRun hy hcast).2.1
    have hB₀P := hframe.read_locks_below_of_earlier_heads_at hrun hnc hsvc hawake hf hcatch
      hnr hm hsp hp0 hpb hz hdes hP hPs hy hc hes hmargin hIH hl
      (by rw [← hes, hslot]; exact hlive) hB₀ hB₀r hK
    exact (Anc.mono hPhi.2 (AC.viableAncestor_anc hPhi.1 hB₀).2).trans hB₀P
  unfold AC.getAnchor
  rcases hD : AC.deepest ell.frame
      (AC.liveLockBlocks sp e.readPoint.locks ell.frame (tr.time i) ∪ {ell.frame.fcRoot})
      with _ | D
  · exact hfP
  · rcases (AC.deepest_mem hD).1 with h | h
    · exact hlk D h
    · exact (Set.mem_singleton_iff.1 h) ▸ hfP

end Consensus.Goldilocks.Healing.Growing

end

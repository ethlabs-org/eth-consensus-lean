module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularClassification
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.HeadLock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Lemmas.Tactic.Linarith
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase

public section

/-! # The next votes after a supporter of label `s`, under growing faults

`FrameWindow.next_votes_of_supporter_at`: the supporter is honest at its
cast of slot `s`, every later voter at its own cast, and ancestry is in the blocks held while
honest. The cast head is classified on the supporter's honest prefix
(`vote_head_classification_of_service_at`): a viable head goes to the caller's base step, a
common-J head propagates through the shared root of the window, and an optimistic anchor goes to
the caller's optimistic step with the write honest at its own cut. -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
variable {hold : Time}

namespace Core

/-- Classification and propagation are independent of the frame's root policy. -/
theorem next_votes_of_supporter_at
    {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
    {frameOf : NodeState (goldilocksNode sp ro) → AC.Frm sp.n (List (FG.Att sp.n))}
    {ini : Fin sp.n → (goldilocksNode sp ro).State} {s : Nat}
    {kindJ : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrun : Consensus.Goldilocks.GoldilocksRunCore u frameOf proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {z : Fin sp.n} {q : Nat} (hz : z ∈ H (tr.time q))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC z q ell e) (hes : e.msg.slot = s)
    (hQU : Q ∈ tr.HonestBlocksAt H) (hQr : Q.root = e.msg.head)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hclass : ∃ Hd ∈ ell.frame.tree, Hd.root = e.msg.head ∧
      (Hd ∈ ell.frame.viableHeads ∨ (kindJ ∧ Hd = J) ∨
        (Hd = AC.getAnchor sp e.readPoint ell.frame (tr.time q) ∧
          ∃ l ∈ e.readPoint.locks, l.slot = e.msg.slot ∧
          ∃ a ≤ q, ∃ D CV, z ∈ H (tr.time a) ∧
            AC.OptimisticLockAt tr.projAC z a e.msg.slot D CV ∧
            sp.ts e.msg.slot ≤ tr.time a ∧ tr.time a < sp.ts e.msg.slot + 2 * sp.Δ ∧
            3 * sp.committeeSize ≤ 4 * (AC.voters CV).ncard ∧ ell.frame.Anc Hd D)))
    (hbase : Q ∈ ell.frame.tree → Q ∈ ell.frame.viableHeads →
      ∀ y i ev, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X)
    (hcommon : kindJ → Q = J →
      ∀ y i ev, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X)
    (hoptimistic : Q = AC.getAnchor sp e.readPoint ell.frame (tr.time q) →
      ∀ a D CV, z ∈ H (tr.time a) → AC.OptimisticLockAt tr.projAC z a s D CV →
      Anc (tr.HonestBlocksAt H) Q D →
      ∀ y i ev, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        AC.VoteExtends (tr.HonestBlocksAt H) ev.msg Q) :
    ∀ y i ev, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X := by
  obtain ⟨Hd, hHd, hHdr, hclass⟩ := hclass
  have hPhiU := (hrun.frameIn_at hnc hz hc.1).2
  have hEQ : Hd = Q := (hrun.coherent hnc).1
    (hPhiU hHd) hQU (hHdr.trans hQr.symm)
  rw [hEQ] at hHd hclass
  rcases hclass with hv | hj | ho
  · exact hbase hHd hv
  · exact hcommon hj.1 hj.2
  · obtain ⟨hA, l, hl, hls, a, hai, D, CV, hza, hop, -, -, -, hQD⟩ := ho
    have hheads := hoptimistic hA a D CV hza (hes ▸ hop) (hQD.mono hPhiU)
    intro y i ev hy hv hesv
    obtain ⟨W, hW, hWr, hQW⟩ := hheads y i ev hy hv hesv
    exact ⟨W, hW, hWr, hXQ.trans hQW⟩

end Core

/-- Supporter classification separates viable, common-root and optimistic-anchor cases. -/
theorem FrameWindow.next_votes_of_supporter_at {s₀ s floor : Nat}
    {kindJ : Prop} {J X Q : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts s + 6 * sp.Δ) floor kindJ J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts ((s - 1 : Nat) : Int))
    (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {z : Fin sp.n} {q : Nat} (hz : z ∈ H (tr.time q))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC z q ell e) (hes : e.msg.slot = s)
    (hQU : Q ∈ tr.HonestBlocksAt H) (hQr : Q.root = e.msg.head)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (hbase : Q ∈ ell.frame.tree → floor ≤ ((tr.state z q).fg.σ Q.root).h →
      (kindJ → Anc (tr.HonestBlocksAt H) J X) →
      ∀ y i ev, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X)
    (hoptimistic : Q = AC.getAnchor sp e.readPoint ell.frame (tr.time q) →
      ∀ a D CV, z ∈ H (tr.time a) → AC.OptimisticLockAt tr.projAC z a s D CV →
      Anc (tr.HonestBlocksAt H) Q D →
      ∀ y i ev, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        AC.VoteExtends (tr.HonestBlocksAt H) ev.msg Q) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ y i ev, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X := by
  have hΔ := sp.toParams.hΔ
  have hU := Compose.Growing.honestBlocksAt_coherent hrun hnc
  have hprev : sp.ts ((s - 1 : Nat) : Int) = sp.ts s - 4 * sp.Δ := by
    rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one, AC.ts_sub_one]
  have hq0 := hrun.time_nonneg q
  have htq := (Compose.Growing.cast_head_fcRoot_at hrun hnc hz hc).2
  rw [hes] at htq
  have hslot := (Compose.Growing.castAt_spec_at hrun hnc hz hc).2.1.symm.trans hes
  have hqt : sp.ts s₀ ≤ tr.time q :=
    (AC.ts_le_iff_le_slot sp hq0 _).2 (by rw [hslot]; omega)
  have hqhi : tr.time q ≤ sp.ts s + 6 * sp.Δ := by linarith only [hΔ, htq]
  have hrootVotes : kindJ → Anc (tr.HonestBlocksAt H) X J →
      ∀ y i ev, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        AC.VoteExtends (tr.HonestBlocksAt H) ev.msg X := by
    intro hk hXJ y i ev hy ⟨elly, hcy, hey⟩ hev
    have hi0 := hrun.time_nonneg i
    have hcast : AC.CastAt tr.projAC y i elly ev := ⟨hcy, hey⟩
    obtain ⟨hPhi, hPhiU⟩ := Compose.Growing.frameIn_at hrun hnc hy hcy
    have hsl := (Compose.Growing.castAt_spec_at hrun hnc hy hcast).2.1.symm.trans hev
    have hlo : sp.ts s₀ ≤ tr.time i :=
      (AC.ts_le_iff_le_slot sp hi0 _).2 (by rw [hsl]; push_cast; omega)
    have hhi := (Compose.Growing.cast_head_fcRoot_at hrun hnc hy hcast).2
    rw [hev] at hhi
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := AC.ts_succ s
    have hhi' : tr.time i ≤ sp.ts s + 6 * sp.Δ := by linarith only [hΔ, hhi, hts]
    have hr := (Compose.Growing.acRun_upTo hrun hnc hi0).localRun
    have hcast' := Compose.Growing.ac_castAt_upTo.mpr ⟨le_rfl, hcast⟩
    obtain ⟨W, hW, hWr, hRW⟩ := AC.castAt_head_anc hr hy hcast' (Or.inr rfl)
      (fun L hL => (AC.liveLockBlock_candidate hPhi hL).elim
        (fun h => Or.inr h.2.1) Or.inl) Relation.ReflTransGen.refl
    have hRW := hRW.mono hPhiU
    rw [Compose.Growing.frame_of_projAC_at hrun hy hcy] at hRW
    have hkind := (hframe.kind_iff y i hy hlo hhi').mpr hk
    have hroot : (tr.state y i).fg.fcRoot = J :=
      (ite_eq_left hkind).trans (hframe.root_eq y i hy hlo hhi' hk)
    change Anc (tr.HonestBlocksAt H) (tr.state y i).fg.fcRoot W at hRW
    rw [hroot] at hRW
    exact ⟨W, hPhiU hW, hWr, hXJ.trans hRW⟩
  obtain ⟨Hd, hHd, hHdr, hclass⟩ := vote_head_classification_of_service_at hframe
    hrun hnc hsvc hawake hf hcatch hnr hz hc hqhi (hqhi.trans hmb)
    (hes ▸ hwarm) (hes ▸ hpos) (hes ▸ hs₀) (by simpa only [hes] using hm) (by
      rw [hes]; simp only [AC.freeze]
      have hcast : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by omega
      rw [← hcast]; linarith only [hΔ, hm]) hK
  have hPhi := Compose.Growing.frameIn_at hrun hnc hz hc.1
  have hfr := Compose.Growing.frame_of_projAC_at hrun hz hc.1
  apply Core.next_votes_of_supporter_at hrun.toCore hnc hz hc hes hQU hQr hXQ
    ⟨Hd, hHd, hHdr, hclass.imp And.right (fun h => h)⟩
    (hoptimistic := hoptimistic)
  · intro hQt hv
    have hvQ := hv
    rw [hfr] at hvQ
    have hJQ : kindJ → Anc (tr.HonestBlocksAt H) J Q := by
      intro hk
      have hkind := (hframe.kind_iff z q hz hqt hqhi).mpr hk
      have hroot := (hPhi.1.fcRoot_anc_viableHeads Q hv).mono hPhi.2
      rw [hfr] at hroot
      change Anc (tr.HonestBlocksAt H) (tr.state z q).fg.fcRoot Q at hroot
      rwa [show (tr.state z q).fg.fcRoot = (tr.state z q).fg.J from ite_eq_left hkind,
        hframe.root_eq z q hz hqt hqhi hk] at hroot
    by_cases hJX : kindJ → Anc (tr.HonestBlocksAt H) J X
    · apply hbase hQt ?_ hJX
      rw [← hframe.floor_eq z q hz hqt hqhi]
      exact hvQ.2.2.2
    · push Not at hJX
      obtain ⟨hk, hn⟩ := hJX
      exact hrootVotes hk ((AC.anc_total hU hXQ (hJQ hk)).resolve_right hn)
  · intro hk hQJ
    exact hrootVotes hk (hQJ ▸ hXQ)

end Consensus.Goldilocks.Healing.Growing.KernelProof

end

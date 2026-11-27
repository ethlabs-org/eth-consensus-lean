module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowEndpoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowRegularBoundary
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FastLockRenewalCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorFast
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Prot
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Update
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Fresh fast locks at every slot of a pre-reset frame window

In a frame window that holds from before a warm honest proposal `P` of slot `u` through the slot
`N + 1` update, every node honest at the update of a slot `r ∈ [u, N]` passes the fast test of
that update on a block extending `P`, unvetoed by its live locks. The proposers of the slots after
`u` need not be honest: the honest votes of those slots extend `P` by the regular write of slot
`u`, and their heads, held by their honest voters, are above every honest finalized tip of the
window because `P` is floor-viable there. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}
variable {hold : Time}

/-- The window's common floor puts every honest finalized tip in the window, within the
horizon, below a floor-viable block. -/
theorem FrameWindow.finalized_below_of_witness_at {lo hi : Time} {floor : Nat}
    {kindJ : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H lo hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {b : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c)) (hcb : tr.time c ≤ b)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ P.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J P) :
    ∀ x q, x ∈ H (tr.time q) → lo ≤ tr.time q → tr.time q ≤ hi → tr.time q ≤ b →
      Anc (tr.HonestBlocksAt H) (tr.state x q).fg.F P :=
  fun _ q hx hlo hhi hqb => hframe.finalized_below_descendant_at hrun hnc hx hz hz
    (sp.toParams.fg.faults_lt_quorum_margin
      (hf _ (le_max_of_le_left (hrun.time_nonneg q)) (max_le hqb hcb))) hlo hhi hP hh hJ hP .refl

/-- **The update of a later slot extends `P`.** When every honest vote of slot `s + 1` extends a
block `P` above the finalized tip of every honest observation in `[lo, hi]`, the update of slot
`s + 1` of a node honest there, inside `[lo, hi]`, confirms a block extending `P` and its fast
test selects one: the honest votes reach it before `t_{s+1} + 2Δ` with their heads, wherever
those heads were proposed, because the heads are above its finalized tip. At the slot committees
`K` of a run from `K`'s committee start. -/
theorem update_result_extends_of_finalized_at {K : AC.CommitteeDict sp.n}
    {lo hi : Time}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartUpTo tr H (gbar g) b)
    {s : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts (s + 1 : Nat))
    (hjoin : ∀ x, x ∈ H (sp.ts (s + 1 : Nat) + sp.Δ) →
      AC.JoinedAt tr.projAC x (sp.ts (s + 1 : Nat) + sp.Δ))
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hfin : ∀ x q, x ∈ H (tr.time q) → lo ≤ tr.time q → tr.time q ≤ hi → tr.time q ≤ b →
      Anc (tr.HonestBlocksAt H) (tr.state x q).fg.F P) (hPg : P.root ≠ sp.genesisRoot)
    (hext : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC y k (s + 1) ell)
    (hklo : lo ≤ tr.time k) (hkhi : tr.time k ≤ hi) (hkb : tr.time k ≤ b)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ C, AC.getConfirmation sp (tr.projAC.state y k) ell.frame (s + 1) = some C ∧
      Anc (tr.HonestBlocksAt H) P C ∧
      ∃ D, AC.fastSelect sp (tr.projAC.state y k) ell.frame (s + 1) C = some D ∧
        Anc (tr.HonestBlocksAt H) P D := by
  exact Core.update_result_extends_of_finalized_at hrun.toCore hnc hsvc hawake hf hcatch
    hnr hm hjoin hfin hPg hext hy hu hklo hkhi hkb hK

/-- **The update of a later slot extends `P`.** When every honest vote of slot `s + 1` extends a
floor-viable block `P`, the update of slot `s + 1` of a node honest there, inside the window,
confirms a block extending `P` and its fast test selects one: the honest votes reach it before
`t_{s+1} + 2Δ` with their heads, wherever those heads were proposed, because the heads are above
its finalized tip (`update_result_extends_of_finalized_at`). At the slot committees `K` of a run
from `K`'s committee start. -/
theorem FrameWindow.update_result_extends_at {K : AC.CommitteeDict sp.n}
    {lo hi : Time} {floor : Nat} {kindJ : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H lo hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts (s + 1 : Nat))
    (hjoin : ∀ x, x ∈ H (sp.ts (s + 1 : Nat) + sp.Δ) →
      AC.JoinedAt tr.projAC x (sp.ts (s + 1 : Nat) + sp.Δ))
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c)) (hcb : tr.time c ≤ b)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ P.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J P) (hPg : P.root ≠ sp.genesisRoot)
    (hext : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC y k (s + 1) ell)
    (hklo : lo ≤ tr.time k) (hkhi : tr.time k ≤ hi) (hkb : tr.time k ≤ b)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ C, AC.getConfirmation sp (tr.projAC.state y k) ell.frame (s + 1) = some C ∧
      Anc (tr.HonestBlocksAt H) P C ∧
      ∃ D, AC.fastSelect sp (tr.projAC.state y k) ell.frame (s + 1) C = some D ∧
        Anc (tr.HonestBlocksAt H) P D := by
  exact update_result_extends_of_finalized_at hrun hnc hsvc hawake hf hcatch
    (noRestartUpTo_iff.mpr fun y k hy hr _ => hnr y k hy hr) hm hjoin
    (hframe.finalized_below_of_witness_at hrun hnc hf hz hcb hP hh hJ) hPg hext hy hu hklo hkhi
    hkb hK

/-- **No live lock of a later update conflicts with `P`.** At the update of slot `s + 1` of a
node honest there, every stored lock is compatible with `P` when the honest votes of slots
`s + 1` and `s + 2` extend `P`: an older label went through the unlock of the node's slot-`s + 2`
vote branch, where the honest members of the slot-`s + 1` committee support `P`; a new fast label
lies below an honest vote of its slot; a new slow label lies below the result of an update of
slot `s + 1`, which extends `P`. At the slot committees `K` of a run from `K`'s committee start. -/
theorem update_locks_compatible_of_finalized_at {K : AC.CommitteeDict sp.n}
    {lo hi : Time}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartUpTo tr H (gbar g) b)
    {s : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts (s + 1 : Nat)) (hlo : lo ≤ sp.ts (s + 1 : Nat))
    (hjoin : ∀ x, x ∈ H (sp.ts (s + 1 : Nat) + sp.Δ) →
      AC.JoinedAt tr.projAC x (sp.ts (s + 1 : Nat) + sp.Δ))
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hfin : ∀ x q, x ∈ H (tr.time q) → lo ≤ tr.time q → tr.time q ≤ hi → tr.time q ≤ b →
      Anc (tr.HonestBlocksAt H) (tr.state x q).fg.F P) (hPg : P.root ≠ sp.genesisRoot)
    (hext : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hext₁ : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e → e.msg.slot = s + 2 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC y k (s + 1) ell)
    (hkhi : tr.time k ≤ hi) (hkb : tr.time k ≤ b)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ l ∈ (tr.projAC.state y k).locks, ∀ L ∈ tr.HonestBlocksAt H, L.root = l.block →
      Compatible (tr.HonestBlocksAt H) L P := by
  exact Core.update_locks_compatible_of_finalized_at hrun.toCore hnc hsvc hawake hf hcatch
    hnr hm hlo hjoin hfin hPg hext hext₁ hy hu hkhi hkb hK

/-- **No live lock of a later update conflicts with `P`.** At the update of slot `s + 1` of a
node honest there, every stored lock is compatible with `P` when the honest votes of slots
`s + 1` and `s + 2` extend `P`: an older label went through the unlock of the node's slot-`s + 2`
vote branch, where the honest members of the slot-`s + 1` committee support `P`; a new fast label
lies below an honest vote of its slot; a new slow label lies below the result of an update of
slot `s + 1`, which extends `P` (`update_locks_compatible_of_finalized_at`). At the slot
committees `K` of a run from `K`'s committee start. -/
theorem FrameWindow.update_locks_compatible_at {K : AC.CommitteeDict sp.n}
    {lo hi : Time} {floor : Nat} {kindJ : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H lo hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts (s + 1 : Nat)) (hlo : lo ≤ sp.ts (s + 1 : Nat))
    (hjoin : ∀ x, x ∈ H (sp.ts (s + 1 : Nat) + sp.Δ) →
      AC.JoinedAt tr.projAC x (sp.ts (s + 1 : Nat) + sp.Δ))
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c)) (hcb : tr.time c ≤ b)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ P.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J P) (hPg : P.root ≠ sp.genesisRoot)
    (hext : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hext₁ : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e → e.msg.slot = s + 2 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC y k (s + 1) ell)
    (hkhi : tr.time k ≤ hi) (hkb : tr.time k ≤ b)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ l ∈ (tr.projAC.state y k).locks, ∀ L ∈ tr.HonestBlocksAt H, L.root = l.block →
      Compatible (tr.HonestBlocksAt H) L P := by
  exact update_locks_compatible_of_finalized_at hrun hnc hsvc hawake hf hcatch
    (noRestartUpTo_iff.mpr fun y k hy hr _ => hnr y k hy hr) hm hlo hjoin
    (hframe.finalized_below_of_witness_at hrun hnc hf hz hcb hP hh hJ) hPg hext hext₁ hy hu
    hkhi hkb hK

/-- The fast test of a block passes at its ancestors. -/
private theorem fastTest_of_anc {FGP : Type} {A : AC.ACState sp.n} {Φ : AC.Frm sp.n FGP}
    {s : Nat} {B D : AC.Blk sp.n FGP} (hBD : Φ.Anc B D) (hD : AC.FastTest sp A Φ s D) :
    AC.FastTest sp A Φ s B :=
  hD.trans (Nat.mul_le_mul_left 2
    (Set.ncard_le_ncard (AC.supporters_antitone sp FGP Φ _ _ B D hBD) (Set.toFinite _)))

/-- **The fast update of an unvetoed fast block.** At an update whose result `C` extends a
non-genesis block `P` of the frame that passes the fast test and that no live lock vetoes, the
deepest unvetoed fast block of the path, the block of the update's fast lock, extends `P`. -/
theorem fast_update_of_unvetoed_at
    {y : Fin sp.n} {k s : Nat} {ell : ACLabel (goldilocksNode sp)}
    (hy : y ∈ H (tr.time k))
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hu : AC.UpdateAt tr.projAC y k s ell)
    {C P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hconf : AC.getConfirmation sp (tr.projAC.state y k) ell.frame s = some C)
    (hPt : P ∈ ell.frame.tree) (hPg : P.root ≠ sp.genesisRoot) (hPC : ell.frame.Anc P C)
    (hnv : ¬ AC.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P)
    (hfast : AC.FastTest sp (tr.projAC.state y k) ell.frame s P) :
    ∃ D CV, AC.FastUpdateAt tr.projAC y k s D CV ∧ Anc (tr.HonestBlocksAt H) P D :=
  Core.fast_update_of_unvetoed_at hy hrun.toCore hnc hu hconf hPt hPg hPC hnv hfast

/-- The renewal and the window facts behind it. -/
private theorem pre_core_at {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} {s₀ u N floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts (N + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hmb : sp.ts (N + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hK : CommitteeHalfUpTo tr H K g b) :
    (∀ r, u ≤ r → r ≤ N → ∀ y, y ∈ H (sp.ts r + 6 * sp.Δ) →
      ∃ j D CV, AC.FastUpdateAt tr.projAC y j r D CV ∧ Anc (tr.HonestBlocksAt H) P D) ∧
      (u ≤ N → P.root ≠ sp.genesisRoot ∧ ∃ z₀ c, z₀ ∈ H (tr.time c) ∧ tr.time c ≤ b ∧
        P ∈ (tr.state z₀ c).fg.tree ∧ floor ≤ ((tr.state z₀ c).fg.σ P.root).h ∧
        (kindJ → Anc (tr.HonestBlocksAt H) J P) ∧
        (u + 1 ≤ N → ∀ m, u + 1 ≤ m → m ≤ N + 1 → ∀ x i e, x ∈ H (tr.time i) →
          AC.VoteAt tr.projAC x i e → e.msg.slot = m →
            AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)) := by
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hstep (a : Nat) : sp.ts (a + 1 : Nat) = sp.ts a + 4 * sp.Δ := AC.ts_succ a
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hsubw {lo hi : Time} (hl : sp.ts s₀ ≤ lo) (hh : hi ≤ sp.ts (N + 1 : Nat) + 2 * sp.Δ) :
      FrameWindow tr H lo hi floor kindJ J :=
    ⟨fun w i hw hlo hhi => hframe.floor_eq w i hw (hl.trans hlo) (hhi.trans hh),
     fun w i hw hlo hhi => hframe.kind_iff w i hw (hl.trans hlo) (hhi.trans hh),
     fun w i hw hlo hhi => hframe.root_eq w i hw (hl.trans hlo) (hhi.trans hh)⟩
  have hsu : sp.ts s₀ ≤ sp.ts u := hts (by omega)
  have hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u := by linarith
  -- the slot-`u` update of a node honest there writes a fast lock on `P` itself
  have base : u ≤ N → ∀ y, y ∈ H (sp.ts u + 6 * sp.Δ) →
      ∃ j ell, AC.UpdateAt tr.projAC y j u ell ∧ P.root ≠ sp.genesisRoot ∧
        ∃ D CV, AC.FastUpdateAt tr.projAC y j u D CV ∧ Anc (tr.HonestBlocksAt H) P D := by
    intro huN y hy
    have huN' := hts (show u + 1 ≤ N + 1 by omega)
    have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ = sp.ts u + 6 * sp.Δ := by rw [hstep]; ring
    have hun := KernelProof.honest_vote_heads_eq_at (hsubw le_rfl (by linarith)) hrun hnc hsvc
      hawake hf hcatch hnr hm hwarm (by linarith) hz hdes hP hPs hK
    have hjoin := fun w hw => joined_voteTime_of_warm_frame_at hrun hnr hm
      (by omega : s₀ + 1 ≤ u) (y := w) hw
    obtain ⟨j, ell, hu, hconf, hnv, hfast, -⟩ :=
      KernelProof.fresh_fast_lock_update_at hrun hnc hsvc hawake hf hcatch hnr hmargin hjoin
        (by linarith) (hsubw hsu (by linarith)) hz hdes hP hPs hun (hT ▸ hy) hK
    have hj : y ∈ H (tr.time j) := by
      have h : tr.time j = sp.ts u + 6 * sp.Δ := hu.2.2.1
      rw [h]; exact hy
    obtain ⟨⟨hPt, hPg, -⟩, hPf⟩ := (AC.deepest_mem hfast).1
    exact ⟨j, ell, hu, hPg, fast_update_of_unvetoed_at hj hrun hnc hu hconf hPt hPg .refl hnv hPf⟩
  have hwit : (u ≤ N → P.root ≠ sp.genesisRoot ∧ ∃ z₀ c, z₀ ∈ H (tr.time c) ∧ tr.time c ≤ b ∧
          P ∈ (tr.state z₀ c).fg.tree ∧ floor ≤ ((tr.state z₀ c).fg.σ P.root).h ∧
          (kindJ → Anc (tr.HonestBlocksAt H) J P) ∧
          (u + 1 ≤ N → ∀ m, u + 1 ≤ m → m ≤ N + 1 → ∀ x i e, x ∈ H (tr.time i) →
            AC.VoteAt tr.projAC x i e → e.msg.slot = m →
              AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)) := by
    intro huN
    -- an honest node at the slot-`u` update supplies the regular origin and the witness of `P`
    have hu6 : sp.ts u + 6 * sp.Δ ≤ b := by
      have := hts (show u + 1 ≤ N + 1 by omega)
      linarith [hstep u]
    obtain ⟨y₀, hy₀⟩ : (H (sp.ts u + 6 * sp.Δ)).Nonempty := by
      have hcs := hK.cs2 u (by linarith) (by linarith) (sp.ts u + 6 * sp.Δ)
        (by linarith [AC.gbar_nonneg g]) hu6
      have hsplit : (K.committee u ∩ H (sp.ts u + 6 * sp.Δ)).ncard +
          (K.committee u ∩ (H (sp.ts u + 6 * sp.Δ))ᶜ).ncard = sp.committeeSize := by
        rw [← hK.facts.hsize u, Set.inter_comm (K.committee u) (H (sp.ts u + 6 * sp.Δ))ᶜ,
          ← Set.sdiff_eq_compl_inter]
        exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
      obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (s := K.committee u ∩
        H (sp.ts u + 6 * sp.Δ)) (by omega)
      exact ⟨x, hx.2⟩
    obtain ⟨c, ell₀, hu₀, hPg, D₀, CV₀, hfu₀, hPD₀⟩ := base (by omega) y₀ hy₀
    have hc : tr.time c = sp.ts u + 6 * sp.Δ := hu₀.2.2.1
    have hz₀ : y₀ ∈ H (tr.time c) := by rw [hc]; exact hy₀
    have hcb : tr.time c ≤ b := hc ▸ hu6
    -- `P` is floor-viable at that update
    have hu1N : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ sp.ts (N + 1 : Nat) + 2 * sp.Δ := by
      have := hts (show u + 1 ≤ N + 1 by omega); linarith
    obtain ⟨-, -, hvP⟩ := (hsubw hsu hu1N).proposal_viable_after_votes_at
      hrun hnc hsvc hf hnr (by linarith) (hu1N.trans hmb)
      hz hdes hP hPs hz₀ hu₀.1 (by rw [hc]; linarith) (by rw [hc, hstep]; linarith)
    have hclo : sp.ts s₀ ≤ tr.time c := by rw [hc]; linarith
    have hchi : tr.time c ≤ sp.ts (N + 1 : Nat) + 2 * sp.Δ := by
      have := hts (show u + 1 ≤ N + 1 by omega); rw [hc]; linarith [hstep u]
    have hfr₀ := (hrun.cutLaw y₀ c (.ac ell₀) (Compose.projAC_callAt.mp hu₀.1) hz₀).1
    rw [hfr₀] at hvP
    have hPz : P ∈ (tr.state y₀ c).fg.tree := hvP.1
    have hh : floor ≤ ((tr.state y₀ c).fg.σ P.root).h := by
      rw [← hframe.floor_eq y₀ c hz₀ hclo hchi]; exact hvP.2.2.2
    have hJ : kindJ → Anc (tr.HonestBlocksAt H) J P := fun hkd => by
      rw [← hframe.root_eq y₀ c hz₀ hclo hchi hkd]
      have hroot : (tr.state y₀ c).fg.fcRoot = (tr.state y₀ c).fg.J :=
        ite_eq_left ((hframe.kind_iff y₀ c hz₀ hclo hchi).mpr hkd)
      have hanc := hvP.2.2.1
      rw [hroot] at hanc
      exact hanc.mono (fun B hB =>
        ⟨y₀, c, tr.time c, hrun.time_nonneg c, (fun q hq => hrun.time_mono hq.le), hz₀, hB⟩)
    -- every honest vote of the slots `u + 1, …, N + 1` extends `P`
    have hext_of : u + 1 ≤ N → ∀ m, u + 1 ≤ m → m ≤ N + 1 → ∀ x i e, x ∈ H (tr.time i) →
        AC.VoteAt tr.projAC x i e → e.msg.slot = m →
          AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
      intro huN1
      have hreg := (hsubw le_rfl (by linarith)).regular_later_heads_at (N := N + 1) hrun hnc
        hsvc hawake hf hcatch hnr (by omega) (by omega) (by omega) hm (by omega) (by linarith)
        hz₀ (Or.inl ⟨CV₀, hfu₀⟩) hK
      intro m hm1 hm2 x i e hx hv hes
      obtain ⟨W, hW, hWr, hDW⟩ := (hreg m hm1 hm2).1 x i e hx hv hes
      exact ⟨W, hW, hWr, hPD₀.trans hDW⟩
    exact ⟨hPg, y₀, c, hz₀, hcb, hPz, hh, hJ, hext_of⟩
  refine ⟨?_, hwit⟩
  intro r hur hrN y hy
  rcases Nat.eq_or_lt_of_le hur with rfl | hlt
  · obtain ⟨j, -, -, -, h⟩ := base hrN y hy
    exact ⟨j, h⟩
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  obtain ⟨hPg, y₀, c, hz₀, hcb, hPz, hh, hJ, hext_of'⟩ := hwit (by omega)
  have hext_of := hext_of' (by omega)
  -- the update of slot `s + 1`
  have hTs : sp.ts (s + 1 + 1 : Nat) + 2 * sp.Δ = sp.ts (s + 1 : Nat) + 6 * sp.Δ := by
    rw [hstep]; ring
  have hTb : sp.ts (s + 1 + 1 : Nat) + 2 * sp.Δ ≤ b := by
    have := hts (show s + 1 + 1 ≤ N + 1 by omega); linarith
  have hs₀s := hts (show s₀ ≤ s + 1 by omega)
  have hm1 : gbar g + 4 * sp.Δ ≤ sp.ts (s + 1 : Nat) := by linarith
  obtain ⟨k, ell, hu⟩ := update_call_of_awake_at hrun hnc hawake hnr
    (u := s + 1) (by linarith) hTb (by rw [hTs]; exact hy)
  have hk' : tr.time k = sp.ts (s + 1 : Nat) + 6 * sp.Δ := hu.2.2.1
  have hyk : y ∈ H (tr.time k) := by rw [hk']; exact hy
  have hklo : sp.ts s₀ ≤ tr.time k := by rw [hk']; linarith
  have hkhi : tr.time k ≤ sp.ts (N + 1 : Nat) + 2 * sp.Δ := by
    rw [hk', ← hTs]; have := hts (show s + 1 + 1 ≤ N + 1 by omega); linarith
  have hkb : tr.time k ≤ b := hkhi.trans hmb
  have hjoin1 := fun w hw => joined_voteTime_of_warm_frame_at hrun hnr hm
    (by omega : s₀ + 1 ≤ s + 1) (y := w) hw
  have hext1 := hext_of (s + 1) (by omega) (by omega)
  have hext2 := hext_of (s + 2) (by omega) (by omega)
  obtain ⟨C, hconf, hPC, D, hfs, hPD⟩ := hframe.update_result_extends_at hrun hnc hsvc hawake
    hf hcatch hnr hm1 hjoin1 hz₀ hcb hPz hh hJ hPg hext1 hyk hu hklo hkhi hkb hK
  have hlocks := hframe.update_locks_compatible_at hrun hnc hsvc hawake hf hcatch hnr hm1
    hs₀s hjoin1 hz₀ hcb hPz hh hJ hPg hext1 hext2 hyk hu hkhi hkb hK
  have hr := (Compose.goldilocks_ac_projection_from (hrun.upTo (hrun.time_nonneg k))
    (hnc.upTo (tr.time k))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hc' : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩
  have hPhi := AC.frameIn_of_callAt hr hyk hc'
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono (hrun.time_nonneg k)
  have hΦU : ell.frame.tree ⊆ tr.HonestBlocksAt H := fun Q hQ => hsub (hPhi.2 hQ)
  have hfr := (hrun.cutLaw y k (.ac ell) (Compose.projAC_callAt.mp hu.1) hyk).1
  have hFe : ell.frame.F = (tr.state y k).fg.F := by rw [hfr]; rfl
  have hFP : Anc (tr.HonestBlocksAt H) ell.frame.F P := by
    rw [hFe]
    exact hframe.finalized_below_descendant_at hrun hnc hyk hz₀ hz₀
      (sp.toParams.fg.faults_lt_quorum_margin
        (hf _ (le_max_of_le_left (hrun.time_nonneg k)) (max_le hkb hcb)))
      hklo hkhi hPz hh hJ hPz .refl
  obtain ⟨⟨hDt, -, -⟩, hDf⟩ := (AC.deepest_mem hfs).1
  have hCt := (AC.deepest_mem hconf).1.1
  have hPt : P ∈ ell.frame.tree := AC.frame_mem_of_between sp hU hPhi.1 hΦU hDt hPD hFP
  have hPDf : ell.frame.Anc P D := AC.anc_tree_of_anc_U hU hPhi.1 hΦU hPt hPD hDt
  have hPCf : ell.frame.Anc P C := AC.anc_tree_of_anc_U hU hPhi.1 hΦU hPt hPC hCt
  exact ⟨k, fast_update_of_unvetoed_at hyk hrun hnc hu hconf hPt hPg hPCf
    (no_veto_of_lock_roots_compatible_at hrun hnc hyk hu.1 hPt hlocks) (fastTest_of_anc hPDf hDf)⟩


/-- **The fast lock an update writes.** At an update whose result is `C` and whose deepest
unvetoed fast block of the path is `D`, the update stores a fast lock of its slot on the viable
ancestor of `D`, with expiry at least two slots later, while it is live. -/
theorem fastLock_mem_updateConfirmation_of_select {FGP : Type} {A : AC.ACState sp.n}
    {Φ : AC.Frm sp.n FGP} {t : Time} {u : Nat} {C D : AC.Blk sp.n FGP}
    (hconf : AC.getConfirmation sp A Φ u = some C)
    (hD : AC.deepest Φ {X | X ∈ AC.confirmationPath sp Φ C ∧
      ¬ AC.conflictsWithLock sp A.locks Φ t X ∧ AC.FastTest sp A Φ u X} = some D)
    (hDt : D ∈ Φ.tree) (hlive : sp.slot t ≤ u + 2)
    (hcap : ∀ l ∈ A.locks, l.expiry ≤ l.slot + sp.k) (hu : u ≤ sp.slot t) :
    ∃ e, u + 2 ≤ e ∧ (⟨(Φ.viableAncestor D).root, u, true, e⟩ : AC.Lock) ∈
      (AC.updateConfirmation sp A Φ t u).locks :=
  Core.fastLock_mem_updateConfirmation_of_select hconf hD hDt hlive hcap hu

/-- The state after an update of slot `u` of an honest node is the update's result. -/
private theorem post_of_updateAt
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {k u : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC y k u ell) :
    tr.projAC.post k =
      AC.updateConfirmation sp (tr.projAC.state y k) ell.frame (tr.time k) u :=
  Core.post_of_updateAt hrun.toCore hnc hy hu

/-- **The fast floor over one cut of a growing run**: `Compose.fastFloor_run_view` on the prefix
through the cut, for a node honest at the cut. -/
theorem fastFloor_step_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {P : AC.Blk sp.n (List (FG.Att sp.n))} {j m : Nat}
    (hfl : Compose.FastFloorAt tr y k P j m) (hk : sp.slot (tr.time k) ≤ m)
    (hP : P ∈ (tr.state y k).fg.toFrame.tree) (hP' : P ∈ (tr.state y (k + 1)).fg.toFrame.tree)
    (hva : (tr.state y k).fg.toFrame.viableAncestor P = P)
    (hu : (sp.slot (tr.time k) : Int) - 1 ≤ j ∨ Compose.UnlockKeeps tr y k P) :
    Compose.FastFloorAt tr y (k + 1) P j m :=
  Core.fastFloor_step_at hrun.toCore hy hfl hk hP hP' hva hu

/-- **A fresh fast lock is a toFG candidate until its two slots end.** Let an honest node `y`
pass at cut `j` the fast test of its slot-`r` update on a block `D ⪰ P`, where `P` is a viable
head of `y`'s frame at every cut from `j` to a later AC call `i`, and the honest votes of slot
`r + 1` cast by `t_i` extend `P`. While `slot(t_i) ≤ r + 2`, the toFG candidates of the call
hold a block `⪰ P`: the written lock moves (viable ancestor, unlock against the slot-`r + 1`
votes) but stays fast, of slot `r`, and above `P`. At the slot committees `K` of a run from
`K`'s committee start. -/
theorem toFG_candidate_of_viable_head_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g b : Time}
    (hK : CommitteeHalfUpTo tr H K g b)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} {r : Nat} (hgr : gbar g ≤ sp.ts (r + 1 : Nat))
    {y : Fin sp.n} {j : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hfu : AC.FastUpdateAt tr.projAC y j r D CV) (hPD : Anc (tr.HonestBlocksAt H) P D)
    {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y i ell) (hji : j < i)
    (hext : ∀ x k e, x ∈ H (tr.time k) → AC.VoteAt tr.projAC x k e → e.msg.slot = r + 1 →
      tr.time k ≤ tr.time i → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hPk : ∀ k, j ≤ k → k ≤ i → P ∈ (Node.frame (tr.state y k)).tree ∧
      (Node.frame (tr.state y k)).Anc (Node.frame (tr.state y k)).fcRoot P ∧
      P ∈ (Node.frame (tr.state y k)).viableHeads)
    (hib : tr.time i ≤ b)
    (hslot : sp.slot (tr.time i) ≤ r + 2) :
    ∃ B ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i),
      Anc (tr.HonestBlocksAt H) P B :=
  Core.toFG_candidate_of_viable_head_at hrun.toCore hnc hK hgr hfu hPD hy hc hji hext hPk hib hslot

/-- **A fresh fast lock is a toFG candidate until its two slots end.** In a frame window, let an
honest node `y` pass at cut `j` the fast test of its slot-`r` update on a block `D ⪰ P`, for a
floor-viable `P` that the honest votes of slot `r + 1` extend. At any later AC call of `y` in the
window, while `slot(t) ≤ r + 2`, the toFG candidates of the call hold a block `⪰ P`
(`toFG_candidate_of_viable_head_at`: `P` is a viable head of every frame of the window). At
the slot committees `K` of a run from `K`'s committee start. -/
theorem FrameWindow.toFG_candidate_of_fast_update_at {K : AC.CommitteeDict sp.n}
    {lo hi : Time} {floor : Nat} {kindJ : Prop} {J : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H lo hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g b : Time}
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hK : CommitteeHalfUpTo tr H K g b)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c)) (hcb : tr.time c ≤ b)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ (tr.state z c).fg.tree)
    (hh : floor ≤ ((tr.state z c).fg.σ P.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J P)
    {r : Nat} (hgr : gbar g ≤ sp.ts (r + 1 : Nat))
    {y : Fin sp.n} {j : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hfu : AC.FastUpdateAt tr.projAC y j r D CV) (hPD : Anc (tr.HonestBlocksAt H) P D)
    {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y i ell) (hji : j < i)
    (hext : ∀ x k e, x ∈ H (tr.time k) → AC.VoteAt tr.projAC x k e → e.msg.slot = r + 1 →
      tr.time k ≤ tr.time i → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hjlo : lo ≤ tr.time j) (hihi : tr.time i ≤ hi) (hib : tr.time i ≤ b)
    (hslot : sp.slot (tr.time i) ≤ r + 2) :
    ∃ B ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i),
      Anc (tr.HonestBlocksAt H) P B := by
  have hmono := hrun.time_mono
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  obtain ⟨ellj, C, hu, -, hD, -⟩ := id hfu
  have hji' := hmono hji.le
  have hyj : y ∈ H (tr.time j) := hrun.antitone hji' hy
  have hfrj := Compose.Growing.frame_of_projAC_at hrun hyj hu.1
  obtain ⟨hΦj, hΦjU⟩ := Compose.Growing.frameIn_at hrun hnc hyj hu.1
  have hDt := (AC.deepest_mem hD).1.1.1
  have hFPj : Anc (tr.HonestBlocksAt H) ellj.frame.F P := by
    rw [hfrj]
    exact hframe.finalized_below_descendant_at hrun hnc hyj hz hz
      (sp.toParams.fg.faults_lt_quorum_margin
        (hf _ (le_max_of_le_left (hrun.time_nonneg j)) (max_le (hji'.trans hib) hcb)))
      hjlo (hji'.trans hihi) hP hh hJ hP .refl
  have hPj : P ∈ ellj.frame.tree := AC.frame_mem_of_between sp hU hΦj hΦjU hDt hPD hFPj
  have hPyj : P ∈ (tr.state y j).fg.tree := by rw [hfrj] at hPj; exact hPj.1
  -- at every cut of `y` from `j` to `i`, `P` is a viable head of the frame
  have hPk : ∀ k, j ≤ k → k ≤ i → P ∈ (Node.frame (tr.state y k)).tree ∧
      (Node.frame (tr.state y k)).Anc (Node.frame (tr.state y k)).fcRoot P ∧
      P ∈ (Node.frame (tr.state y k)).viableHeads := by
    intro k hjk hki
    have hkt := hmono hki
    have hyk := hrun.antitone hkt hy
    have hklo : lo ≤ tr.time k := hjlo.trans (hmono hjk)
    have hkhi := hkt.trans hihi
    have hPk' : P ∈ (tr.state y k).fg.tree :=
      Compose.Growing.tree_mono_at hrun (hrun.time_nonneg k) hyk (fun q hq => hmono hq.le)
        hjk hPyj
    exact floor_ancestor_mem_frame_at hrun hnc hyk hz
      (sp.toParams.fg.faults_lt_quorum_margin (hf _ (hrun.time_nonneg k) (hkt.trans hib))) hP
      (by rw [hframe.floor_eq y k hyk hklo hkhi]; exact hh)
      (fun hm hcn => by
        have hk := (hframe.kind_iff y k hyk hklo hkhi).mp ⟨hm, hcn⟩
        rw [hframe.root_eq y k hyk hklo hkhi hk]
        exact hJ hk) hPk' .refl
  exact toFG_candidate_of_viable_head_at hrun hnc hK hgr hfu hPD hy hc hji
    hext hPk hib hslot

/-- **A toFG call after the first warm update reads a candidate above `P`.** In a pre-reset
frame window through the update of slot `N + 1`, with a warm honest proposal `P` of slot `u`, every
AC call of an honest node `y` at a time `t` with `t_{u+1} + 2Δ < t ≤ t_{N+1} + 2Δ` (a toFG call at
a signing time, in particular) has a toFG candidate extending `P`. It is the fast lock that `y`
wrote at its update of slot `r = max u (slot(t) − 2)` or `slot(t) − 1`, the latest update strictly
before `t`. The call at `t_{u+1} + 2Δ` itself is the one adjacent to the slot-`u` update of a
node that signs there (`KernelProof.fresh_fast_lock_update_toFG_at`). At the slot committees `K`
of a run from `K`'s committee start. -/
theorem toFG_candidate_pre_at {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} {s₀ u N floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts (N + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hmb : sp.ts (N + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hK : CommitteeHalfUpTo tr H K g b)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y i ell)
    (hlo : sp.ts (u + 1 : Nat) + 2 * sp.Δ < tr.time i)
    (hhi : tr.time i ≤ sp.ts (N + 1 : Nat) + 2 * sp.Δ) :
    ∃ B ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i),
      Anc (tr.HonestBlocksAt H) P B := by
  have hΔ := sp.toParams.hΔ
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hstep (a : Nat) : sp.ts (a + 1 : Nat) = sp.ts a + 4 * sp.Δ := AC.ts_succ a
  have hi0 := hrun.time_nonneg i
  have hib : tr.time i ≤ b := hhi.trans hmb
  have hcore := pre_core_at hframe hrun hnc hsvc hawake hf hcatch hnr hm hwarm hmb hz hdes hP
    hPs hK
  -- the slot of the call and its position in the slot
  set σ := sp.slot (tr.time i) with hσ
  have hσlo : sp.ts σ ≤ tr.time i := (AC.ts_le_iff_le_slot sp hi0 _).2 le_rfl
  have hσhi : tr.time i < sp.ts (σ + 1 : Nat) := by
    by_contra hn
    have := (AC.ts_le_iff_le_slot sp hi0 ((σ + 1 : Nat) : Int)).1 (not_lt.1 hn)
    omega
  have huσ : u + 1 ≤ σ := by
    by_contra hn
    have := hts (show σ + 1 ≤ u + 1 by omega)
    linarith
  have hσN : σ ≤ N + 1 := by
    by_contra hn
    have := hts (show N + 2 ≤ σ by omega)
    have h2 := hstep (N + 1)
    linarith
  -- the latest update strictly before the call
  obtain ⟨r, hur, hrN, hupd, hσr⟩ : ∃ r, u ≤ r ∧ r ≤ N ∧
      sp.ts r + 6 * sp.Δ < tr.time i ∧ σ ≤ r + 2 := by
    by_cases hlate : sp.ts σ + 2 * sp.Δ < tr.time i
    · refine ⟨σ - 1, by omega, by omega, ?_, by omega⟩
      have h := hstep (σ - 1)
      rw [show σ - 1 + 1 = σ by omega] at h
      linarith
    · have hu2 : u + 2 ≤ σ := by
        by_contra hn
        have he : σ = u + 1 := by omega
        rw [he] at hlate
        exact hlate hlo
      refine ⟨σ - 2, by omega, by omega, ?_, by omega⟩
      have h1 := hstep (σ - 2)
      have h2 := hstep (σ - 1)
      rw [show σ - 2 + 1 = σ - 1 by omega] at h1
      rw [show σ - 1 + 1 = σ by omega] at h2
      linarith
  have hyr : y ∈ H (sp.ts r + 6 * sp.Δ) := hrun.antitone hupd.le hy
  obtain ⟨j, D, CV, hfu, hPD⟩ := hcore.1 r hur hrN y hyr
  have hjt : tr.time j = sp.ts r + 6 * sp.Δ := by
    obtain ⟨ellj, -, hu, -⟩ := hfu
    exact hu.2.2.1
  have hji : j < i := by
    by_contra hn
    have := hrun.time_mono (show i ≤ j by omega)
    linarith
  have huN : u + 1 ≤ N := by
    by_contra hn
    have := hts (show N + 1 ≤ u + 1 by omega)
    linarith
  obtain ⟨-, z₀, c, hz₀, hcb, hPz, hh, hJ, hext_of'⟩ := hcore.2 (by omega)
  have hext_of := hext_of' huN
  have hsr := hts (show s₀ ≤ r by omega)
  exact hframe.toFG_candidate_of_fast_update_at hrun hnc hf hK hz₀ hcb hPz hh hJ
    (by have := hts (show r ≤ r + 1 by omega); linarith) hfu hPD hy hc hji
    (fun x k e hx hv hs _ => hext_of (r + 1) (by omega) (by omega) x k e hx hv hs)
    (by rw [hjt]; linarith) hhi hib (by omega)

/-- **A toFG call after the first warm update reads a candidate above `P`, in a real-time frame
window.** `toFG_candidate_pre_at` for a frame window that ends at any `hi ≥ t` (within the
horizon), not at a slot boundary: the window need only reach the call. At the slot committees
`K` of a run from `K`'s committee start. -/
theorem toFG_candidate_pre_within_at {K : AC.CommitteeDict sp.n}
    {g ΔF b hi : Time} {s₀ u floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u) (hhib : hi ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hK : CommitteeHalfUpTo tr H K g b)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y i ell)
    (hlo : sp.ts (u + 1 : Nat) + 2 * sp.Δ < tr.time i) (hhi : tr.time i ≤ hi) :
    ∃ B ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i),
      Anc (tr.HonestBlocksAt H) P B := by
  have hΔ := sp.toParams.hΔ
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (AC.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hstep (a : Nat) : sp.ts (a + 1 : Nat) = sp.ts a + 4 * sp.Δ := AC.ts_succ a
  have hk := sp.two_le_k
  have hi0 := hrun.time_nonneg i
  have hib : tr.time i ≤ b := hhi.trans hhib
  set σ := sp.slot (tr.time i) with hσ
  have hσlo : sp.ts σ ≤ tr.time i := (AC.ts_le_iff_le_slot sp hi0 _).2 le_rfl
  have huσ : u + 1 ≤ σ := by
    by_contra hn
    have hσhi : tr.time i < sp.ts (σ + 1 : Nat) := by
      by_contra hn'
      have := (AC.ts_le_iff_le_slot sp hi0 ((σ + 1 : Nat) : Int)).1 (not_lt.1 hn')
      omega
    have := hts (show σ + 1 ≤ u + 1 by omega)
    linarith
  -- the latest update strictly before the call
  obtain ⟨r, hur, hupd, hσr⟩ : ∃ r, u ≤ r ∧ sp.ts r + 6 * sp.Δ < tr.time i ∧ σ ≤ r + 2 := by
    by_cases hlate : sp.ts σ + 2 * sp.Δ < tr.time i
    · refine ⟨σ - 1, by omega, ?_, by omega⟩
      have h := hstep (σ - 1)
      rw [show σ - 1 + 1 = σ by omega] at h
      linarith
    · have hu2 : u + 2 ≤ σ := by
        by_contra hn
        have he : σ = u + 1 := by omega
        rw [he] at hlate
        exact hlate hlo
      refine ⟨σ - 2, by omega, ?_, by omega⟩
      have h1 := hstep (σ - 2)
      have h2 := hstep (σ - 1)
      rw [show σ - 2 + 1 = σ - 1 by omega] at h1
      rw [show σ - 1 + 1 = σ by omega] at h2
      linarith
  -- the frame window through the update of slot `r`
  have hr6 : sp.ts (r + 1 : Nat) + 2 * sp.Δ = sp.ts r + 6 * sp.Δ := by rw [hstep]; ring
  have hwin : FrameWindow tr H (sp.ts s₀) (sp.ts (r + 1 : Nat) + 2 * sp.Δ) floor kindJ J :=
    ⟨fun w k hw hl hh => hframe.floor_eq w k hw hl (hh.trans (by linarith)),
     fun w k hw hl hh => hframe.kind_iff w k hw hl (hh.trans (by linarith)),
     fun w k hw hl hh => hframe.root_eq w k hw hl (hh.trans (by linarith))⟩
  have hcore := pre_core_at hwin hrun hnc hsvc hawake hf hcatch hnr hm hwarm (by linarith) hz
    hdes hP hPs hK
  have hyr : y ∈ H (sp.ts r + 6 * sp.Δ) := hrun.antitone hupd.le hy
  obtain ⟨j, D, CV, hfu, hPD⟩ := hcore.1 r hur le_rfl y hyr
  have hjt : tr.time j = sp.ts r + 6 * sp.Δ := by
    obtain ⟨ellj, -, hu, -⟩ := hfu
    exact hu.2.2.1
  have hji : j < i := by
    by_contra hn
    have := hrun.time_mono (show i ≤ j by omega)
    linarith
  obtain ⟨-, z₀, c, hz₀, hcb, hPz, hh, hJ, hext_of⟩ := hcore.2 hur
  -- the honest votes of slot `r + 1` extend `P`
  have hext : ∀ x k e, x ∈ H (tr.time k) → AC.VoteAt tr.projAC x k e → e.msg.slot = r + 1 →
      tr.time k ≤ tr.time i → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
    intro x k e hx hv hs hk
    rcases Nat.eq_or_lt_of_le hur with rfl | hlt
    · -- the warm slot's next votes
      have hsu := hts (show s₀ ≤ u by omega)
      have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ hi := by linarith
      have hu1 := hstep u
      have hun := KernelProof.honest_vote_heads_eq_at
        ⟨fun w k hw hl hh => hframe.floor_eq w k hw hl (hh.trans (by linarith)),
         fun w k hw hl hh => hframe.kind_iff w k hw hl (hh.trans (by linarith)),
         fun w k hw hl hh => hframe.root_eq w k hw hl (hh.trans (by linarith))⟩
        hrun hnc hsvc hawake hf hcatch hnr hm hwarm (by linarith) hz hdes hP hPs hK
      have hjoin := fun w hw => joined_voteTime_of_warm_frame_at hrun hnr hm
        (by omega : s₀ + 1 ≤ u) (y := w) hw
      exact FrameWindow.unanimous_next_votes_at
        ⟨fun w k hw hl hh => hframe.floor_eq w k hw (hsu.trans hl) (hh.trans hT),
         fun w k hw hl hh => hframe.kind_iff w k hw (hsu.trans hl) (hh.trans hT),
         fun w k hw hl hh => hframe.root_eq w k hw (hsu.trans hl) (hh.trans hT)⟩
        hrun hnc hsvc hawake hf hcatch hnr (by linarith) hjoin (hT.trans hhib) hz hdes hP hPs
        hun hK x k e hx hv (hk.trans hib) hs
    · exact hext_of hlt (r + 1) (by omega) le_rfl x k e hx hv hs
  have hsr := hts (show s₀ ≤ r by omega)
  exact hframe.toFG_candidate_of_fast_update_at hrun hnc hf hK hz₀ hcb hPz hh hJ
    (by have := hts (show r ≤ r + 1 by omega); linarith) hfu hPD hy hc hji hext
    (by rw [hjt]; linarith) hhi hib (by omega)

end Consensus.Goldilocks.Healing.Growing

end

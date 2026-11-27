module
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

end Consensus.Goldilocks.Healing.Growing

end

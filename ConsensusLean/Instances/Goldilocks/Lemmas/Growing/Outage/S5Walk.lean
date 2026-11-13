module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.S5Geometry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Candidate
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Locks
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Requirements
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Outage under growing faults: the Hi walk, Lo, and the supported rows

At a vote of `y` at cut `i`, `y` honest at `t_i`, from `OutageLockInv D i`:

* `vote_extends_of_hi_at` (H1, vote form): under Hi the walk over the viable vote domain passes
  `P`; every viable head is strictly above `P` by G3′ (`above_of_hi_height_at`, counted at `t_i`);
* `J_anc_of_lo_at`, `not_contest_of_lo_at`: Lo is `Σ.J ⪯ P`, with no contest, at a cut read at
  a time at which its node is honest after every earlier cut;
* `readPoint_liveLockBlocks_compatible_at`: the read point's live locks are compatible with every
  block below `P`; a stored lock by (L) at `t_i`, an optimistic lock of the cast by the fast-lock
  count at the cast's cut;
* `rows_supported_at` (source support): the attestations of `y`'s tree by validators honest at
  `t_i` are sourced by blocks compatible with `P` and extended by a vote, of a node honest at its
  cast, of a slot at most `q`. Each source is below a fast lock of its signer, counted at the
  lock's writing cut. -/

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State}

/-- Two blocks of one coherent set with the same parent root: one below the other is the other. -/
private theorem eq_of_anc_sibling {S : Set (SA.Blk sp.n (List (FG.Att sp.n)))} (hS : Coherent S)
    {Y Y' : SA.Blk sp.n (List (FG.Att sp.n))} (hY' : Y' ∈ S) (hpar : Y'.parent = Y.parent)
    (h : Anc S Y' Y) : Y' = Y := by
  obtain rfl | ⟨Z, hY'Z, hZY⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h
  · rfl
  have hZ : Z ∈ S := hZY.1
  have h₁ := (Anc.slot_le hS hY'Z).1
  have h₂ := hS.2 Z hZ Y' hY' (hpar.trans hZY.2.2)
  omega

/-- An attestation names the entry of its entry state. (As `Outage/Sources`' private
`createAtt_T`.) -/
private theorem createAtt_T {n : Nat} {Λ Λ' : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) : a.T = σe.Th := by
  unfold FG.Record.createAtt at h
  rcases hp : Λ.heightPair σe.h σe.Th with _ | ⟨h', T, τ⟩
  · rw [hp] at h; cases h
  · rw [hp] at h
    dsimp only at h
    split_ifs at h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    unfold FG.Record.heightPair at hp
    split_ifs at hp <;> cases hp <;> rfl

variable (D : OutageLockPremises tr H proposer dg ini)

/-- **The Hi walk**: under Hi at cut `i`, `w` honest at `t_i` with `2 f_{t_i} < n`, a head walk
of the node's frame over the viable tree of an ancestor-closed domain extends `P`, when the live
lock blocks of the walked state are compatible with `P` and the domain's viable tree is nonempty or
the domain is the whole tree. -/
private theorem anc_getHead_of_hi {i : Nat} (hinv : OutageLockInv D i) {w : Fin sp.n}
    (hw : w ∈ H (tr.time i)) (hf : 2 * (H (tr.time i))ᶜ.ncard < sp.n)
    (hHi : HiAt tr H D.P w i) (A : SA.SAState sp.n) (t : Time) (V : SA.View sp.n)
    (σ : Int) {dom : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    (hdom : dom ⊆ (Node.frame (tr.state w i)).tree)
    (hdomA : ∀ B ∈ dom, ∀ X, (Node.frame (tr.state w i)).Anc X B → X ∈ dom)
    (hne : ((Node.frame (tr.state w i)).viableTree dom).Nonempty ∨
      (Node.frame (tr.state w i)).tree ⊆ dom)
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp A.locks (Node.frame (tr.state w i)) t,
      Compatible (tr.HonestBlocksAt H) L D.P) :
    Anc (tr.HonestBlocksAt H) D.P
      (SA.getHead sp A (Node.frame (tr.state w i)) t
        ((Node.frame (tr.state w i)).viableTree dom) V σ) := by
  have hU := D.coherent
  have hd := D.hrun.time_nonneg i
  have ht : ∀ k < i, tr.time k ≤ tr.time i := fun _ hk => D.hrun.time_mono hk.le
  obtain ⟨hPJ, hJP⟩ := hiAt_iff.1 hHi
  set st := (tr.state w i).fg
  set Φ := Node.frame (tr.state w i)
  have hΦ : FrameOK Φ := frameOK_at D.hrun hd hw ht
  have hΦU : Φ.tree ⊆ tr.HonestBlocksAt H := fun Z hZ => tree_held_at hd hw ht hZ.1
  have hR := reachable_at D.hrun hd hw ht
  obtain ⟨-, hJt, -, -, -, ⟨Bm, hBmt, hBmh⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hjm : st.hj < st.hmax := by
    have h := Healing.hj_lt_hmax (D.hrun.upTo hd) hw i
    rwa [Trace.upTo_state tr w ht] at h
  replace hBmh : (st.σ Bm.root).h = st.hmax := hBmh
  have above := fun {X} (hX : X ∈ st.tree) (hh : st.hj + 1 ≤ (st.σ X.root).h) =>
    above_of_hi_height_at D hinv le_rfl hd ht hw hf hHi hX hh
  -- below `Σ.F`: the head is a block of the tree, which extends `Σ.F`
  by_cases hPF : Anc (tr.HonestBlocksAt H) D.P st.F
  · have hmem := SA.getHead_mem hΦ (fun X hX => hdom hX.1) A t V σ
      (T := Φ.viableTree dom)
    exact hPF.trans (Anc.mono hΦU (hΦ.rooted.2 _ hmem))
  have hFP : Anc (tr.HonestBlocksAt H) st.F D.P :=
    ((hinv.caches_at_cut le_rfl hw).1).resolve_right hPF
  -- `P` is held above `Σ.F`, given a held block above it
  have hPΦ : ∀ W ∈ st.tree, Anc (tr.HonestBlocksAt H) D.P W → D.P ∈ Φ.tree := by
    intro W hWt hPW
    have h := held_anc_at D.hrun D.hnc hd hw ht hPW hWt
    have hPt : D.P ∈ st.tree := by
      by_cases he : D.P = W
      · exact he ▸ hWt
      · exact (Anc.mem h he).1
    exact ⟨hPt, held_anc_at D.hrun D.hnc hd hw ht hFP hPt⟩
  by_cases hcond : st.hmax = st.hj + 1 ∧ ¬ st.Contest
  · -- `fc_root = Σ.J ⪰ P`: no viable block is below `P`
    have hfc : Φ.fcRoot = st.J := Store.fcRoot_of_not_contest st hcond.1 hcond.2
    have hJΦ : st.J ∈ Φ.tree := hfc ▸ hΦ.fcRoot_mem
    have hPt := hPΦ st.J hJt hPJ
    refine Anc.mono hΦU (SA.anc_getHead hU hΦ hΦU A t V σ hdom hdomA
      (Or.inr (hfc ▸ SA.anc_tree_of_anc_U hU hΦ hΦU hPt hPJ hJΦ)) hlocks ?_)
    intro X Cx hCx _ hCxP
    have hJP' : Anc (tr.HonestBlocksAt H) st.J D.P := Anc.mono hΦU ((hfc ▸ hCx.2.1).trans hCxP)
    exact absurd (congrArg (·.root) (Anc.antisymm hU hJP' hPJ)) hJP
  -- `fc_root = Σ.F ≺ P`, and the head height floor is at least `h_j + 1`
  have hfc : Φ.fcRoot = st.F := by
    change st.fcRoot = st.F
    unfold Store.fcRoot
    simp only [hcond, ↓reduceIte]
  have hfl : st.hj + 1 ≤ st.headHeightFloor := by
    unfold Store.headHeightFloor
    split_ifs with hc
    · omega
    · have : st.hmax ≠ st.hj + 1 := fun h => hcond ⟨h, hc⟩
      omega
  have hvh : ∀ W ∈ Φ.viableHeads, Anc (tr.HonestBlocksAt H) D.P W ∧ W.root ≠ D.P.root :=
    fun W hW => above hW.1 (hfl.trans hW.2.2.2)
  have hFΦ : st.F ∈ Φ.tree := hfc ▸ hΦ.fcRoot_mem
  -- a viable head in the domain, strictly above `P`
  obtain ⟨W, hWd, hWv⟩ : ∃ W ∈ dom, W ∈ Φ.viableHeads := by
    rcases hne with ⟨X, -, -, W, hWd, hWv, -⟩ | hsub
    · exact ⟨W, hWd, hWv⟩
    · have hFBm := held_anc_at D.hrun D.hnc hd hw ht (hFP.trans (above hBmt
        (show st.hj + 1 ≤ (st.σ Bm.root).h by omega)).1) hBmt
      refine ⟨Bm, hsub ⟨hBmt, hFBm⟩, hBmt, hFBm, ?_, ?_⟩
      · change st.Anc st.fcRoot Bm
        rw [show st.fcRoot = st.F from hfc]
        exact hFBm
      · change st.headHeightFloor ≤ (st.σ Bm.root).h
        unfold Store.headHeightFloor
        split_ifs <;> omega
  have hPW := (hvh W hWv).1
  have hWΦ : W ∈ Φ.tree := hdom hWd
  have hPt := hPΦ W hWΦ.1 hPW
  have hPWΦ := SA.anc_tree_of_anc_U hU hΦ hΦU hPt hPW hWΦ
  have hPv : D.P ∈ Φ.viableTree dom :=
    ⟨hdomA W hWd _ hPWΦ, hfc ▸ SA.anc_tree_of_anc_U hU hΦ hΦU hFΦ hFP hPt, W, hWd, hWv, hPWΦ⟩
  refine Anc.mono hΦU (SA.anc_getHead hU hΦ hΦU A t V σ hdom hdomA (Or.inl hPv) hlocks ?_)
  intro X Cx hCx hpar hCxP
  have hCxPU : Anc (tr.HonestBlocksAt H) Cx D.P := Anc.mono hΦU hCxP
  have hCxΦ : Cx ∈ Φ.tree := hdom hCx.1
  refine ⟨⟨hCx, hpar, Or.inl ?_⟩, fun D' hD' hne => absurd ?_ hne⟩
  · -- the parent of `Cx`, below `P`, is not a viable head
    rintro ⟨W', hW', hW'p⟩
    have hW'Cx : Anc (tr.HonestBlocksAt H) W' Cx :=
      Relation.ReflTransGen.single ⟨hΦU ⟨hW'.1, hW'.2.1⟩, hΦU hCxΦ, hW'p.trans rfl⟩
    obtain ⟨hPW', hW'P⟩ := hvh W' hW'
    exact hW'P (congrArg (·.root) (Anc.antisymm hU (hW'Cx.trans hCxPU) hPW'))
  · -- a viable sibling `D'` of `Cx` is comparable with `P`, hence equal to `Cx`
    obtain ⟨⟨hD'd, -, W', -, hW'v, hD'W'⟩, hD'p, -⟩ := hD'
    have hD'Φ : D' ∈ Φ.tree := hdom hD'd
    have hpar' : D'.parent = Cx.parent := hD'p.trans hpar.symm
    rcases Anc.total hU (Anc.mono hΦU hD'W') (hvh W' hW'v).1 with hD'P | hPD'
    · rcases Anc.total hU hD'P hCxPU with h | h
      · exact eq_of_anc_sibling hU (hΦU hD'Φ) hpar' h
      · exact (eq_of_anc_sibling hU (hΦU hCxΦ) hpar'.symm h).symm
    · exact (eq_of_anc_sibling hU (hΦU hCxΦ) hpar'.symm (hCxPU.trans hPD')).symm

/-- **H1, vote form**: under Hi, a vote of a node honest at its cut extends `P`, given that the
live lock blocks of its read point are compatible with `P`; counted at the cut's time. -/
theorem vote_extends_of_hi_at {i : Nat} (hinv : OutageLockInv D i) {y : Fin sp.n}
    (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hHi : HiAt tr H D.P y i)
    (hL : ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocksAt H) L D.P) :
    SA.VoteExtends (tr.HonestBlocksAt H) e.msg D.P := by
  have hd := D.hrun.time_nonneg i
  have hr := (acRun_upTo D.hrun D.hnc hd).localRun
  have hcT : SA.CastAt (tr.projAC.upTo (tr.time i)) y i ℓ e := sa_castAt_upTo.mpr ⟨le_rfl, hc⟩
  have hf := D.two_faults_lt_at hy ⟨_, projAC_callAt.1 hc.1⟩
  have hfr : ℓ.frame = Node.frame (tr.state y i) := frame_of_projAC_at D.hrun hy hc.1
  obtain ⟨hΦ, hΦU⟩ := frameIn_at D.hrun D.hnc hy hc.1
  obtain ⟨-, -, -, hhead⟩ := castAt_spec_at D.hrun D.hnc hy hc
  have hdomA := SA.voteDomain_anc_from hr D.hrun.vstart hy hcT
  have hne : (ℓ.frame.viableTree (SA.voteDomain sp e.readPoint ℓ.frame e.msg.slot)).Nonempty ∨
      ℓ.frame.tree ⊆ SA.voteDomain sp e.readPoint ℓ.frame e.msg.slot := by
    by_cases hv :
        (ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot)).Nonempty
    · exact Or.inl (hv.mono SA.viableTree_voterBlockTree_subset_voteDomain)
    · exact Or.inr (SA.voteDomain_eq_tree_of_not_viable hv).ge
  rw [hfr] at hdomA hne hL hhead hΦU
  have hanc := anc_getHead_of_hi D hinv hy hf hHi e.readPoint (tr.time i)
    (SA.mergedVoteView sp e.readPoint (Node.frame (tr.state y i)) e.msg.slot)
    ((e.msg.slot : Int) - 1) (fun B hB => SA.voteDomain_subset_tree hB) hdomA hne hL
  refine ⟨_, hΦU (SA.getHead_mem (hfr ▸ hΦ) (fun X hX => SA.voteDomain_subset_tree hX.1) _ _ _ _),
    hhead.symm, hanc⟩

/-- **Lo is `Σ.J ⪯ P`**: `Σ.J`, read at a time at which its node is honest after every earlier
cut, is compatible with `P` (OB-F) and not strictly above it. -/
theorem J_anc_of_lo_at {i : Nat} (hinv : OutageLockInv D i) {y : Fin sp.n} {k : Nat}
    {t : Time} (hk : k ≤ i) (ht0 : 0 ≤ t) (ht : ∀ k' < k, tr.time k' ≤ t) (hy : y ∈ H t)
    (hLo : ¬ HiAt tr H D.P y k) :
    Anc (tr.HonestBlocksAt H) (tr.state y k).fg.J D.P := by
  have hU := D.coherent
  rcases (hinv.caches y k t hk ht0 ht hy).2 with h | h
  · exact h
  · by_cases hr : (tr.state y k).fg.J.root = D.P.root
    · have hJt := (Store.cache_invariants _ _ _ _ (reachable_at D.hrun ht0 hy ht)).2.1
      rw [hU.1 (tree_held_at ht0 hy ht hJt) D.hP.1 hr]
      exact .refl
    · exact absurd (hiAt_iff.2 ⟨h, hr⟩) hLo

/-- **Lo has no contest**, read at a time `t` at which the node is honest after every earlier
cut, with `2 f_t < n`: a contest block's `h_j`-entry is compatible with `P` (its source, held while
honest at `t`, is) and is not `Σ.J`; with `Σ.J ⪯ P` it would be `Σ.J` or above `Σ.J`. -/
theorem not_contest_of_lo_at {i : Nat} (hinv : OutageLockInv D i) {y : Fin sp.n} {k : Nat}
    {t : Time} (hk : k ≤ i) (ht0 : 0 ≤ t) (ht : ∀ k' < k, tr.time k' ≤ t) (hy : y ∈ H t)
    (hf : 2 * (H t)ᶜ.ncard < sp.n) (hLo : ¬ HiAt tr H D.P y k) :
    ¬ (tr.state y k).fg.Contest := by
  have hU := D.coherent
  have hr := D.hrun.upTo ht0
  have hnc' := D.hnc.upTo t
  have hsub := upTo_subset D.hrun ht0
  have hst := Trace.upTo_state tr y ht
  have hJP := J_anc_of_lo_at D hinv hk ht0 ht hy hLo
  have hsrc := (rows_sourced_by D.hrun D.hnc (B := D.P) (n := k)
    (fun x k' hk' hx => hinv.sources x k' (by omega) hx) ht0 ht hy).upTo_held ht
  rw [← hst] at hJP ⊢
  rintro ⟨hm, X, hX, -, hXh, hJX⟩
  have hR := fg_reachable hr.toLocalRun hy k
  have hJt := (Store.cache_invariants _ _ _ _ hR).2.1
  have hJU : ((tr.upTo t).state y k).fg.J ∈ (tr.upTo t).HonestBlocks (H t) := ⟨y, hy, k, hJt⟩
  by_cases h0 : ((tr.upTo t).state y k).fg.hj = 0
  · rw [justified_genesis hr (i := k) h0 hy] at hJX
    exact hJX ((Store.accepted_tree _ _ _ _ hR).2.2.2 X hX)
  obtain ⟨hJh, hJT, -⟩ := justified_honest_source_before hr hnc' hf hy hsrc (by omega)
  obtain ⟨E, hEt, hEX, hEh, hET, D', ⟨hD'P, -⟩, hD's⟩ :=
    frame_crossing_source_before hr hnc' hf hy (i := k) hsrc hX
      (j := ((tr.upTo t).state y k).fg.hj) (by omega)
      (Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) (hXh.trans hm).symm)
  have hEU : E ∈ (tr.upTo t).HonestBlocks (H t) := fg_tree_subset_honest hy k hEt
  obtain ⟨x, hx, k', -, -, hED', -, -⟩ := honest_source_entry hr hnc' hD's hEU rfl
  have hEP : Compatible (tr.HonestBlocksAt H) E D.P :=
    compatible_of_head_anc hU (hED'.mono ((fg_tree_subset_honest hx k').trans hsub)) hD'P
  have back := fun {A W} (hW : W ∈ ((tr.upTo t).state y k).fg.tree)
      (h : Anc (tr.HonestBlocksAt H) A W) =>
    honest_held_anc hr hnc' hy (RunTrace.anc_upTo_of_right D.hrun.toLocalRun D.hnc ht0
      ⟨y, hy, k, hW⟩ h) hW
  rcases hEP with hEP | hPE
  · rcases Anc.total hU hEP hJP with h | h
    · have hEJ := back hJt h
      obtain rfl : E = ((tr.upTo t).state y k).fg.J :=
        held_entry_unique hr hnc' hy hJt hEJ .refl (hEh.trans hJh.symm) hET hJT
      exact hJX hEX
    · have hJE := back hEt h
      obtain rfl : ((tr.upTo t).state y k).fg.J = E :=
        held_entry_unique hr hnc' hy hEt hJE .refl (hJh.trans hEh.symm) hJT hET
      exact hJX hEX
  · exact hJX ((back hEt (hJP.trans hPE)).trans hEX)

/-- **The read point's live locks are compatible with every block below `P`**, at a vote of a
node honest at its cut `i`, of a positive slot: a stored lock by (L) at `t_i`, the cast's
optimistic lock by the fast-lock count at `i` (its counted votes of validators honest at `t_i`
were cast at earlier cuts, at which they were honest). -/
theorem readPoint_liveLockBlocks_compatible_at {i : Nat} (hinv : OutageLockInv D i)
    {y : Fin sp.n} (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hpos : 0 < sp.slot (tr.time i)) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hBP : Anc (tr.HonestBlocksAt H) B D.P) :
    ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocksAt H) L B := by
  intro L hL
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hd := D.hrun.time_nonneg i
  have hm := D.hrun.time_mono
  have hcall : tr.IsCall y i := ⟨_, projAC_callAt.1 hc.1⟩
  obtain ⟨hΦ, hΦU⟩ := frameIn_at D.hrun D.hnc hy hc.1
  obtain ⟨l', hl', B₀, hB₀, hB₀r, -, rfl⟩ := SA.mem_liveLockBlocks hΦ hL
  obtain ⟨B', hB', hB'r, h⟩ := SA.readPoint_locks_provenance_strict (acRun_upTo D.hrun D.hnc hd)
    hy (sa_castAt_upTo.mpr ⟨le_rfl, hc⟩) hpos l' hl'
  obtain rfl : B₀ = B' := hΦ.coherent.1 hB₀ hB' (hB₀r.trans hB'r.symm)
  refine compatible_of_anc_right hU hBP
    (compatible_of_head_anc hU ((SA.viableAncestor_anc hΦ hB₀).2.mono hΦU) ?_)
  rcases h with ⟨l, hl, B₁, hB₁, hB₁r, hanc⟩ | ⟨B₁, CV, hfl, hcut, hanc⟩
  · rw [projAC_upTo_state D.hrun le_rfl, projAC_state_at D.hrun hy] at hl
    obtain ⟨L', hL', hL'r, hcomp⟩ := hinv.locks_at_cut le_rfl hy l hl
    obtain rfl : B₁ = L' :=
      hU.1 (hΦU hB₁) (tree_held_at hd hy (fun _ hk => hm hk.le) hL') (hB₁r.trans hL'r.symm)
    exact compatible_of_head_anc hU (hanc.mono hΦU) hcomp
  · obtain ⟨-, hfl⟩ := (sa_optimisticLockAt_upTo hm).mp hfl
    refine compatible_of_head_anc hU (hanc.mono hΦU)
      (fastLock_compatible_at hinv.toOutageVoteInv hy (Or.inr hfl) (fun v hv hvH => ?_)
        fun hsK => D.hzc _ ?_ ⟨y, i, hy, hcall, le_rfl⟩)
    · obtain ⟨j, hj, e', hve, he'⟩ := hcut v hv hvH
      obtain ⟨hjd, hve⟩ := sa_voteAt_upTo.mp hve
      exact ⟨j, hj, e', hVoteAt_iff.2 ⟨D.hrun.antitone hjd hvH, hve⟩, he'⟩
    · -- the cast's slot is at most `j₀ + k`, so `t_i < t_{j₀+k} + 4Δ`
      have h := (SA.ts_le_iff_le_slot sp hd ((sp.slot (tr.time i) + 1 : Nat) : Int))
      have hlt : tr.time i < sp.ts ((sp.slot (tr.time i) + 1 : Nat) : Int) := by
        by_contra hge
        have := h.1 (not_lt.1 hge)
        omega
      have hK := ts_le_ts (sp := sp) (show sp.slot (tr.time i) ≤ D.j₀ + sp.k from hsK)
      have hts : sp.ts ((sp.slot (tr.time i) + 1 : Nat) : Int) =
          sp.ts (sp.slot (tr.time i) : Nat) + 4 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      linarith only [hlt, hts, hK, hΔ]

include D in
/-- **A fast lock has an extending supporter**, counted at its writing cut `c` (`2 f_{t_c} < n`):
a counted vote by a validator honest at `t_c`, cast at a cut at which it was honest, whose head
extends the lock block. -/
private theorem fastLock_extending_vote_at {c s : Nat} {y : Fin sp.n} (hy : y ∈ H (tr.time c))
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC y c s B CV) :
    ∃ x j e, HVoteAt tr H x j e ∧ e.msg.slot = s ∧
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  obtain ⟨hcount, hCV⟩ := fastLock_counted_at D.hrun D.hnc hy hfl
  have hf := D.two_faults_lt_at hy (fastLockAt_isCall hfl)
  obtain ⟨v, hv, hvH⟩ : ∃ v ∈ CV, v.val ∈ H (tr.time c) := by
    by_contra hno
    push Not at hno
    have hsub : {u | ∃ v ∈ CV, v.val = u} ⊆ (H (tr.time c))ᶜ := by
      rintro u ⟨v, hv, rfl⟩
      exact hno v hv
    have := Set.ncard_le_ncard hsub
    omega
  obtain ⟨j, -, e, hve, rfl⟩ := fastLock_honest_vote_at D.hrun D.hnc hy hfl hv hvH
  obtain ⟨hvs, R, hR, hRr, -, hBR⟩ := hCV _ hv
  exact ⟨e.msg.val, j, e, hve, hvs, R, hR, hRr, hBR⟩

/-- **The attestations at a restored vote are supported** (source support): at a slot-`(q+1)`
vote of `y` honest at its cut `i`, every attestation of `y`'s tree by a validator honest at `t_i`
has a source compatible with `P` ((SRC) before `i`), held by its signer, and extended by a vote,
of a node honest at its cast, of a slot `≤ q`. The source is the viable ancestor of a fast stored
lock of the signer; its fast origin, written at a cut at which the signer was honest, has an
extending supporter counted there, of the lock's slot, which is at most `q`: a fast update of a
later slot is written after the vote, and an optimistic lock of slot `q + 1` before a held
attestation is excluded (`no_optimistic_before_held_row_at`, counted at the lock's cut). -/
theorem rows_supported_at {i : Nat} (hinv : OutageLockInv D i) {y : Fin sp.n}
    (hy : y ∈ H (tr.time i)) {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e) {q : Nat}
    (hs : e.msg.slot = q + 1) :
    HonestRowsSourcedAt tr H (fun Ds => Compatible (tr.HonestBlocksAt H) Ds D.P ∧
      ∃ x k e', HVoteAt tr H x k e' ∧ e'.msg.slot ≤ q ∧
        SA.VoteExtends (tr.HonestBlocksAt H) e'.msg Ds) y i := by
  have hrun := D.hrun
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hd := hrun.time_nonneg i
  have hm := hrun.time_mono
  have hst : ∀ x k, k ≤ i → (tr.upTo (tr.time i)).state x k = tr.state x k :=
    fun x k hk => RunTrace.upTo_state_of_le hm (hm hk)
  have hr := hrun.upTo hd
  have hti : tr.time i ≤ sp.ts q + 5 * sp.Δ := by
    have h : tr.time i ≤ sp.ts (e.msg.slot : Int) + sp.Δ :=
      (cast_head_fcRoot_at hrun D.hnc hy hc).2
    rw [hs] at h
    simp only [SAParams.ts] at h ⊢
    push_cast at h
    linarith only [h]
  refine honestRowsSourcedAt_iff.2 fun X hX a ha hav => ?_
  obtain ⟨m, hmi, hmacc, k, hkm, hsg, havk⟩ := honest_row_signed_before_at hrun D.hnc hy hX ha hav
  obtain ⟨src, hcall⟩ := id hsg
  obtain ⟨j, rfl, ℓz, hcj, hcl, -, hC, hfg⟩ := attest_source hr.toLocalRun hav
    ((Trace.upTo_callAt _).mpr ⟨hm (show k ≤ i by omega), hcall⟩)
  have hj1 : j + 1 ≤ i := by omega
  obtain ⟨hjd, hcj⟩ := (Trace.upTo_callAt _).mp hcj
  rw [hst a.val j (by omega)] at hC
  rw [hst a.val (j + 1) hj1, hst a.val j (by omega)] at hfg
  have hav' : a.val ∈ H (tr.time j) := hrun.antitone hjd hav
  have hfr := (hrun.cutLaw a.val j _ hcj hav').1
  have hto : SA.ToFGAt tr.projAC a.val j ℓz src :=
    ⟨projAC_callAt.2 hcj, hcl, by rw [projAC_state_at hrun hav']; exact hC⟩
  have hcand := toFG_candidate hC
  have hst' : src ∈ (tr.state a.val (j + 1)).fg.tree := by
    have h' := hcand.1.1
    rw [hfr] at h'
    rw [hfg]
    exact h'.1
  have hR := fg_reachable hr.toLocalRun hav (j + 1)
  rw [hst a.val (j + 1) hj1] at hR
  obtain ⟨⟨E, -, hEr, -, -, hET⟩, -⟩ := Store.entry_state_of_source _ _ _ _ hR _ hst'
  have hT := createAtt_T (hrun.cutLaw a.val (j + 1) _ hcall havk).1
  rw [← hEr, hET] at hT
  refine ⟨src, ⟨hinv.sources a.val j (by omega) hav' ℓz src hto, ?_⟩, a.val, j + 1, hav, hj1,
    hst', hT.symm⟩
  -- the source is the viable ancestor of a fast stored lock
  obtain ⟨hΦ, hΦU⟩ := frameIn_at hrun D.hnc hav' (projAC_callAt.2 hcj)
  obtain ⟨hsv, l, hl, hlb, hlf, -⟩ := hcand
  obtain ⟨l₀, hl₀, B, hB, hBr, -, rfl⟩ := hl
  obtain ⟨hVt, hVB⟩ := SA.viableAncestor_anc hΦ hB
  obtain rfl : src = ℓz.frame.viableAncestor B := hΦ.coherent.1 hsv.1 hVt hlb.symm
  obtain ⟨j', hj'j, B', CV, hfl, hyj', L, hLU, hLr, hLB'⟩ :=
    fastLock_provenance_at hrun D.hnc (hrun.time_nonneg j) (fun _ hk => hm hk.le) hav' hl₀ hlf
  obtain rfl : L = B := hU.1 hLU (hΦU hB) (hLr.trans hBr.symm)
  have hf := D.two_faults_lt_at hyj' (fastLockAt_isCall hfl)
  obtain ⟨w, jw, ew, hvw, hws, Hd, hHd, hHdr, hB'Hd⟩ := fastLock_extending_vote_at D hyj' hfl
  refine ⟨w, jw, ew, hvw, ?_, Hd, hHd, hHdr, (Anc.mono hΦU hVB).trans (hLB'.trans hB'Hd)⟩
  -- the lock's slot is at most `q`
  rw [hws]
  have hj'i : tr.time j' ≤ tr.time i := hm (by omega)
  by_contra hlt
  push Not at hlt
  rcases hfl with ⟨ℓu, -, hu, -⟩ | hO
  · have ht : tr.time j' = sp.ts l₀.slot + 6 * sp.Δ := hu.2.2.1
    have := ts_le_ts (sp := sp) hlt
    have hts : sp.ts (q + 1 : Nat) = sp.ts q + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    linarith only [ht, this, hts, hj'i, hti, hΔ]
  · rcases Nat.lt_or_ge l₀.slot (q + 2) with hl2 | hl2
    · obtain hq : l₀.slot = q + 1 := by omega
      rw [hq] at hO
      exact no_optimistic_before_held_row_at hrun D.hnc hy hc hs hmacc hmi
        (hrun.antitone (hm hmi.le) hav) hkm hsg hyj' (by omega) hO hf
    · obtain ⟨ℓO, A, -, hslot, -⟩ := id hO
      have h := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg j') (l₀.slot : Int)).2
        (le_of_eq (by rw [show sp.slot (tr.time j') = l₀.slot from hslot]))
      have h' : sp.ts (l₀.slot : Int) ≤ tr.time j' := h
      have := ts_le_ts (sp := sp) hl2
      have hts : sp.ts (q + 2 : Nat) = sp.ts q + 8 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      change sp.ts (l₀.slot : Nat) ≤ tr.time j' at h'
      linarith only [h', this, hts, hj'i, hti, hΔ]

end Consensus.Goldilocks.Compose.Growing

end

module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageS5.Geometry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageS5.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Count
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageLockSafety.Reader
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.OutageReader
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # `OutageS5`: the restored votes

Inside lock safety's cut
induction, at an honest vote of slot `q + 1 > r` at cut `i`, from `OutageLockInv D i` and receiver
service from `b₁`:

* `vote_extends_of_hi` (H1, vote form): under Hi the walk over the viable vote domain passes `P`
  (the domain is ancestor-closed, `voteDomain_anc`, its viable tree is nonempty, every viable head
  is strictly above `P` by G3′, `above_of_hi_height` in `OutageS5/Geometry`);
* `viable_at_vote_of_lo` (G4): under Lo (no contest, `not_contest_of_lo`) `P` is viable at the
  vote: the honest witness head is frozen (`honest_head_accepted_after`), and below the floor the
  `h_max` carrier's floor entry is above `P` with a source extended by an honest vote of a slot
  `≤ q` (`rows_supported`), whose head is frozen and viable;
* `carryAt_after`: `Carry_y` for honest slot-`q` votes above `Σ.F`;
* `outage_s5_inner` (INV): root cover, Hi, or Lo with the batch walk
  (`vote_extends_of_batch` for `q > r` by induction, `vote_extends_of_counted_batch` with the
  cohort `A₀` for `q = r`); the read point's live locks are compatible with `P` by
  `readPoint_liveLockBlocks_compatible_at` at the cast cut;
* `outage_s5_step` (lock safety's `hS5`), `restored_votes_extend`, `restored_majority`
  (`ExtendingMajority`). -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

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

/-- **An honest head of a slot at most `q` is accepted by `y` before the freeze `t_q + 3Δ`**,
under receiver service from `g ≤ t_q + Δ`, at an honest slot-`(q+1)` vote of `y` whose `Σ.F` it
extends: its voter accepted it by `t_q + Δ` (or it is genesis), and `y`, joined (so with no
restart after `t_q`), receives it by `max(τ, g) + Δ ≤ t_q + 2Δ`. -/
theorem honest_head_accepted_after (hrun : GoldilocksRun proposer dg H tr)
    (hnc : NoCollRun dg tr) {g : Time} {y : Fin sp.n} (hy : y ∈ H)
    (hS : ReceiverServiceAfter H (tr.HonestBlocks H) g y tr.projAC) {q : Nat}
    (hg : g ≤ sp.ts q + sp.Δ) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = q + 1) {x : Fin sp.n} (hx : x ∈ H) {k : Nat}
    {e' : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt tr.projAC x k e')
    (hs' : e'.msg.slot ≤ q) {Hd : SA.Blk sp.n (List (FG.Att sp.n))}
    (hHd : Hd ∈ tr.HonestBlocks H) (hHdr : Hd.root = e'.msg.head)
    (hFHd : Anc (tr.HonestBlocks H) ℓ.frame.F Hd) :
    SA.AcceptedBefore tr.projAC y Hd (sp.ts q + 3 * sp.Δ) := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨ℓ', hcx, hex⟩ := hv
  -- the head is in its voter's tree, and the vote is cast by `t_{slot} + Δ ≤ t_q + Δ`
  obtain ⟨⟨Hd', hHd't, hHd'r, -⟩, hkt⟩ := cast_head_fcRoot hr hx ⟨hcx, hex⟩
  rw [frame_of_projAC hrun hx hcx] at hHd't
  obtain rfl : Hd = Hd' :=
    ((projFG_localRun hrun hnc).coherent.1 ⟨x, hx, k, hHd't.1⟩ hHd (hHd'r.trans hHdr.symm)).symm
  have hkt' : tr.time k ≤ sp.ts q + sp.Δ := by
    have h1 : tr.time k ≤ sp.ts (e'.msg.slot : Int) + sp.Δ := hkt
    have h2 := ts_le_ts (sp := sp) hs'
    linarith only [h1, h2]
  obtain ⟨hrs, hti⟩ := honest_vote_restarts hrun hnc hy hc hs
  have hrs' : ∀ c ≤ i, tr.RestartAt y c → tr.time c ≤ sp.ts q := fun c hc' ⟨ℓr, hcr, hrr⟩ =>
    hrs c hc' ⟨ℓr, projAC_callAt.2 hcr, hrr⟩
  -- its voter accepted it (or it is genesis)
  rcases Healing.tree_accepted hrun.toLocalRun hx hHd't.1 with hgen | ⟨m, hm, hA⟩
  · exact Or.inl (by rw [hgen]; rfl)
  obtain ⟨ℓa, hca, hba, hta⟩ := accept_next hrun.toLocalRun hx hA
  have hacc : tr.projAC.AcceptAt x (m + 1) Hd := ⟨ℓa, projAC_callAt.2 hca, hba⟩
  have hmt : tr.time (m + 1) ≤ sp.ts q + sp.Δ := by
    rw [hta]; exact (hrun.time_mono hm.le).trans hkt'
  have hdl : ∀ c ≤ i, tr.projAC.deadline y c (max (tr.projAC.time (m + 1)) g) ≤
      sp.ts q + 2 * sp.Δ := fun c hc' => by
    rw [projAC_deadline]
    have := deadline_le_of_restarts (fun k hk hr' => hrs' k (hk.trans hc') hr')
      (max (tr.time (m + 1)) g) sp.Δ
    have h₁ : max (max (tr.time (m + 1)) g) (sp.ts q) ≤ sp.ts q + sp.Δ :=
      max_le (max_le hmt hg) (le_add_of_nonneg_right hΔ.le)
    change tr.deadline y c (max (tr.time (m + 1)) g) sp.Δ ≤ _
    linarith only [this, h₁]
  obtain ⟨k', hk'i, hAy, hk't⟩ := hS.relay x hx (m + 1) Hd hacc i ℓ hc.1
    (by have := hdl i le_rfl; change _ ≤ tr.time i; linarith only [this, hti, hΔ]) hFHd
  exact Or.inr ⟨k', hAy, by have := hdl k' hk'i; linarith only [this, hk't, hΔ]⟩

/-- **`Carry_y` after the outage's GST** (`carryAt_of_writer_window` with receiver service): at an
honest slot-`(s+1)` vote of `y`, under receiver service from `g ≤ t_s + Δ`, `Carry_y(s, ·, ·)` holds
for honest slot-`s` votes whose heads extend `y`'s `Σ.F`: each is sent by its voter by `t_s + Δ`
and its head accepted by then, so `y` (joined, no restart after `t_s`) holds the vote and accepts
the head and its ancestors before `t_s + 3Δ`. -/
theorem carryAt_after (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {g : Time} {y : Fin sp.n} (hy : y ∈ H)
    (hS : ReceiverServiceAfter H (tr.HonestBlocks H) g y tr.projAC) {s : Nat}
    (hg : g ≤ sp.ts s + sp.Δ) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y i ℓ e)
    (hs : e.msg.slot = s + 1) {CV : Set (Vote sp.n)}
    (hCV : ∀ v ∈ CV, ∃ x ∈ H, ∃ k e', SA.VoteAt tr.projAC x k e' ∧ e'.msg = v ∧ v.slot = s ∧
      ∃ Hv ∈ tr.HonestBlocks H, Hv.root = v.head ∧ Anc (tr.HonestBlocks H) ℓ.frame.F Hv) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  obtain ⟨-, hys, hyj, -⟩ := SA.castAt_spec hr hy hc
  obtain ⟨hrsy, hti⟩ := honest_vote_restarts hrun hnc hy hc hs
  have hdl : ∀ k ≤ i, ∀ τ, τ < sp.ts s + 2 * sp.Δ →
      tr.projAC.deadline y k τ < sp.ts s + 3 * sp.Δ := by
    intro k hk τ hτ
    have h₁ := Compose.ac_deadline_le_of_restarts (T := tr.projAC)
      (fun k' hk' hr' => hrsy k' (hk'.trans hk) hr') τ
    have h₂ := max_lt hτ (show sp.ts s < sp.ts s + 2 * sp.Δ by linarith only [hΔ])
    change tr.projAC.deadline y k τ ≤ max τ (sp.ts s) + sp.Δ at h₁
    linarith only [h₁, h₂]
  obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy i ℓ hc.1
  refine ⟨hr.awake_of_call y hy i ℓ hc.1, hyj, fun v hv => ?_, fun v hv => ?_⟩
  · -- the head and its ancestors are accepted before the freeze
    obtain ⟨x, hx, k, e', hv', rfl, hvs, Hv, hHv, hHvr, hFHv⟩ := hCV _ hv
    refine ⟨Hv, hHv, hHvr, fun X hX => ?_⟩
    rcases honest_head_accepted_after hrun hnc hy hS hg hc hs hx hv' hvs.le hHv hHvr hFHv with
      hgen | ⟨ky, ⟨ℓk, hck, hcall⟩, hkyt⟩
    · left
      obtain rfl : Hv = G := hU.1 hHv hGU (hgen.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hX with rfl | ⟨Q, -, hQ⟩
      · exact hGr
      · exact absurd (hQ.2.2.symm.trans hGp) (Option.some_ne_none _)
    rcases frame_anc_accepted hr hy ky ℓk hck Hv
      ((SA.accept_new sp hr hy ⟨ℓk, hck, hcall⟩).1 ℓk hck) X hX with hgen | ⟨k, hk, hkX⟩
    · exact Or.inl hgen
    · exact Or.inr ⟨k, hkX, lt_of_le_of_lt (hr.time_mono hk) hkyt⟩
  · -- the vote is held before the freeze
    obtain ⟨x, hx, k, ev, hvk, hev, hvs, -⟩ := hCV v hv
    obtain ⟨ℓv, hcv, hevv⟩ := id hvk
    have hsend : tr.projAC.SendOrAdmit x k v := ⟨ℓv, hcv, Or.inl ⟨ev, hevv, hev⟩⟩
    have hk1 : sp.ts s ≤ tr.projAC.time k := by
      have h := (SA.castAt_spec hr hx ⟨hcv, hevv⟩).2.1
      rw [hev, hvs] at h
      exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega)
    have hk2 : tr.projAC.time k ≤ sp.ts s + sp.Δ := by
      have h := (cast_head_fcRoot hr hx ⟨hcv, hevv⟩).2
      rw [hev, hvs] at h
      exact h
    have hmx : max (tr.projAC.time k) g < sp.ts s + 2 * sp.Δ :=
      max_lt (by linarith only [hk2, hΔ]) (by linarith only [hg, hΔ])
    obtain ⟨k', hk'i, hkk', hp, hk'dl⟩ := hS.message x hx k v hsend i ℓ hc.1
      (by have := hdl i le_rfl _ hmx; change _ ≤ tr.time i; linarith only [this, hti, hΔ])
    have hk'lt : tr.projAC.time k' < sp.ts s + 3 * sp.Δ := hk'dl.trans (hdl k' hk'i _ hmx)
    obtain ⟨ℓ', hc', -⟩ := id hp
    have hnr : ∀ r, k' + 1 ≤ r → r < i + 1 → ¬ tr.projAC.RestartAt y r := by
      rintro r hr1 hr2 ⟨ℓr, hcr, hrr⟩
      obtain ⟨u, -, hu, -, hprev⟩ := hr.sleep_of_restart y hy r ℓr hcr hrr
      have h₁ := hprev k' (by omega) ℓ' hc'
      have h₂ : tr.projAC.time r ≤ sp.ts s := hrsy r (by omega) ⟨ℓr, hcr, hrr⟩
      linarith only [h₁, h₂, hu, hk1, hkk']
    have hsk' : sp.slot (tr.projAC.time k') = s :=
      SA.slot_of_mem sp s (hk1.trans hkk') (by rw [hts]; linarith only [hk'lt, hΔ])
    have hheld : ∀ u ∈ (tr.projAC.state y (k' + 1)).pool s,
        SA.HeldBefore e.readPoint u (sp.ts s + 3 * sp.Δ) := by
      intro u hu
      have hus : u.slot = s := SA.state_pool_slot sp hr hy (k' + 1) s u hu
      obtain ⟨hpool, hstamp⟩ := Healing.readPoint_pool_of_ne hr hy hc (σ := s) (by omega)
      have hu' := SA.pool_mono hr hy (show k' + 1 ≤ i + 1 by omega) hnr s hu
      refine ⟨by rw [hus, ← hpool]; exact hu', ?_⟩
      rw [← hstamp u hus]
      rcases SA.pool_origin hr hy (i + 1) u (by rw [hus]; exact hu') with
        ⟨k₁, hk₁, hsend₁, hst₁, -⟩ | ⟨k₁, hk₁, ℓ₁, hc₁, hr₁, hst₁, -⟩
      · rw [hst₁, SA.etime_of_lt_of]
        by_cases hk₁k' : k₁ ≤ k'
        · exact lt_of_le_of_lt (hr.time_mono hk₁k') hk'lt
        · obtain ⟨ℓ₁, hc₁, ⟨e₁, he₁, rfl⟩ | ⟨-, hn₁, -⟩⟩ := hsend₁
          · have h := (cast_head_fcRoot hr hy ⟨hc₁, he₁⟩).2
            rw [hus] at h
            linarith only [h, hΔ]
          · exact absurd (SA.pool_mono hr hy (show k' + 1 ≤ k₁ by omega)
              (fun r h₁ h₂ => hnr r h₁ (by omega)) _ (by rw [hus]; exact hu)) hn₁
      · rw [hst₁, SA.etime_of_lt_of]
        have : tr.projAC.time k₁ ≤ sp.ts s := hrsy k₁ (by omega) ⟨ℓ₁, hc₁, hr₁⟩
        linarith only [this, hΔ]
    by_cases hv' : v ∈ (tr.projAC.state y (k' + 1)).pool s
    · exact Or.inl (hheld v hv')
    · rcases SA.held_of_processAt hr hy hp (by rw [hvs, hsk']; omega) (by rw [hvs, hsk']) with
        h | ⟨a, ha, c, hc'', hac, hav, hcv⟩
      · rw [hvs] at h
        exact absurd h hv'
      · have ha' : a ∈ (tr.projAC.state y (k' + 1)).pool s := by rw [← hvs]; exact ha
        have hc' : c ∈ (tr.projAC.state y (k' + 1)).pool s := by rw [← hvs]; exact hc''
        refine Or.inr ⟨a, c, hac, ?_, ?_, hav, hcv, SA.state_pool_slot sp hr hy _ s a ha',
          SA.state_pool_slot sp hr hy _ s c hc', hheld a ha', hheld c hc'⟩
        · rintro rfl; exact hv' ha'
        · rintro rfl; exact hv' hc'

variable (D : OutageLockPremises tr H proposer dg)

/-- **The Hi walk**: under Hi at cut `i`, a head walk of the node's frame over the viable tree of
an ancestor-closed domain extends `P`, when the live lock blocks of the walked state are
compatible with `P` and the domain's viable tree is nonempty or the domain is the whole tree. -/
private theorem anc_getHead_of_hi {i : Nat} (hinv : OutageLockInv D i) {w : Fin sp.n}
    (hw : w ∈ H) (hHi : HiAt tr H D.P w i) (A : SA.SAState sp.n) (t : Time) (V : SA.View sp.n)
    (σ : Int) {dom : Set (SA.Blk sp.n (List (FG.Att sp.n)))}
    (hdom : dom ⊆ (Node.frame (tr.state w i)).tree)
    (hdomA : ∀ B ∈ dom, ∀ X, (Node.frame (tr.state w i)).Anc X B → X ∈ dom)
    (hne : ((Node.frame (tr.state w i)).viableTree dom).Nonempty ∨
      (Node.frame (tr.state w i)).tree ⊆ dom)
    (hlocks : ∀ L ∈ SA.liveLockBlocks sp A.locks (Node.frame (tr.state w i)) t,
      Compatible (tr.HonestBlocks H) L D.P) :
    Anc (tr.HonestBlocks H) D.P
      (SA.getHead sp A (Node.frame (tr.state w i)) t
        ((Node.frame (tr.state w i)).viableTree dom) V σ) := by
  have hU := D.coherent
  obtain ⟨hPJ, hJP⟩ := hiAt_iff.1 hHi
  set st := (tr.state w i).fg
  set Φ := Node.frame (tr.state w i)
  have hΦ : FrameOK Φ := frameOK_state D.hrun.toLocalRun hw i
  have hΦU : Φ.tree ⊆ tr.HonestBlocks H := fun Z hZ => ⟨w, hw, i, hZ.1⟩
  have hR := fg_reachable D.hrun.toLocalRun hw i
  obtain ⟨-, hJt, -, -, -, ⟨Bm, hBmt, hBmh⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
  have hjm : st.hj < st.hmax := Healing.hj_lt_hmax D.hrun hw i
  replace hBmh : (st.σ Bm.root).h = st.hmax := hBmh
  -- below `Σ.F`: the head is a block of the tree, which extends `Σ.F`
  by_cases hPF : Anc (tr.HonestBlocks H) D.P st.F
  · have hmem := SA.getHead_mem hΦ (fun X hX => hdom hX.1) A t V σ
      (T := Φ.viableTree dom)
    exact hPF.trans (Anc.mono hΦU (hΦ.rooted.2 _ hmem))
  have hFP : Anc (tr.HonestBlocks H) st.F D.P :=
    ((hinv.caches w hw i le_rfl).1).resolve_right hPF
  -- `P` is held above `Σ.F`, given a held block above it
  have hPΦ : ∀ W ∈ st.tree, Anc (tr.HonestBlocks H) D.P W → D.P ∈ Φ.tree := by
    intro W hWt hPW
    have h := honest_held_anc D.hrun D.hnc hw hPW hWt
    have hPt : D.P ∈ st.tree := by
      by_cases he : D.P = W
      · exact he ▸ hWt
      · exact (Anc.mem h he).1
    exact ⟨hPt, honest_held_anc D.hrun D.hnc hw hFP hPt⟩
  by_cases hcond : st.hmax = st.hj + 1 ∧ ¬ st.Contest
  · -- `fc_root = Σ.J ⪰ P`: no viable block is below `P`
    have hfc : Φ.fcRoot = st.J := Store.fcRoot_of_not_contest st hcond.1 hcond.2
    have hJΦ : st.J ∈ Φ.tree := hfc ▸ hΦ.fcRoot_mem
    have hPt := hPΦ st.J hJt hPJ
    refine Anc.mono hΦU (SA.anc_getHead hU hΦ hΦU A t V σ hdom hdomA
      (Or.inr (hfc ▸ SA.anc_tree_of_anc_U hU hΦ hΦU hPt hPJ hJΦ)) hlocks ?_)
    intro X Cx hCx _ hCxP
    have hJP' : Anc (tr.HonestBlocks H) st.J D.P := Anc.mono hΦU ((hfc ▸ hCx.2.1).trans hCxP)
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
  have hvh : ∀ W ∈ Φ.viableHeads, Anc (tr.HonestBlocks H) D.P W ∧ W.root ≠ D.P.root :=
    fun W hW => above_of_hi_height D hinv hw le_rfl hHi hW.1 (hfl.trans hW.2.2.2)
  have hFΦ : st.F ∈ Φ.tree := hfc ▸ hΦ.fcRoot_mem
  -- a viable head in the domain, strictly above `P`
  obtain ⟨W, hWd, hWv⟩ : ∃ W ∈ dom, W ∈ Φ.viableHeads := by
    rcases hne with ⟨X, -, -, W, hWd, hWv, -⟩ | hsub
    · exact ⟨W, hWd, hWv⟩
    · refine ⟨Bm, hsub ⟨hBmt, ?_⟩, ?_⟩
      · exact honest_held_anc D.hrun D.hnc hw (hFP.trans (above_of_hi_height D hinv hw le_rfl hHi
          hBmt (show st.hj + 1 ≤ (st.σ Bm.root).h by omega)).1) hBmt
      · have hFBm := honest_held_anc D.hrun D.hnc hw (hFP.trans (above_of_hi_height D hinv hw
          le_rfl hHi hBmt (show st.hj + 1 ≤ (st.σ Bm.root).h by omega)).1) hBmt
        refine ⟨hBmt, hFBm, ?_, ?_⟩
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
  have hCxPU : Anc (tr.HonestBlocks H) Cx D.P := Anc.mono hΦU hCxP
  have hCxΦ : Cx ∈ Φ.tree := hdom hCx.1
  refine ⟨⟨hCx, hpar, Or.inl ?_⟩, fun D' hD' hne => absurd ?_ hne⟩
  · -- the parent of `Cx`, below `P`, is not a viable head
    rintro ⟨W', hW', hW'p⟩
    have hW'Cx : Anc (tr.HonestBlocks H) W' Cx :=
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

/-- **H1, vote form**: under Hi, an honest vote extends `P`, given that the live lock blocks of
its read point are compatible with `P` (lock safety's (i) at the read point). -/
theorem vote_extends_of_hi {i : Nat} (hinv : OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) (hHi : HiAt tr H D.P y i)
    (hL : ∀ L ∈ SA.liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible (tr.HonestBlocks H) L D.P) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg D.P := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc).localRun
  have hfr : ℓ.frame = Node.frame (tr.state y i) :=
    (D.hrun.cutLaw y hy i _ (projAC_callAt.1 hc.1)).1
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  obtain ⟨-, -, -, hhead⟩ := SA.castAt_spec hr hy hc
  have hdomA := SA.voteDomain_anc hr hy hc
  have hne : (ℓ.frame.viableTree (SA.voteDomain sp e.readPoint ℓ.frame e.msg.slot)).Nonempty ∨
      ℓ.frame.tree ⊆ SA.voteDomain sp e.readPoint ℓ.frame e.msg.slot := by
    by_cases hv :
        (ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot)).Nonempty
    · exact Or.inl (hv.mono SA.viableTree_voterBlockTree_subset_voteDomain)
    · exact Or.inr (SA.voteDomain_eq_tree_of_not_viable hv).ge
  rw [hfr] at hdomA hne hL hhead hΦU
  have hanc := anc_getHead_of_hi D hinv hy hHi e.readPoint (tr.time i)
    (SA.mergedVoteView sp e.readPoint (Node.frame (tr.state y i)) e.msg.slot)
    ((e.msg.slot : Int) - 1) (fun B hB => SA.voteDomain_subset_tree hB) hdomA hne hL
  refine ⟨_, hΦU (SA.getHead_mem (hfr ▸ hΦ) (fun X hX => SA.voteDomain_subset_tree hX.1) _ _ _ _),
    hhead.symm, hanc⟩

/-- **Lo is `Σ.J ⪯ P`**: `Σ.J` is compatible with `P` (OB-F, `OutageLockInv.caches`), and not
strictly above it. -/
theorem J_anc_of_lo {i : Nat} (hinv : OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    (hk : k ≤ i) (hLo : ¬ HiAt tr H D.P y k) :
    Anc (tr.HonestBlocks H) (tr.state y k).fg.J D.P := by
  have hU := D.coherent
  rcases (hinv.caches y hy k hk).2 with h | h
  · exact h
  · by_cases hr : (tr.state y k).fg.J.root = D.P.root
    · have hJt := (Store.cache_invariants _ _ _ _ (fg_reachable D.hrun.toLocalRun hy k)).2.1
      rw [hU.1 (fg_tree_subset_honest hy k hJt) D.hP.1 hr]
      exact .refl
    · exact absurd (hiAt_iff.2 ⟨h, hr⟩) hLo

/-- **Lo has no contest**: a contest block's `h_j`-entry is compatible with `P`
(its honest source is) and is not `Σ.J`; with `Σ.J ⪯ P` it would be `Σ.J` or above `Σ.J`. -/
theorem not_contest_of_lo {i : Nat} (hinv : OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} (hk : k ≤ i) (hLo : ¬ HiAt tr H D.P y k) : ¬ (tr.state y k).fg.Contest := by
  have hU := D.coherent
  have hJP := J_anc_of_lo D hinv hy hk hLo
  rintro ⟨hm, X, hX, -, hXh, hJX⟩
  have hR := fg_reachable D.hrun.toLocalRun hy k
  have hJt := (Store.cache_invariants _ _ _ _ hR).2.1
  by_cases h0 : (tr.state y k).fg.hj = 0
  · rw [justified_genesis D.hrun (i := k) h0 hy] at hJX
    exact hJX ((Store.accepted_tree _ _ _ _ hR).2.2.2 X hX)
  have hsrc := rows_sourced D.hrun D.hnc (B := D.P) (n := k)
    (fun x hx k' hk' => hinv.sources x hx k' (by omega)) hy
  obtain ⟨hJh, hJT, -⟩ := justified_honest_source_before D.hrun D.hnc D.two_faults_lt hy hsrc
    (by omega)
  obtain ⟨E, hEt, hEX, hEh, hET, D', hD'P, hD's⟩ :=
    frame_crossing_source_before D.hrun D.hnc D.two_faults_lt hy (i := k) hsrc hX
      (j := (tr.state y k).fg.hj) (by omega) (by omega)
  have hEU : E ∈ tr.HonestBlocks H := fg_tree_subset_honest hy k hEt
  obtain ⟨x, hx, k', -, -, hED', -, -⟩ := honest_source_entry D.hrun D.hnc hD's hEU rfl
  have hEP : Compatible (tr.HonestBlocks H) E D.P :=
    compatible_of_anc hU (hED'.mono (fg_tree_subset_honest hx k')) hD'P
  rcases hEP with hEP | hPE
  · rcases Anc.total hU hEP hJP with h | h
    · have hEJ := honest_held_anc D.hrun D.hnc hy h hJt
      obtain rfl : E = (tr.state y k).fg.J :=
        held_entry_unique D.hrun D.hnc hy hJt hEJ .refl (hEh.trans hJh.symm) hET hJT
      exact hJX hEX
    · have hJE := honest_held_anc D.hrun D.hnc hy h hEt
      obtain rfl : (tr.state y k).fg.J = E :=
        held_entry_unique D.hrun D.hnc hy hEt hJE .refl (hJh.trans hEh.symm) hJT hET
      exact hJX hEX
  · exact hJX ((honest_held_anc D.hrun D.hnc hy (hJP.trans hPE) hEt).trans hEX)

/-- **The honest attestations at a restored vote are supported** (source support): at
an honest slot-`(q+1)` vote of `y` at cut `i`, every honest attestation of `y`'s tree has an honest
source compatible with `P` (lock safety's (SRC) before `i`) and extended by an honest vote of a slot
`≤ q`. The source is the viable ancestor of a fast stored lock of the signer (`ac_to_fg`'s
candidates are fast); its fast origin has an honest counted vote (`fastLock_honest_vote`), of the
lock's slot, which is at most `q`: a fast update of a later slot is written after the vote, and
an optimistic lock of slot `q + 1` before a held attestation is excluded
(`no_optimistic_before_held_row_of`). -/
theorem rows_supported {i : Nat} (hinv : OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) {q : Nat} (hs : e.msg.slot = q + 1) :
    HonestRowsSourced tr H (fun Ds => Compatible (tr.HonestBlocks H) Ds D.P ∧
      ∃ x ∈ H, ∃ k e', SA.VoteAt tr.projAC x k e' ∧ e'.msg.slot ≤ q ∧
        SA.VoteExtends (tr.HonestBlocks H) e'.msg Ds) y i := by
  have hr' := goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc
  have hr := hr'.localRun
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hti : tr.time i ≤ sp.ts q + 5 * sp.Δ := by
    have h : tr.time i ≤ sp.ts (e.msg.slot : Int) + sp.Δ := (cast_head_fcRoot hr hy hc).2
    rw [hs] at h
    simp only [SAParams.ts] at h ⊢
    push_cast at h
    linarith only [h]
  refine honestRowsSourced_iff.2 fun X hX a ha hav => ?_
  obtain ⟨m, hmi, hm, k, hkm, hsg⟩ := honest_row_signed_before D.hrun D.hnc hy hX ha hav
  obtain ⟨src, hcall⟩ := id hsg
  obtain ⟨j, rfl, ℓz, hcj, hcl, -, hC, hfg⟩ := attest_source D.hrun.toLocalRun hav hcall
  have hfr := (D.hrun.cutLaw a.val hav j _ hcj).1
  have hto : SA.ToFGAt tr.projAC a.val j ℓz src :=
    ⟨projAC_callAt.2 hcj, hcl, by rw [projAC_state D.hrun.toLocalRun hav j]; exact hC⟩
  -- the source is an honest source of the attestation's target
  have hcand := toFG_candidate hC
  have hst : src ∈ (tr.state a.val (j + 1)).fg.tree := by
    have h' := hcand.1.1
    rw [hfr] at h'
    rw [hfg]
    exact h'.1
  obtain ⟨⟨E, -, hEr, -, -, hET⟩, -⟩ :=
    Store.entry_state_of_source _ _ _ _ (fg_reachable D.hrun.toLocalRun hav (j + 1)) _ hst
  have hT := createAtt_T (D.hrun.cutLaw a.val hav (j + 1) _ hcall).1
  rw [← hEr, hET] at hT
  refine ⟨src, ⟨hinv.sources a.val hav j (by omega) ℓz src hto, ?_⟩,
    isHonestSource_iff.2 ⟨a.val, hav, j + 1, hst, hT.symm⟩⟩
  -- the source is the viable ancestor of a fast stored lock
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hav (projAC_callAt.2 hcj)
  obtain ⟨hsv, l, hl, hlb, hlf, -⟩ := hcand
  obtain ⟨l₀, hl₀, B, hB, hBr, -, rfl⟩ := hl
  obtain ⟨hVt, hVB⟩ := SA.viableAncestor_anc hΦ hB
  obtain rfl : src = ℓz.frame.viableAncestor B := hΦ.coherent.1 hsv.1 hVt hlb.symm
  have hl₀' : l₀ ∈ (tr.projAC.state a.val j).locks := by
    rw [projAC_state D.hrun.toLocalRun hav j]; exact hl₀
  obtain ⟨j', hj'j, B', CV, hfl, L, hLU, hLr, hLB'⟩ := SA.fast_lock_provenance hr hav j l₀ hl₀' hlf
  obtain rfl : L = B := hU.1 hLU (hΦU hB) (hLr.trans hBr.symm)
  obtain ⟨w, hw, jw, ew, hvw, hws, Hd, hHd, hHdr, hB'Hd⟩ :=
    SA.fastLock_honest_vote hr' D.two_faults_lt hav hfl
  refine ⟨w, hw, jw, ew, hvw, ?_, Hd, hHd, hHdr, (Anc.mono hΦU hVB).trans (hLB'.trans hB'Hd)⟩
  -- the lock's slot is at most `q`
  rw [hws]
  have hj'i : tr.time j' ≤ tr.time i := D.hrun.time_mono (by omega)
  by_contra hlt
  push Not at hlt
  rcases hfl with ⟨ℓu, -, hu, -⟩ | hO
  · have ht : tr.time j' = sp.ts l₀.slot + 6 * sp.Δ := hu.2.2.1
    have := ts_le_ts (sp := sp) hlt
    have hts : sp.ts (q + 1 : Nat) = sp.ts q + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    change tr.time j' ≤ tr.time i at hj'i
    linarith only [ht, this, hts, hj'i, hti, hΔ]
  · rcases Nat.lt_or_ge l₀.slot (q + 2) with hl2 | hl2
    · obtain hq : l₀.slot = q + 1 := by omega
      rw [hq] at hO
      exact no_optimistic_before_held_row_of D.hrun D.hnc D.two_faults_lt hy hc hs hm hmi hav
        hkm hsg hav (by omega) hO
    · obtain ⟨ℓO, A, -, hslot, -⟩ := id hO
      have h := (SA.ts_le_iff_le_slot sp (hr.time_nonneg j') (l₀.slot : Int)).2
        (le_of_eq (by rw [hslot]))
      have h' : sp.ts (l₀.slot : Int) ≤ tr.time j' := h
      have := ts_le_ts (sp := sp) hl2
      have hts : sp.ts (q + 2 : Nat) = sp.ts q + 8 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      change sp.ts (l₀.slot : Nat) ≤ tr.time j' at h'
      linarith only [h', this, hts, hj'i, hti, hΔ]

include D in
/-- A block held below a source's entry height is below the entry. (As `Compose/Sleepy/Frame.lean`'s
private `below_entry`.) -/
private theorem below_entry {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {B Ds E : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ (tr.state y i).fg.tree) (hE : E ∈ (tr.state y i).fg.tree)
    (hD : IsHonestSource tr H Ds E.root) (hDB : Compatible (tr.HonestBlocks H) Ds B)
    (hlt : ((tr.state y i).fg.σ B.root).h < ((tr.state y i).fg.σ E.root).h) :
    (tr.state y i).fg.Anc B E := by
  have hU := D.coherent
  obtain ⟨x, hx, k, -, -, hED, -, -⟩ := honest_source_entry D.hrun D.hnc hD ⟨y, hy, i, hE⟩ rfl
  have hEDU : Anc (tr.HonestBlocks H) E Ds := hED.mono (fg_tree_subset_honest hx k)
  have no : ¬ Anc (tr.HonestBlocks H) E B := fun h => by
    have := (honest_held_height D.hrun D.hnc hy (honest_held_anc D.hrun D.hnc hy h hB)).1
    omega
  rcases hDB with h | h
  · exact absurd (hEDU.trans h) no
  · rcases Anc.total hU h hEDU with h' | h'
    · exact honest_held_anc D.hrun D.hnc hy h' hE
    · exact absurd h' no

/-- **G4**: at a Lo honest vote of slot `q + 1 ≥ r + 1` above `Σ.F`, with
receiver service from `b₁`, a protected block `P` that some honest slot-`q` vote extends is
viable at the vote. The witness head is frozen; below the floor (`h_max − 1`, no contest under
Lo), the `h_max` carrier's floor entry is above `P` and the head of an honest vote extending its
source (`rows_supported`) is frozen and viable. -/
theorem viable_at_vote_of_lo {i : Nat} (hinv : OutageLockInv D i) {y : Fin sp.n} (hy : y ∈ H)
    (hS : ReceiverServiceAfter H (tr.HonestBlocks H) D.b₁ y tr.projAC)
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ℓ e) {q : Nat} (hs : e.msg.slot = q + 1) (hrq : D.r ≤ q)
    (hLo : ¬ HiAt tr H D.P y i) (hFP : Anc (tr.HonestBlocks H) (tr.state y i).fg.F D.P)
    (hw : ∃ x ∈ H, ∃ k e', SA.VoteAt tr.projAC x k e' ∧ e'.msg.slot = q ∧
      SA.VoteExtends (tr.HonestBlocks H) e'.msg D.P) :
    SA.ViableAtVote ℓ e (q + 1) D.P := by
  have hr := (goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc).localRun
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hfr : ℓ.frame = Node.frame (tr.state y i) :=
    (D.hrun.cutLaw y hy i _ (projAC_callAt.1 hc.1)).1
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  have hFℓ : ℓ.frame.F = (tr.state y i).fg.F := by rw [hfr]; rfl
  have hg : D.b₁ ≤ sp.ts q + sp.Δ := by
    have := ts_le_ts (sp := sp) hrq
    linarith only [this, D.hr.1]
  -- the head of an honest vote of a slot `≤ q` above `Σ.F` is frozen at `y`
  have frozen : ∀ x ∈ H, ∀ k e', SA.VoteAt tr.projAC x k e' → e'.msg.slot ≤ q →
      ∀ Z, SA.VoteExtends (tr.HonestBlocks H) e'.msg Z →
      Anc (tr.HonestBlocks H) (tr.state y i).fg.F Z →
      ∃ W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame (q + 1), Anc (tr.HonestBlocks H) Z W := by
    intro x hx k e' hv hs' Z ⟨Hd, hHd, hHdr, hZHd⟩ hFZ
    have hFHd : Anc (tr.HonestBlocks H) ℓ.frame.F Hd := hFℓ ▸ hFZ.trans hZHd
    exact ⟨Hd, accepted_voter_tree D.hrun D.hnc hy hc hs hHd
      (honest_head_accepted_after D.hrun D.hnc hy hS hg hc hs hx hv hs' hHd hHdr hFHd) hFHd, hZHd⟩
  have hvt : ∀ W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame (q + 1),
      W ∈ (tr.state y i).fg.tree := by
    intro W hW
    have := hW.1
    rw [hfr] at this
    exact this.1
  -- (K2): a frozen viable block above `P`
  have hK2 : ∃ W ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
      Anc (tr.HonestBlocks H) D.P W ∧ (tr.state y i).fg.IsViable W := by
    rw [hs]
    have hR := fg_reachable D.hrun.toLocalRun hy i
    have hfl : (tr.state y i).fg.headHeightFloor = (tr.state y i).fg.hmax - 1 := by
      unfold Store.headHeightFloor
      simp only [not_contest_of_lo D hinv hy le_rfl hLo, ↓reduceIte]
    obtain ⟨x, hx, k, e', hv, hs', hext⟩ := hw
    obtain ⟨Hx, hHx, hPHx⟩ := frozen x hx k e' hv hs'.le D.P hext hFP
    have hHxt := hvt Hx hHx
    by_cases hle : (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ Hx.root).h
    · exact ⟨Hx, hHx, hPHx, hle⟩
    -- below the floor: the floor entry of an `h_max` carrier is above `P`
    obtain ⟨-, -, -, -, -, ⟨X, hX, hXh⟩, -⟩ := Store.cache_invariants _ _ _ _ hR
    have hHx1 := (honest_held_chain D.hrun hy hHxt).1
    have hPHx' := honest_held_anc D.hrun D.hnc hy hPHx hHxt
    have hPt : D.P ∈ (tr.state y i).fg.tree := by
      by_cases he : D.P = Hx
      · exact he ▸ hHxt
      · exact (Anc.mem hPHx' he).1
    have hPh := (honest_held_height D.hrun D.hnc hy hPHx').1
    obtain ⟨E, hEt, -, hEh, -, Ds, ⟨hDsP, x', hx', k', e'', hv', hs'', hext'⟩, hDs⟩ :=
      frame_crossing_source_before D.hrun D.hnc D.two_faults_lt hy (i := i)
        (rows_supported D hinv hy hc hs) hX (j := (tr.state y i).fg.hmax - 1) (by omega) (by omega)
    have hPE := below_entry D hy hPt hEt hDs hDsP (by omega)
    obtain ⟨z, hz, kz, -, -, hEDs, -, -⟩ := honest_source_entry D.hrun D.hnc hDs
      (fg_tree_subset_honest hy i hEt) rfl
    have hEDsU : Anc (tr.HonestBlocks H) E Ds := hEDs.mono (fg_tree_subset_honest hz kz)
    have hPDs : Anc (tr.HonestBlocks H) D.P Ds :=
      (hPE.mono (fg_tree_subset_honest hy i)).trans hEDsU
    obtain ⟨W, hW, hDsW⟩ := frozen x' hx' k' e'' hv' hs'' Ds hext' (hFP.trans hPDs)
    have hEW := honest_held_anc D.hrun D.hnc hy (hEDsU.trans hDsW) (hvt W hW)
    have hWh := (honest_held_height D.hrun D.hnc hy hEW).1
    refine ⟨W, hW, hPDs.trans hDsW, ?_⟩
    change (tr.state y i).fg.headHeightFloor ≤ _
    omega
  rcases vote_viable D.hrun D.hnc hy hc (B := D.P) (hinv.caches y hy i le_rfl) (Or.inl hK2) with
    h | h
  · rw [hs] at h
    exact Or.inl h
  · right
    have hFP' : Anc (tr.HonestBlocks H) ℓ.frame.F D.P := hFℓ ▸ hFP
    have hPt := SA.frame_mem_of_between sp hU hΦ hΦU hΦ.fcRoot_mem h hFP'
    exact SA.anc_tree_of_anc_U hU hΦ hΦU hPt h hΦ.fcRoot_mem

/-- The invariant at the cuts before `i` holds at the cuts before every `k ≤ i`. -/
theorem OutageLockInv.mono {i k : Nat} (h : OutageLockInv D i) (hk : k ≤ i) :
    OutageLockInv D k where
  votes x hx k' hk' := h.votes x hx k' (by omega)
  late x hx k' hk' := h.late x hx k' (by omega)
  results y hy k' hk' := h.results y hy k' (by omega)
  locks y hy k' hk' := h.locks y hy k' (by omega)
  sources y hy k' hk' := h.sources y hy k' (by omega)
  caches y hy k' hk' := h.caches y hy k' (by omega)
  viable y hy k' hk' := h.viable y hy k' (by omega)
  protPrev x hx c ℓ hu hb k' hck hk' := h.protPrev x hx c ℓ hu hb k' hck (by omega)
  protCover x hx c ℓ hu hb k' hck hk' := h.protCover x hx c ℓ hu hb k' hck (by omega)

include D in
/-- A vote of slot `q` is cast at a cut before a cast of slot `q + 1`. -/
private theorem cut_lt_of_slot {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {k k' : Nat}
    {e e' : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt tr.projAC y k e)
    (hv' : SA.VoteAt tr.projAC x k' e') {q : Nat} (hs : e.msg.slot = q + 1)
    (hs' : e'.msg.slot = q) : k' < k := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨h1, -⟩ := OutageVoteInv.ts_le_cast D hy hv
  obtain ⟨-, h2⟩ := OutageVoteInv.ts_le_cast D hx hv'
  rw [hs] at h1
  rw [hs'] at h2
  have hts : sp.ts (q + 1 : Nat) = sp.ts q + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  by_contra hle
  have := D.hrun.time_mono (show k ≤ k' by omega)
  linarith only [h1, h2, hts, this, hΔ]

/-- An honest slot-`r` caster is in the cohort `A₀` or a late waker. -/
private theorem caster_mem_r {x : Fin sp.n} (hx : x ∈ H) {k : Nat}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.VoteAt tr.projAC x k e) (hs : e.msg.slot = D.r) :
    x ∈ D.A₀ ∪ D.W := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have ha := D.ha
  have hrk := D.hrk
  obtain ⟨hts, hte⟩ := OutageVoteInv.ts_le_cast D hx hv
  rw [hs] at hts hte
  have hcallk : tr.IsCall x k := by
    obtain ⟨ℓ, hc, -⟩ := hv
    exact ⟨_, projAC_callAt.1 hc⟩
  have hrK := ts_le_ts (sp := sp) hrk.2
  have hjr := ts_le_ts (sp := sp) (show D.j₀ ≤ D.r by omega)
  have hz := D.hz (tr.time k) (by linarith only [hts, hte, hrK, hjr, hΔ])
    ⟨x, hx, k, hcallk, le_rfl⟩
  exact D.hawake x hx (tr.time k) (by linarith only [ha, hts, hte, hrK, hjr, hΔ]) hz
    (D.hrun.awake_of_call x hx k hcallk)

/-- **INV, the inner cut induction**: from the invariant at the cuts before `i`
and receiver service from `b₁`, every honest vote at a cut `≤ i` of a slot after `r` extends `P`.
Root cover, Hi (H1) or Lo (G4 and the batch walk: the honest slot-`q` votes, all extending `P`
by induction, or `A₀`'s for `q = r`, are carried and outnumber the rest). It reads the invariant at
cut `i` only (`readPoint_liveLockBlocks_compatible_at` at each cast cut). -/
theorem outage_s5_inner
    (hS : ∀ y ∈ H, ReceiverServiceAfter H (tr.HonestBlocks H) D.b₁ y tr.projAC)
    (i : Nat) (hinv : OutageLockInv D i) :
    ∀ k ≤ i, ∀ y ∈ H, ∀ e, SA.VoteAt tr.projAC y k e → D.r < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e.msg D.P := by
  have hr' := goldilocks_ac_projection sp ro dg H tr proposer D.hrun D.hnc
  have hr := hr'.localRun
  have hU := D.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hki y hy e hv hrs
  obtain ⟨q, hs⟩ : ∃ q, e.msg.slot = q + 1 := ⟨e.msg.slot - 1, by omega⟩
  have hrq : D.r ≤ q := by omega
  have hinvk := hinv.mono D hki
  obtain ⟨ℓ, hc⟩ := id hv
  have hcast : SA.CastAt tr.projAC y k ℓ e := hc
  have hsl := (SA.castAt_spec hr hy hcast).2.1
  have hfr : ℓ.frame = Node.frame (tr.state y k) :=
    (D.hrun.cutLaw y hy k _ (projAC_callAt.1 hcast.1)).1
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcast.1
  have hFℓ : ℓ.frame.F = (tr.state y k).fg.F := by rw [hfr]; rfl
  have hL := readPoint_liveLockBlocks_compatible_at hinvk hy hcast
    (show 0 < sp.slot (tr.time k) by change 0 < sp.slot (tr.projAC.time k); omega) .refl
  have hcallk : tr.IsCall y k := ⟨_, projAC_callAt.1 hcast.1⟩
  have htk := (OutageVoteInv.ts_le_cast D hy hv).1
  rw [hs] at htk
  have hts : sp.ts (q + 1 : Nat) = sp.ts q + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hcallq : ∃ x ∈ H, ∃ j, tr.IsCall x j ∧ sp.ts q + sp.Δ ≤ tr.time j :=
    ⟨y, hy, k, hcallk, by linarith only [htk, hts, hΔ]⟩
  have hg : D.b₁ ≤ sp.ts q + sp.Δ := by
    have := ts_le_ts (sp := sp) hrq
    linarith only [this, D.hr.1]
  -- root cover
  by_cases hPF : Anc (tr.HonestBlocks H) D.P (tr.state y k).fg.F
  · obtain ⟨Hd, hHd, hHdr, -⟩ := SA.honest_head_frame hr hy hcast
    exact ⟨Hd, hΦU hHd, hHdr, hPF.trans (hFℓ ▸ Anc.mono hΦU (hΦ.rooted.2 Hd hHd))⟩
  have hFP : Anc (tr.HonestBlocks H) (tr.state y k).fg.F D.P :=
    ((hinvk.caches y hy k le_rfl).1).resolve_right hPF
  -- Hi
  by_cases hHi : HiAt tr H D.P y k
  · exact vote_extends_of_hi D hinvk hy hcast hHi hL
  -- Lo: a carried honest batch extending `P`
  have hcarry : ∀ SX ⊆ H, (∀ x ∈ SX, ∀ j e', SA.VoteAt tr.projAC x j e' → e'.msg.slot = q →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg D.P) →
      SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e q
        {v | ∃ x ∈ SX, ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg = v ∧ v.slot = q} := by
    intro SX hSX hall
    refine carryAt_after D.hrun D.hnc hy (hS y hy) hg hcast hs fun v hv' => ?_
    obtain ⟨x, hx, j, e', hve, rfl, hvs⟩ := hv'
    obtain ⟨Hd, hHd, hHdr, hPHd⟩ := hall x hx j e' hve hvs
    exact ⟨x, hSX hx, j, e', hve, rfl, hvs, Hd, hHd, hHdr, hFℓ ▸ hFP.trans hPHd⟩
  have hviab : (∃ x ∈ H, ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg.slot = q ∧
      SA.VoteExtends (tr.HonestBlocks H) e'.msg D.P) → SA.ViableAtVote ℓ e (q + 1) D.P :=
    viable_at_vote_of_lo D hinvk hy (hS y hy) hcast hs hrq hHi hFP
  rcases hrq.lt_or_eq with hrq' | rfl
  · -- `q > r`: every honest slot-`q` vote extends `P` (induction)
    have hall : ∀ x ∈ H, ∀ j e', SA.VoteAt tr.projAC x j e' → e'.msg.slot = q →
        SA.VoteExtends (tr.HonestBlocks H) e'.msg D.P := fun x hx j e' hve hvs =>
      ih j (cut_lt_of_slot D hx hy hv hve hs hvs) (by
        have := cut_lt_of_slot D hx hy hv hve hs hvs; omega) x hx e' hve (by omega)
    have hfb := D.hFB q hcallq
    have hsub : {x | x ∈ H ∧ tr.awake x (sp.ts q + sp.Δ) ∧ tr.JoinedAt x (sp.ts q + sp.Δ)} ⊆
        {x | x ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg.slot = q} := by
      rintro x ⟨hx, haw, hjn⟩
      obtain ⟨j, e', hve, hvs, -⟩ :=
        vote_of_awake_joined D.hrun D.hnc hx (mayVote_stock D.hrun D.hnc hx _) haw hjn
      exact ⟨hx, j, e', hve, hvs⟩
    have hcount : Hᶜ.ncard <
        {x | x ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg.slot = q}.ncard :=
      lt_of_lt_of_le hfb (Set.ncard_le_ncard hsub (Set.toFinite _))
    obtain ⟨x, hx, j, e', hve, hvs⟩ : ∃ x ∈ H, ∃ j e', SA.VoteAt tr.projAC x j e' ∧
        e'.msg.slot = q := by
      by_contra hno
      push Not at hno
      have : {x | x ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg.slot = q} = ∅ :=
        Set.eq_empty_of_forall_notMem fun x ⟨hx, j, e', hve, hvs⟩ => hno x hx j e' hve hvs
      rw [this, Set.ncard_empty] at hcount
      omega
    exact vote_extends_of_batch hr' hy hcast hs (hviab ⟨x, hx, j, e', hve, hvs,
      hall x hx j e' hve hvs⟩) hall hcount (hcarry H subset_rfl hall) hL
  · -- `q = r`: the cohort `A₀` casts and extends `P`; the others are in `Hᶜ ∪ W`
    have hσ := D.hσ
    have hrk := D.hrk
    have hall : ∀ x ∈ D.A₀, ∀ j e', SA.VoteAt tr.projAC x j e' → e'.msg.slot = D.r →
        SA.VoteExtends (tr.HonestBlocks H) e'.msg D.P := fun x hx j e' hve hvs =>
      hinvk.votes x (D.hA₀ hx) j (cut_lt_of_slot D (D.hA₀ hx) hy hv hve hs hvs) e' hve
        (by omega) (by omega) (Or.inr hx)
    have hSXv : ∀ x ∈ D.A₀, ∃ j e', SA.VoteAt tr.projAC x j e' ∧ e'.msg.slot = D.r := by
      intro x hx
      obtain ⟨haw, hjn⟩ := OutageVoteInv.cohort_ready D hx hrk.1 hrk.2 hcallq
      obtain ⟨j, e', hve, hvs, -⟩ := vote_of_awake_joined D.hrun D.hnc (D.hA₀ hx)
        (mayVote_stock D.hrun D.hnc (D.hA₀ hx) _) haw hjn
      exact ⟨j, e', hve, hvs⟩
    have hW : SA.voters (SA.mergedVoteView sp e.readPoint ℓ.frame (D.r + 1)).votes ⊆
        D.A₀ ∪ (Hᶜ ∪ D.W) := by
      rintro w ⟨v, hvm, rfl⟩
      by_cases hw : v.val ∈ H
      · obtain ⟨j, -, e', hve, he'⟩ := SA.honest_merged_vote hr' hy hcast hvm hw
        have hvs : e'.msg.slot = D.r := by
          rw [he']; exact SA.merged_vote_slot hr hy hcast v hvm
        rcases caster_mem_r D hw hve hvs with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl hw)
    have hcount : (D.A₀ ∪ (Hᶜ ∪ D.W)).ncard < 2 * D.A₀.ncard := by
      have := Set.ncard_union_le D.A₀ (Hᶜ ∪ D.W)
      have := D.hcohort
      omega
    obtain ⟨x, hx⟩ : D.A₀.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      rintro h
      have := D.hcohort
      rw [h, Set.ncard_empty] at this
      omega
    obtain ⟨j, e', hve, hvs⟩ := hSXv x hx
    exact vote_extends_of_counted_batch hr' hy hcast hs
      (hviab ⟨x, D.hA₀ hx, j, e', hve, hvs, hall x hx j e' hve hvs⟩) D.hA₀ hSXv hall hW hcount
      (hcarry D.A₀ D.hA₀ hall) hL

/-- **Lock safety's `hS5`**: compatibility past the lock lifetime, from
the inner induction at the cast cut. -/
theorem outage_s5_step
    (hS : ∀ y ∈ H, ReceiverServiceAfter H (tr.HonestBlocks H) D.b₁ y tr.projAC) :
    OutageS5StepAt D := by
  rw [outageS5StepAt_iff]
  intro i hinv y hy e hv hs
  have hrk := D.hrk
  exact (outage_s5_inner D hS i hinv i le_rfl y hy e hv (by omega)).voteCompat

/-- **INV at all cuts**: every honest vote of a slot after `r` extends `P`. -/
theorem restored_votes_extend
    (hS : ∀ y ∈ H, ReceiverServiceAfter H (tr.HonestBlocks H) D.b₁ y tr.projAC)
    (hinv : ∀ i, OutageLockInv D i) :
    ∀ y ∈ H, ∀ k e, SA.VoteAt tr.projAC y k e → D.r < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e.msg D.P :=
  fun y hy k e hv hs => outage_s5_inner D hS k (hinv k) k le_rfl y hy e hv hs

/-- **`ExtendingMajority` at every restored label**: `q = r` by the cohort count
(`restored_majority_at_r`), `q > r` by INV and the fault bound (`extendingMajority_of_all`). -/
theorem restored_majority
    (hS : ∀ y ∈ H, ReceiverServiceAfter H (tr.HonestBlocks H) D.b₁ y tr.projAC)
    (hinv : ∀ i, OutageLockInv D i) (q : Nat) (hq : D.r ≤ q)
    (hcall : ∃ x ∈ H, ∃ i, tr.IsCall x i ∧ sp.ts q + sp.Δ ≤ tr.time i) :
    ExtendingMajority tr H D.P q := by
  rcases hq.lt_or_eq with hq | rfl
  · exact extendingMajority_of_all D.hrun D.hnc
      (fun x hx k e hv hs => restored_votes_extend D hS hinv x hx k e hv (by omega))
      (D.hFB q hcall)
  · exact restored_majority_at_r D hinv hcall

end Consensus.Goldilocks.Compose

end

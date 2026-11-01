module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Batch
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Vote
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts

-- Keep the operational proposal prerequisites with their pivot consumers.
set_option linter.style.longFile 2800

public section

/-! # Goldilocks Healing: the pivot of an honest ready proposal after the drain (interface)

Post-reset `Compose.pivot` (A1.7, workbench#12 §2) for `ready_unanimous`: an honest ready
proposal `P` at `t_u ≥ R` has duty head `Q = P.parent`. Under reset premises, `Catch(2Δ)`
and three OPEN compatibility/support suppliers, its walk contains `D` with a viable
path to `Q`. Each honest slot-`u` voter whose earlier honest slot-`u` votes are `P` walks
through `P` or that path. Voters need not reach the proposer's own unlocked anchor.

The proof replaces Sleepy old origins with `OldSrc u`, HR.4 high origins before `t_u`:
* HR.4 (R3) puts every old source below every honest slot-`u` vote;
* stored proposal locks are compatible with old sources; non-current live vote locks have
  viable ancestors below the proposal parent (OPEN source-service obligations);
* an earlier honest supporter puts slot-`u` locks below `P`;
* `D` is deepest among the walk's start and the old sources on the walk.

Held viability lets the walk pass old sources. Fork-choice roots are genesis or below an old
source: high `J` uses a crossing row; low `J` uses the relayed reset seed and no top-height contest.
No universal low-row premise is needed. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-! ### Blocks and walks (private copies of `Compose/Service/Pivot`) -/

section Walk
variable {FGP : Type}
/-- A descendant inside the tree of a block of the tree is in the tree. -/
private theorem mem_of_anc_left {Φ : SA.Frm sp.n FGP} {A B : SA.Blk sp.n FGP} (h : Φ.Anc A B)
    (hA : A ∈ Φ.tree) : B ∈ Φ.tree := by
  by_cases hAB : A = B
  · exact hAB ▸ hA
  · exact (Anc.mem h hAB).2

/-- The upper end of an ancestry inside `U` from a block of `U` is in `U`. -/
private theorem mem_of_anc_right {U : Set (SA.Blk sp.n FGP)} {A B : SA.Blk sp.n FGP}
    (h : Anc U A B) (hA : A ∈ U) : B ∈ U := by
  by_cases hAB : A = B
  · exact hAB ▸ hA
  · exact (Anc.mem h hAB).2

/-- A block between two blocks of a well-formed frame's tree (ancestry in a coherent `U` holding
the tree) is in the tree. -/
private theorem mem_between {U : Set (SA.Blk sp.n FGP)} (hU : Coherent U) {Φ : SA.Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {A B C : SA.Blk sp.n FGP} (hA : A ∈ Φ.tree)
    (hC : C ∈ Φ.tree) (hAB : Anc U A B) (hBC : Anc U B C) : B ∈ Φ.tree := by
  have hFB : Anc U Φ.F B := (Anc.mono hΦU (hΦ.rooted.2 A hA)).trans hAB
  revert hC
  induction hBC with
  | refl => exact id
  | @tail c d hBc e ih =>
    intro hd
    refine ih ?_
    by_cases hdF : d = Φ.F
    · subst hdF
      have h1 := (Anc.slot_le hU (hFB.trans hBc)).1
      have h2 := hU.2 c e.1 _ e.2.1 e.2.2
      omega
    obtain rfl | ⟨p, -, hp⟩ :=
      (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hΦ.rooted.2 d hd)
    · exact absurd rfl hdF
    obtain rfl : p = c := hU.1 (hΦU hp.1) e.1 (Option.some_injective _ (hp.2.2.symm.trans e.2.2))
    exact hp.1

/-- A proper ancestor of a block is an ancestor of its parent. -/
private theorem anc_parent {U : Set (SA.Blk sp.n FGP)} (hU : Coherent U)
    {A B Q : SA.Blk sp.n FGP} (h : Anc U A B) (hne : A ≠ B) (hBQ : B.parent = some Q.root)
    (hQ : Q ∈ U) : Anc U A Q := by
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨Y, hAY, hY⟩
  · exact absurd heq.symm hne
  obtain rfl : Y = Q := hU.1 hY.1 hQ (Option.some_injective _ (hY.2.2.symm.trans hBQ))
  exact hAY

/-- The anchor is a live lock block or `fc_root`. -/
private theorem anchor_mem (Φ : SA.Frm sp.n FGP) (A : SA.SAState sp.n) (t : Time) :
    SA.getAnchor sp A Φ t ∈ SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot} := by
  unfold SA.getAnchor
  cases hd : SA.deepest Φ (SA.liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) with
  | none => exact Or.inr rfl
  | some D => exact (SA.deepest_mem hd).1

/-- The anchor of a well-formed frame is in its tree. -/
private theorem anchor_tree {Φ : SA.Frm sp.n FGP} (hΦ : FrameOK Φ) (A : SA.SAState sp.n)
    (t : Time) : SA.getAnchor sp A Φ t ∈ Φ.tree := by
  rcases anchor_mem Φ A t with h | h
  · exact h.1
  · exact (Set.mem_singleton_iff.1 h) ▸ hΦ.fcRoot_mem

/-- The duty head of a proposal is the walk of the full viable tree from its start, the anchor
after the proposal's unlocking. -/
private theorem acProposal_walk {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP} {t : Time}
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (h : (SA.acProposal sp A Φ t).2 = some (d, pay)) :
    ∃ A₁ : SA.SAState sp.n,
      A₁.locks = SA.unlock sp A.locks Φ t ((sp.slot t : Int) - 1) (SA.View.ofLists pay) ∧
      d.start = SA.getAnchor sp A₁ Φ t ∧
      d.head = SA.getHead sp A₁ Φ t (Φ.viableTree Φ.tree) (SA.View.ofLists pay)
        ((sp.slot t : Int) - 1) := by
  unfold SA.acProposal at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, rfl, rfl, rfl⟩

end Walk

/-! ### Run facts (private copies of `Compose/Service/Pivot` and `Outcome/Supplier`) -/

/-- `f < n/2` under `Healthy(g)`. -/
private theorem faulty_lt_half (hp : ResetPremises tr H proposer dg g ΔF a) (x : Fin sp.n) :
    2 * Hᶜ.ncard < sp.n := by
  have := hp.healthy.2.2
  have := Fin.pos x
  have hn : sp.n = sp.toParams.n := rfl
  omega

/-- Blocks with the same fields are equal. -/
private theorem block_eq {X Y : SA.Blk sp.n (List (FG.Att sp.n))} (h0 : X.root = Y.root)
    (h1 : X.parent = Y.parent) (h2 : X.slot = Y.slot) (h3 : X.proposer = Y.proposer)
    (h4 : X.input = Y.input) (h5 : X.fgPayload = Y.fgPayload) (h6 : X.acPayload = Y.acPayload) :
    X = Y := by
  cases X
  cases Y
  simp_all

/-- An honest block with the root of an honest proposal is that proposal (`NoColl`). -/
private theorem eq_proposal (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt p k P) {R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : R ∈ tr.HonestBlocks H) (hr : R.root = P.root) : R = P := by
  obtain ⟨⟨⟨acc, hcB⟩, hpos⟩, hpp, -⟩ := hP
  rcases Compose.blockCall_cases hrun.toLocalRun hp hcB with
    hg | ⟨j, x, rfl, -, hPr, d, pay, -, hB, -⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  have hok : P.RootOk dg := by rw [hB]; rfl
  have hpr : P.proposer = proposer P.slot := by
    rw [hpp, hB]
    exact hPr.2.2.symm
  have hpar : P.parent ≠ none := by rw [hB]; simp [Node.mkBlock]
  have hocc : tr.Occurs P := ⟨p, _, acc, hcB⟩
  obtain ⟨y, hy, i, hRt⟩ := hR
  rcases Compose.tree_cases hrun.toLocalRun hy hRt with rfl | ⟨k', -, hk'⟩
  · have := (hnc _ (Set.mem_insert _ _) P (Or.inr hocc)
      (hrun.genesis_root_ok.symm.trans (hr.trans hok))).1
    exact absurd this.symm (by simpa [Params.genesisBlock] using hpar)
  obtain ⟨hRok, hRpr, -⟩ := Compose.accept_facts hrun.toLocalRun hy hk'
  obtain ⟨h1, h2, h3, h4, h5⟩ := hnc R (Or.inr ⟨y, k', true, hk'⟩) P (Or.inr hocc)
    (hRok.symm.trans (hr.trans hok))
  exact block_eq hr h1 h2 (by rw [hRpr, hpr, h2]) h3 h4 h5

/-- A fast lock of label `s` is written at or after `t_s`. -/
private theorem ts_le_of_fastLock (hp : ResetPremises tr H proposer dg g ΔF a) {x : Fin sp.n}
    {i s : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC x i s D CV) : sp.ts s ≤ tr.time i := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  rcases hfl with ⟨ℓ, C, ⟨-, -, ht, -⟩, -⟩ | ⟨ℓ, A, -, hsl, -⟩
  · have ht' : tr.time i = sp.ts s + 6 * sp.Δ := ht
    rw [ht']
    linarith
  · have hsl' : sp.slot (tr.time i) = s := hsl
    exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) s).2 (by omega)

/-- A fast lock of a label `m < u` written by `t_u + Δ` is written before `t_u` (an update of
`m` runs at `t_m + 6Δ`, so `m ≤ u − 2`; an optimistic check of `m` runs in slot `m`). -/
private theorem fastLock_time_lt (hp : ResetPremises tr H proposer dg g ΔF a) {x : Fin sp.n}
    {r m u : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : SA.FastLockAt tr.projAC x r m D CV) (hmu : m < u)
    (htr : tr.time r ≤ sp.ts u + sp.Δ) : tr.time r < sp.ts u := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  rcases hfl with ⟨ℓ, C, ⟨-, -, ht, -⟩, -⟩ | ⟨ℓ, A, -, hsl, -⟩
  · have ht' : tr.time r = sp.ts m + 6 * sp.Δ := ht
    rw [ht'] at htr ⊢
    simp only [SAParams.ts] at htr ⊢
    have hm2 : (m : Int) + 2 ≤ u := by
      by_contra hcon
      have h1 : (u : Int) ≤ m + 1 := by omega
      nlinarith
    nlinarith
  · have hsl' : sp.slot (tr.time r) = m := hsl
    by_contra hcon
    have := (SA.ts_le_iff_le_slot sp (hr.time_nonneg r) u).1 (not_lt.1 hcon)
    have : sp.slot (tr.projAC.time r) = sp.slot (tr.time r) := rfl
    omega

/-- **The reset seed**: a high origin of a label `≤ slot(a)` written by `a` (as `Supplier`'s
`reset_seed`, keeping the write time). -/
private theorem reset_seed (hp : ResetPremises tr H proposer dg g ΔF a) :
    ∃ v r l O, HighOrigin tr H g v r l O ∧ l ≤ sp.slot a ∧ tr.time r ≤ a := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨⟨y, hy, k, att, hs, hh, rfl⟩, -⟩ := hp.reset
  obtain ⟨r, hrk, l, O, ho, -⟩ := high_row_source hp hy hs hh.ge
  obtain ⟨-, D, CV, -, hfl, -⟩ := highOrigin_mem hp ho
  have h₀ : tr.time r ≤ tr.time k := hr.time_mono hrk.le
  have h₁ : sp.ts l ≤ tr.time k := (ts_le_of_fastLock hp hfl).trans h₀
  exact ⟨y, r, l, O, ho,
    by exact_mod_cast (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) l).1 h₁, h₀⟩

/-- The reset precedes every slot start after the drain. -/
private theorem reset_lt_ts (hp : ResetPremises tr H proposer dg g ΔF a) {u : Nat}
    (hR : drainTime sp a ≤ sp.ts u) : a < sp.ts u := by
  have hΔ := sp.toParams.hΔ
  have hca := cutZ_lt_reset hp.run hp.healthy hp.reset
  have hlt := lt_cutZ sp g
  have hg := le_gbar g
  have hg0 := gbar_nonneg g
  have ha0 : 0 ≤ a := by linarith
  have h3 : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
    have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
    omega
  have h4 : sp.ts ((sp.slot a : Int) + 1) ≤ drainTime sp a := by
    rw [drainTime_eq]
    exact (SA.ts_le_iff sp).2 (by push_cast; omega)
  linarith

/-- A deepest block of a set is the one `deepest` returns. -/
private theorem deepest_eq_of_isDeepest {Φ : SA.Frm sp.n (List (FG.Att sp.n))}
    {S : Set (SA.Blk sp.n (List (FG.Att sp.n)))} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : SA.IsDeepest Φ S D) : SA.deepest Φ S = some D := by
  have hex : ∃ B, SA.IsDeepest Φ S B := ⟨D, h⟩
  cases hd : SA.deepest Φ S with
  | none =>
    unfold SA.deepest at hd
    simp only [hex, ↓reduceDIte, reduceCtorEq] at hd
  | some D' =>
    have h' := SA.deepest_mem hd
    by_contra hne
    have hne' : D' ≠ D := fun h => hne (congrArg some h)
    rcases h.2 D' h'.1 hne' with h₁ | ⟨h₁, h₂⟩ <;>
      rcases h'.2 D h.1 (Ne.symm hne') with h₃ | ⟨h₃, h₄⟩ <;> omega

/-- An honest validator is not an equivocator in an honest node's pool of a slot. -/
private theorem honest_not_equivocator_pool (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n}
    (hy : y ∈ H) (c s : Nat) {u : Fin sp.n} (hu : u ∈ H) :
    u ∉ SA.equivocators {v | v ∈ (tr.projAC.state y c).pool s} := by
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun.localRun
  rintro ⟨v, hv, w, hw, hvw, rfl, hwv⟩
  obtain ⟨jv, -, ev, hev, rfl⟩ := hrun.honest.pool_vote y hy c s _ hv hu
  obtain ⟨jw, -, ew, hew, rfl⟩ := hrun.honest.pool_vote y hy c s _ hw (hwv ▸ hu)
  rw [hwv] at hew
  obtain ⟨-, rfl⟩ := (SA.one_vote_per_slot sp) _ ro H _ _ hr _ hu jv jw ev ew hev hew
    ((SA.state_pool_slot sp hr hy c s _ hv).trans (SA.state_pool_slot sp hr hy c s _ hw).symm)
  exact hvw rfl

/-! ### No optimistic check of the proposal's slot before it (copies of `Compose/Service/Pivot`) -/

/-- The AC cuts of a tick by position (C0.4). -/
private theorem tick_ac_positions {y : Fin sp.n} {st : NodeState (goldilocksNode sp ro)}
    {t : Time} {x c : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (h : (Node.exec proposer dg y st t (.tick x)).2[c]? = some (Cut.ac ℓ)) :
    (ℓ.call = .tick ∧ c = 0) ∨ ℓ.call = .toFG ∨
      (Node.Proposes proposer y t ∧
        ((ℓ.call = .proposal ∧ c = 1) ∨ (ℓ.call ≠ .proposal ∧ 2 ≤ c))) := by
  obtain ⟨ℓt, pc, uc, hlt, hcs, hpc, ℓu, hlu, huc⟩ :=
    @Compose.tick_order sp.toParams (goldilocksNode sp ro) proposer dg y st t x
  have huc' : ∀ ℓ', Cut.ac ℓ' ∈ uc → ℓ'.call = .toFG := by
    intro ℓ' hm
    rcases huc with rfl | ⟨C, rfl⟩ | ⟨C, a, rfl⟩ <;> simp at hm <;> (rw [hm]; exact hlu)
  change (Node.onTick proposer dg y st t x).2[c]? = _ at h
  rw [hcs] at h
  rcases c with _ | c
  · simp only [List.getElem?_cons_zero, Option.some.injEq, Cut.ac.injEq] at h
    exact Or.inl ⟨h ▸ hlt, rfl⟩
  rw [List.getElem?_cons_succ] at h
  rcases hpc with ⟨-, rfl⟩ | ⟨hpr, ℓ₀, hℓ₀, hpc⟩
  · exact Or.inr (Or.inl (huc' ℓ (by simpa using List.mem_of_getElem? h)))
  obtain ⟨rest, rfl, hrest⟩ : ∃ rest, pc = Cut.ac ℓ₀ :: rest ∧
      ∀ ℓ', Cut.ac ℓ' ∈ rest → ℓ'.call ≠ .proposal := by
    rcases hpc with rfl | ⟨B, -, -, rfl | ⟨ℓ', hℓ', rfl⟩⟩
    · exact ⟨[], rfl, by simp⟩
    · exact ⟨_, rfl, by simp⟩
    · refine ⟨_, rfl, fun ℓ'' hm => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, Cut.ac.injEq, reduceCtorEq, false_or,
        or_false] at hm
      rw [hm, hℓ']
      simp
  rcases c with _ | c
  · simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq, Cut.ac.injEq] at h
    exact Or.inr (Or.inr ⟨hpr, Or.inl ⟨h ▸ hℓ₀, rfl⟩⟩)
  rw [List.cons_append, List.getElem?_cons_succ] at h
  rcases List.mem_append.1 (List.mem_of_getElem? h) with hm | hm
  · exact Or.inr (Or.inr ⟨hpr, Or.inr ⟨hrest ℓ hm, by omega⟩⟩)
  · exact Or.inr (Or.inl (huc' ℓ hm))

/-- No honest optimistic check selects a block of the proposal's slot before its actual call. -/
theorem proposal_no_optimistic_of_run
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {p : Fin sp.n}
    (hpH : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt p i ℓp)
    (hcall : ℓp.call = .proposal)
    (hti : tr.time i = sp.ts s) :
    ∀ x ∈ H, ∀ k' < i, ∀ C CV, ¬ SA.OptimisticLockAt tr.projAC x k' s C CV := by
  intro z hz c hci C CV hO
  have hr' := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hr'.localRun
  have hl := hrun.toLocalRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  obtain ⟨gi, ei, ki, hgi, rfl, hki⟩ := Compose.call_in_group hl hpH (Compose.projAC_callAt.1 hc)
  rw [hti] at hgi hki
  obtain ⟨xi, rfl⟩ := Compose.acProposal_in_tick (List.mem_of_getElem? hki) hcall
  obtain ⟨hpr, hki1⟩ : Node.Proposes proposer p (sp.ts s) ∧ ki = 1 := by
    rcases tick_ac_positions hki with ⟨h, -⟩ | h | ⟨hpr, ⟨-, h⟩ | ⟨h, -⟩⟩
    · rw [hcall] at h; cases h
    · rw [hcall] at h; cases h
    · exact ⟨hpr, h⟩
    · exact absurd hcall h
  have hlen := (List.getElem?_eq_some_iff.1 hki).1
  obtain ⟨ℓO, AO, hpt, hslc, hsel, -⟩ := hO
  have hct : tr.time c ≤ sp.ts s := hti ▸ hrun.time_mono hci.le
  unfold SA.optimisticSelect at hsel
  dsimp only at hsel
  split_ifs at hsel
  have h34 := (SA.deepest_mem hsel).1.2.1
  rw [hslc] at h34
  have hnoH : SA.optimisticVoters sp AO ℓO.frame s C ⊆ Hᶜ := by
    rintro u ⟨v, hv, rfl, -⟩ huH
    obtain ⟨hvs, j', hj', e', ⟨ℓ', hc', he'⟩, rfl⟩ :=
      SA.optimisticPoint_pool_vote hr' hz hpt hv huH
    have hsl' : sp.slot (tr.projAC.time j') = s :=
      (SA.castAt_spec hr huH ⟨hc', he'⟩).2.1.symm.trans hvs
    have htj : tr.time j' = sp.ts s := le_antisymm ((hrun.time_mono hj').trans hct)
      ((SA.ts_le_iff_le_slot sp (hr.time_nonneg j') (s : Int)).2 (by rw [hsl']))
    obtain ⟨g', eu, k₁, hg, hjeq, hk₁⟩ := Compose.call_in_group hl huH (Compose.projAC_callAt.1 hc')
    rw [htj] at hg hk₁
    obtain ⟨htick, hnp, hnt, hnr⟩ := Compose.honest_vote_call hrun hnc huH ⟨hc', he'⟩
    have hph : eu.phase ≤ 1 := by
      rcases lt_trichotomy g' gi with h | rfl | h
      · have := hl.phase_order _ huH _ hpH g' gi (sp.ts s) eu _ hg hgi h
        simpa [Node.Event.phase] using this
      · obtain ⟨_, hn₁⟩ := (Compose.group_call hg).1
        obtain ⟨_, hn₂⟩ := (Compose.group_call hgi).1
        have hnode : e'.msg.val = p := hn₁.1.symm.trans hn₂.1
        rw [hnode] at hg
        rw [Compose.group_phase hg hgi]
        simp [Node.Event.phase]
      · exact absurd (Compose.group_start hgi hg h.le (by omega)) h.ne'
    cases eu with
    | tick xu =>
      rcases tick_ac_positions hk₁ with ⟨h, -⟩ | h | ⟨hpu, ⟨h, -⟩ | ⟨-, hk₁2⟩⟩
      · have h5 := htick h
        have hslts : sp.slot (sp.ts s) = s := by
          simpa using (SA.slot_arithmetic sp s).1 0 (by omega)
        rw [htj, hslts] at h5
        linarith
      · exact hnt h
      · exact hnp h
      have hup : e'.msg.val = p := hpu.2.2.symm.trans hpr.2.2
      rw [hup] at hg
      have := hl.tick_unique p hpH g' gi (sp.ts s) ⟨xu, hg⟩ ⟨xi, hgi⟩
      omega
    | restart =>
      have hmem := List.mem_of_getElem? hk₁
      simp only [Node.exec, Node.restart, Node.acCall, List.mem_singleton, Cut.ac.injEq] at hmem
      exact hnr (by rw [hmem])
    | _ => simp [Node.Event.phase] at hph
  have := Set.ncard_le_ncard hnoH (Set.toFinite _)
  omega

/-- Whole-run specialization of operational proposal ordering. -/
private theorem proposal_no_optimistic (hp : ResetPremises tr H proposer dg g ΔF a) {p : Fin sp.n}
    (hpH : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt p i ℓp)
    (hcall : ℓp.call = .proposal) (hti : tr.time i = sp.ts s) :
    ∀ x ∈ H, ∀ k' < i, ∀ C CV, ¬ SA.OptimisticLockAt tr.projAC x k' s C CV :=
  proposal_no_optimistic_of_run hp.run hp.noColl (faulty_lt_half hp p) hpH hc hcall hti

/-! ### Old sources -/

/-- **The old sources of slot `u`**: the HR.4 high origins written before `t_u` (the post-reset
counterpart of `Compose.pivot`'s old origins; their labels are below `u`). -/
private def OldSrc (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (g : Time) (u : Nat)
    (O : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∃ (x : Fin sp.n) (i j : Nat), HighOrigin tr H g x i j O ∧ tr.time i < sp.ts u

/-- Compare the actual cache and origin within a fixed horizon using only held
chains and prior signed-row origins. No later tick is required. -/
theorem finalized_compatible_high_origin_before
    (hp : ResetPremises tr H proposer dg g ΔF a) (Q : Time)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (_hcQ : tr.time c ≤ Q)
    {x : Fin sp.n} {i j : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j O) (_hiQ : tr.time i ≤ Q) :
    Compatible (tr.HonestBlocks H) (tr.state z c).fg.F O := by
  have hr := Compose.fg_reachable hp.run.toLocalRun hz c
  have hU := honest_coherent hp
  have hsub : (tr.state z c).fg.tree ⊆ tr.HonestBlocks H := fun _ h => ⟨z, hz, c, h⟩
  by_cases hh : HZ tr H g + 1 ≤ (tr.state z c).fg.hj
  · obtain ⟨_, hJm, hFJ, ⟨C, hC, hCJ, _⟩, -⟩ := Store.cache_invariants _ _ _ _ hr
    obtain ⟨E, hE, hEr, hEC, hcase⟩ := Store.J_entry_of_reachable hr hC
    obtain rfl : E = (tr.state z c).fg.J := hU.1 (hsub hE) (hsub hJm) (hEr.trans hCJ)
    rcases hcase with hg | ⟨hJh, hJT⟩
    · obtain ⟨_, _, _, _, _, _, _, _, _, hO⟩ := highOrigin_mem hp ho
      exact Or.inl ((hFJ.mono hsub).trans
        (Compose.honest_genesis_root_anc hp.run hU (hsub hJm)
          (congrArg (·.root) hg) ⟨x, ho.1, i, hO⟩))
    · obtain ⟨W, _, att, _, v, _, d, _, _, _, r, _, b, B, hB, hJB⟩ :=
        left_entry_origin hp hz hJm hJT (by omega) hEC
          (by have := Store.hj_lt_h hr hC; omega)
      have hFB := (hFJ.mono hsub).trans hJB
      have hcmp := (height_scoped_retention sp ro proposer dg H tr g ΔF
        hp.run hp.healthy hp.noColl a hp.reset).comparable v r b B x i j O hB ho
      rcases hcmp with h | h
      · exact Or.inl (hFB.trans h)
      · exact Anc.total hU hFB h
  · obtain ⟨_, _, _, _, _, _, _, _, _, hO⟩ := highOrigin_mem hp ho
    exact Or.inl (low_finalized_below_high_block hp hz ho.1 hO
      (high_of_anc hp ho ho.1 hO .refl) (by omega))

/-- The causal cache comparison also permits an origin written after the receiver cut. -/
theorem ResetPremisesUpTo.finalized_compatible_high_origin {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (hcb : ∀ q < c, tr.time q ≤ b)
    {x : Fin sp.n} {i j : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j O) (hib : tr.time i ≤ b) :
    Compatible (tr.HonestBlocks H) (tr.state z c).fg.F O := by
  have hr := Compose.fg_reachable hp.run.toLocalRun hz c
  have hU := hp.honest_coherent
  have hsub : (tr.state z c).fg.tree ⊆ tr.HonestBlocks H := fun _ h => ⟨z, hz, c, h⟩
  by_cases hh : HZ tr H g + 1 ≤ (tr.state z c).fg.hj
  · obtain ⟨_, hJm, hFJ, ⟨C, hC, hCJ, _⟩, _⟩ := Store.cache_invariants _ _ _ _ hr
    obtain ⟨E, hE, hEr, hEC, hcase⟩ := Store.J_entry_of_reachable hr hC
    obtain rfl : E = (tr.state z c).fg.J := hU.1 (hsub hE) (hsub hJm) (hEr.trans hCJ)
    rcases hcase with hg | ⟨hJh, hJT⟩
    · obtain ⟨_, _, _, _, _, _, _, _, _, hO⟩ := hp.highOrigin_mem ho
      exact Or.inl ((hFJ.mono hsub).trans
        (Compose.honest_genesis_root_anc hp.run hU (hsub hJm)
          (congrArg (·.root) hg) ⟨x, ho.1, i, hO⟩))
    · obtain ⟨_, _, _, _, v, _, d, hdc, _, _, r, hrd, m, B, hB, hJB⟩ :=
        hp.left_entry_origin hz hJm hJT (by omega) hEC
          (by have := Store.hj_lt_h hr hC; omega)
      have hFB := (hFJ.mono hsub).trans hJB
      rcases hp.origins_compatible hB (hcb r (by omega)) ho hib with h | h
      · exact Or.inl (hFB.trans h)
      · exact Anc.total hU hFB h
  · exact Or.inl (hp.low_finalized_below_origin hz c (by omega) ho)

/-- Whole-run cache comparison permits an origin written after the receiver cut. -/
theorem finalized_compatible_high_origin_at_any_cut
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat}
    {x : Fin sp.n} {i j : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j O) :
    Compatible (tr.HonestBlocks H) (tr.state z c).fg.F O := by
  exact finalized_compatible_high_origin_before hp (max (tr.time c) (tr.time i)) hz
    (le_max_left _ _) ho (le_max_right _ _)

/-- Post-reset specialization retained for callers with an explicit reset cut bound. -/
theorem finalized_compatible_high_origin (hp : ResetPremises tr H proposer dg g ΔF a)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (_hac : a ≤ tr.time c)
    {x : Fin sp.n} {i j : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j O) :
    Compatible (tr.HonestBlocks H) (tr.state z c).fg.F O :=
  finalized_compatible_high_origin_at_any_cut hp hz ho

/-- A post-reset finalized cache is below a high origin written no later than its cut. -/
theorem finalized_below_high_origin (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (ha : a ≤ tr.time k) :
    ∃ x r b B, HighOrigin tr H g x r b B ∧ tr.time r ≤ tr.time k ∧
      Anc (tr.HonestBlocks H) (tr.state y k).fg.F B := by
  have hr := Compose.fg_reachable hp.run.toLocalRun hy k
  have hU := honest_coherent hp
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocks H := fun _ h => ⟨y, hy, k, h⟩
  obtain ⟨hFm, hJm, hFJ, ⟨C, hC, hCJ, hChj⟩, -⟩ :=
    Store.cache_invariants _ _ _ _ hr
  obtain ⟨E, hE, hEr, hEC, hcase⟩ := Store.J_entry_of_reachable hr hC
  obtain rfl : E = (tr.state y k).fg.J := hU.1 (hsub hE) (hsub hJm) (hEr.trans hCJ)
  rcases hcase with hg | ⟨hJh, hJT⟩
  · obtain ⟨v, r, b, B, ho, _, ht⟩ := reset_seed hp
    have hFG := (Store.accepted_tree _ _ _ _ hr).2.2.2 _ hFm
    rw [← hg] at hFG
    have he := (hFJ.mono hsub).antisymm hU (hFG.mono hsub)
    obtain ⟨_, _, _, _, _, _, _, _, _, hB⟩ := highOrigin_mem hp ho
    exact ⟨v, r, b, B, ho, ht.trans ha,
      Compose.honest_genesis_root_anc hp.run hU (hsub hFm)
        (congrArg (·.root) (he.trans hg)) ⟨v, ho.1, r, hB⟩⟩
  by_cases hh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj
  · obtain ⟨W, _, att, _, v, _, d, hdk, _, _, r, hrd, b, B, ho, hJB⟩ :=
      left_entry_origin hp hy hJm hJT (by omega) hEC
        (by have := Store.hj_lt_h hr hC; omega)
    exact ⟨v, r, b, B, ho, hp.run.time_mono (by omega), (hFJ.mono hsub).trans hJB⟩
  obtain ⟨v, r, b, B, ho, _, ht⟩ := reset_seed hp
  refine ⟨v, r, b, B, ho, ht.trans ha, ?_⟩
  rcases finalized_compatible_high_origin hp hy ha ho with h | h
  · exact h
  have hhigh := high_of_anc hp ho hy hJm (h.trans (hFJ.mono hsub))
  omega

/-- A high supporting head accepted by an honest voter before the previous slot's relay
deadline is held in the proposal frame. Its height rules out pre-GST acceptance. -/
private theorem proposal_relay_high (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {u i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u)
    {x : Fin sp.n} {r l : Nat} {O B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hOB : Anc (tr.HonestBlocks H) O B)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (hacc : tr.projAC.AcceptAt z c B)
    (hct : tr.time c < sp.ts ((u : Int) - 1) + 2 * sp.Δ)
    (hFB : Anc (tr.HonestBlocks H) ℓp.frame.F B) :
    B ∈ ℓp.frame.tree ∧ SA.AcceptedBefore tr.projAC p B (sp.ts ((u : Int) - 1) + 3 * sp.Δ) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  have hgc : g ≤ tr.time c := by
    have := (cutZ_lt_of_anc hp ho hz (acceptAt_mem hp hz hacc) hOB).1
    have := lt_cutZ sp g
    have := le_gbar g
    linarith
  have hsi : sp.slot (tr.time i) = u := by
    rw [hti]; simpa using (SA.slot_arithmetic sp u).1 0 (by omega)
  have hts : sp.ts (u : Int) = sp.ts ((u : Int) - 1) + 4 * sp.Δ := by
    simp only [SAParams.ts]; ring
  have hrs := Compose.proposal_call_restarts hp.run hp.noColl hpH hci hcall hd
  rw [hsi] at hrs
  have hdl : ∀ k ≤ i, tr.projAC.deadline p k (tr.projAC.time c) ≤
      sp.ts ((u : Int) - 1) + 3 * sp.Δ := fun k hk => by
    have hd := deadline_le_restarts (T := tr.projAC)
      (fun c' hc' hr' => hrs c' (hc'.trans hk) hr') (tr.projAC.time c)
    have := max_le hct.le (show sp.ts ((u : Int) - 1) ≤ sp.ts ((u : Int) - 1) + 2 * sp.Δ by
      linarith)
    change _ ≤ max (tr.time c) (sp.ts ((u : Int) - 1)) + sp.Δ at hd
    linarith
  have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF g (tr.time c) hp.run.toLocalRun (syncRun_of_gst hp.healthy.1 le_rfl)
  obtain ⟨k, hki, hak, hkt⟩ := hsync.2 z hz c B hacc hgc le_rfl p hpH i ℓp hci
    (by have := hdl i le_rfl; change _ ≤ tr.time i; linarith) hFB
  exact ⟨SA.mem_tree_of_acceptAt sp hr hpH hak hki hci hFB,
    Or.inr ⟨k, hak, lt_of_lt_of_le hkt (hdl k hki)⟩⟩

/-- Actual-call relay of a high supporting head to the proposal frame. -/
theorem ResetPremisesUpTo.proposal_relay_high {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) {u i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u)
    {x : Fin sp.n} {r l : Nat} {O B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hOB : Anc (tr.HonestBlocks H) O B)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (hacc : tr.projAC.AcceptAt z c B)
    (hct : tr.time c < sp.ts ((u : Int) - 1) + 2 * sp.Δ)
    (hFB : Anc (tr.HonestBlocks H) ell.frame.F B) :
    B ∈ ell.frame.tree ∧ SA.AcceptedBefore tr.projAC p B (sp.ts ((u : Int) - 1) + 3 * sp.Δ) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  have hgc : g ≤ tr.time c := by
    have := (hp.cutZ_lt_of_anc ho hz (hp.acceptAt_mem hz hacc) hOB).1
    have := lt_cutZ sp g
    have := le_gbar g
    linarith
  have hsi : sp.slot (tr.time i) = u := by
    rw [hti]; simpa using (SA.slot_arithmetic sp u).1 0 (by omega)
  have hts : sp.ts (u : Int) = sp.ts ((u : Int) - 1) + 4 * sp.Δ := by
    simp only [SAParams.ts]; ring
  have hrs := Compose.proposal_call_restarts hp.run hp.noColl hpH hci hcall hd
  rw [hsi] at hrs
  have hdl : ∀ k ≤ i, tr.projAC.deadline p k (tr.projAC.time c) ≤
      sp.ts ((u : Int) - 1) + 3 * sp.Δ := fun k hk => by
    have hd := deadline_le_restarts (T := tr.projAC)
      (fun c' hc' hr' => hrs c' (hc'.trans hk) hr') (tr.projAC.time c)
    have := max_le hct.le (show sp.ts ((u : Int) - 1) ≤ sp.ts ((u : Int) - 1) + 2 * sp.Δ by
      linarith)
    change _ ≤ max (tr.time c) (sp.ts ((u : Int) - 1)) + sp.Δ at hd
    linarith
  obtain ⟨k, hki, hak, hkt⟩ := (hp.sync.syncAC hp.run le_rfl).2 z hz c B hacc hgc le_rfl
    p hpH i ell hci (by have := hdl i le_rfl; change _ ≤ tr.time i; linarith) hFB
  exact ⟨SA.mem_tree_of_acceptAt sp hr hpH hak hki hci hFB,
    Or.inr ⟨k, hak, lt_of_lt_of_le hkt (hdl k hki)⟩⟩

/-- The label of an old source is below `u`. -/
private theorem label_lt_of_old (hp : ResetPremises tr H proposer dg g ΔF a)
    {u : Nat} {x : Fin sp.n}
    {i j : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j O)
    (ht : tr.time i < sp.ts u) : j < u := by
  obtain ⟨-, D, CV, -, hfl, -⟩ := highOrigin_mem hp ho
  by_contra hcon
  have h1 : sp.ts u ≤ sp.ts j := (SA.ts_le_iff sp).2 (by omega)
  linarith [ts_le_of_fastLock hp hfl]

/-- An old source is held by the proposer, or below its finalized cache. Relay starts at an
honest supporting vote head, not at the possibly later write of the origin. -/
private theorem proposal_holds_old (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {u i : Nat} (hai : a ≤ tr.time i)
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hO : OldSrc tr H g u O) :
    O ∈ ℓp.frame.tree ∨ Anc (tr.HonestBlocks H) O ℓp.frame.F := by
  obtain ⟨x, r, l, ho, hrt⟩ := hO
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun.localRun
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hpH hci
  have hcmp := finalized_compatible_high_origin hp hpH hai ho
  have hfr := Compose.frame_of_projAC hp.run hpH hci
  have hF : ℓp.frame.F = (tr.state p i).fg.F := by rw [hfr]; rfl
  rw [← hF] at hcmp
  rcases hcmp with hFO | hOF
  · left
    obtain ⟨ℓ, D, CV, hcx, hfl, -, -, -, hOD, -⟩ := highOrigin_mem hp ho
    obtain ⟨z, hz, j, e, hv, hes, B, hB, hBr, hDB⟩ :=
      SA.fastLock_honest_vote hrun (faulty_lt_half hp p) ho.1 hfl
    have hOB := (hOD.mono (SA.frameIn_of_callAt hr ho.1 hcx).2).trans hDB
    obtain ⟨ℓz, hcz, he⟩ := hv
    obtain ⟨⟨B', hB't, hB'r, -⟩, hjt⟩ := Compose.cast_head_fcRoot hr hz ⟨hcz, he⟩
    have hEq : B' = B := hr.coherent.1 ((SA.frameIn_of_callAt hr hz hcz).2 hB't) hB
      (hB'r.trans hBr.symm)
    rw [hEq] at hB't
    have hlu := label_lt_of_old hp ho hrt
    have hts : sp.ts l ≤ sp.ts ((u : Int) - 1) := (SA.ts_le_iff sp).2 (by omega)
    have hjt' : tr.time j ≤ sp.ts ((u : Int) - 1) + sp.Δ := by
      rw [hes] at hjt
      change tr.time j ≤ sp.ts l + sp.Δ at hjt
      linarith
    rcases Compose.frame_anc_accepted hr hz j ℓz hcz B hB't B .refl with hg | ⟨c, hcj, hacc⟩
    · exact False.elim ((cutZ_lt_of_anc hp ho hz
        (mem_tree_of_frame hp.run hz hcz hB't) hOB).2 hg)
    have hct : tr.time c < sp.ts ((u : Int) - 1) + 2 * sp.Δ := by
      have := hr.time_mono hcj
      change tr.time c ≤ tr.time j at this
      linarith
    have hBt := (proposal_relay_high hp hpH hci hcall hd hti ho hOB hz hacc hct
      (hFO.trans hOB)).1
    exact mem_between hr.coherent hΦ hΦU hΦ.rooted.1 hBt hFO hOB
  · exact Or.inr hOF

/-- An earlier high source is held at a bounded actual proposal, or finalized there. -/
theorem ResetPremisesUpTo.proposal_holds_old {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) {u i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    {x : Fin sp.n} {r l : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hrt : tr.time r < sp.ts u) :
    O ∈ ell.frame.tree ∨ Anc (tr.HonestBlocks H) O ell.frame.F := by
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun.localRun
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hpH hci
  have hrb : tr.time r ≤ b := hrt.le.trans (hti ▸ hib)
  have hcmp := hp.finalized_compatible_high_origin hpH
    (fun q hqi => (hp.run.time_mono hqi.le).trans hib) ho hrb
  have hfr := Compose.frame_of_projAC hp.run hpH hci
  have hF : ell.frame.F = (tr.state p i).fg.F := by rw [hfr]; rfl
  rw [← hF] at hcmp
  rcases hcmp with hFO | hOF
  · left
    obtain ⟨ellX, D, CV, hcx, hfl, _, _, _, hOD, _⟩ := hp.highOrigin_mem ho
    have hf : 2 * Hᶜ.ncard < sp.n := by have := hp.faults; have := Fin.pos p; omega
    obtain ⟨z, hz, j, e, hv, hes, B, hB, hBr, hDB⟩ :=
      SA.fastLock_honest_vote hrun hf ho.1 hfl
    have hOB := (hOD.mono (SA.frameIn_of_callAt hr ho.1 hcx).2).trans hDB
    obtain ⟨ellZ, hcz, he⟩ := hv
    obtain ⟨⟨B', hB't, hB'r, _⟩, hjt⟩ := Compose.cast_head_fcRoot hr hz ⟨hcz, he⟩
    have hEq : B' = B := hr.coherent.1 ((SA.frameIn_of_callAt hr hz hcz).2 hB't) hB
      (hB'r.trans hBr.symm)
    rw [hEq] at hB't
    have htr : sp.ts l ≤ tr.time r := by
      rcases hfl with ⟨ell', C, ⟨_, _, ht, _⟩, _⟩ | ⟨ell', A, _, hsl, _⟩
      · change tr.time r = sp.ts l + 6 * sp.Δ at ht
        linarith
      · exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg r) l).mpr (by omega)
    have hlu : l < u := by exact_mod_cast (SA.ts_lt_iff sp).mp (htr.trans_lt hrt)
    have hts : sp.ts l ≤ sp.ts ((u : Int) - 1) := (SA.ts_le_iff sp).mpr (by omega)
    have hjt' : tr.time j ≤ sp.ts ((u : Int) - 1) + sp.Δ := by
      rw [hes] at hjt
      change tr.time j ≤ sp.ts l + sp.Δ at hjt
      linarith
    rcases Compose.frame_anc_accepted hr hz j ellZ hcz B hB't B .refl with hg | ⟨c, hcj, hacc⟩
    · exact False.elim ((hp.cutZ_lt_of_anc ho hz
        (mem_tree_of_frame hp.run hz hcz hB't) hOB).2 hg)
    have hct : tr.time c < sp.ts ((u : Int) - 1) + 2 * sp.Δ := by
      have := hr.time_mono hcj
      change tr.time c ≤ tr.time j at this
      linarith
    have hBt := (hp.proposal_relay_high hpH hci hcall hd hti ho hOB hz hacc hct
      (hFO.trans hOB)).1
    exact mem_between hr.coherent hΦ hΦU hΦ.rooted.1 hBt hFO hOB
  · exact Or.inr hOF

/-- Conditional seed receipt at a proposal, including the finalized-equality case. -/
private theorem proposal_holds_high_of_finalized
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {u i : Nat} (hai : a ≤ tr.time i)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) {x : Fin sp.n} {r l : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x r l O)
    (hrt : tr.time r < sp.ts u) (hFO : Anc (tr.HonestBlocks H) ell.frame.F O) :
    O ∈ ell.frame.tree := by
  rcases proposal_holds_old hp hpH hai hci hcall hd hti ⟨x, r, l, ho, hrt⟩ with hO | hOF
  · exact hO
  · have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
    obtain ⟨hPhi, -⟩ := SA.frameIn_of_callAt hr hpH hci
    have he := Anc.antisymm hr.coherent hOF hFO
    rw [he]
    exact hPhi.rooted.1

/-- Root comparison for an actual proposal duty and an arbitrary held target. -/
theorem held_target_proposal_root_before
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r i u : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBx : B ∈ (tr.state x r).fg.tree)
    (hai : a ≤ tr.time i) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B → B ∈ ell.frame.tree)
    (hseed : ∃ v q m S, HighOrigin tr H g v q m S ∧ tr.time q < sp.ts u ∧
      Compatible (tr.HonestBlocks H) B S)
    (hcompare : ∀ v q m O, q < i → HighOrigin tr H g v q m O →
      Compatible (tr.HonestBlocks H) B O) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B := by
  by_cases hlow : (tr.state p i).fg.hj ≤ HZ tr H g
  · obtain ⟨v, q, m, S, hS, hm, hBS⟩ := hseed
    have hFS := low_finalized_below_origin hp hpH i hlow hS
    have hFF : ell.frame.F = (tr.state p i).fg.F := by
      rw [Compose.frame_of_projAC hp.run hpH hci]; rfl
    have hSt := proposal_holds_high_of_finalized hp hpH hai hci hcall hd hti hS hm
      (by rw [hFF]; exact hFS)
    exact low_root_of_held_seed_at_call hp hx hBx hpH hS hci
      (frame_tree_subset hp hpH hci hSt) hlow hBS hheld
  · exact high_J_root_of_held_at_call_before hp hx hBx hpH hci (by omega) hcompare

/-- Bounded root comparison uses only an actual proposal and earlier source comparisons. -/
theorem ResetPremisesUpTo.held_target_proposal_root_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r i u : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBx : B ∈ (tr.state x r).fg.tree)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B → B ∈ ell.frame.tree)
    (hseed : ∃ v q m S, HighOrigin tr H g v q m S ∧ tr.time q < sp.ts u ∧
      Compatible (tr.HonestBlocks H) B S)
    (hcompare : ∀ v q m O, q < i → HighOrigin tr H g v q m O →
      Compatible (tr.HonestBlocks H) B O) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B := by
  by_cases hlow : (tr.state p i).fg.hj ≤ HZ tr H g
  · obtain ⟨v, q, m, S, hS, hm, hBS⟩ := hseed
    have hFS := hp.low_finalized_below_origin hpH i hlow hS
    have hFF : ell.frame.F = (tr.state p i).fg.F := by
      rw [Compose.frame_of_projAC hp.run hpH hci]; rfl
    have hSt : S ∈ ell.frame.tree := by
      rcases hp.proposal_holds_old hpH hci hcall hd hti hib hS hm with h | h
      · exact h
      · rw [hFF] at h
        have he := Anc.antisymm hp.honest_coherent h hFS
        rw [he, ← hFF]
        exact (SA.frameIn_of_callAt
          (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
          hpH hci).1.rooted.1
    exact hp.low_root_of_held_seed_at_call hx hBx hpH hS hci
      (mem_tree_of_frame hp.run hpH hci hSt) hlow hBS hheld
  · exact hp.high_J_root_of_held_at_call_before hx hBx hpH hci (by omega) hcompare

/-! ### Sources of the proposer's rows -/

/-- A high row signed before a proposal has a strictly earlier source cut and label.
The entry remains explicit so a crossing proof can identify it by root coherence. -/
theorem proposal_high_row_source_before (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hti : tr.time i = sp.ts u) {v : Fin sp.n} (hv : v ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hki : k < i) (hs : tr.SignAt v k att)
    (hh : HZ tr H g + 1 ≤ att.h) :
    ∃ r l O E, r < k ∧ l < u ∧ HighOrigin tr H g v r l O ∧
      tr.time r < sp.ts u ∧ E ∈ (tr.state v r).fg.tree ∧ E.root = att.T ∧
      Compose.IsHonestSource tr H E att.T ∧ Anc (tr.HonestBlocks H) E O := by
  obtain ⟨r, hrk, l, O, ho, E, hE, hEO, hEr, -, hET⟩ := high_row_source hp hv hs hh
  obtain ⟨-, D, CV, -, hfl, -⟩ := highOrigin_mem hp ho
  have hrt : tr.time r ≤ sp.ts u := hti ▸ hp.run.time_mono (by omega)
  have hlu : l < u := by
    have hle : l ≤ u := by
      have := (SA.ts_le_iff sp).1 ((ts_le_of_fastLock hp hfl).trans hrt)
      exact_mod_cast this
    by_contra hn
    have hlu : l = u := by omega
    rw [hlu] at hfl
    rcases hfl with ⟨ℓ, C, ⟨-, -, ht, -⟩, -⟩ | hop
    · have ht' : tr.time r = sp.ts u + 6 * sp.Δ := ht
      have := sp.toParams.hΔ
      linarith
    · exact proposal_no_optimistic hp hpH hci hcall hti v hv r (by omega) D CV hop
  exact ⟨r, l, O, E, hrk, hlu, ho,
    fastLock_time_lt hp hfl hlu (by have := sp.toParams.hΔ; linarith), hE, hEr,
    Compose.isHonestSource_iff.2 ⟨v, hv, r, hE, hET.trans hEr⟩,
    hEO.mono (fun X hX => ⟨v, hv, r, hX⟩)⟩

/-- An origin already preceding an honest signature before a proposal has an older label.
This bound does not require the origin to precede a later receiving cast. -/
theorem origin_label_lt_at_proposal (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) {v : Fin sp.n} {r l : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hri : r < i) (ho : HighOrigin tr H g v r l O) : l < u := by
  obtain ⟨-, D, CV, -, hf, -⟩ := highOrigin_mem hp ho
  have hrt : tr.time r ≤ sp.ts u := hti ▸ hp.run.time_mono hri.le
  have hle : l ≤ u := by
    exact_mod_cast (SA.ts_le_iff sp).mp ((ts_le_of_fastLock hp hf).trans hrt)
  by_contra hn
  have hlu : l = u := by omega
  rw [hlu] at hf
  rcases hf with ⟨ell', C, ⟨-, -, ht, -⟩, -⟩ | hop
  · have ht' : tr.time r = sp.ts u + 6 * sp.Δ := ht
    have := sp.toParams.hΔ
    linarith
  · exact proposal_no_optimistic hp hpH hci hcall hti v ho.1 r hri D CV hop

/-- Finite high-origin labels preceding an actual proposal are strictly older. -/
theorem ResetPremisesUpTo.origin_label_lt_at_proposal {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) {v : Fin sp.n} {r l : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hri : r < i) (ho : HighOrigin tr H g v r l O) : l < u := by
  obtain ⟨_, D, CV, _, hfl, _⟩ := hp.highOrigin_mem ho
  have hrt : tr.time r ≤ sp.ts u := hti ▸ hp.run.time_mono hri.le
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  rcases hfl with ⟨ell', C, ⟨_, _, ht, _⟩, _⟩ | hop
  · have ht' : tr.time r = sp.ts l + 6 * sp.Δ := ht
    exact_mod_cast (SA.ts_lt_iff sp).mp (show sp.ts l < sp.ts u by linarith)
  · obtain ⟨_, _, _, hsl, _⟩ := id hop
    have hle : l ≤ u := by
      have hts : sp.ts l ≤ tr.time r :=
        (SA.ts_le_iff_le_slot sp (hr.time_nonneg r) l).mpr (by omega)
      exact_mod_cast (SA.ts_le_iff sp).mp (hts.trans hrt)
    have hf : 2 * Hᶜ.ncard < sp.n := by have := hp.faults; have := Fin.pos p; omega
    have hne : l ≠ u := fun he => proposal_no_optimistic_of_run hp.run hp.noColl hf hpH
      hci hcall hti v ho.1 r hri D CV (he ▸ hop)
    omega

/-- Floor crossing at a proposal uses the full held tree and the actual proposal cut. -/
theorem high_floor_source_at_proposal
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {x p : Fin sp.n} {r l i u : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l B) (hpH : p ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u)
    (hpair : ∀ v r l O, r < i → HighOrigin tr H g v r l O →
      ∀ v' r' l' O', r' < i → HighOrigin tr H g v' r' l' O' →
      Compatible (tr.HonestBlocks H) O O')
    (hcomp : ∀ v r l O, r < i → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocks H) B O)
    (hfloor : ((tr.state x r).fg.σ B.root).h < (tr.state p i).fg.headHeightFloor) :
    ∃ v r l O E, r < i ∧ HighOrigin tr H g v r l O ∧ l < u ∧
      E ∈ (tr.state p i).fg.tree ∧ Anc (tr.HonestBlocks H) E O ∧
      Anc (tr.HonestBlocks H) B O ∧
      (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ E.root).h := by
  apply high_floor_source_of_row_bound hp ho hpH (u := u) ?_ hpair hcomp hfloor
  intro W hW att ha v hv d hs hdi r l O hrd hO
  exact origin_label_lt_at_proposal hp hpH hci hcall hti (by omega) hO

/-- A bounded high floor at an actual proposal has a strictly older signed-row source. -/
theorem ResetPremisesUpTo.high_floor_source_at_proposal {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x p : Fin sp.n} {r l i u : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l B) (hpH : p ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hti : tr.time i = sp.ts u) (hrb : tr.time r ≤ b) (hib : tr.time i ≤ b)
    (hfloor : ((tr.state x r).fg.σ B.root).h < (tr.state p i).fg.headHeightFloor) :
    ∃ v q m O E, q < i ∧ HighOrigin tr H g v q m O ∧ m < u ∧
      E ∈ (tr.state p i).fg.tree ∧ Anc (tr.HonestBlocks H) E O ∧
      Anc (tr.HonestBlocks H) B O ∧
      (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ E.root).h := by
  obtain ⟨v, q, m, O, E, hqi, hO, hmu, hE, hEO, hBO, hfloor, _⟩ :=
    hp.high_floor_signed_source_of_row_bound ho hpH (u := u)
      (fun W hW att ha v hv d hsign hdi q m O hqd hO =>
        hp.origin_label_lt_at_proposal hpH hci hcall hti (by omega) hO)
      (fun v q m O hqi hO v' q' m' O' hqi' hO' =>
        hp.origins_compatible hO ((hp.run.time_mono hqi.le).trans hib)
          hO' ((hp.run.time_mono hqi'.le).trans hib))
      (fun v q m O hqi hO => hp.origins_compatible ho hrb hO
        ((hp.run.time_mono hqi.le).trans hib)) hfloor
  exact ⟨v, q, m, O, E, hqi, hO, hmu, hE, hEO, hBO, hfloor⟩

/-- Arbitrary-target proposal domain from actual receipt and bounded source comparisons. -/
theorem held_target_proposal_domain_before
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r i u : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBx : B ∈ (tr.state x r).fg.tree)
    (hai : a ≤ tr.time i) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B → B ∈ ell.frame.tree)
    (hseed : ∃ v q m S, HighOrigin tr H g v q m S ∧ tr.time q < sp.ts u ∧
      Compatible (tr.HonestBlocks H) B S)
    (hcompare : ∀ v q m O, q < i → HighOrigin tr H g v q m O →
      Compatible (tr.HonestBlocks H) B O) :
    Anc (tr.HonestBlocks H) B ell.frame.fcRoot ∨ B ∈ ell.frame.viableTree ell.frame.tree := by
  have hroot := held_target_proposal_root_before hp hx hpH hBx hai hci hcall hd hti
    hheld hseed hcompare
  by_cases hcovered : Anc (tr.HonestBlocks H) B ell.frame.fcRoot
  · exact Or.inl hcovered
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  have hrootB := hroot.resolve_right hcovered
  have hFB := (hPhi.F_anc_fcRoot.mono hPhiU).trans hrootB
  have hBt := hheld hFB
  have hBy := frame_tree_subset hp hpH hci hBt
  have hreach := Compose.fg_reachable hp.run.toLocalRun hpH i
  have hfr := Compose.frame_of_projAC hp.run hpH hci
  have hdesc : ∃ C ∈ ell.frame.tree, Anc (tr.HonestBlocks H) B C ∧
      (tr.state p i).fg.IsViable C := by
    by_cases hfloor : (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ B.root).h
    · exact ⟨B, hBt, .refl, hfloor⟩
    have hBfloor := lt_of_not_ge hfloor
    obtain ⟨v, q, m, S, hS, hqt, hBS⟩ := hseed
    obtain ⟨-, -, -, -, -, -, -, -, -, hSsrc⟩ := highOrigin_mem hp hS
    have finish : ∀ {z q n O E}, HighOrigin tr H g z q n O → tr.time q < sp.ts u →
        E ∈ (tr.state p i).fg.tree → Anc (tr.HonestBlocks H) E O →
        (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ E.root).h →
        Compatible (tr.HonestBlocks H) B O →
        ∃ C ∈ ell.frame.tree, Anc (tr.HonestBlocks H) B C ∧ (tr.state p i).fg.IsViable C := by
      intro z q n O E ho hqt hE hEO hEf hcomp
      have hBO : Anc (tr.HonestBlocks H) B O := by
        rcases hcomp with h | h
        · exact h
        · have hh := σ_h_le_of_anc hreach (anc_tree_of_anc hp hpH (hEO.trans h) hBy)
          omega
      have hOt := proposal_holds_high_of_finalized hp hpH hai hci hcall hd hti ho hqt
        (hFB.trans hBO)
      have hOy := frame_tree_subset hp hpH hci hOt
      have hh := σ_h_le_of_anc hreach (anc_tree_of_anc hp hpH hEO hOy)
      exact ⟨O, hOt, hBO, hEf.trans hh⟩
    by_cases hSf : (tr.state p i).fg.headHeightFloor ≤ ((tr.state v q).fg.σ S.root).h
    · have hBS' : Anc (tr.HonestBlocks H) B S := by
        rcases hBS with h | h
        · exact h
        · have hSy := mem_tree_of_anc hp hpH h hBy
          have hh := σ_h_le_of_anc hreach (anc_tree_of_anc hp hpH h hBy)
          rw [← σ_eq_run hp hS.1 hpH hSsrc hSy] at hh
          omega
      have hSt := proposal_holds_high_of_finalized hp hpH hai hci hcall hd hti hS hqt
        (hFB.trans hBS')
      have hSy := frame_tree_subset hp hpH hci hSt
      refine ⟨S, hSt, hBS', ?_⟩
      change (tr.state p i).fg.headHeightFloor ≤ _
      rw [← σ_eq_run hp hS.1 hpH hSsrc hSy]
      exact hSf
    · have hret := height_scoped_retention sp ro proposer dg H tr g ΔF
        hp.run hp.healthy hp.noColl a hp.reset
      obtain ⟨z, q', n, O, E, hqi, ho, hn, hE, hEO, _, hEf⟩ :=
        high_floor_source_at_proposal hp hS hpH hci hcall hti
          (fun v r l O _ ho v' r' l' O' _ ho' => hret.comparable v r l O v' r' l' O' ho ho')
          (fun z q' n O _ ho => hret.comparable v q m S z q' n O hS ho)
          (lt_of_not_ge hSf)
      obtain ⟨-, D, CV, -, hf, -⟩ := highOrigin_mem hp ho
      have htime : tr.time q' < sp.ts u := fastLock_time_lt hp hf hn
        (by have := hp.run.time_mono hqi.le; rw [hti] at this; have := sp.toParams.hΔ; linarith)
      exact finish ho htime hE hEO hEf (hcompare z q' n O hqi ho)
  obtain ⟨C, hCt, hBC, hCv⟩ := hdesc
  have hrootB' := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.fcRoot_mem hrootB hBt
  have hBC' := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hBt hBC hCt
  refine Or.inr ⟨hBt, hrootB', C, hCt, ?_, hBC'⟩
  have hCf : C ∈ (Node.frame (tr.state p i)).tree := hfr ▸ hCt
  have hrootC := hrootB'.trans hBC'
  rw [hfr] at hrootC ⊢
  exact ⟨hCf.1, hCf.2, Anc.mono (fun _ h => h.1) hrootC, hCv⟩

/-- Finite proposal domain for a held target compared with earlier high sources. -/
theorem ResetPremisesUpTo.held_target_proposal_domain_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r i u : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hBx : B ∈ (tr.state x r).fg.tree)
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B → B ∈ ell.frame.tree)
    (hseed : ∃ v q m S, HighOrigin tr H g v q m S ∧ tr.time q < sp.ts u ∧
      Compatible (tr.HonestBlocks H) B S)
    (hcompare : ∀ v q m O, q < i → HighOrigin tr H g v q m O →
      Compatible (tr.HonestBlocks H) B O) :
    Anc (tr.HonestBlocks H) B ell.frame.fcRoot ∨ B ∈ ell.frame.viableTree ell.frame.tree := by
  have hroot := hp.held_target_proposal_root_before hx hpH hBx hci hcall hd hti hib
    hheld hseed hcompare
  by_cases hcovered : Anc (tr.HonestBlocks H) B ell.frame.fcRoot
  · exact Or.inl hcovered
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  have hrootB := hroot.resolve_right hcovered
  have hFB := (hPhi.F_anc_fcRoot.mono hPhiU).trans hrootB
  have hBt := hheld hFB
  have hBy := mem_tree_of_frame hp.run hpH hci hBt
  have hreach := Compose.fg_reachable hp.run.toLocalRun hpH i
  have hfr := Compose.frame_of_projAC hp.run hpH hci
  have held : ∀ {z q m O}, HighOrigin tr H g z q m O → tr.time q < sp.ts u →
      Anc (tr.HonestBlocks H) B O → O ∈ ell.frame.tree := by
    intro z q m O ho hqt hBO
    rcases hp.proposal_holds_old hpH hci hcall hd hti hib ho hqt with h | h
    · exact h
    · have he := Anc.antisymm hr.coherent h (hFB.trans hBO)
      rw [he]
      exact hPhi.rooted.1
  have hdesc : ∃ C ∈ ell.frame.tree, Anc (tr.HonestBlocks H) B C ∧
      (tr.state p i).fg.IsViable C := by
    by_cases hfloor : (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ B.root).h
    · exact ⟨B, hBt, .refl, hfloor⟩
    obtain ⟨v, q, m, S, hS, hqt, hBS⟩ := hseed
    obtain ⟨_, _, _, _, _, _, _, _, _, hSsrc⟩ := hp.highOrigin_mem hS
    by_cases hSf : (tr.state p i).fg.headHeightFloor ≤ ((tr.state v q).fg.σ S.root).h
    · have hBS' : Anc (tr.HonestBlocks H) B S := by
        rcases hBS with h | h
        · exact h
        · have hSy := hp.mem_tree_of_anc hpH h hBy
          have hh := σ_h_le_of_anc hreach (hp.anc_tree_of_anc hpH h hBy)
          rw [← hp.σ_eq_run hS.1 hpH hSsrc hSy] at hh
          omega
      have hSt := held hS hqt hBS'
      refine ⟨S, hSt, hBS', ?_⟩
      change (tr.state p i).fg.headHeightFloor ≤ _
      rw [← hp.σ_eq_run hS.1 hpH hSsrc (mem_tree_of_frame hp.run hpH hci hSt)]
      exact hSf
    · obtain ⟨z, q', n, O, E, hqi, ho, hn, hE, hEO, _, hEf⟩ :=
        hp.high_floor_source_at_proposal hS hpH hci hcall hti
          (hqt.le.trans (hti ▸ hib)) hib (lt_of_not_ge hSf)
      have hBO : Anc (tr.HonestBlocks H) B O := by
        rcases hcompare z q' n O hqi ho with h | h
        · exact h
        · have hh := σ_h_le_of_anc hreach (hp.anc_tree_of_anc hpH (hEO.trans h) hBy)
          omega
      obtain ⟨_, D, CV, _, hf, _⟩ := hp.highOrigin_mem ho
      have htime : tr.time q' < sp.ts u := by
        rcases hf with ⟨ell', C, ⟨_, _, ht, _⟩, _⟩ | ⟨ell', A, _, hsl, _⟩
        · have ht' : tr.time q' = sp.ts n + 6 * sp.Δ := ht
          have hle := hp.run.time_mono hqi.le
          rw [hti, ht'] at hle
          rw [ht']
          simp only [SAParams.ts] at hle ⊢
          have hΔ := sp.toParams.hΔ
          have hn2 : (n : Int) + 2 ≤ u := by
            by_contra h
            have : (u : Int) ≤ n + 1 := by omega
            nlinarith
          nlinarith
        · by_contra h
          have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg q') u).mp (not_lt.mp h)
          change sp.slot (tr.time q') = n at hsl
          omega
      have hOt := held ho htime hBO
      have hh := σ_h_le_of_anc hreach
        (hp.anc_tree_of_anc hpH hEO (mem_tree_of_frame hp.run hpH hci hOt))
      exact ⟨O, hOt, hBO, hEf.trans hh⟩
  obtain ⟨C, hCt, hBC, hCv⟩ := hdesc
  have hrootB' := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.fcRoot_mem hrootB hBt
  have hBC' := SA.anc_tree_of_anc_U hr.coherent hPhi hPhiU hBt hBC hCt
  refine Or.inr ⟨hBt, hrootB', C, hCt, ?_, hBC'⟩
  have hCf : C ∈ (Node.frame (tr.state p i)).tree := hfr ▸ hCt
  have hrootC := hrootB'.trans hBC'
  rw [hfr] at hrootC ⊢
  exact ⟨hCf.1, hCf.2, Anc.mono (fun _ h => h.1) hrootC, hCv⟩

/-- Finite receipt of a raw writer's ancestor at a later slot start. -/
theorem ResetPremisesUpTo.raw_writer_held_at_slot_start {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i u : Nat}
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hwriter : SA.ResultAt tr.projAC x r s C CV ∨ SA.FastLockAt tr.projAC x r s C CV)
    (hBC : Anc (tr.HonestBlocks H) B C) (hs : SA.gbar g + 4 * sp.Δ ≤ sp.ts s)
    (hsu : s < u) {ell : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ell) (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b)
    (hFB : Anc (tr.HonestBlocks H) ell.frame.F B) : B ∈ ell.frame.tree := by
  have hS := healthy_base_of_reset_catch_before hp hc
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hstep : sp.ts s + 4 * sp.Δ ≤ tr.time i := by
    rw [hti]
    have ht := (SA.ts_le_iff sp).mpr (show (s : Int) + 1 ≤ u by omega)
    simp only [SA.SAParams.ts] at ht ⊢
    nlinarith
  obtain ⟨v, _, D, hD, hDr, hBD, hg | ⟨q, hq, hqt⟩⟩ :=
    raw_writer_relay_source hr hx hwriter hBC
  all_goals obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  · obtain ⟨G, hG, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hpH _ _ hci
    have hDG : D = G := hr.coherent.1 hD hG (hg.trans hGr.symm)
    subst D
    have hGD : G ∈ ell.frame.tree := by
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp (hFB.trans hBD) with he | ⟨c, _, hpar⟩
      · exact he ▸ hPhi.rooted.1
      · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
    exact SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hGD hBD hFB
  · have hFD := hFB.trans hBD
    have hDt : D ∈ ell.frame.tree := by
      by_cases hg : SA.gbar g ≤ tr.time q
      · have hd := deadline_le_restarts (T := tr.projAC) (c := i)
          (fun k hki hr' => restart_le_before hp hpH (Compose.projAC_restartAt.mp hr')
            ((hp.run.time_mono hki).trans hib)) (tr.time q)
        have hdl : tr.projAC.deadline p i (tr.time q) ≤ tr.time i := by
          have ht : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts s := by
            have hbase := (SA.ts_le_iff_le_slot sp (gbar_nonneg g)
              (sp.slot (SA.gbar g))).mpr (by omega)
            simp only [SAParams.ts] at hbase hs ⊢
            push_cast at *
            linarith
          change _ ≤ max (tr.time q) (sp.ts (sp.slot (SA.gbar g) + 1 : Nat)) + sp.Δ at hd
          have hm : max (tr.time q) (sp.ts (sp.slot (SA.gbar g) + 1 : Nat)) ≤
              sp.ts s + 2 * sp.Δ := max_le hqt.le (by linarith)
          linarith
        obtain ⟨k, hki, hak, _⟩ := hS.sync.relay x hx q D hq hg p hpH i ell hci
          (hdl.trans hib) hdl hFD
        exact SA.mem_tree_of_acceptAt sp hr hpH hak hki hci hFD
      · obtain ⟨k, hki, hak, _⟩ := hS.catchUp.relay x hx q D hq (not_le.mp hg)
          p hpH i ell hci (by change _ ≤ tr.time i; linarith) hib hFD
        exact SA.mem_tree_of_acceptAt sp hr hpH hak hki hci hFD
    exact SA.frame_mem_of_between sp hr.coherent hPhi hPhiU hDt hBD hFB

/-- A clean protected source compares with every high origin inside the horizon. -/
theorem ResetPremisesUpTo.protected_source_compatible_high_origin {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} (hx : x ∈ H) {r s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    {y : Fin sp.n} {q t : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g y q t D) (hqb : tr.time q ≤ b) :
    Compatible (tr.HonestBlocks H) B D := by
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun.localRun
  have hts := hp.clean_window_timing hs s (by have := sp.two_le_k; omega)
  have evidence : ∃ C CV,
      (SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV) ∧
      Anc (tr.HonestBlocks H) B C := by
    rcases hsource with ⟨CV, ⟨ell, C, hu, hR, _, hfast, _⟩ | hop⟩ | ⟨ell, C, hu, hR, _, hslow, _⟩
    · exact ⟨C, _, Or.inl ⟨ell, hu, hR, rfl⟩,
        ((SA.deepest_mem hfast).1.1.2.2).mono (SA.frameIn_of_callAt hr hx hu.1).2⟩
    · exact ⟨B, CV, Or.inr hop, .refl⟩
    · exact ⟨C, _, Or.inl ⟨ell, hu, hR, rfl⟩,
        ((SA.deepest_mem hslow).1.1.2.2).mono (SA.frameIn_of_callAt hr hx hu.1).2⟩
  obtain ⟨C, CV, hC, hBC⟩ := evidence
  rcases lt_trichotomy t s with h | rfl | h
  · have supporter : ∃ z ∈ H, ∃ j ≤ r, ∃ e, SA.VoteAt tr.projAC z j e ∧
        e.msg.slot = s ∧ SA.VoteExtends (tr.HonestBlocks H) e.msg C := by
      rcases hC with hC | hC
      · obtain ⟨z, hz, j, hjr, e, hv, _, hes, hCH⟩ :=
          hp.result_supporter hc hx hC (.refl : Anc (tr.HonestBlocks H) C C) hrb hts
        exact ⟨z, hz, j, hjr.le, e, hv, hes, hCH⟩
      · exact (hp.optimistic_supporter hx hC).2
    obtain ⟨z, hz, j, hjr, e, hv, hes, W, hW, hWr, hCW⟩ := supporter
    exact hp.target_compatible_older_origin ho hqb hz hv
      ((hp.run.time_mono hjr).trans hrb) hes h ⟨W, hW, hWr, hBC.trans hCW⟩
  · obtain ⟨DV, hst⟩ := ho.2.2.1
    obtain ⟨_, E, hfl, hDE⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
    have hcomp : Compatible (tr.HonestBlocks H) C E := by
      rcases hfl with ⟨ell, R, hu, hR, _, hfast, _⟩ | hop
      · have hER := ((SA.deepest_mem hfast).1.1.2.2).mono
          (SA.frameIn_of_callAt hr ho.1 hu.1).2
        rcases hp.result_source_compatible hc ho.1 hx
          ⟨ell, hu, hR, rfl⟩ hC hqb hrb hts with h | h
        · exact Or.inr (hER.trans h)
        · exact SA.anc_total hr.coherent h hER
      · exact hp.sources_same_label_compatible hc hx ho.1 hC (Or.inr hop) hrb hqb hts
    rcases hcomp with h | h
    · exact SA.anc_total hr.coherent (hBC.trans h) hDE
    · exact SA.anc_total hr.coherent hBC (hDE.trans h)
  · obtain ⟨DV, hst⟩ := ho.2.2.1
    obtain ⟨_, E, hfl, hDE⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
    have hf : 2 * Hᶜ.ncard < sp.n := by have := hp.faults; have := Fin.pos x; omega
    have hEB : Compatible (tr.HonestBlocks H) E B :=
      SA.fastLock_compatible_of_votes hrun ho.1 (Nat.lt_succ_self q) hfl hf (by
        intro z hz j hj e ⟨ell, hcast⟩ hes
        have hjb := (hp.run.time_mono (Nat.lt_succ_iff.mp hj)).trans hqb
        rcases hsource with ⟨CV, hfast⟩ | hslow
        · exact hp.fast_source_votes_before hc hx hfast hs hrb j hjb z hz ell e hcast (by omega)
        · exact hp.slow_source_votes_before hc hx hslow hs hrb j hjb z hz ell e hcast (by omega))
    rcases hEB with h | h
    · exact Or.inr (hDE.trans h)
    · exact SA.anc_total hr.coherent h hDE

/-- Clean raw sources have the actual proposal domain, without a source-before-proposal
cut assumption. Writer service is driven by the source label, including old acceptances. -/
theorem clean_source_proposal_domain_before
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i u : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hsu : s < u)
    (hR : drainTime sp a ≤ sp.ts u) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) :
    Anc (tr.HonestBlocks H) B ell.frame.fcRoot ∨ B ∈ ell.frame.viableTree ell.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have evidence : ∃ C CV, (SA.ResultAt tr.projAC x r s C CV ∨ SA.FastLockAt tr.projAC x r s C CV) ∧
      Anc (tr.HonestBlocks H) B C ∧ B ∈ (tr.state x r).fg.tree := by
    rcases hsource with ⟨CV, hf⟩ | hsl
    · refine ⟨B, CV, Or.inr hf, .refl, ?_⟩
      rcases hf with ⟨ellX, C, hupd, _, _, hdeep, _⟩ | ⟨ellX, A, hpt, _, hsel, _⟩
      · exact frame_tree_subset hp hx hupd.1 (SA.deepest_mem hdeep).1.1.1
      · unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        exact frame_tree_subset hp hx hpt.1 (SA.deepest_mem hsel).1.1
    · obtain ⟨ellX, C, hupd, hconf, _, hdeep, _⟩ := hsl
      have hB := (SA.deepest_mem hdeep).1.1
      exact ⟨C, _, Or.inl ⟨ellX, hupd, hconf, rfl⟩,
        hB.2.2.mono (SA.frameIn_of_callAt hr hx hupd.1).2,
        frame_tree_subset hp hx hupd.1 hB.1⟩
  obtain ⟨C, CV, hw, hBC, hBx⟩ := evidence
  obtain ⟨v, q, m, S, hS, hm, hqt⟩ := reset_seed hp
  have hat : a < sp.ts u := reset_lt_ts hp hR
  have htiming : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have ht := cutZ_le_ts_of_highOrigin hp hS
    have hz := lt_cutZ sp g
    have hsm : sp.ts (m + 1 : Nat) ≤ sp.ts s := (SA.ts_le_iff sp).mpr
      (by rw [cleanLabel_eq] at hs; omega)
    have he : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
      simp only [SA.SAParams.ts]; push_cast; ring
    rw [he] at hsm
    have := sp.toParams.hΔ
    linarith
  refine held_target_proposal_domain_before hp hx hpH hBx (by rw [hti]; exact hat.le)
    hci hcall hd hti ?_ ?_ ?_
  · exact raw_writer_held_at_slot_start hp hc hx hpH hw hBC htiming hsu hci hti
  · exact ⟨v, q, m, S, hS, hqt.trans_lt hat,
      clean_source_compatible_high_origin hp hc hx hsource hs hS⟩
  · intro v q m O _ ho
    exact clean_source_compatible_high_origin hp hc hx hsource hs ho

/-- A clean protected source has the actual finite proposal domain, without cut ordering. -/
theorem ResetPremisesUpTo.clean_source_proposal_domain_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i u : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hsu : s < u) (hrb : tr.time r ≤ b)
    (hR : drainTime sp a ≤ sp.ts u) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) :
    Anc (tr.HonestBlocks H) B ell.frame.fcRoot ∨ B ∈ ell.frame.viableTree ell.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have evidence : ∃ C CV, (SA.ResultAt tr.projAC x r s C CV ∨ SA.FastLockAt tr.projAC x r s C CV) ∧
      Anc (tr.HonestBlocks H) B C ∧ B ∈ (tr.state x r).fg.tree := by
    rcases hsource with ⟨CV, hf⟩ | hsl
    · refine ⟨B, CV, Or.inr hf, .refl, ?_⟩
      rcases hf with ⟨ellX, C, hupd, _, _, hdeep, _⟩ | ⟨ellX, A, hpt, _, hsel, _⟩
      · exact hp.frame_tree_subset hx hupd.1 (SA.deepest_mem hdeep).1.1.1
      · unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        exact hp.frame_tree_subset hx hpt.1 (SA.deepest_mem hsel).1.1
    · obtain ⟨ellX, C, hupd, hconf, _, hdeep, _⟩ := hsl
      have hB := (SA.deepest_mem hdeep).1.1
      exact ⟨C, _, Or.inl ⟨ellX, hupd, hconf, rfl⟩,
        hB.2.2.mono (SA.frameIn_of_callAt hr hx hupd.1).2,
        hp.frame_tree_subset hx hupd.1 hB.1⟩
  obtain ⟨C, CV, hw, hBC, hBx⟩ := evidence
  obtain ⟨v, q, m, S, hS, hqb, hm⟩ := hp.reset_seed
  have htiming : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have ht := hp.cutZ_le_ts_of_highOrigin hS
    have hz := lt_cutZ sp g
    have hsm : sp.ts (m + 1 : Nat) ≤ sp.ts s := (SA.ts_le_iff sp).mpr
      (by rw [cleanLabel_eq] at hs; omega)
    have he : sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ := by
      simp only [SA.SAParams.ts]; push_cast; ring
    rw [he] at hsm
    have := sp.toParams.hΔ
    linarith
  have hqt : tr.time q < sp.ts u := by
    obtain ⟨_, D, DV, _, hf, _⟩ := hp.highOrigin_mem hS
    have hmu : m + 2 ≤ u := by
      rw [drainTime_eq] at hR
      have := (SA.ts_le_iff sp).mp hR
      omega
    rcases hf with ⟨ellX, R, ⟨_, _, ht, _⟩, _⟩ | ⟨ellX, A, _, hsl, _⟩
    · have ht' : tr.time q = sp.ts m + 6 * sp.Δ := ht
      have htu := (SA.ts_le_iff sp).mpr (show (m : Int) + 2 ≤ u by omega)
      simp only [SAParams.ts] at ht' htu ⊢
      have := sp.toParams.hΔ
      nlinarith
    · by_contra h
      have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg q) u).mp (not_lt.mp h)
      change sp.slot (tr.time q) = m at hsl
      omega
  refine hp.held_target_proposal_domain_before hx hpH hBx hci hcall hd hti hib ?_ ?_ ?_
  · exact hp.raw_writer_held_at_slot_start hc hx hpH hw hBC htiming hsu hci hti hib
  · exact ⟨v, q, m, S, hS, hqt,
      hp.protected_source_compatible_high_origin hc hx hsource hs hrb hS hqb⟩
  · intro v q m O hqi ho
    exact hp.protected_source_compatible_high_origin hc hx hsource hs hrb ho
      ((hp.run.time_mono hqi.le).trans hib)

/-- The completed predecessor batch makes a proposal extend every clean raw source
whose label is at least two slots earlier. -/
theorem clean_source_proposal_parent_before
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i u : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hsu : s + 2 ≤ u)
    (hR : drainTime sp a ≤ sp.ts u) {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) : Anc (tr.HonestBlocks H) B d.head := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  rcases clean_source_proposal_domain_before hp hc hx hpH hsource hs (by omega) hR
      hci hcall hd hti with hBF | hV
  · obtain ⟨_, hhead⟩ := Compose.acProposal_start_anc_head hPhi hd
    obtain ⟨A₁, _, hstart, _⟩ := acProposal_walk hd
    rw [hstart] at hhead
    exact hBF.trans (Anc.mono hPhiU ((SA.fcRoot_anc_getAnchor hPhi A₁ (tr.time i)).trans hhead))
  have hFB := (hPhi.rooted.2 B hV.1).mono hPhiU
  obtain ⟨σ, rfl⟩ : ∃ σ, u = σ + 1 := ⟨u - 1, by omega⟩
  have hσ : sp.ts (σ + 1 : Nat) = sp.ts σ + 4 * sp.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  have votes : ∀ z ∈ H, ∀ q e, SA.VoteAt tr.projAC z q e → s < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
    rintro z hz q e ⟨ell', hc'⟩ hslot
    exact clean_source_votes_before hp hc (max (tr.time r) (tr.time q)) hx hsource hs
      (le_max_left _ _) q (le_max_right _ _) z hz ell' e hc' hslot
  have hσg : SA.gbar g + 4 * sp.Δ ≤ sp.ts σ := by
    obtain ⟨v, q, m, S, hseed, hm, -⟩ := reset_seed hp
    have ht := cutZ_le_ts_of_highOrigin hp hseed
    have hz := lt_cutZ sp g
    have hle : sp.ts m ≤ sp.ts σ := (SA.ts_le_iff sp).mpr
      (by rw [cleanLabel_eq] at hs; omega)
    linarith
  have hhigh : SA.HighLocksCompatible (tr.HonestBlocks H) (tr.projAC.state p i)
      (tr.time i) σ B := by
    refine SA.highLocksCompatible_iff.2 fun l hl _ hlσ X hX hXr => ?_
    obtain ⟨L, hL, hLr, O, hLO, q, hqi, CV, hO⟩ := SA.lock_below_origin hr hpH i l hl
    obtain rfl : X = L := hU.1 hX hL (hXr.trans hLr.symm)
    have hcomp : Compatible (tr.HonestBlocks H) O B := by
      rcases hO with ⟨ell', ⟨-, -, ht, -⟩, -⟩ | ⟨ellO, A, hpt, hsl, hsel, -⟩
      · have htime := hr.time_mono hqi.le
        have hle := (SA.ts_le_iff sp).mpr (show (σ : Int) ≤ l.slot by omega)
        change tr.time q ≤ tr.time i at htime
        change tr.time q = sp.ts l.slot + 6 * sp.Δ at ht
        rw [hti, hσ] at htime
        exfalso
        linarith
      · have hΦU := (SA.frameIn_of_callAt hr hpH hpt.1).2
        unfold SA.optimisticSelect at hsel
        dsimp only at hsel
        split_ifs at hsel
        have h34 := (SA.deepest_mem hsel).1.2.1
        rw [hsl] at h34
        refine SA.origin_compatible hU hΦU h34 hS.two_faulty_lt fun v hv hvH => ?_
        obtain ⟨hvs, q', _, e', hv', rfl⟩ := SA.optimisticPoint_pool_vote hS.run hpH hpt hv hvH
        exact votes _ hvH q' e' hv' (by rw [hvs]; omega)
    rcases hcomp with h | h
    · exact Or.inl (hLO.trans h)
    · exact SA.anc_total hU hLO h
  refine SA.batch_proposal hS.run hS.two_faulty_lt (SA.honest_voters_half hS hσg)
    (fun z hz q e hv he => votes z hz q e hv (by omega)) hpH hci
    (SA.proposal_slot hti) hd ⟨hV.1, Or.inl hV⟩ ?_ hhigh
  intro z hz q e hv he
  obtain ⟨H', hH', hHr', hBH⟩ := votes z hz q e hv (by omega)
  obtain ⟨Hd, hHd, hHdr, -, hh⟩ := SA.late_vote_held_of_frame hS hpH hci hσg
    (by change _ ≤ tr.time i; rw [hti, hσ]; linarith) hz hv he fun Hd hHd hHdr => by
      rw [hU.1 hHd hH' (hHdr.trans hHr'.symm)]
      exact hFB.trans hBH
  obtain ⟨hmem, -, hbs⟩ := hh i (Or.inl rfl)
  exact SA.heldAtProposal_iff.2 ⟨Or.inl hmem, Hd, hHd, hHdr,
    (hHdr ▸ hbs).trans (WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _))⟩

/-- The immediately preceding optimistic source reaches and constrains the proposal. -/
theorem clean_optimistic_proposal_parent
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hR : drainTime sp a ≤ sp.ts (s + 1 : Nat))
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) : Anc (tr.HonestBlocks H) B d.head := by
  have hS := healthy_base_of_reset_catch hp hc
  have hr := hS.run.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  have hsg : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    obtain ⟨v, q, m, S, hseed, hm, -⟩ := reset_seed hp
    have ht := cutZ_le_ts_of_highOrigin hp hseed
    have hz := lt_cutZ sp g
    have hle : sp.ts m ≤ sp.ts s := (SA.ts_le_iff sp).mpr
      (by rw [cleanLabel_eq] at hs; omega)
    linarith
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  rcases clean_source_proposal_domain_before hp hc hx hpH (Or.inl ⟨CV, Or.inr hop⟩) hs
      (by omega) hR hci hcall hd hti with hBF | hV
  · obtain ⟨_, hhead⟩ := Compose.acProposal_start_anc_head hPhi hd
    obtain ⟨A₁, _, hstart, _⟩ := acProposal_walk hd
    rw [hstart] at hhead
    exact hBF.trans (Anc.mono hPhiU ((SA.fcRoot_anc_getAnchor hPhi A₁ (tr.time i)).trans hhead))
  have hFB := (hPhi.rooted.2 B hV.1).mono hPhiU
  have hhigh : SA.HighLocksCompatible (tr.HonestBlocks H) (tr.projAC.state p i)
      (tr.time i) s B := by
    refine SA.highLocksCompatible_iff.2 fun l hl _ hls X hX hXr => ?_
    obtain ⟨q, hqi, D, hw, L, hL, hLr, hLD⟩ := SA.lock_provenance hr hpH i l hl
    obtain rfl : L = X := hr.coherent.1 hL hX (hLr.trans hXr.symm)
    have hqt : tr.time q ≤ sp.ts (s + 1 : Nat) := hti ▸ hp.run.time_mono hqi.le
    rcases hw with ⟨CV', hop'⟩ | ⟨ell', hupd⟩
    · have hle : l.slot ≤ s + 1 := by
        exact_mod_cast (SA.ts_le_iff sp).mp ((ts_le_of_fastLock hp (Or.inr hop')).trans hqt)
      have hne : l.slot ≠ s + 1 := by
        intro he
        exact proposal_no_optimistic hp hpH hci hcall hti p hpH q hqi D CV' (he ▸ hop')
      have he : l.slot = s := by omega
      rw [he] at hop'
      rcases SA.fastLock_fastLock_compatible hS hpH (Or.inr hop') hx (Or.inr hop)
          (by linarith) with h | h
      · exact Or.inl (hLD.trans h)
      · exact SA.anc_total hr.coherent hLD h
    · have ht : tr.time q = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
      have hle := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ l.slot by omega)
      rw [hts] at hqt
      exfalso
      linarith
  refine optimistic_first_proposal_anc hS.run hS.two_faulty_lt hx hop .refl hpH hci
    (SA.proposal_slot hti) hd ⟨hV.1, Or.inl hV⟩ ?_ hhigh
  intro v hv
  obtain ⟨hvs, hsend, D, hD, hDr, hBD, hacc⟩ := fastLock_writer hr hx (Or.inr hop) v hv
  have hFD := hFB.trans hBD
  refine SA.heldAtProposal_of_writer hr (hS.syncAC le_rfl (sp.ts s + 2 * sp.Δ))
    (by linarith) le_rfl hx hpH hci hti
    (fun k _ hk => lt_of_le_of_lt (hS.restart_le hpH hk) (by linarith)) hvs hsend
    ⟨D, hD, hDr, hFD, ?_⟩
  rcases hacc with hg | ⟨q, hq, hqt⟩
  · exact Or.inl hg
  by_cases hg : SA.gbar g ≤ tr.time q
  · exact Or.inr (Or.inl ⟨q, hq, hg, hqt⟩)
  · obtain ⟨k, hki, hak, hkt⟩ := hS.catchUp x hx q D hq (not_le.mp hg) p hpH i ell hci
      (by change _ ≤ tr.time i; rw [hti, hts]; linarith) hFD
    exact Or.inr (Or.inr ⟨k, hki, hak, by change tr.time k < _ at hkt ⊢; linarith⟩)

/-- A clean optimistic source extends the next actual proposal within the finite horizon. -/
theorem ResetPremisesUpTo.clean_optimistic_proposal_parent {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x p : Fin sp.n} (hx : x ∈ H) (hpH : p ∈ H) {r s i : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    (hR : drainTime sp a ≤ sp.ts (s + 1 : Nat))
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hib : tr.time i ≤ b) :
    Anc (tr.HonestBlocks H) B d.head := by
  have hS := healthy_base_of_reset_catch_before hp hc
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hf : 2 * Hᶜ.ncard < sp.n := by have := hp.faults; have := Fin.pos x; omega
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  have hsg : SA.gbar g + 4 * sp.Δ ≤ sp.ts s := by
    have ht := hp.clean_window_timing hs s (by have := sp.two_le_k; omega)
    have hz := lt_cutZ sp g
    linarith
  have hrs : ∀ k ≤ i, tr.projAC.RestartAt p k → tr.time k < sp.ts s := by
    intro k hki hk
    have ht := restart_le_before hp hpH (Compose.projAC_restartAt.mp hk)
      ((hp.run.time_mono hki).trans hib)
    have hs0 := (SA.ts_le_iff_le_slot sp (gbar_nonneg g)
      (sp.slot (SA.gbar g))).mpr (by omega)
    have hclean := hp.clean_window_timing hs s (by have := sp.two_le_k; omega)
    rw [cutZ_eq] at hclean
    have hlt : sp.slot (SA.gbar g) + 1 < s := by
      have := (SA.ts_le_iff sp).mp hclean
      omega
    exact ht.trans_lt ((SA.ts_lt_iff sp).mpr (by exact_mod_cast hlt))
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hpH hci
  rcases hp.clean_source_proposal_domain_before hc hx hpH (Or.inl ⟨CV, Or.inr hop⟩) hs
      (by omega) hrb hR hci hcall hd hti hib with hBF | hV
  · obtain ⟨_, hhead⟩ := Compose.acProposal_start_anc_head hPhi hd
    obtain ⟨A₁, _, hstart, _⟩ := acProposal_walk hd
    rw [hstart] at hhead
    exact hBF.trans (Anc.mono hPhiU ((SA.fcRoot_anc_getAnchor hPhi A₁ (tr.time i)).trans hhead))
  have hFB := (hPhi.rooted.2 B hV.1).mono hPhiU
  have hhigh : SA.HighLocksCompatible (tr.HonestBlocks H) (tr.projAC.state p i)
      (tr.time i) s B := by
    refine SA.highLocksCompatible_iff.2 fun l hl _ hls X hX hXr => ?_
    obtain ⟨q, hqi, D, hw, L, hL, hLr, hLD⟩ := SA.lock_provenance hr hpH i l hl
    obtain rfl : L = X := hr.coherent.1 hL hX (hLr.trans hXr.symm)
    have hqt : tr.time q ≤ sp.ts (s + 1 : Nat) := hti ▸ hp.run.time_mono hqi.le
    rcases hw with ⟨CV', hop'⟩ | ⟨ell', hupd⟩
    · have hle : l.slot ≤ s + 1 := by
        obtain ⟨ell', A, _, hsl, _⟩ := hop'
        change sp.slot (tr.time q) = l.slot at hsl
        have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg q) (l.slot : Int)).mpr (by omega)
        exact_mod_cast (SA.ts_le_iff sp).mp (this.trans hqt)
      have hne : l.slot ≠ s + 1 := by
        intro he
        exact proposal_no_optimistic_of_run hp.run hp.noColl hf hpH hci hcall hti
          p hpH q hqi D CV' (he ▸ hop')
      have he : l.slot = s := by omega
      rw [he] at hop'
      rcases hp.optimistic_sources_compatible hpH hx hop' hop with h | h
      · exact Or.inl (hLD.trans h)
      · exact SA.anc_total hr.coherent hLD h
    · have ht : tr.time q = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
      have hle := (SA.ts_le_iff sp).mpr (show (s : Int) ≤ l.slot by omega)
      rw [hts] at hqt
      exfalso
      linarith
  refine optimistic_first_proposal_anc hS.run hf hx hop .refl hpH hci
    (SA.proposal_slot hti) hd ⟨hV.1, Or.inl hV⟩ ?_ hhigh
  intro v hv
  obtain ⟨hvs, hsend, D, hD, hDr, hBD, hacc⟩ := fastLock_writer hr hx (Or.inr hop) v hv
  have hFD := hFB.trans hBD
  refine SA.heldAtProposal_of_writer hr (hp.sync.syncAC hp.run (le_gbar g))
    (by linarith) le_rfl hx hpH hci hti hrs hvs hsend ⟨D, hD, hDr, hFD, ?_⟩
  rcases hacc with hg | ⟨q, hq, hqt⟩
  · exact Or.inl hg
  by_cases hg : SA.gbar g ≤ tr.time q
  · exact Or.inr (Or.inl ⟨q, hq, hg, hqt⟩)
  · obtain ⟨k, hki, hak, hkt⟩ := hS.catchUp.relay x hx q D hq (not_le.mp hg) p hpH i ell hci
      (by change _ ≤ tr.time i; rw [hti, hts]; linarith) hib hFD
    exact Or.inr (Or.inr ⟨k, hki, hak, by change tr.time k < _ at hkt ⊢; linarith⟩)

/-- The packed old-source interface of the proposal row ordering lemma. -/
private theorem proposal_high_row (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hti : tr.time i = sp.ts u) {v : Fin sp.n} (hv : v ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hki : k < i) (hs : tr.SignAt v k att)
    (hh : HZ tr H g + 1 ≤ att.h) :
    ∃ E O, Compose.IsHonestSource tr H E att.T ∧ OldSrc tr H g u O ∧
      Anc (tr.HonestBlocks H) E O := by
  obtain ⟨r, l, O, E, _, _, ho, ht, _, _, hE, hEO⟩ :=
    proposal_high_row_source_before hp hpH hci hcall hti hv hki hs hh
  exact ⟨E, O, hE, ⟨v, r, l, ho, ht⟩, hEO⟩

/-- Global high-origin comparability excludes contests at high justification heights. -/
private theorem no_high_contest (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) (i : Nat) :
    ¬ ((tr.state p i).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state p i).fg.hmax) := by
  have hU := honest_coherent hp
  have hreach := Compose.fg_reachable hp.run.toLocalRun hpH i
  have hsub : (tr.state p i).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨p, hpH, i, hX⟩
  have hret := height_scoped_retention sp ro proposer dg H tr g ΔF
    hp.run hp.healthy hp.noColl a hp.reset
  have hupper : ∀ {v₁ v₂ : Fin sp.n} {r₁ l₁ r₂ l₂ : Nat}
      {O₁ O₂ : SA.Blk sp.n (List (FG.Att sp.n))}, HighOrigin tr H g v₁ r₁ l₁ O₁ →
      HighOrigin tr H g v₂ r₂ l₂ O₂ → ∃ z ∈ H, ∃ m C, C ∈ (tr.state z m).fg.tree ∧
        Anc (tr.HonestBlocks H) O₁ C ∧ Anc (tr.HonestBlocks H) O₂ C := by
    intro v₁ v₂ r₁ l₁ r₂ l₂ O₁ O₂ ho₁ ho₂
    obtain ⟨-, -, -, -, -, -, -, -, -, hO₁⟩ := highOrigin_mem hp ho₁
    obtain ⟨-, -, -, -, -, -, -, -, -, hO₂⟩ := highOrigin_mem hp ho₂
    rcases hret.comparable v₁ r₁ l₁ O₁ v₂ r₂ l₂ O₂ ho₁ ho₂ with h | h
    · exact ⟨v₂, ho₂.1, r₂, O₂, hO₂, h, .refl⟩
    · exact ⟨v₁, ho₁.1, r₁, O₁, hO₁, .refl, h⟩
  have hnc : ¬ ((tr.state p i).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state p i).fg.hmax) := by
    rintro ⟨⟨hmj, C, hC, -, hCh, hJC⟩, hmax⟩
    obtain ⟨-, hJm, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -⟩ := Store.cache_invariants _ _ _ _ hreach
    obtain ⟨EJ, hEJ, hEJr, hEJB, hcase⟩ := Store.J_entry_of_reachable hreach hBj
    obtain rfl : EJ = (tr.state p i).fg.J := hU.1 (hsub hEJ) (hsub hJm) (hEJr.trans hBjJ)
    rcases hcase with hg | ⟨hJh, hJT⟩
    · exact hJC (hg ▸ (Store.accepted_tree _ _ _ _ hreach).2.2.2 C hC)
    have hJlt := Store.hj_lt_h hreach hBj
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ho₂, hJO⟩ :=
      left_entry_origin hp hpH hJm hJT (by omega) hEJB (by omega)
    obtain ⟨EC, hEC, hECC, hECh, hECT⟩ :=
      entry_at_height hreach hC (h := (tr.state p i).fg.hj) (by omega) (by omega)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ho₁, hECO⟩ :=
      left_entry_origin hp hpH hEC hECT (by omega) hECC (by omega)
    obtain ⟨z, hz, m, C', hC', hO₁C, hO₂C⟩ := hupper ho₁ ho₂
    have h₁ := hECO.trans hO₁C
    have h₂ := hJO.trans hO₂C
    have hEC' := mem_tree_of_anc hp hz h₁ hC'
    have hJ' := mem_tree_of_anc hp hz h₂ hC'
    have hσ₁ := σ_eq_run hp hpH hz hEC hEC'
    have hσ₂ := σ_eq_run hp hpH hz hJm hJ'
    have he := entry_root_eq hp hz hC' h₁ h₂
      (by rw [← hσ₁, ← hσ₂, hECh, hJh, hBjhj]) (by rw [← hσ₁]; exact hECT)
      (by rw [← hσ₂]; exact hJT)
    obtain rfl : EC = (tr.state p i).fg.J := hU.1 (hsub hEC) (hsub hJm) he
    exact hJC hECC
  exact hnc

/-- A held high origin is below the root or in the full viable tree at an active cut. -/
private theorem held_high_origin_viable (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {c : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt p c ℓ)
    {x : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (ht : sp.ts (j + 1 : Nat) ≤ tr.time c)
    (hBt : B ∈ ℓ.frame.tree) :
    B ∈ ℓ.frame.viableTree ℓ.frame.tree ∨ ℓ.frame.Anc B ℓ.frame.fcRoot := by
  have hU := honest_coherent hp
  have hreach := Compose.fg_reachable hp.run.toLocalRun hpH c
  have hsub : (tr.state p c).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨p, hpH, c, hX⟩
  have hfr := Compose.frame_of_projAC hp.run hpH hc
  have hBf : B ∈ (Node.frame (tr.state p c)).tree := hfr ▸ hBt
  have hBh := high_of_anc hp ho hpH hBf.1 .refl
  have hret := height_scoped_retention sp ro proposer dg H tr g ΔF
    hp.run hp.healthy hp.noColl a hp.reset
  have hcache := vote_state_caches hp c (fun k _ => retention_inv hp k) ho hpH ht
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt
    (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun hpH hc
  have hroot : Compatible (tr.HonestBlocks H) ℓ.frame.fcRoot B := by
    rw [hfr]
    change Compatible _ (tr.state p c).fg.fcRoot B
    unfold Store.fcRoot
    split_ifs with hchoose
    · by_cases hhigh : HZ tr H g + 1 ≤ (tr.state p c).fg.hj
      · exact hcache.2 hhigh
      · have hmax := (Store.cache_invariants _ _ _ _ hreach).2.2.2.2.1 B hBf.1
        have hJB : (tr.state p c).fg.Anc (tr.state p c).fg.J B := by
          by_contra hn
          exact hchoose.2 ⟨hchoose.1, B, hBf.1, hBf.2, by omega, hn⟩
        exact Or.inl (hJB.mono hsub)
    · exact hcache.1
  rcases hroot with hfB | hBfroot
  swap
  · exact Or.inr (SA.anc_tree_of_anc_U hU hΦ hΦU hBt hBfroot hΦ.fcRoot_mem)
  have hfB' := SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBt
  have hfBs : (tr.state p c).fg.Anc (tr.state p c).fg.fcRoot B := by
    rw [hfr] at hfB'
    exact hfB'.mono (fun _ h => h.1)
  have hdesc : ∃ C ∈ (tr.state p c).fg.tree, (tr.state p c).fg.Anc B C ∧
      (tr.state p c).fg.IsViable C := by
    by_cases hle : (tr.state p c).fg.headHeightFloor ≤ ((tr.state p c).fg.σ B.root).h
    · exact ⟨B, hBf.1, .refl, hle⟩
    have hfloor := lt_of_not_ge hle
    have hcon : ¬ (tr.state p c).fg.Contest := fun h => by
      unfold Store.headHeightFloor at hfloor
      simp only [h, ↓reduceIte] at hfloor
      exact no_high_contest hp hpH c ⟨h, by omega⟩
    have hfl : (tr.state p c).fg.headHeightFloor = (tr.state p c).fg.hmax - 1 := by
      unfold Store.headHeightFloor
      simp only [hcon, ↓reduceIte]
    rw [hfl] at hfloor
    obtain ⟨-, -, -, -, -, ⟨C, hC, hCh⟩, -⟩ := Store.cache_invariants _ _ _ _ hreach
    obtain ⟨E, hE, hEC, hEh, hET⟩ :=
      entry_at_height hreach hC (h := (tr.state p c).fg.hmax - 1) (by omega) (by omega)
    obtain ⟨_, _, _, _, v, _, _, _, _, _, r, _, l, O, hoO, hEO⟩ :=
      left_entry_origin hp hpH hE hET (by omega) hEC (by omega)
    have hcmp : Compatible (tr.HonestBlocks H) E B := by
      rcases hret.comparable v r l O x i j B hoO ho with h | h
      · exact Or.inl (hEO.trans h)
      · exact Anc.total hU hEO h
    have hBE : Anc (tr.HonestBlocks H) B E := by
      rcases hcmp with h | h
      · have := σ_h_le_of_anc hreach (anc_tree_of_anc hp hpH h hBf.1)
        omega
      · exact h
    refine ⟨C, hC, (anc_tree_of_anc hp hpH hBE hE).trans hEC, ?_⟩
    change (tr.state p c).fg.headHeightFloor ≤ _
    omega
  obtain ⟨C, hC, hBC, hvC⟩ := hdesc
  have hCf : C ∈ (Node.frame (tr.state p c)).tree := ⟨hC, hBf.2.trans hBC⟩
  have hCt : C ∈ ℓ.frame.tree := hfr ▸ hCf
  have hCv : C ∈ ℓ.frame.viableHeads := by
    rw [hfr]
    exact ⟨hC, hCf.2, hfBs.trans hBC, hvC⟩
  exact Or.inl ⟨hBt, hfB', C, hCt, hCv,
    SA.anc_tree_of_anc_U hU hΦ hΦU hBt (hBC.mono hsub) hCt⟩

/-- A block above every old source reaches the proposal's floor. Only high crossing
quorums matter: the reset seed already makes the block high. -/
private theorem proposal_floor_above_old (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ℓp : ACLabel (goldilocksNode sp ro)} (hci : tr.projAC.CallAt p i ℓp)
    (hcall : ℓp.call = .proposal) (hti : tr.time i = sp.ts u)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state p i).fg.tree)
    (hBold : ∀ O, OldSrc tr H g u O → Anc (tr.HonestBlocks H) O B) :
    (tr.state p i).fg.headHeightFloor ≤ ((tr.state p i).fg.σ B.root).h := by
  have hU := honest_coherent hp
  have hreach := Compose.fg_reachable hp.run.toLocalRun hpH i
  have hsub : (tr.state p i).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨p, hpH, i, hX⟩
  obtain ⟨v₀, r₀, l₀, O₀, ho₀, -, hr₀⟩ := reset_seed hp
  have hBh := high_of_anc hp ho₀ hpH hB
    (hBold O₀ ⟨v₀, r₀, l₀, ho₀, hr₀.trans_lt (reset_lt_ts hp hR)⟩)
  have hnc := no_high_contest hp hpH i
  by_contra hle
  have hfloor := lt_of_not_ge hle
  have hcon : ¬ (tr.state p i).fg.Contest := fun hcon => by
    unfold Store.headHeightFloor at hfloor
    simp only [hcon, ↓reduceIte] at hfloor
    exact hnc ⟨hcon, by omega⟩
  have hfl : (tr.state p i).fg.headHeightFloor = (tr.state p i).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    simp only [hcon, ↓reduceIte]
  rw [hfl] at hfloor
  obtain ⟨-, -, -, -, -, ⟨C, hC, hCh⟩, -⟩ := Store.cache_invariants _ _ _ _ hreach
  obtain ⟨E, hE, hEC, hEh, hET⟩ :=
    entry_at_height hreach hC (h := (tr.state p i).fg.hmax - 1) (by omega) (by omega)
  obtain ⟨W, hW, att, ha, v, hv, k, hki, hs, haT, _⟩ :=
    left_entry_origin hp hpH hE hET (by omega) hEC (by omega)
  obtain ⟨Es, hEs, hEsr, hEsh⟩ := signAt_entry hp.run hv hs
  have hEq : Es = E := hU.1 ⟨v, hv, k, hEs⟩ (hsub hE) (hEsr.trans haT)
  have hah : HZ tr H g + 1 ≤ att.h := by
    rw [← hEsh, hEq, σ_eq_run hp hv hpH (hEq ▸ hEs) hE, hEh]
    omega
  obtain ⟨D, O, hDs, hO, hDO⟩ := proposal_high_row hp hpH hci hcall hti hv hki hs hah
  obtain ⟨z, hz, m, -, -, hED, -, -⟩ :=
    Compose.honest_source_entry hp.run hp.noColl hDs (hsub hE) haT.symm
  have hEB := ((Anc.mono (T := tr.HonestBlocks H) (fun X hX => ⟨z, hz, m, hX⟩) hED).trans
    hDO).trans (hBold O hO)
  have := σ_h_le_of_anc hreach (anc_tree_of_anc hp hpH hEB hB)
  omega

/-! ### The proposal walk and fork-choice roots -/

/-- An optimistic prefix compares with an old high origin. Strictly earlier origin
labels use historical vote extension; equal labels use fast/optimistic compatibility. -/
theorem optimistic_prefix_compatible_old
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {r u : Nat}
    {D L O : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hop : SA.OptimisticLockAt tr.projAC p r (u - 1) D CV)
    (_hLu : L ∈ tr.HonestBlocks H) (hLD : Anc (tr.HonestBlocks H) L D)
    {x : Fin sp.n} {i j : Nat} (ho : HighOrigin tr H g x i j O)
    (_hOld : tr.time i < sp.ts u) (hj : j ≤ u - 1) :
    Compatible (tr.HonestBlocks H) L O := by
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hDO : Compatible (tr.HonestBlocks H) D O := by
    rcases hj.lt_or_eq with hj | rfl
    · apply SA.optimisticLock_compatible hrun (faulty_lt_half hp p) hpH hop
      intro z hz q e hv hs
      obtain ⟨ell, hc, he⟩ := hv
      have hvotes := (historical_activation_before hp (tr.time q) q le_rfl).2
      exact ((rawVoteAt_iff _ _ _).mp hvotes O j
        ((historicalTargets_iff O j).mpr ⟨x, i, ho⟩) z hz ell e ⟨hc, he⟩
        (by omega) le_rfl).1
    · obtain ⟨CV', hst⟩ := ho.2.2.1
      obtain ⟨_, C, hfl, hOC⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
      have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H
        (fun v => v.val) tr proposer ΔF (sp.ts (u - 1 : Nat)) (sp.ts (u - 1 + 1 : Nat) + sp.Δ)
        hp.run.toLocalRun (syncRun_of_gst hp.healthy.1 (le_ts_of_highOrigin hp ho))
      rcases SA.fastLock_same_slot hrun hpH (Or.inr hop) ho.1 hfl hsync
        (faulty_lt_half hp p) with hDC | hCD
      · exact SA.anc_total hrun.localRun.coherent hDC hOC
      · exact Or.inr (hOC.trans hCD)
  rcases hDO with hDO | hOD
  · exact Or.inl (hLD.trans hDO)
  · exact SA.anc_total hrun.localRun.coherent hLD hOD

/-- At proposal time, stored high locks can only come from an optimistic write of the
previous label. Regular updates are too late and current-label optimism is excluded. -/
private theorem proposal_stored_locks_compatible_old
    (hp : ResetPremises tr H proposer dg g ΔF a)
    (_hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (_hR : drainTime sp a ≤ sp.ts u)
    {i : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hti : tr.time i = sp.ts u) :
    ∀ O, OldSrc tr H g u O →
      SA.HighLocksCompatible (tr.HonestBlocks H) (tr.projAC.state p i)
        (tr.time i) (u - 1) O := by
  intro O hO
  obtain ⟨x, q, j, ho, hOld⟩ := hO
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun.localRun
  have hΔ := sp.toParams.hΔ
  rw [SA.highLocksCompatible_iff]
  intro l hl _ hlabel L hL hLr
  obtain ⟨r, hri, D, hwrite, L', hL', hL'r, hLD⟩ := SA.lock_provenance hr hP.1 i l hl
  obtain rfl : L' = L := hr.coherent.1 hL' hL (hL'r.trans hLr.symm)
  have hrt : tr.time r ≤ sp.ts u := hti ▸ hp.run.time_mono hri.le
  rcases hwrite with ⟨CV, hop⟩ | ⟨ell, hupd⟩
  · have hle : l.slot ≤ u := by
      have ht := ts_le_of_fastLock hp (Or.inr hop)
      have := (SA.ts_le_iff sp).mp (ht.trans hrt)
      exact_mod_cast this
    have hne : l.slot ≠ u := by
      intro heq
      exact proposal_no_optimistic hp hP.1 hci hcall hti p hP.1 r hri D CV (heq ▸ hop)
    have heq : l.slot = u - 1 := by omega
    rw [heq] at hop
    exact optimistic_prefix_compatible_old hp hP.1 hop hL hLD ho hOld
      (by have := label_lt_of_old hp ho hOld; omega)
  · have ht : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
    have hslots : sp.ts u ≤ sp.ts (l.slot + 1 : Nat) :=
      (SA.ts_le_iff sp).mpr (by omega)
    have hsucc : sp.ts (l.slot + 1 : Nat) = sp.ts l.slot + 4 * sp.Δ := by
      simp only [SA.SAParams.ts]; push_cast; ring
    rw [hsucc] at hslots
    linarith

/-- A non-current read-point lock sits below a raw source of the receiver. Its source
precedes the receiving cast, not necessarily the proposal. -/
theorem vote_old_lock_source_before (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u)
    (hR : drainTime sp a ≤ sp.ts u)
    {l : SA.Lock} (hl : l ∈ e.readPoint.locks) (hne : l.slot ≠ u)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k)
    {L : SA.Blk sp.n (List (FG.Att sp.n))}
    (hL : L ∈ ell.frame.tree) (hLr : L.root = l.block) :
    ∃ r D, r < j ∧ cleanLabel sp a + sp.k + 2 ≤ l.slot ∧ l.slot < u ∧
      ((∃ CV, SA.FastLockAt tr.projAC y r l.slot D CV) ∨
        SA.SlowLockAt tr.projAC y r l.slot D) ∧
      Anc (tr.HonestBlocks H) (ell.frame.viableAncestor L) D := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc.1
  have hslot : sp.slot (tr.time j) = u := ((SA.castAt_spec hr hy hc).2.1).symm.trans hes
  have hclean : cleanLabel sp a + sp.k + 2 ≤ l.slot := by
    rw [drainTime_eq] at hR
    have := (SA.ts_le_iff sp).mp hR
    rw [hslot] at hlive
    rw [cleanLabel_eq]
    omega
  have hu : 0 < u := by
    rw [drainTime_eq] at hR
    have := (SA.ts_le_iff sp).mp hR
    omega
  obtain ⟨l₀, hl₀, hs, B, hB, hBr, L', hL', hL'r, hLB⟩ :=
    SA.readPoint_locks_below_stored hr hy hc
      (by change 0 < sp.slot (tr.time j); rw [hslot]; exact hu) l hl
      (by change l.slot ≠ sp.slot (tr.time j); simpa only [hslot] using hne)
  obtain rfl : L' = L := hPhi.coherent.1 hL' hL (hL'r.trans hLr.symm)
  obtain ⟨r, hrj, D, hraw, X, hX, hXr, hXD⟩ :
      ∃ r < j, ∃ D,
        ((∃ CV, SA.FastLockAt tr.projAC y r l₀.slot D CV) ∨
          SA.SlowLockAt tr.projAC y r l₀.slot D) ∧
        ∃ X ∈ tr.HonestBlocks H, X.root = l₀.block ∧ Anc (tr.HonestBlocks H) X D := by
    cases hf : l₀.fast with
    | false =>
      obtain ⟨r, hrj, D, hslow, hX⟩ := SA.slow_lock_provenance hr hy j l₀ hl₀ hf
      exact ⟨r, hrj, D, Or.inr hslow, hX⟩
    | true =>
      obtain ⟨r, hrj, D, CV, hfast, hX⟩ := SA.fast_lock_provenance hr hy j l₀ hl₀ hf
      exact ⟨r, hrj, D, Or.inl ⟨CV, hfast⟩, hX⟩
  obtain rfl : X = B := hr.coherent.1 hX (hPhiU hB) (hXr.trans hBr.symm)
  have hle : l₀.slot ≤ u := by
    have ht : sp.ts l₀.slot ≤ tr.time r := by
      rcases hraw with ⟨CV, hf⟩ | ⟨ellX, C, hupd, _⟩
      · exact ts_le_of_fastLock hp hf
      · have ht : tr.time r = sp.ts l₀.slot + 6 * sp.Δ := hupd.2.2.1
        have hΔ : 0 < sp.Δ := sp.toParams.hΔ
        linarith
    have htj : l₀.slot ≤ sp.slot (tr.time j) := by
      exact_mod_cast (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg j) l₀.slot).mp
        (ht.trans (hp.run.time_mono hrj.le))
    omega
  refine ⟨r, D, hrj, hclean, by omega, hs ▸ hraw, ?_⟩
  exact (Anc.mono hPhiU ((SA.anc_viableAncestor ell.frame L').trans hLB)).trans hXD

section Support

variable (hp : ResetPremises tr H proposer dg g ΔF a)
  (hc : CatchRun tr H g (2 * sp.Δ))
  {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
  (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
  {i : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
  {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
  (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
  (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
  (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root)
  {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
  {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
  (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = u)
  (hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' →
    e'.msg.slot = u → e'.msg.head = P.root)

include hp hc hP hR hci hcall hd hti hPQ hy hcy hes hE in
set_option linter.unusedSectionVars false in
/-- Non-current live locks move back below the proposal parent. -/
theorem vote_old_live_lock_below_parent
    {l : SA.Lock} (hl : l ∈ e.readPoint.locks) (hne : l.slot ≠ u)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k)
    {L : SA.Blk sp.n (List (FG.Att sp.n))}
    (hL : L ∈ ℓy.frame.tree) (hLr : L.root = l.block) :
    Anc (tr.HonestBlocks H) (ℓy.frame.viableAncestor L) d.head := by
  obtain ⟨r, D, hrj, hclean, hlu, hsource, hLD⟩ :=
    vote_old_lock_source_before hp hy hcy hes hR hl hne hlive hL hLr
  apply hLD.trans
  by_cases hgap : l.slot + 2 ≤ u
  · exact clean_source_proposal_parent_before hp hc hy hP.1 hsource hclean hgap hR
      hci hcall hd hti
  have he : u = l.slot + 1 := by omega
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have htj := (Compose.cast_head_fcRoot hr hy hcy).2
  rw [hes, he] at htj
  have hrt := hp.run.time_mono hrj.le
  have hts : sp.ts (l.slot + 1 : Nat) = sp.ts l.slot + 4 * sp.Δ := by
    simp only [SA.SAParams.ts]; push_cast; ring
  have hΔ := sp.toParams.hΔ
  rcases hsource with ⟨CV, hfast⟩ | ⟨ellX, C, hupd, _⟩
  · rcases hfast with ⟨ellX, C, hupd, _⟩ | hop
    · have ht : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
      rw [hts] at htj
      change tr.time j ≤ _ at htj
      exfalso
      linarith
    · exact clean_optimistic_proposal_parent hp hc hy hP.1 hop hclean (he ▸ hR)
        hci hcall hd (he ▸ hti)
  · have ht : tr.time r = sp.ts l.slot + 6 * sp.Δ := hupd.2.2.1
    rw [hts] at htj
    change tr.time j ≤ _ at htj
    exfalso
    linarith

end Support

/-- Every old source is below the proposal's duty head. Relay and high-origin viability put
the source on the walk; earlier-label votes or the same-label optimistic quorum favor its
chain. -/
private theorem reset_proposal_passes (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (_hPQ : P.parent = some d.head.root) :
    ∀ O, OldSrc tr H g u O → Anc (tr.HonestBlocks H) O d.head := by
  intro O hO
  have hpH := hP.1
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hret := height_scoped_retention sp ro proposer dg H tr g ΔF
    hp.run hp.healthy hp.noColl a hp.reset
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hpH hci
  obtain ⟨x, r, l, ho, hrt⟩ := hO
  have hlu := label_lt_of_old hp ho hrt
  obtain ⟨s, rfl⟩ : ∃ s, u = s + 1 := ⟨u - 1, by omega⟩
  have hslot := SA.proposal_slot (tr := tr.projAC) hti
  have hai : a ≤ tr.time i := by rw [hti]; exact (reset_lt_ts hp hR).le
  rcases proposal_holds_old hp hpH hai hci hcall hd hti ⟨x, r, l, ho, hrt⟩ with hOt | hOF
  swap
  · obtain ⟨hstart, hsQ⟩ := Compose.acProposal_start_anc_head hΦ hd
    exact hOF.trans (Anc.mono hΦU ((hΦ.rooted.2 _ hstart).trans hsQ))
  have hV := held_high_origin_viable hp hpH hci ho
    (by rw [hti]; exact (SA.ts_le_iff sp).2 (by omega)) hOt
  have hFO := (hΦ.rooted.2 O hOt).mono hΦU
  have hhigh : SA.HighLocksCompatible (tr.HonestBlocks H) (tr.projAC.state p i)
      (tr.time i) s O := by
    exact proposal_stored_locks_compatible_old hp hc hP hR hci hcall hti O
      ⟨x, r, l, ho, hrt⟩
  have hcut : cutZ sp.toParams g ≤ sp.ts s :=
    (cutZ_le_ts_of_highOrigin hp ho).trans ((SA.ts_le_iff sp).2 (by omega))
  have hgs : g ≤ sp.ts s := by
    have := le_gbar g
    have := lt_cutZ sp g
    linarith
  have hrs : ∀ k ≤ i, tr.projAC.RestartAt p k → tr.projAC.time k < sp.ts s := by
    intro k _ hk
    have := restart_le hp hpH (Compose.projAC_restartAt.1 hk)
    have hcZ := cutZ_eq sp g
    have htlt : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) < cutZ sp.toParams g := by
      rw [hcZ]
      exact (SA.ts_lt_iff sp).2 (by omega)
    exact lt_of_le_of_lt this (htlt.trans_le hcut)
  have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF g (sp.ts s + 2 * sp.Δ) hp.run.toLocalRun (syncRun_of_gst hp.healthy.1 le_rfl)
  have hheld : ∀ z ∈ H, ∀ v : SA.Vote sp.n, v.slot = s →
      (∃ k, tr.projAC.SendOrAdmit z k v ∧ sp.ts s ≤ tr.projAC.time k ∧
        tr.projAC.time k < sp.ts s + 2 * sp.Δ) →
      (∃ B ∈ tr.HonestBlocks H, B.root = v.head ∧ Anc (tr.HonestBlocks H) O B ∧
        (B.root = sp.genesisRoot ∨ ∃ k, tr.projAC.AcceptAt z k B ∧
          tr.projAC.time k < sp.ts s + 2 * sp.Δ)) →
      SA.HeldAtProposal (tr.projAC.state p i) ℓp.frame s v := by
    rintro z hz v hvs hsend ⟨B, hB, hBr, hOB, hacc⟩
    apply SA.heldAtProposal_of_writer hr hsync hgs le_rfl hz hpH hci hti hrs hvs hsend
    refine ⟨B, hB, hBr, hFO.trans hOB, ?_⟩
    rcases hacc with hg | ⟨k, hk, hkt⟩
    · exact Or.inl hg
    refine Or.inr (Or.inl ⟨k, hk, ?_, hkt⟩)
    have := (cutZ_lt_of_anc hp ho hz (acceptAt_mem hp hz hk) hOB).1
    have := lt_cutZ sp g
    have := le_gbar g
    change g ≤ tr.time k
    linarith
  by_cases hls : l < s
  · have hvotes : ∀ z ∈ H, ∀ k e, SA.VoteAt tr.projAC z k e → e.msg.slot = s →
        SA.VoteExtends (tr.HonestBlocks H) e.msg O := by
      rintro z hz k e ⟨ℓ, hcz, he⟩ hes
      exact (hret.votes x r l O ho z hz k ℓ e ⟨hcz, he⟩ (by omega)).1
    refine SA.batch_proposal hrun (faulty_lt_half hp p) (half_committee hp hcut) hvotes hpH hci
      hslot hd ⟨hOt, hV⟩ ?_ hhigh
    intro z hz k e hv hes
    obtain ⟨B, hB, hBr, hOB⟩ := hvotes z hz k e hv hes
    obtain ⟨ℓz, hcz, he⟩ := hv
    obtain ⟨⟨B', hB't, hB'r, -⟩, hkt⟩ := Compose.cast_head_fcRoot hr hz ⟨hcz, he⟩
    have hEq : B' = B := hU.1 ((SA.frameIn_of_callAt hr hz hcz).2 hB't) hB (hB'r.trans hBr.symm)
    rw [hEq] at hB't
    rw [hes] at hkt
    refine hheld z hz e.msg hes ⟨k, ⟨ℓz, hcz, Or.inl ⟨e, he, rfl⟩⟩, ?_, by linarith⟩
      ⟨B, hB, hBr, hOB, ?_⟩
    · exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) s).2
        (by have := (SA.castAt_spec hr hz ⟨hcz, he⟩).2.1; omega)
    · rcases Compose.frame_anc_accepted hr hz k ℓz hcz B hB't B .refl with hg | ⟨k', hkk, hk⟩
      · exact Or.inl hg
      · exact Or.inr ⟨k', hk, by have := hr.time_mono hkk; linarith⟩
  · have hls : l = s := by omega
    obtain ⟨ℓx, D, CV, hcx, hfl, _, _, _, hOD, _⟩ := highOrigin_mem hp ho
    rw [hls] at hfl
    rcases hfl with ⟨ℓ', C, ⟨_, _, ht, _⟩, _⟩ | hop
    · have ht' : tr.time r = sp.ts s + 6 * sp.Δ := ht
      have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      linarith
    refine optimistic_first_proposal_anc hrun (faulty_lt_half hp p) ho.1 hop
      (hOD.mono (SA.frameIn_of_callAt hr ho.1 hcx).2) hpH hci hslot hd ⟨hOt, hV⟩ ?_ hhigh
    intro v hv
    obtain ⟨hvs, hsend, B, hB, hBr, hDB, hacc⟩ := fastLock_writer hr ho.1 (Or.inr hop) v hv
    exact hheld x ho.1 v hvs hsend ⟨B, hB, hBr,
      (hOD.mono (SA.frameIn_of_callAt hr ho.1 hcx).2).trans hDB, hacc⟩

/-- A crossing below an origin written before a serving proposal is below its duty parent.
The explicit timestamp preserves the provenance needed by bounded report consumers. -/
theorem crossing_below_proposal_parent
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root)
    {x : Fin sp.n} {r l : Nat} {X O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hrt : tr.time r < sp.ts u)
    (hXO : Anc (tr.HonestBlocks H) X O) : Anc (tr.HonestBlocks H) X d.head :=
  hXO.trans (reset_proposal_passes hp hc hP hR hci hcall hd hti hPQ O ⟨x, r, l, ho, hrt⟩)

/-- The `6Δ` report cutoff precedes the serving slot at least two labels later. -/
theorem crossing_below_serving_parent
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u e : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ell) (hcall : ell.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ell.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root)
    {x : Fin sp.n} {r l q : Nat} {X O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hrq : tr.time r ≤ tr.time q)
    (hq : tr.time q ≤ sp.ts e + 6 * sp.Δ) (heu : e + 2 ≤ u)
    (hXO : Anc (tr.HonestBlocks H) X O) : Anc (tr.HonestBlocks H) X d.head := by
  apply crossing_below_proposal_parent hp hc hP hR hci hcall hd hti hPQ ho ?_ hXO
  have hslots := (SA.ts_le_iff sp).mpr (show (e : Int) + 2 ≤ u by omega)
  have hΔ := sp.toParams.hΔ
  simp only [SA.SAParams.ts] at hslots hq ⊢
  nlinarith

/-- The proposal root is genesis or below an old source. High `J` has a crossing row signed
before the proposal. Low `J` is below the held reset seed by the root's no-contest condition. -/
private theorem reset_proposal_fcRoot (hp : ResetPremises tr H proposer dg g ΔF a)
    (_hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (_hPQ : P.parent = some d.head.root) :
    ℓp.frame.fcRoot.root = sp.genesisRoot ∨
      ∃ O, OldSrc tr H g u O ∧ Anc (tr.HonestBlocks H) ℓp.frame.fcRoot O := by
  have hpH := hP.1
  have hU := honest_coherent hp
  have hr := Compose.fg_reachable hp.run.toLocalRun hpH i
  have hsub : (tr.state p i).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨p, hpH, i, hX⟩
  have hfr := Compose.frame_of_projAC hp.run hpH hci
  obtain ⟨hFm, hJm, hFJ, ⟨B, hBm, hBJ, hBhj⟩, hmax, -⟩ :=
    Store.cache_invariants _ _ _ _ hr
  obtain ⟨E, hEm, hEr, hEB, hcase⟩ := Store.J_entry_of_reachable hr hBm
  obtain rfl : E = (tr.state p i).fg.J := hU.1 (hsub hEm) (hsub hJm) (hEr.trans hBJ)
  have hroot : (tr.state p i).fg.fcRoot = (tr.state p i).fg.J ∨
      (tr.state p i).fg.fcRoot = (tr.state p i).fg.F := by
    unfold Store.fcRoot
    split_ifs <;> simp
  rcases hcase with hg | ⟨hJh, hJT⟩
  · left
    rw [hfr]
    rcases hroot with h | h
    · exact congrArg (·.root) (h.trans hg)
    · have hJF := (Store.accepted_tree _ _ _ _ hr).2.2.2 _ hFm
      rw [← hg] at hJF
      have he := Anc.antisymm hU (hFJ.mono hsub) (hJF.mono hsub)
      exact congrArg (·.root) (h.trans (he.trans hg))
  by_cases hh : HZ tr H g + 1 ≤ (tr.state p i).fg.hj
  · obtain ⟨W, hW, att, ha, v, hv, k', hki, hs, haT, -⟩ :=
      left_entry_origin hp hpH hJm hJT (by omega) hEB
        (by have := Store.hj_lt_h hr hBm; omega)
    obtain ⟨E', hE', hE'r, hE'h⟩ := signAt_entry hp.run hv hs
    obtain rfl : E' = (tr.state p i).fg.J :=
      hU.1 ⟨v, hv, k', hE'⟩ (hsub hJm) (hE'r.trans haT)
    have hah : HZ tr H g + 1 ≤ att.h := by
      rw [← hE'h, σ_eq_run hp hv hpH hE' hJm, hJh, hBhj]
      exact hh
    obtain ⟨D, O, hDs, hO, hDO⟩ := proposal_high_row hp hpH hci hcall hti hv hki hs hah
    obtain ⟨z, hz, r, -, -, hJD, -, -⟩ :=
      Compose.honest_source_entry hp.run hp.noColl hDs (hsub hJm) haT.symm
    have hJO := (Anc.mono (T := tr.HonestBlocks H) (fun X hX => ⟨z, hz, r, hX⟩) hJD).trans hDO
    right
    refine ⟨O, hO, ?_⟩
    rw [hfr]
    change Anc _ (tr.state p i).fg.fcRoot O
    rcases hroot with h | h
    · rw [h]; exact hJO
    · rw [h]; exact (hFJ.mono hsub).trans hJO
  obtain ⟨v, r, l, O, ho, hl, hrt⟩ := reset_seed hp
  have hO : OldSrc tr H g u O := ⟨v, r, l, ho, hrt.trans_lt (reset_lt_ts hp hR)⟩
  have hFO : Anc (tr.HonestBlocks H) (tr.state p i).fg.F O := by
    rcases finalized_compatible_high_origin hp hpH
      (by rw [hti]; exact (reset_lt_ts hp hR).le) ho with h | h
    · exact h
    · have hOJ := h.trans (hFJ.mono hsub)
      have := high_of_anc hp ho hpH hJm hOJ
      rw [hJh, hBhj] at this
      omega
  right
  refine ⟨O, hO, ?_⟩
  rw [hfr]
  change Anc _ (tr.state p i).fg.fcRoot O
  unfold Store.fcRoot
  split_ifs with hchoose
  · have hOt : O ∈ ℓp.frame.tree := by
      rcases proposal_holds_old hp hpH (by rw [hti]; exact (reset_lt_ts hp hR).le)
        hci hcall hd hti hO with h | h
      · exact h
      · rw [hfr] at h
        have := high_of_anc hp ho hpH hJm (h.trans (hFJ.mono hsub))
        rw [hJh, hBhj] at this
        omega
    rw [hfr] at hOt
    have hOh := high_of_anc hp ho hpH hOt.1 .refl
    have hOm := hmax O hOt.1
    have hJO : (tr.state p i).fg.Anc (tr.state p i).fg.J O := by
      by_contra hn
      exact hchoose.2 ⟨hchoose.1, O, hOt.1, hOt.2, by omega, hn⟩
    exact hJO.mono hsub
  · exact hFO

section SourceVotes

variable (hp : ResetPremises tr H proposer dg g ΔF a)
  (hc : CatchRun tr H g (2 * sp.Δ))
  {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
  (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
  {i : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
  {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
  (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
  (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
  (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root)
  {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
  {ℓy : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
  (hcy : SA.CastAt tr.projAC y j ℓy e) (hes : e.msg.slot = u)
  (hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' →
    e'.msg.slot = u → e'.msg.head = P.root)

set_option linter.unusedSectionVars false in
include hp hc hP hR hci hcall hd hti hPQ hy hcy hes hE in
/-- The proposal anchor is supported when the receiving vote extends its actual raw
lock sources. Unlocking only moves the anchor back; the source writer remains the proposer.
The unused `hE` binder is retained to match `proposal_start_supported` exactly. -/
theorem proposal_start_supported_of_source_votes
    (hsources : ∀ r l B, r < i →
      ((∃ CV, SA.FastLockAt tr.projAC p r l B CV) ∨ SA.SlowLockAt tr.projAC p r l B) →
      cleanLabel sp a + sp.k + 2 ≤ l → l < u →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B) :
    Anc (tr.HonestBlocks H) d.start
      (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
        (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame u))
        (SA.mergedVoteView sp e.readPoint ℓy.frame u) ((u : Int) - 1)) := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hP.1 hci
  obtain ⟨hΨ, hΨU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hhead := SA.getHead_mem hΨ
    (T := ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame u))
    (fun _ h => h.1.1) e.readPoint (tr.time j)
    (SA.mergedVoteView sp e.readPoint ℓy.frame u) ((u : Int) - 1)
  have hheadr := (SA.castAt_spec hr hy hcy).2.2.2
  rw [hes] at hheadr
  have extend : ∀ B, SA.VoteExtends (tr.HonestBlocks H) e.msg B →
      Anc (tr.HonestBlocks H) B
        (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
          (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame u))
          (SA.mergedVoteView sp e.readPoint ℓy.frame u) ((u : Int) - 1)) := by
    rintro B ⟨W, hW, hWr, hBW⟩
    obtain rfl := hr.coherent.1 hW (hΨU hhead) (hWr.trans hheadr)
    exact hBW
  obtain ⟨A₁, hA₁, hstart, -⟩ := acProposal_walk hd
  rw [hstart]
  rcases anchor_mem ℓp.frame A₁ (tr.time i) with hlock | hroot
  swap
  · rw [Set.mem_singleton_iff.1 hroot]
    rcases reset_proposal_fcRoot hp hc hP hR hci hcall hd hti hPQ with hg | ⟨O, hO, hfO⟩
    · exact Compose.honest_genesis_root_anc hp.run hr.coherent (hΦU hΦ.fcRoot_mem) hg
        (hΨU hhead)
    · obtain ⟨x, r, l, ho, hOld⟩ := hO
      apply hfO.trans (extend O ?_)
      exact ((rawVoteAt_iff _ _ _).mp
        (historical_activation_before hp (tr.time j) j le_rfl).2 O l
        ((historicalTargets_iff O l).mpr ⟨x, r, ho⟩) y hy ℓy e hcy
        (by rw [hes]; exact label_lt_of_old hp ho hOld) le_rfl).1
  obtain ⟨hL, l', ⟨l, hl, B, hB, hBr, hlive, rfl⟩, hlL⟩ := hlock
  have heq := hΦ.coherent.1 hL (SA.viableAncestor_anc hΦ hB).1 hlL.symm
  rw [heq]
  rw [hA₁] at hl
  obtain ⟨l₁, hl₁, hs, _, B₁, hB₁, hB₁r, B', hB', hB'r, hBB₁⟩ :=
    ((SA.locks_move_back sp) _ ℓp.frame _ (tr.time i) hΦ).2.2 _ _ l hl
  obtain rfl : B' = B := hΦ.coherent.1 hB' hB (hB'r.trans hBr.symm)
  have hlo : cleanLabel sp a + sp.k + 2 ≤ l₁.slot := by
    rw [drainTime_eq] at hR
    have h := (SA.ts_le_iff sp).mp hR
    have hslot : sp.slot (tr.time i) = u := by
      rw [hti]
      exact SA.slot_of_mem sp u le_rfl (by
        have hΔ : 0 < sp.Δ := sp.toParams.hΔ
        simp only [SA.SAParams.ts]; push_cast; linarith)
    rw [hslot] at hlive
    rw [cleanLabel_eq]
    omega
  obtain ⟨r, hri, D, horig, L, hLU, hLr, hLD⟩ :
      ∃ r < i, ∃ D,
        ((∃ CV, SA.FastLockAt tr.projAC p r l₁.slot D CV) ∨
          SA.SlowLockAt tr.projAC p r l₁.slot D) ∧
        ∃ L ∈ tr.HonestBlocks H, L.root = l₁.block ∧ Anc (tr.HonestBlocks H) L D := by
    cases hf : l₁.fast with
    | false =>
      obtain ⟨r, hri, D, hsl, hL⟩ := SA.slow_lock_provenance hr hP.1 i l₁ hl₁ hf
      exact ⟨r, hri, D, Or.inr hsl, hL⟩
    | true =>
      obtain ⟨r, hri, D, CV, hfl, hL⟩ := SA.fast_lock_provenance hr hP.1 i l₁ hl₁ hf
      exact ⟨r, hri, D, Or.inl ⟨CV, hfl⟩, hL⟩
  obtain rfl : L = B₁ := hr.coherent.1 hLU (hΦU hB₁) (hLr.trans hB₁r.symm)
  have hlt : l₁.slot < u := by
    obtain ⟨r', hri', D', hw, _⟩ := SA.lock_provenance hr hP.1 i l₁ hl₁
    have hrt : tr.time r' ≤ sp.ts u := hti ▸ hp.run.time_mono hri'.le
    rcases hw with ⟨CV, hop⟩ | ⟨ell, hupd⟩
    · have hle := (SA.ts_le_iff sp).mp ((ts_le_of_fastLock hp (Or.inr hop)).trans hrt)
      have hne : l₁.slot ≠ u := fun he =>
        proposal_no_optimistic hp hP.1 hci hcall hti p hP.1 r' hri' D' CV (he ▸ hop)
      omega
    · have ht : tr.time r' = sp.ts l₁.slot + 6 * sp.Δ := hupd.2.2.1
      have hΔ : 0 < sp.Δ := sp.toParams.hΔ
      have ht' : sp.ts l₁.slot < sp.ts u := by linarith
      exact_mod_cast (SA.ts_lt_iff sp).mp ht'
  exact (Anc.mono hΦU ((SA.anc_viableAncestor ℓp.frame B').trans hBB₁)).trans
    (hLD.trans (extend D (hsources r l₁.slot D hri horig hlo hlt)))

include hp hc hP hR hci hcall hd hti hPQ hy hcy hes hE in
/-- The proposal start is supported through clean raw-source vote induction. -/
theorem proposal_start_supported :
    Anc (tr.HonestBlocks H) d.start
      (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
        (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame u))
        (SA.mergedVoteView sp e.readPoint ℓy.frame u) ((u : Int) - 1)) := by
  apply proposal_start_supported_of_source_votes hp hc hP hR hci hcall hd hti hPQ hy hcy hes hE
  intro r l B hri horig hclean hlu
  exact clean_source_votes_before hp hc (max (tr.time i) (tr.time j)) hP.1 horig hclean
    ((hp.run.time_mono hri.le).trans (le_max_left _ _)) j (le_max_right _ _)
    y hy ℓy e hcy (by rw [hes]; exact hlu)

end SourceVotes

/-- Above every old source, the proposal walk consists of viable heads. The reset seed makes
the suffix high; a higher floor would produce a high crossing below an old source, contradicting
its height. Together with `fc_root ⪯ start ⪯ D`, this proves viability. -/
private theorem reset_suffix_viable (hp : ResetPremises tr H proposer dg g ΔF a)
    (_hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (_hPQ : P.parent = some d.head.root)
    (D : SA.Blk sp.n (List (FG.Att sp.n))) (hDt : D ∈ ℓp.frame.tree)
    (hsD : ℓp.frame.Anc d.start D) (hDold : ∀ O, OldSrc tr H g u O → Anc (tr.HonestBlocks H) O D) :
    ∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads := by
  intro X hDX _
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hP.1 hci
  have hXt : X ∈ ℓp.frame.tree := mem_of_anc_left hDX hDt
  have hDXU := hDX.mono hΦU
  obtain ⟨A₁, -, hstart, -⟩ := acProposal_walk hd
  have hfX : ℓp.frame.Anc ℓp.frame.fcRoot X := by
    rw [hstart] at hsD
    exact ((SA.fcRoot_anc_getAnchor hΦ A₁ (tr.time i)).trans hsD).trans hDX
  rw [Compose.frame_of_projAC hp.run hP.1 hci] at hXt hfX ⊢
  obtain ⟨hXs, hFX⟩ := hXt
  refine ⟨hXs, hFX, hfX.mono (fun _ h => h.1), ?_⟩
  exact proposal_floor_above_old hp hP.1 hR hci hcall hti hXs
    (fun O hO => (hDold O hO).trans hDXU)

/-- A reset seed above the reader's finalized cache has reached every post-drain call. -/
private theorem seed_held (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {c : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y c ℓ) (ht : a + sp.Δ < tr.time c)
    {v : Fin sp.n} {r l : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g v r l O) (hrt : tr.time r ≤ a)
    (hFO : Anc (tr.HonestBlocks H) ℓ.frame.F O) : O ∈ ℓ.frame.tree := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨-, -, -, -, -, -, -, -, -, hOr⟩ := highOrigin_mem hp ho
  rcases tree_accepted hp.run.toLocalRun ho.1 hOr with hg | ⟨k, hkr, hak⟩
  · exact False.elim ((cutZ_lt_of_anc hp ho ho.1 hOr .refl).2 (congrArg (·.root) hg))
  have hOk : O ∈ (tr.state v (k + 1)).fg.tree := by
    rw [tr.state_succ_of_call hak,
      (Store.tree_grows _ _ _ _ (Compose.fg_reachable hp.run.toLocalRun ho.1 k)).1
        O _ (hp.run.toLocalRun.cutLaw v ho.1 k _ hak).2.1]
    exact Set.mem_insert _ _
  have hkt : cutZ sp.toParams g < tr.time k := by
    by_contra hn
    obtain ⟨m, hm⟩ := exists_firstCutAfter hp.run hp.healthy ho.1
    have hkm : k < m := by
      by_contra h
      have := hp.run.time_mono (not_lt.1 h)
      linarith [hm.2]
    have hOm := Compose.tree_mono hp.run.toLocalRun ho.1 (by omega : k + 1 ≤ m) hOk
    have hh := h_le_HZ_of_firstCut ho.1 hm hp hOm
    rw [← σ_eq_run hp ho.1 ho.1 hOr hOm] at hh
    have hhigh := ho.2.2.2
    omega
  obtain ⟨ℓk, hck, hblock, hsame⟩ := Compose.accept_next hp.run.toLocalRun ho.1 hak
  have hkA : tr.projAC.AcceptAt v (k + 1) O := ⟨ℓk, Compose.projAC_callAt.2 hck, hblock⟩
  have hka : tr.time k ≤ a := (hp.run.time_mono hkr.le).trans hrt
  have hrestart : ∀ j ≤ c, tr.projAC.RestartAt y j → tr.projAC.time j ≤ tr.time k := by
    intro j _ hj
    have hjt := restart_le hp hy (Compose.projAC_restartAt.1 hj)
    have hz : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) < cutZ sp.toParams g := by
      rw [cutZ_eq sp g]
      exact (SA.ts_lt_iff sp).2 (by omega)
    change tr.time j ≤ tr.time k
    linarith
  have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF g (tr.time k) hp.run.toLocalRun (syncRun_of_gst hp.healthy.1 le_rfl)
  obtain ⟨j, hjc, haj, -⟩ := hsync.2 v ho.1 (k + 1) O hkA
    (by change g ≤ tr.time (k + 1); rw [hsame]
        linarith [lt_cutZ sp g, le_gbar g, sp.toParams.hΔ])
    (by change tr.time (k + 1) ≤ tr.time k; exact hsame.le) y hy c ℓ hc
    (by
      have hd := deadline_le_restarts hrestart (tr.projAC.time (k + 1))
      change tr.projAC.deadline y c (tr.time (k + 1)) ≤
        max (tr.time (k + 1)) (tr.time k) + sp.Δ at hd
      change tr.projAC.deadline y c (tr.time (k + 1)) ≤ tr.time c
      rw [hsame] at hd ⊢
      rw [max_self] at hd
      linarith) hFO
  exact SA.mem_tree_of_acceptAt sp hr hy haj hjc hc hFO

/-- The vote root is genesis or below an old source (hence satisfies the original disjunction).
An actual crossing row's origin label is strictly below the vote's label
(`row_origin_label_lt`); the low-`J` case relays the reset seed. -/
private theorem reset_vote_root_source (hp : ResetPremises tr H proposer dg g ΔF a)
    {u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = u) :
    ℓy.frame.fcRoot.root = sp.genesisRoot ∨
      (∃ O, OldSrc tr H g u O ∧ Anc (tr.HonestBlocks H) ℓy.frame.fcRoot O) := by
  have hU := honest_coherent hp
  have hrun := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hr := Compose.fg_reachable hp.run.toLocalRun hy j
  have hsub : (tr.state y j).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, j, hX⟩
  have hfr := Compose.frame_of_projAC hp.run hy hcy.1
  have htupper : tr.time j ≤ sp.ts u + sp.Δ := by
    have ht := (Compose.cast_head_fcRoot hrun hy hcy).2
    rw [hes] at ht
    exact ht
  have htlow : sp.ts u ≤ tr.time j := by
    have hs := (SA.castAt_spec hrun hy hcy).2.1
    change e.msg.slot = sp.slot (tr.time j) at hs
    exact (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg j) u).2 (by omega)
  obtain ⟨hFm, hJm, hFJ, ⟨B, hBm, hBJ, hBhj⟩, hmax, -⟩ :=
    Store.cache_invariants _ _ _ _ hr
  obtain ⟨E, hEm, hEr, hEB, hcase⟩ := Store.J_entry_of_reachable hr hBm
  obtain rfl : E = (tr.state y j).fg.J := hU.1 (hsub hEm) (hsub hJm) (hEr.trans hBJ)
  have hroot : (tr.state y j).fg.fcRoot = (tr.state y j).fg.J ∨
      (tr.state y j).fg.fcRoot = (tr.state y j).fg.F := by
    unfold Store.fcRoot
    split_ifs <;> simp
  rcases hcase with hg | ⟨hJh, hJT⟩
  · left
    rw [hfr]
    rcases hroot with h | h
    · exact congrArg (·.root) (h.trans hg)
    · have hJF := (Store.accepted_tree _ _ _ _ hr).2.2.2 _ hFm
      rw [← hg] at hJF
      have he := Anc.antisymm hU (hFJ.mono hsub) (hJF.mono hsub)
      exact congrArg (·.root) (h.trans (he.trans hg))
  right
  by_cases hh : HZ tr H g + 1 ≤ (tr.state y j).fg.hj
  · obtain ⟨W, hW, att, ha, v, hv, d, hdj, hs, haT, r, hrd, l, O, ho, hJO⟩ :=
      left_entry_origin hp hy hJm hJT (by omega) hEB
        (by have := Store.hj_lt_h hr hBm; omega)
    have hlu : l < u := hes ▸ row_origin_label_lt hp hy hcy hW ha hv hs hdj hrd ho
    obtain ⟨ℓw, D, CV, hcw, hfl, -⟩ := highOrigin_mem hp ho
    have hrt := fastLock_time_lt hp hfl hlu
      ((hp.run.time_mono (by omega : r ≤ j)).trans htupper)
    refine ⟨O, ⟨v, r, l, ho, hrt⟩, ?_⟩
    rw [hfr]
    change Anc _ (tr.state y j).fg.fcRoot O
    rcases hroot with h | h
    · rw [h]; exact hJO
    · rw [h]; exact (hFJ.mono hsub).trans hJO
  obtain ⟨v, r, l, O, ho, hl, hrt⟩ := reset_seed hp
  have hO : OldSrc tr H g u O := ⟨v, r, l, ho, hrt.trans_lt (reset_lt_ts hp hR)⟩
  have hFO : Anc (tr.HonestBlocks H) (tr.state y j).fg.F O := by
    rcases finalized_compatible_high_origin hp hy
      ((reset_lt_ts hp hR).le.trans htlow) ho with h | h
    · exact h
    · have := high_of_anc hp ho hy hJm (h.trans (hFJ.mono hsub))
      rw [hJh, hBhj] at this
      omega
  refine ⟨O, hO, ?_⟩
  rw [hfr]
  change Anc _ (tr.state y j).fg.fcRoot O
  unfold Store.fcRoot
  split_ifs with hchoose
  · have hat : a + sp.Δ < tr.time j := by
      have ha0 : 0 ≤ a := by
        linarith [cutZ_lt_reset hp.run hp.healthy hp.reset, lt_cutZ sp g,
          SA.gbar_nonneg g, sp.toParams.hΔ]
      have hat : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
        have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
        omega
      rw [drainTime_eq] at hR
      have hgap : sp.ts ((sp.slot a : Int) + 1) + sp.Δ ≤
          sp.ts (sp.slot a + 2 * sp.k + 5 : Nat) := by
        simp only [SAParams.ts]; push_cast
        nlinarith [sp.toParams.hΔ, sp.two_le_k]
      linarith
    have hFO' : Anc (tr.HonestBlocks H) ℓy.frame.F O := by rw [hfr]; exact hFO
    have hOt := seed_held hp hy hcy.1 hat ho hrt hFO'
    rw [hfr] at hOt
    have hOh := high_of_anc hp ho hy hOt.1 .refl
    have hOm := hmax O hOt.1
    have hJO : (tr.state y j).fg.Anc (tr.state y j).fg.J O := by
      by_contra hn
      exact hchoose.2 ⟨hchoose.1, O, hOt.1, hOt.2, by omega, hn⟩
    exact hJO.mono hsub
  · exact hFO

/-- Any bound on all pre-slot high origins also bounds the post-drain voter root. -/
theorem reset_vote_root_below_bound (hp : ResetPremises tr H proposer dg g ΔF a)
    {u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : P ∈ tr.HonestBlocks H)
    (hbound : ∀ x r b B, HighOrigin tr H g x r b B → tr.time r < sp.ts u →
      Anc (tr.HonestBlocks H) B P)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y j ell e)
    (hs : e.msg.slot = u) : Anc (tr.HonestBlocks H) ell.frame.fcRoot P := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  rcases reset_vote_root_source hp hR hy hc hs with hg | ⟨B, ⟨x, r, b, ho, ht⟩, hroot⟩
  · obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc.1
    exact Compose.honest_genesis_root_anc hp.run hr.coherent (hPhiU hPhi.fcRoot_mem) hg hP
  · exact hroot.trans (hbound x r b B ho ht)

private theorem reset_vote_fcRoot (hp : ResetPremises tr H proposer dg g ΔF a)
    (_hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y j ell e)
    (hs : e.msg.slot = u)
    (_hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = u →
      e'.msg.head = P.root) :
    ell.frame.fcRoot.root = sp.genesisRoot ∨
      (∃ O, OldSrc tr H g u O ∧ Anc (tr.HonestBlocks H) ell.frame.fcRoot O) ∨
      Anc (tr.HonestBlocks H) ell.frame.fcRoot P :=
  (reset_vote_root_source hp hR hy hc hs).imp_right Or.inl

/-! ### The anchors -/

/-- **A voter's anchor is below `D`, or on `P`'s chain above `D`**: for a block `D` above every
old source and below `Q = P.parent`, at an honest slot-`u` vote whose earlier honest slot-`u`
votes are `P`. A live lock of slot `u` sits below an optimistic selection with an honest
supporter among the earlier votes, so below `P`; one of another slot has its viable ancestor
below the proposal parent by the explicit source-service supplier; `fc_root` by
`reset_vote_fcRoot`. -/
private theorem reset_vote_anchor (hp : ResetPremises tr H proposer dg g ΔF a)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
    (hPQ : P.parent = some Q.root) (hQU : Q ∈ tr.HonestBlocks H)
    (hDQ : Anc (tr.HonestBlocks H) D Q) (hDU : D ∈ tr.HonestBlocks H)
    (hDold : ∀ O, OldSrc tr H g u O → Anc (tr.HonestBlocks H) O D)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = u)
    (hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = u →
      e'.msg.head = P.root)
    (hlocks : ∀ l ∈ e.readPoint.locks, l.slot ≠ u →
      sp.slot (tr.time j) ≤ l.slot + sp.k →
      ∀ L ∈ ℓy.frame.tree, L.root = l.block →
        Anc (tr.HonestBlocks H) (ℓy.frame.viableAncestor L) Q) :
    Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) D ∨
      (Anc (tr.HonestBlocks H) D (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) ∧
        Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) P ∧
        P ∈ tr.HonestBlocks H) := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hrun'.localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨hpH, -, -, hPp, -, -⟩ := id hP
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hs0 : 0 < u := by
    have h := hR
    rw [drainTime_eq] at h
    have := (SA.ts_le_iff sp).1 h
    omega
  have hslj : e.msg.slot = sp.slot (tr.time j) := (SA.castAt_spec hr hy hcy).2.1
  have htj : tr.time j ≤ sp.ts u + sp.Δ := hes ▸ (Compose.cast_head_fcRoot hr hy hcy).2
  have htR : drainTime sp a ≤ tr.time j :=
    hR.trans ((SA.ts_le_iff_le_slot sp (hr.time_nonneg j) u).2 (by
      change (u : Int) ≤ sp.slot (tr.time j); rw [← hslj, hes]))
  have hDP : ∀ hPU : P ∈ tr.HonestBlocks H, Anc (tr.HonestBlocks H) D P := fun hPU =>
    hDQ.trans (Relation.ReflTransGen.single ⟨hQU, hPU, hPQ⟩)
  have hat := anchor_tree hΦ e.readPoint (tr.time j)
  have haS := anchor_mem ℓy.frame e.readPoint (tr.time j)
  generalize SA.getAnchor sp e.readPoint ℓy.frame (tr.time j) = an at hat haS ⊢
  rcases haS with ⟨-, l', hl', hl'r⟩ | haf
  swap
  · -- `fc_root`
    rw [Set.mem_singleton_iff.1 haf]
    have hfU := hΦU hΦ.fcRoot_mem
    rcases reset_vote_fcRoot hp hc ⟨hpH, hP.2⟩ hR hy hcy hes hE with hg | ⟨O, hO, hfO⟩ | hfP
    · exact Or.inl (Compose.honest_genesis_root_anc hrun hU hfU hg hDU)
    · exact Or.inl (hfO.trans (hDold O hO))
    · have hPU := mem_of_anc_right hfP hfU
      rcases Anc.total hU hfP (hDP hPU) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hfP, hPU⟩
  -- a live lock block: the viable ancestor of the block of a read-point lock
  obtain ⟨l, hl, B, hB, hBr, hlive, rfl⟩ := hl'
  obtain rfl : an = ℓy.frame.viableAncestor B :=
    hΦ.coherent.1 hat (SA.viableAncestor_anc hΦ hB).1 hl'r.symm
  have haB : Anc (tr.HonestBlocks H) (ℓy.frame.viableAncestor B) B :=
    Anc.mono hΦU (SA.anc_viableAncestor _ B)
  by_cases hls : l.slot = u
  · -- a lock of slot `u`: below an optimistic selection with an honest earlier supporter
    obtain ⟨Φ', A', D', -, hΦ'U, -, h34, hpool, -, L, hLU, hLr, hLD'⟩ :=
      SA.lock_origin_readPoint hrun' hy hcy l hl (by rw [hes, hls]; omega)
    obtain rfl : L = B := hU.1 hLU (hΦU hB) (hLr.trans hBr.symm)
    have hf := faulty_lt_half hp y
    obtain ⟨x, ⟨v, hv, rfl, R, hRt, hRr, hDR⟩, hxH⟩ :=
      Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
        (t := SA.optimisticVoters sp A' Φ' l.slot D') (by omega)
    have hvH : v.val ∈ H := not_not.1 hxH
    obtain ⟨hvs, j', hj', e', hv', rfl⟩ := hpool v hv hvH
    have hRP : R = P := eq_proposal hrun hnc hpH hPp (hΦ'U hRt)
      (hRr.trans (hE _ hvH j' hj' e' hv' (hvs.trans hls)))
    rw [hRP] at hRt hDR
    have hPU : P ∈ tr.HonestBlocks H := hΦ'U hRt
    have haP := haB.trans (hLD'.trans (Anc.mono hΦ'U hDR))
    rcases Anc.total hU haP (hDP hPU) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, haP, hPU⟩
  · have haQ := hlocks l hl hls hlive B hB hBr
    rcases Anc.total hU haQ hDQ with h | h
    · exact Or.inl h
    · have hPU : P ∈ tr.HonestBlocks H := by
        have hacc := Compose.proposal_accepted hrun hnc hpH hPp
        refine ⟨p, hpH, k + 1, ?_⟩
        rw [tr.state_succ_of_call hacc,
          (Store.tree_grows _ _ _ _ (Compose.fg_reachable hrun.toLocalRun hpH _)).1 P _
            (hrun.toLocalRun.cutLaw p hpH _ _ hacc).2.1]
        exact Set.mem_insert _ _
      exact Or.inr ⟨h, haQ.trans (Relation.ReflTransGen.single ⟨hQU, hPU, hPQ⟩), hPU⟩

/-- A held block extending every pre-slot origin reaches the voter's height floor. -/
theorem reset_vote_floor_above_old
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat} (hR : drainTime sp a ≤ sp.ts u)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ (tr.state y j).fg.tree)
    (hBold : ∀ x r l O, HighOrigin tr H g x r l O → tr.time r < sp.ts u →
      Anc (tr.HonestBlocks H) O B) :
    (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ B.root).h := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy j
  obtain ⟨v₀, r₀, l₀, O₀, ho₀, -, hr₀⟩ := reset_seed hp
  have hBh := high_of_anc hp ho₀ hy hB
    (hBold v₀ r₀ l₀ O₀ ho₀ (hr₀.trans_lt (reset_lt_ts hp hR)))
  have hnc := no_high_contest hp hy j
  by_contra hle
  have hfloor := lt_of_not_ge hle
  have hcon : ¬ (tr.state y j).fg.Contest := fun hcon => by
    unfold Store.headHeightFloor at hfloor
    simp only [hcon, ↓reduceIte] at hfloor
    exact hnc ⟨hcon, by omega⟩
  have hfl : (tr.state y j).fg.headHeightFloor = (tr.state y j).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    simp only [hcon, ↓reduceIte]
  rw [hfl] at hfloor
  obtain ⟨-, -, -, -, -, ⟨C, hC, hCh⟩, -⟩ := Store.cache_invariants _ _ _ _ hreach
  obtain ⟨E, hE, hEC, hEh, hET⟩ :=
    entry_at_height hreach hC (h := (tr.state y j).fg.hmax - 1) (by omega) (by omega)
  obtain ⟨W, hW, att, ha, v, hv, d, hdj, hs, -, r, hrd, l, O, ho, hEO⟩ :=
    left_entry_origin hp hy hE hET (by omega) hEC (by omega)
  have hlu : l < u := hes ▸ row_origin_label_lt hp hy hc hW ha hv hs hdj hrd ho
  obtain ⟨-, D, CV, -, hf, -⟩ := highOrigin_mem hp ho
  have hrt : tr.time r < sp.ts u := fastLock_time_lt hp hf hlu
    ((hp.run.time_mono (by omega)).trans (hes ▸ (Compose.cast_head_fcRoot hr hy hc).2))
  have hEB := hEO.trans (hBold v r l O ho hrt)
  have := σ_h_le_of_anc hreach (anc_tree_of_anc hp hy hEB hB)
  omega

/-- Before the first disagreeing vote, the voter root is below the actual proposal. -/
theorem reset_vote_root_below_proposal
    (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {elly : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j elly e)
    (hes : e.msg.slot = u)
    (hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = u →
      e'.msg.head = P.root) : Anc (tr.HonestBlocks H) elly.frame.fcRoot P := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hP.1 hci
  obtain ⟨hPsi, hPsiU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hQU := hPhiU (mem_of_anc_left hsQ hst)
  have hacc := Compose.proposal_accepted hp.run hp.noColl hP.1 hP.2.2.2.1
  have hPU : P ∈ tr.HonestBlocks H := by
    refine ⟨p, hP.1, k + 1, ?_⟩
    rw [tr.state_succ_of_call hacc,
      (Store.tree_grows _ _ _ _ (Compose.fg_reachable hp.run.toLocalRun hP.1 _)).1 P _
        (hp.run.toLocalRun.cutLaw p hP.1 _ _ hacc).2.1]
    exact Set.mem_insert _ _
  rcases reset_vote_fcRoot hp hc hP hR hy hcy hes hE with hg | ⟨O, hO, hroot⟩ | hroot
  · exact Compose.honest_genesis_root_anc hp.run hr.coherent (hPsiU hPsi.fcRoot_mem) hg hPU
  · exact hroot.trans ((reset_proposal_passes hp hc hP hR hci hcall hd hti hPQ O hO).trans
      (.single ⟨hQU, hPU, hPQ⟩))
  · exact hroot

/-- **The pivot after the drain** (open: through the four residual steps above). -/
theorem reset_pivot (hp : ResetPremises tr H proposer dg g ΔF a) (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)}
    {pay : Payload sp.n} (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ℓp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hPQ : P.parent = some d.head.root) :
    ∃ D, ℓp.frame.Anc d.start D ∧ ℓp.frame.Anc D d.head ∧
      (∀ X, ℓp.frame.Anc D X → ℓp.frame.Anc X d.head → X ∈ ℓp.frame.viableHeads) ∧
      ∀ y ∈ H, ∀ j ℓy e, SA.CastAt tr.projAC y j ℓy e → e.msg.slot = u →
        (∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = u →
          e'.msg.head = P.root) →
        ∃ X, (X = P ∨ (ℓp.frame.Anc D X ∧ ℓp.frame.Anc X d.head)) ∧
          ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j)) X ∧
          ℓy.frame.Anc X (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
            (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame u))
            (SA.mergedVoteView sp e.readPoint ℓy.frame u) ((u : Int) - 1)) := by
  have hrun := hp.run
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hp.noColl
  have hr := hrun'.localRun
  have hU : Coherent (tr.HonestBlocks H) := hr.coherent
  have hret := height_scoped_retention sp ro proposer dg H tr g ΔF
    hp.run hp.healthy hp.noColl a hp.reset
  have hpH : p ∈ H := hP.1
  obtain ⟨hΦp, hΦpU⟩ := SA.frameIn_of_callAt hr hpH hci
  -- the proposal walk, from its start to `Q`
  obtain ⟨hstart, hsQ⟩ := Compose.acProposal_start_anc_head hΦp hd
  have hQt : d.head ∈ ℓp.frame.tree := mem_of_anc_left hsQ hstart
  have hpass := reset_proposal_passes hp hc hP hR hci hcall hd hti hPQ
  -- `D`: the deepest of the start and the old sources on the proposal walk
  obtain ⟨D, hD⟩ := SA.exists_deepest hΦp (S := {X | X ∈ ℓp.frame.tree ∧
      ℓp.frame.Anc d.start X ∧ ℓp.frame.Anc X d.head ∧ (X = d.start ∨ OldSrc tr H g u X)})
    (fun X hX => hX.1) ⟨d.start, hstart, .refl, hsQ, Or.inl rfl⟩
  obtain ⟨hDt, hsD, hDQ, hDk⟩ := (SA.deepest_mem hD).1
  have hmax := SA.anc_deepest hΦp (fun X hX => hX.1)
    (fun X hX Y hY => Anc.total hΦp.coherent hX.2.2.1 hY.2.2.1) hD
  have hDold : ∀ O, OldSrc tr H g u O → Anc (tr.HonestBlocks H) O D := by
    intro O hO
    have hOQ := hpass O hO
    rcases Anc.total hU hOQ (Anc.mono hΦpU hsQ) with h | h
    · exact h.trans (Anc.mono hΦpU hsD)
    have hOt := mem_between hU hΦp hΦpU hstart hQt h hOQ
    exact Anc.mono hΦpU (hmax O ⟨hOt, SA.anc_tree_of_anc_U hU hΦp hΦpU hstart h hOt,
      SA.anc_tree_of_anc_U hU hΦp hΦpU hOt hOQ hQt, Or.inr hO⟩)
  refine ⟨D, hsD, hDQ,
    reset_suffix_viable hp hc hP hR hci hcall hd hti hPQ D hDt hsD hDold,
    fun y hy j ℓy e hcy hes hE => ?_⟩
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hcy.1
  have hhead := (SA.castAt_spec hr hy hcy).2.2.2
  rw [hes] at hhead
  have hat := anchor_tree hΦ e.readPoint (tr.time j)
  have hah : ℓy.frame.Anc (SA.getAnchor sp e.readPoint ℓy.frame (tr.time j))
      (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
        (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame u))
        (SA.mergedVoteView sp e.readPoint ℓy.frame u) ((u : Int) - 1)) :=
    SA.anc_ghost (fun B hB => hB.1.1) _ hat
  have hht := mem_of_anc_left hah hat
  -- The vote's head extends `D`: direct start support, or HR.4 (R3).
  have hDh : Anc (tr.HonestBlocks H) D (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
      (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame u))
      (SA.mergedVoteView sp e.readPoint ℓy.frame u) ((u : Int) - 1)) := by
    rcases hDk with rfl | ⟨x, i', j', ho, hti'⟩
    · exact proposal_start_supported hp hc hP hR hci hcall hd hti hPQ hy hcy hes hE
    obtain ⟨Hd, hHd, hHdr, hDHd⟩ :=
      (hret.votes x i' j' D ho y hy j ℓy e hcy (by rw [hes]; exact label_lt_of_old hp ho hti')).1
    rwa [hU.1 hHd (hΦU hht) (hHdr.trans hhead)] at hDHd
  rcases reset_vote_anchor hp hc hP hR hPQ (hΦpU hQt) (Anc.mono hΦpU hDQ) (hΦpU hDt)
      hDold hy hcy hes hE (fun l hl hne hlive L hL hLr =>
        vote_old_live_lock_below_parent hp hc hP hR hci hcall hd hti hPQ hy hcy hes hE
          hl hne hlive hL hLr) with haD | ⟨hDa, haP, hPU⟩
  · have hDt' := mem_between hU hΦ hΦU hat hht haD hDh
    exact ⟨D, Or.inr ⟨.refl, hDQ⟩, SA.anc_tree_of_anc_U hU hΦ hΦU hat haD hDt',
      SA.anc_tree_of_anc_U hU hΦ hΦU hDt' hDh hht⟩
  by_cases haPe : SA.getAnchor sp e.readPoint ℓy.frame (tr.time j) = P
  · exact ⟨P, Or.inl rfl, haPe ▸ .refl, haPe ▸ hah⟩
  have haQ := anc_parent hU haP haPe hPQ (hΦpU hQt)
  have hat' := mem_between hU hΦp hΦpU hDt hQt hDa haQ
  exact ⟨_, Or.inr ⟨SA.anc_tree_of_anc_U hU hΦp hΦpU hDt hDa hat',
    SA.anc_tree_of_anc_U hU hΦp hΦpU hat' haQ hQt⟩, .refl, hah⟩

end Consensus.Goldilocks.Healing

end

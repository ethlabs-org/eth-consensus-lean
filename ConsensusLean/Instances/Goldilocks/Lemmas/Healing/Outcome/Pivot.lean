module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
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

/-- **No honest optimistic check of slot `s` selects a block before the proposal**
(`Compose.proposal_no_optimistic` with `Healthy(g)`'s `2f < n`). -/
private theorem proposal_no_optimistic (hp : ResetPremises tr H proposer dg g ΔF a) {p : Fin sp.n}
    (hpH : p ∈ H) {s i : Nat}
    {ℓp : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt p i ℓp)
    (hcall : ℓp.call = .proposal)
    (hti : tr.time i = sp.ts s) :
    ∀ x ∈ H, ∀ k' < i, ∀ C CV, ¬ SA.OptimisticLockAt tr.projAC x k' s C CV := by
  intro z hz c hci C CV hO
  have hrun := hp.run
  have hnc := hp.noColl
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
  have hf := faulty_lt_half hp p
  have := Set.ncard_le_ncard hnoH (Set.toFinite _)
  omega

/-! ### Old sources -/

/-- **The old sources of slot `u`**: the HR.4 high origins written before `t_u` (the post-reset
counterpart of `Compose.pivot`'s old origins; their labels are below `u`). -/
private def OldSrc (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n)) (g : Time) (u : Nat)
    (O : SA.Blk sp.n (List (FG.Att sp.n))) : Prop :=
  ∃ (x : Fin sp.n) (i j : Nat), HighOrigin tr H g x i j O ∧ tr.time i < sp.ts u

/-- R2 also compares a pre-call finalized cache with an origin written later: compare at a
future honest tick, then use monotonicity of `F` backwards. -/
private theorem finalized_compatible_high_origin (hp : ResetPremises tr H proposer dg g ΔF a)
    {z : Fin sp.n} (hz : z ∈ H) {c : Nat} (hac : a ≤ tr.time c)
    {x : Fin sp.n} {i j : Nat} {O : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j O) :
    Compatible (tr.HonestBlocks H) (tr.state z c).fg.F O := by
  have hΔ := sp.toParams.hΔ
  have hga : SA.gbar g < a := by
    have := cutZ_lt_reset hp.run hp.healthy hp.reset
    have := lt_cutZ sp g
    linarith
  have hcτ := le_max_left (tr.time c) (tr.time i)
  have hiτ := le_max_right (tr.time c) (tr.time i)
  set τ := max (tr.time c) (tr.time i)
  have hτ0 : 0 ≤ τ := (hp.run.time_nonneg c).trans hcτ
  have hτT : τ < sp.ts ((sp.slot τ : Int) + 1) := not_le.1 fun h => by
    have := (SA.ts_le_iff_le_slot sp hτ0 _).1 h
    omega
  obtain ⟨k, q, hg⟩ := hp.run.tick_of_awake z hz _ (by linarith)
    ⟨4 * ((sp.slot τ : Int) + 1), by simp only [SA.SAParams.ts]; ring⟩
    (hp.healthy.2.1 z hz _ (by change SA.gbar g ≤ _; linarith))
  obtain ⟨hcall, ht⟩ := tick_first_cut hg
  have hck : c ≤ k := le_of_not_gt fun h => by
    have := hp.run.time_mono h.le
    linarith
  have hik : i ≤ k := le_of_not_gt fun h => by
    have := hp.run.time_mono h.le
    linarith
  have hcmp := ((height_scoped_retention sp ro proposer dg H tr g ΔF hp.run hp.healthy hp.noColl a
    hp.reset).caches z hz k ⟨_, hcall⟩ (by linarith) x i j O ho hik).1
  have hmono : Anc (tr.HonestBlocks H) (tr.state z c).fg.F (tr.post k).fg.F := by
    rw [← tr.state_succ_of_call hcall]
    exact run_F_mono hp.run.toLocalRun hz (by omega)
  rcases hcmp with h | h
  · exact Or.inl (hmono.trans h)
  · exact Anc.total (honest_coherent hp) hmono h

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

/-! ### Sources of the proposer's rows -/

/-- A high row signed before the proposal has an old high origin. The write cannot be an
optimistic check of the proposal's slot, and a regular write in that slot is later. -/
private theorem proposal_high_row (hp : ResetPremises tr H proposer dg g ΔF a)
    {p : Fin sp.n} (hpH : p ∈ H) {i u : Nat} {ℓp : ACLabel (goldilocksNode sp ro)}
    (hci : tr.projAC.CallAt p i ℓp) (hcall : ℓp.call = .proposal)
    (hti : tr.time i = sp.ts u) {v : Fin sp.n} (hv : v ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hki : k < i) (hs : tr.SignAt v k att)
    (hh : HZ tr H g + 1 ≤ att.h) :
    ∃ E O, Compose.IsHonestSource tr H E att.T ∧ OldSrc tr H g u O ∧
      Anc (tr.HonestBlocks H) E O := by
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
  refine ⟨E, O, Compose.isHonestSource_iff.2 ⟨v, hv, r, hE, hET.trans hEr⟩,
    ⟨v, r, l, ho, ?_⟩,
    hEO.mono (fun X hX => ⟨v, hv, r, hX⟩)⟩
  exact fastLock_time_lt hp hfl hlu (by have := sp.toParams.hΔ; linarith)

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
/-- OPEN: the proposal start has direct support at the actual vote head. -/
theorem proposal_start_supported :
    Anc (tr.HonestBlocks H) d.start
      (SA.getHead sp e.readPoint ℓy.frame (tr.time j)
        (ℓy.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓy.frame u))
        (SA.mergedVoteView sp e.readPoint ℓy.frame u) ((u : Int) - 1)) := by
  sorry

include hp hc hP hR hci hcall hd hti hPQ hy hcy hes hE in
/-- OPEN: non-current live locks move back below the proposal parent. -/
theorem vote_old_live_lock_below_parent
    {l : SA.Lock} (hl : l ∈ e.readPoint.locks) (hne : l.slot ≠ u)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k)
    {L : SA.Blk sp.n (List (FG.Att sp.n))}
    (hL : L ∈ ℓy.frame.tree) (hLr : L.root = l.block) :
    Anc (tr.HonestBlocks H) (ℓy.frame.viableAncestor L) d.head := by
  sorry

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
private theorem reset_vote_fcRoot (hp : ResetPremises tr H proposer dg g ΔF a)
    (_hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (_hP : ReadyProposal tr H proposer p k u P) (hR : drainTime sp a ≤ sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓy : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ℓy e)
    (hes : e.msg.slot = u)
    (_hE : ∀ x ∈ H, ∀ j' < j, ∀ e', SA.VoteAt tr.projAC x j' e' → e'.msg.slot = u →
      e'.msg.head = P.root) :
    ℓy.frame.fcRoot.root = sp.genesisRoot ∨
      (∃ O, OldSrc tr H g u O ∧ Anc (tr.HonestBlocks H) ℓy.frame.fcRoot O) ∨
      Anc (tr.HonestBlocks H) ℓy.frame.fcRoot P := by
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
  right; left
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

module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: HR.1, the conjuncts and the assembly

HR.1 over a Goldilocks run under `Healthy(g)` and `NoColl`, with `c_z = t_{slot(ḡ)+3}` and `H_z`
the greatest honest `Σ.h_max` after all events at `c_z`. Proved on paper (claims HR.1, status S),
one lemma per conjunct:
(a) an honest attestation signed at or before `c_z` has height `≤ Σ.h_max ≤ H_z` (the frontier only
rises; `Healthy(g)` gives a cut after `c_z`) (`signed_le_HZ`); from `c_z` on, `ac_to_fg` returns
the block of a live fast lock written after `ḡ` (A1.5 with `τ = ḡ` on the AC projection)
(`toFG_fastLock`);
(b) the chain of a block of state height `≥ H_z + 2` carries an honest attestation of height
`H_z + 1` (G0.2 (f): a chain leaves a height only with `q > f` attestations of it)
(`honest_row_of_height`); (c) at the reset `a_z`: `a_z > c_z` (`cutZ_lt_reset`), no honest high
attestation before it (`reset_le_of_high`), the frontier at the ticks at `a_z` is `≤ H_z + 1`
(`hmax_le_at_reset`: a higher one carries an honest attestation of height `H_z + 1` signed before
the tick, by the tick order), so the attestations at `a_z` are `≤ H_z + 1` (`signed_le_at_reset`),
and the namers of the high entries before `a_z − Δ` are the faulty validators, fewer than `q`
(`namers_lt_q`: an honest namer would
have signed a high attestation before `a_z`, the state of an entry being the same at every honest
node); the last clause is time arithmetic. The coherence of the honest blocks (for (c)'s namers) and
the honest-object facts of A1.5 come from `Compose.goldilocks_ac_projection`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-! ## The cut `c_z` and the frontier `H_z` -/

/-- At most one cut is the first cut after a time. -/
theorem FirstCutAfter.unique {N S L : Type} {tr : Trace N S L} {j j' : Nat} {t : Time}
    (h : FirstCutAfter tr j t) (h' : FirstCutAfter tr j' t) : j = j' := by
  rcases lt_trichotomy j j' with hlt | rfl | hlt
  · exact absurd (h'.1 j hlt) (not_le.2 h.2)
  · rfl
  · exact absurd (h.1 j' hlt) (not_le.2 h'.2)

section Frontier

variable {P : Params} {A : NodeAC P} {tr : RunTrace A} {H : Set (Fin P.n)} {g : Time}

/-- The `Σ.h_max` of an honest node after all events at `c_z` is at most `H_z`. -/
theorem hmax_le_HZ {y : Fin P.n} (hy : y ∈ H) {j : Nat} (hj : FirstCutAfter tr j (cutZ P g)) :
    (tr.state y j).fg.hmax ≤ HZ tr H g := by
  refine le_csSup (((Set.finite_range fun z => (tr.state z j).fg.hmax).subset ?_).bddAbove)
    ⟨y, hy, j, hj, rfl⟩
  rintro _ ⟨z, -, j', hj', rfl⟩
  obtain rfl := hj'.unique hj
  exact ⟨z, rfl⟩

end Frontier

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF : Time}

/-- Under `Healthy(g)` (an honest node awake from `ḡ` on, so the run goes on), some cut is the
first cut after `c_z`. -/
theorem exists_firstCutAfter (hrun : GoldilocksRun proposer dg H tr) (hh : tr.HealthyRun H ΔF g)
    {y : Fin sp.n} (hy : y ∈ H) : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g) := by
  classical
  have hle : gbar g ≤ cutZ sp.toParams g + 1 := by
    have := lt_cutZ sp g
    have := sp.toParams.hΔ
    linarith
  obtain ⟨i, -, hi⟩ := hrun.awake_in_horizon y hy _ (hh.2.1 y hy _ hle)
  have hex : ∃ i, cutZ sp.toParams g < tr.time i := ⟨i, by linarith⟩
  exact ⟨Nat.find hex, fun k hk => not_lt.1 (Nat.find_min hex hk), Nat.find_spec hex⟩

/-- `f < q` under `Healthy(g)`'s `f ≤ ⌊(n − 1)/3⌋`. -/
theorem faulty_lt_q (hh : tr.HealthyRun H ΔF g) : Hᶜ.ncard < sp.toParams.fg.q := by
  have h3 := hh.2.2
  have hn := sp.toParams.hn
  change Hᶜ.ncard < (2 * sp.toParams.n + 2) / 3
  omega

/-- The height pair an honest node signs names a block it holds, of that height. -/
theorem signAt_entry (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hs : tr.SignAt y k att) :
    ∃ E ∈ (tr.state y k).fg.tree, E.root = att.T ∧ ((tr.state y k).fg.σ E.root).h = att.h := by
  obtain ⟨src, hc⟩ := hs
  exact Store.exists_entry_of_createAtt (Compose.fg_reachable hrun.toLocalRun hy k)
    (hrun.cutLaw y hy k _ hc).1

/-- An honest signed attestation comes from an actual earlier report, with its full
entry/source witnesses. The report and signing have the same time and FG store. -/
theorem signAt_report_entry (hrun : GoldilocksRun proposer dg H tr) {v : Fin sp.n}
    (hv : v ∈ H) {k : Nat} {a : FG.Att sp.n} (hs : tr.SignAt v k a) :
    ∃ j, k = j + 1 ∧ tr.time j = tr.time k ∧
      ∃ ℓ C E, SA.ToFGAt tr.projAC v j ℓ C ∧
        C ∈ (tr.state v j).fg.tree ∧ E ∈ (tr.state v j).fg.tree ∧
        E.root = a.T ∧ (tr.state v j).fg.Anc E C ∧
        ((tr.state v j).fg.σ C.root).Th = E.root ∧
        ((tr.state v j).fg.σ E.root).Th = E.root ∧
        ((tr.state v j).fg.σ E.root).h = ((tr.state v j).fg.σ C.root).h ∧
        ((tr.state v j).fg.σ C.root).h = a.h := by
  obtain ⟨C, hc⟩ := hs
  obtain ⟨j, rfl, ℓ, hj, hcall, ht, hret, hfg⟩ := Compose.attest_source hrun.toLocalRun hv hc
  have hpc : tr.projAC.CallAt v j ℓ := Compose.projAC_callAt.2 hj
  have hC : C ∈ ℓ.frame.tree := by
    change (SA.acToFG sp _ _ _).2 = some C at hret
    unfold SA.acToFG at hret
    split_ifs at hret
    split at hret
    · cases hret
    · rename_i C' hC'
      split_ifs at hret
      cases hret
      exact (SA.deepest_mem hC').1.1.1
  have hCt : C ∈ (tr.state v j).fg.tree := by
    rw [(hrun.cutLaw v hv j _ hj).1] at hC
    exact hC.1
  have hsigned := (hrun.cutLaw v hv (j + 1) _ hc).1
  rw [hfg] at hsigned
  obtain ⟨E, hE, hEr, hEC, hTh, hET, hEh, hCa⟩ :=
    Store.entry_of_createAtt (Compose.fg_reachable hrun.toLocalRun hv j) hCt hsigned
  refine ⟨j, rfl, ht, ℓ, C, E, ⟨hpc, hcall, ?_⟩, hCt, hE, hEr, hEC, hTh, hET, hEh, hCa⟩
  rw [Compose.projAC_state hrun.toLocalRun hv j]
  exact hret

/-- A cache strictly ahead of a held target is backed by an actual earlier
honest report at a strictly higher height. No report at the reader is invented. -/
theorem cache_ahead_report (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < sp.toParams.fg.q)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {P X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X = (tr.state y i).fg.F ∨ X = (tr.state y i).fg.J)
    (hP : P ∈ (tr.state y i).fg.tree)
    (hPX : Anc (tr.HonestBlocks H) P X) (hne : P ≠ X) :
    ∃ v ∈ H, ∃ j < i, ∃ k < i, ∃ a : FG.Att sp.n, ∃ ℓ C,
      tr.SignAt v k a ∧ k = j + 1 ∧ tr.time j = tr.time k ∧ tr.time j ≤ tr.time i ∧
      SA.ToFGAt tr.projAC v j ℓ C ∧ a.T = X.root ∧
      X ∈ (tr.state v j).fg.tree ∧ Anc (tr.HonestBlocks H) X C ∧
      ((tr.state v j).fg.σ C.root).Th = X.root ∧
      ((tr.state v j).fg.σ C.root).h = ((tr.state y i).fg.σ X.root).h ∧
      ((tr.state y i).fg.σ P.root).h < ((tr.state y i).fg.σ X.root).h := by
  have hr := Compose.fg_reachable hrun.toLocalRun hy i
  have hU := Compose.honest_blocks_coherent hrun.toLocalRun hnc
  have hsub : (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fun _ h => ⟨y, hy, i, h⟩
  have hXt : X ∈ (tr.state y i).fg.tree := by
    rcases hX with rfl | rfl
    · exact (Goldilocks.Store.cache_invariants _ _ _ _ hr).1
    · exact (Goldilocks.Store.cache_invariants _ _ _ _ hr).2.1
  rcases Compose.cache_quorum hr X (hX.elim Or.inr Or.inl) with hg | ⟨q, hq, hrows⟩
  · have he := Compose.honest_eq_genesis hrun hU (hsub hXt) hg
    rw [he] at hPX
    rcases Relation.ReflTransGen.cases_tail hPX with heq | ⟨Y, _, hY⟩
    · exact False.elim (hne (heq.symm.trans he.symm))
    · exact absurd hY.2.2 (by simp [Params.genesisBlock])
  have hex : ∃ v ∈ q, v ∈ H := by
    by_contra h
    have hsubq : (↑q : Set (Fin sp.n)) ⊆ Hᶜ := fun v hv hvH => h ⟨v, hv, hvH⟩
    have hn := Set.ncard_le_ncard hsubq (Set.toFinite _)
    rw [Set.ncard_coe_finset] at hn
    exact (not_lt_of_ge (hq.trans hn)) hf
  obtain ⟨v, hvq, hv⟩ := hex
  obtain ⟨B, hB, a, ha, hav, haX⟩ := hrows v hvq
  have haH : a.val ∈ H := hav ▸ hv
  obtain ⟨m, hmi, _, k, hkm, hs⟩ := Compose.honest_row_signed_before hrun hnc hy hB ha haH
  obtain ⟨j, hkj, ht, ℓ, C, E, hto, hC, hE, hEr, hEC, hTh, hET, hEh, _⟩ :=
    signAt_report_entry hrun haH hs
  have hsubv : (tr.state a.val j).fg.tree ⊆ tr.HonestBlocks H := fun _ h => ⟨a.val, haH, j, h⟩
  have he : E = X := hU.1 (hsubv hE) (hsub hXt) (hEr.trans haX)
  subst E
  have hrv := Compose.fg_reachable hrun.toLocalRun haH j
  have hσ := Store.σ_eq_of_mem hr hrv hU.1 hsub hsubv hXt hE
  have hPX' := Compose.honest_held_anc hrun hnc haH hPX hE
  have hPv : P ∈ (tr.state a.val j).fg.tree := (Anc.mem hPX' hne).1
  have hσP := Store.σ_eq_of_mem hr hrv hU.1 hsub hsubv hP hPv
  have hlt : ((tr.state a.val j).fg.σ P.root).h < ((tr.state a.val j).fg.σ X.root).h := by
    obtain ⟨hle, heq⟩ := Compose.honest_held_height hrun hnc haH hPX'
    apply lt_of_le_of_ne hle
    intro hh
    have hentry := (heq hh.symm).symm.trans hET
    obtain ⟨⟨E, hE', hEr', hEP, _, _⟩, _⟩ :=
      Goldilocks.Store.entry_state_of_source _ _ _ _ hrv P hPv
    have he : E = X := hU.1 (hsubv hE') (hsubv hE) (hEr'.trans hentry)
    subst E
    exact hne (hPX'.antisymm (hU.mono hsubv) hEP)
  refine ⟨a.val, haH, j, by omega, k, by omega, a, ℓ, C, hs, hkj, ht,
    hrun.time_mono (by omega), hto, haX, hE, hEC.mono hsubv, hTh, ?_, ?_⟩
  · rw [hσ]
    exact hEh.symm
  · rw [hσP, hσ]
    exact hlt

/-- The height pair an honest node signs is at most its `Σ.h_max`. -/
theorem signAt_h_le (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {att : FG.Att sp.n} (hs : tr.SignAt y k att) : att.h ≤ (tr.state y k).fg.hmax := by
  obtain ⟨src, hc⟩ := hs
  exact Store.createAtt_h_le (Compose.fg_reachable hrun.toLocalRun hy k) (hrun.cutLaw y hy k _ hc).1

/-! ## HR.1 (a) -/

/-- An actual cut after `c_z` bounds every honest attestation signed at or before `c_z`,
without requiring healthy continuation of the run. -/
theorem signed_le_HZ_of_snapshot (hrun : GoldilocksRun proposer dg H tr)
    (hsnapshot : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g))
    {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {att : FG.Att sp.n} (hs : tr.SignAt y k att)
    (hk : tr.time k ≤ cutZ sp.toParams g) : att.h ≤ HZ tr H g := by
  obtain ⟨j, hj⟩ := hsnapshot
  have hkj : k ≤ j := by
    by_contra hc
    have := hrun.time_mono (le_of_not_ge hc)
    linarith [hj.2]
  exact (signAt_h_le hrun hy hs).trans ((hmax_mono hrun.toLocalRun hy hkj).trans (hmax_le_HZ hy hj))

/-- **HR.1 (a), first part.** An honest attestation signed at or before `c_z` has height `≤ H_z`. -/
theorem signed_le_HZ (hrun : GoldilocksRun proposer dg H tr) (hh : tr.HealthyRun H ΔF g)
    {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {att : FG.Att sp.n} (hs : tr.SignAt y k att)
    (hk : tr.time k ≤ cutZ sp.toParams g) : att.h ≤ HZ tr H g :=
  signed_le_HZ_of_snapshot hrun (exists_firstCutAfter hrun hh hy) hy hs hk

/-- **HR.1 (a), second part (A1.5 with `τ = ḡ`).** From `c_z` on, a block `C` that `ac_to_fg`
returns at an honest node is the block of one of its live fast locks, whose label has a fast-lock
write at that node after `ḡ`, on a descendant of `C`. -/
theorem toFG_fastLock (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} (hto : SA.ToFGAt tr.projAC x i ℓ C)
    (hi : cutZ sp.toParams g ≤ tr.time i) :
    ∃ l ∈ SA.liveLocks sp (tr.state x i).ac.locks ℓ.frame (tr.time i),
      l.fast = true ∧ l.block = C.root ∧
      ∃ i' < i, ∃ B CV, SA.FastLockAt tr.projAC x i' l.slot B CV ∧ gbar g < tr.time i' ∧
        Anc (tr.HonestBlocks H) C B := by
  have hacr := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  obtain ⟨hc, -, hC⟩ := hto
  obtain ⟨hCv, l, hl, hlb, hlf, hls⟩ := SA.toFG_candidate hC
  have hst := Compose.projAC_state hrun.toLocalRun hx i
  rw [hst] at hl
  refine ⟨l, hl, hlf, hlb, ?_⟩
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  obtain ⟨j, hj, B', CV', hfl, L, hL, hLr, hLB'⟩ :=
    SA.fast_lock_provenance hacr.localRun hx i l₀ (hst ▸ hl₀) hlf
  have hU := hacr.localRun.coherent
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hacr.localRun.frameLaw x hx i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1
  refine ⟨j, hj, B', CV', hfl, ?_, ?_⟩
  · -- the lock was written in a slot after `ḡ`'s
    have hg0 := gbar_nonneg g
    have hcz : (sp.slot (gbar g) : Int) + 3 ≤ sp.slot (tr.time i) := by
      have h := (SA.ts_le_iff_le_slot sp (hacr.localRun.time_nonneg i) _).1
        ((cutZ_eq sp g).symm.le.trans hi)
      push_cast at h
      exact h
    have h1 : sp.slot (gbar g) + 1 ≤ l₀.slot := by
      change sp.slot (tr.time i) ≤ l₀.slot + 2 at hls
      omega
    have hτ : gbar g < sp.ts (l₀.slot : Int) := by
      refine lt_of_lt_of_le (not_le.1 fun h => ?_)
        ((SA.ts_le_iff sp (a := (sp.slot (gbar g) : Int) + 1) (b := l₀.slot)).2 (by omega))
      have := ((SA.ts_le_iff_le_slot sp hg0) _).1 h
      omega
    rcases hfl with ⟨ℓ', C', ⟨-, -, ht, -⟩, -⟩ | ⟨ℓ', A', -, hs, -⟩
    · have ht' : tr.time j = sp.ts (l₀.slot : Int) + 6 * sp.Δ := ht
      rw [ht']
      have := sp.toParams.hΔ
      linarith
    · refine lt_of_lt_of_le hτ ?_
      rw [← hs]
      exact ((SA.ts_le_iff_le_slot sp (hacr.localRun.time_nonneg j)) _).2 le_rfl
  · -- `C` is the viable ancestor of the lock's block, which is `L`
    have hCt : C ∈ ℓ.frame.tree := hCv.1
    obtain ⟨hvat, hva⟩ := SA.viableAncestor_anc hΦ hB₀
    have hCe : C = ℓ.frame.viableAncestor B₀ := hU.1 (hΦU hCt) (hΦU hvat) hlb.symm
    have hLe : L = B₀ := hU.1 hL (hΦU hB₀) (hLr.trans hB₀r.symm)
    subst hCe hLe
    exact (Anc.mono hΦU hva).trans hLB'

/-! ## HR.1 (b) -/

/-- **HR.1 (b) (G0.2 (f)).** The chain of an honest accepted block of state height `≥ H_z + 2`
carries an honest attestation of height `H_z + 1`. -/
theorem honest_row_of_height (hrun : GoldilocksRun proposer dg H tr) (hh : tr.HealthyRun H ΔF g)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y i).fg.tree) (hXh : HZ tr H g + 2 ≤ ((tr.state y i).fg.σ X.root).h) :
    ∃ Y, (tr.state y i).fg.Anc Y X ∧ ∃ att ∈ Y.fgPayload, att.val ∈ H ∧ att.h = HZ tr H g + 1 :=
  Store.exists_honest_att_of_lt (Compose.fg_reachable hrun.toLocalRun hy i) (faulty_lt_q hh) hX _
    (by omega) (by omega)

/-! ## HR.1 (c) -/

/-- A reset is strictly after `c_z` whenever its frontier has an actual snapshot cut. -/
theorem cutZ_lt_reset_of_snapshot (hrun : GoldilocksRun proposer dg H tr)
    (hsnapshot : ∃ j, FirstCutAfter tr j (cutZ sp.toParams g)) {a : Time}
    (hR : IsReset tr H g a) : cutZ sp.toParams g < a := by
  obtain ⟨⟨y, hy, k, att, hs, hatt, rfl⟩, -⟩ := hR
  by_contra hc
  have := signed_le_HZ_of_snapshot hrun hsnapshot hy hs (not_lt.1 hc)
  omega

/-- **HR.1 (c), `a_z > c_z`.** -/
theorem cutZ_lt_reset (hrun : GoldilocksRun proposer dg H tr) (hh : tr.HealthyRun H ΔF g) {a : Time}
    (hR : IsReset tr H g a) : cutZ sp.toParams g < a := by
  obtain ⟨y, hy, _⟩ := hR.1
  exact cutZ_lt_reset_of_snapshot hrun (exists_firstCutAfter hrun hh hy) hR

/-- An honest attestation on a block that a node holds at its `fg_attest` cut was signed before the
reset when that cut is at or before the reset (it was signed before that cut's time), so its
height is at most `H_z`. -/
private theorem held_row_lt (hrun : GoldilocksRun proposer dg H tr) (hh : tr.HealthyRun H ΔF g)
    {a : Time} (hR : IsReset tr H g a) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {s : Option (FG.Att sp.n)}
    (hc : tr.CallAt y k (.fg (.attest C s))) (hk : tr.time k ≤ a)
    {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y k).fg.tree) :
    ((tr.state y k).fg.σ X.root).h < HZ tr H g + 2 := by
  by_contra hXh
  obtain ⟨Y, hYX, att, hatt, hattH, hatth⟩ :=
    honest_row_of_height hrun hh hy k hX (not_lt.1 hXh)
  have hY : Y ∈ (tr.state y k).fg.tree := by
    by_cases he : Y = X
    · exact he ▸ hX
    · exact (Anc.mem hYX he).1
  obtain ⟨j, hj, hjk⟩ := signed_before_attest hrun.toLocalRun hy hc hY hatt hattH
  have := hR.2 _ hattH j att hj hatth
  linarith

/-- **HR.1 (c), no honest high attestation before the reset.** -/
theorem reset_le_of_high (hrun : GoldilocksRun proposer dg H tr) (hh : tr.HealthyRun H ΔF g)
    {a : Time}
    (hR : IsReset tr H g a) {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {att : FG.Att sp.n}
    (hs : tr.SignAt y k att) (hatt : HZ tr H g + 1 ≤ att.h) : a ≤ tr.time k := by
  rcases hatt.lt_or_eq with hatt | hatt
  · by_contra hk
    obtain ⟨E, hE, -, hEh⟩ := signAt_entry hrun hy hs
    obtain ⟨src, hc⟩ := hs
    have := held_row_lt hrun hh hR hy hc (not_le.1 hk).le hE
    omega
  · exact hR.2 y hy k att hs hatt.symm

/-- **HR.1 (c), the frontier at the ticks at the reset is `≤ H_z + 1`.** -/
theorem hmax_le_at_reset (hrun : GoldilocksRun proposer dg H tr) (hh : tr.HealthyRun H ΔF g)
    {a : Time}
    (hR : IsReset tr H g a) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {src : SA.Blk sp.n (List (FG.Att sp.n))} {signed : Option (FG.Att sp.n)}
    (hc : tr.CallAt y k (.fg (.attest src signed))) (hk : tr.time k = a) :
    (tr.state y k).fg.hmax ≤ HZ tr H g + 1 := by
  obtain ⟨-, -, -, -, -, ⟨X, hX, hXh⟩, -⟩ := Store.cache_invariants _ _ _ _
    (Compose.fg_reachable hrun.toLocalRun hy k)
  have := held_row_lt hrun hh hR hy hc hk.le hX
  omega

/-- **HR.1 (c), the attestations signed at the reset have height `≤ H_z + 1`.** -/
theorem signed_le_at_reset (hrun : GoldilocksRun proposer dg H tr) (hh : tr.HealthyRun H ΔF g)
    {a : Time} (hR : IsReset tr H g a) {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {att : FG.Att sp.n}
    (hs : tr.SignAt y k att) (hk : tr.time k = a) : att.h ≤ HZ tr H g + 1 := by
  obtain ⟨src, hc⟩ := hs
  exact (signAt_h_le hrun hy ⟨src, hc⟩).trans (hmax_le_at_reset hrun hh hR hy hc hk)

/-- An entry of a high honest chain has, at the honest node that holds it, a state of height
`≥ H_z + 1`. -/
private theorem highEntry_h {E : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrun : GoldilocksRun proposer dg H tr)
    (hE : E ∈ HighEntries tr H (HZ tr H g)) :
    ∃ y ∈ H, ∃ i, E ∈ (tr.state y i).fg.tree ∧ HZ tr H g + 1 ≤ ((tr.state y i).fg.σ E.root).h := by
  obtain ⟨y, hy, i, hE, B, hB, hBh, hBT⟩ := hE
  obtain ⟨⟨E', hE', hE'r, -, hE'h, -⟩, -⟩ := Store.entry_state_of_source _ _ _ _
    (Compose.fg_reachable hrun.toLocalRun hy i) B hB
  have hE'E : E' = E := by
    have h1 : (tr.state y i).fg.blocks E.root = some E := hE
    have h2 : (tr.state y i).fg.blocks E'.root = some E' := hE'
    rw [hE'r, hBT] at h2
    exact Option.some.inj (h2.symm.trans h1)
  subst hE'E
  exact ⟨y, hy, i, hE', hE'h ▸ hBh⟩

/-- **HR.1 (c), the first clause of (K1_𝓔) of G1.10 with `T₀ = a_z − Δ`.** The namers of a high
entry by `a_z − Δ` are the faulty validators: an honest one would have signed an attestation of
height `≥ H_z + 1` (the entry's state is the same at every honest node) before `a_z`. -/
theorem namers_lt_q (hrun : GoldilocksRun proposer dg H tr) (hh : tr.HealthyRun H ΔF g)
    (hnc : Compose.NoCollRun dg tr) {a : Time} (hR : IsReset tr H g a)
    {E : SA.Blk sp.n (List (FG.Att sp.n))} (hE : E ∈ HighEntries tr H (HZ tr H g)) :
    (Store.namers sp.toParams (Payload sp.n) H tr.projFG (a - sp.Δ) E).ncard <
      sp.toParams.fg.q := by
  have hinj :=
    (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun.coherent.1
  obtain ⟨y, hy, i, hEy, hEh⟩ := highEntry_h hrun hE
  refine lt_of_le_of_lt (Set.ncard_le_ncard (fun v hv => ?_) (Set.toFinite _)) (faulty_lt_q hh)
  rcases hv with hv | ⟨j, att, hs, hj, hT⟩
  · exact hv
  intro hvH
  have hs := signAt_of_projFG hs
  obtain ⟨E', hE', hE'r, hE'h⟩ := signAt_entry hrun hvH hs
  obtain rfl : E' = E := hinj ⟨v, hvH, j, hE'⟩ ⟨y, hy, i, hEy⟩ (hE'r.trans hT)
  have hσ := Store.σ_eq_of_mem (Compose.fg_reachable hrun.toLocalRun hy i)
    (Compose.fg_reachable hrun.toLocalRun hvH j) hinj (fun B hB => ⟨y, hy, i, hB⟩)
    (fun B hB => ⟨v, hvH, j, hB⟩) hEy hE'
  have := reset_le_of_high hrun hh hR hvH hs (by rw [← hE'h, ← hσ]; exact hEh)
  have := sp.toParams.hΔ
  change tr.time j ≤ a - sp.Δ at hj
  linarith

/-- **HR.1, cut and reset.** -/
theorem cut_and_reset : CutAndReset := by
  intro sp ro proposer dg H tr g ΔF hrun hh hnc
  refine ⟨cutZ_le sp g, fun y hy k att hs hk => signed_le_HZ hrun hh hy hs hk,
    fun x hx i ℓ C hto hi => toFG_fastLock hrun hnc hx hto hi,
    fun y hy i X hX hXh => honest_row_of_height hrun hh hy i hX hXh, fun a hR => ?_⟩
  refine ⟨cutZ_lt_reset hrun hh hR,
    fun y hy k att hs hatt => reset_le_of_high hrun hh hR hy hs hatt,
    fun y hy k src signed hc hk => hmax_le_at_reset hrun hh hR hy hc hk,
    fun y hy k att hs hk => signed_le_at_reset hrun hh hR hy hs hk,
    fun 𝓔 h𝓔 E hE => namers_lt_q hrun hh hnc hR (h𝓔 hE), fun T hT y hy k att hs hk => ?_⟩
  have := sp.toParams.hΔ
  constructor <;> linarith

end Consensus.Goldilocks.Healing

end

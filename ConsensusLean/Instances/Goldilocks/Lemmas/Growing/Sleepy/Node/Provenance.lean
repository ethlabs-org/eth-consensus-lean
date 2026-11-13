module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.LiftFrame
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries

public section

/-! # Goldilocks under `Sleepy` with growing faults: provenance of records, sources, rows, caches

The growing-fault forms of the provenance part of S1 (`Compose/Sleepy/Provenance`), each the
static lemma on the prefix through one time:

* `record_origin_at` (state read at `t`, the node honest at `t`): the record names a block of the
  node's tree that is genesis or an origin within `b ≥ t`;
* `source_on_chain_at` (the node honest at its cut): every FG source is on the chain of the
  origins within `b`;
* `row_on_chain_at` (the signer honest at its signing): an honest attestation names a block on
  the chain of the origins within `b`;
* `caches_on_chain_at` (state read at `t`, the node honest at `t`, `2 f_t < n`): `Σ.F` and `Σ.J`
  are on the chain of the origins within `b ≥ t`. The quorum count is charged at the reading time
  `t`: a target quorum has a member honest at `t` (`f_t < n/2 < q`), whose attestation, signed
  before `t`, is honest. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- With `2 f < n`, a quorum has an honest member (`f < n/2 < q`). -/
private theorem honest_of_quorum_two (hf : 2 * Hᶜ.ncard < sp.n) {Q : Finset (Fin sp.n)}
    (hQ : sp.toParams.fg.q ≤ Q.card) : ∃ v ∈ Q, v ∈ H := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hHc : (Q : Set (Fin sp.n)).ncard ≤ Hᶜ.ncard :=
    Set.ncard_le_ncard (fun v hv => hno v hv) (Set.toFinite _)
  rw [Set.ncard_coe_finset] at hHc
  have hq : sp.toParams.fg.q = (2 * sp.n + 2) / 3 := rfl
  omega

/-- `caches_on_chain_upTo` with the count `2 f < n` in place of a slot count. -/
theorem caches_on_chain_of_two {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {b : Time}
    (hi : ∀ k < i, tr.time k ≤ b) :
    OnOriginChainWithin tr H (tr.state y i).fg.F b ∧
      OnOriginChainWithin tr H (tr.state y i).fg.J b := by
  have hfg := projFG_localRun hrun hnc
  have hst : tr.projFG.store y i = (tr.state y i).fg := by
    simp only [FGTrace.store, projFG_state hrun.toLocalRun hy i]
  have hsub : (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, i, hX⟩
  have hX : ∀ X ∈ ({(tr.state y i).fg.J, (tr.state y i).fg.F} :
      Set (SA.Blk sp.n (List (FG.Att sp.n)))), X ∈ (tr.state y i).fg.tree →
      OnOriginChainWithin tr H X b := by
    intro X hXJF hXt
    rcases cache_quorum (fg_reachable hrun.toLocalRun hy i) X hXJF with hg | ⟨Q, hQ, hQv⟩
    · exact onOriginChainWithin_iff.2 (Or.inl hg)
    obtain ⟨v, hvQ, hvH⟩ := honest_of_quorum_two hf hQ
    obtain ⟨Z, hZ, a, ha, rfl, haT⟩ := hQv v hvQ
    rcases Store.tree_accepted hfg hy (hst ▸ hZ) with rfl | ⟨k, hki, hk⟩
    · simp [Params.genesisBlock] at ha
    obtain ⟨hkn, hkl⟩ := hk
    rw [RunTrace.projFG, Option.bind_eq_some_iff] at hkl
    obtain ⟨c, hc, hcl⟩ := hkl
    cases c with
    | ac ℓ => simp [RunTrace.fgLabel] at hcl
    | fg ℓ =>
      simp only [RunTrace.fgLabel, Option.some.injEq] at hcl
      subst hcl
      obtain ⟨j, hjk, hsign⟩ := hrun.att_unforgeable y hy k a
        (Or.inr ⟨Z, ⟨true, hkn, hc⟩, ha⟩) hvH
      obtain ⟨E, hE, hEr, hEc⟩ :=
        row_on_chain_upTo hrun hnc hvH hsign fun k' hk' => hi k' (by omega)
      obtain rfl : X = E := (honest_coherent hrun hnc).1 (hsub hXt) hE (haT.symm.trans hEr.symm)
      exact hEc
  obtain ⟨hFt, hJt, -⟩ := Store.cache_invariants _ _ _ _ (fg_reachable hrun.toLocalRun hy i)
  exact ⟨hX _ (Or.inr rfl) hFt, hX _ (Or.inl rfl) hJt⟩

end Consensus.Goldilocks.Compose

namespace Consensus.Goldilocks.Compose.Growing

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- A block on the chain of the origins (within `b'`) of the prefix through `d` is on the chain of
the origins within `b'` of the run. -/
theorem onOriginChainWithin_of_upTo {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    {d b' : Time}
    (hd : 0 ≤ d) {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : Compose.OnOriginChainWithin (tr.upTo d) (H d) B b') : OnOriginChainWithin tr H B b' := by
  rcases Compose.onOriginChainWithin_iff.1 h with hg | ⟨C, s, hC, hBC⟩
  · exact onOriginChainWithin_iff.2 (Or.inl hg)
  · exact onOriginChainWithin_iff.2
      (Or.inr ⟨C, s, originWithin_of_upTo hrun hC, hBC.mono (upTo_subset hrun hd)⟩)

/-- **The record names genesis or an origin**: the state of `y` before cut `i`, read at a time
`t ∈ [0, b]` at or after every earlier cut, with `y` honest at `t`. -/
theorem record_origin_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} {t b : Time} (ht0 : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t)
    (htb : t ≤ b) (hy : y ∈ H t) :
    ∃ C ∈ (tr.state y i).fg.tree, C.root = (tr.state y i).ac.latestConfirmed ∧
      (C.root = sp.genesisRoot ∨ ∃ s, OriginWithin tr H C s b) := by
  have hst := Trace.upTo_state tr y hi
  obtain ⟨C, hC, hCr, h⟩ := Compose.record_origin_before (hrun.upTo ht0) (hnc.upTo _) hy i
  rw [hst] at hC hCr
  refine ⟨C, hC, hCr, h.imp_right fun ⟨s, hs⟩ => ⟨s, ?_⟩⟩
  exact (originBefore_of_upTo hrun hs).within fun k hk => (hi k hk).trans htb

/-- **Every FG source is on the chain of the origins within `b`**, for a node honest at its cut,
whose earlier cuts are at times `≤ b`. -/
theorem source_on_chain_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} {b : Time} (hy : y ∈ H (tr.time i)) (hi : ∀ k < i, tr.time k ≤ b)
    {ℓ : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : SA.ToFGAt tr.projAC y i ℓ C) : OnOriginChainWithin tr H C b := by
  have hd := hrun.time_nonneg i
  obtain ⟨hc, hcall, hC⟩ := h
  have h' : SA.ToFGAt (tr.upTo (tr.time i)).projAC y i ℓ C := by
    rw [RunTrace.upTo_projAC]
    exact ⟨(Trace.upTo_callAt_of_le _ le_rfl).2 hc, hcall, by
      rw [projAC_upTo_state hrun le_rfl]; exact hC⟩
  exact onOriginChainWithin_of_upTo hrun hd
    (Compose.source_on_chain_upTo (hrun.upTo hd) (hnc.upTo _) hy hi h')

/-- **Every honest attestation names a block on the chain of the origins within `b`**, for a signer
honest at its signing, whose earlier cuts are at times `≤ b`. -/
theorem row_on_chain_at (hrun : Growing.GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr)
    {x : Fin sp.n} {k : Nat} {a : FG.Att sp.n} (hx : x ∈ H (tr.time k)) (h : tr.SignAt x k a)
    {b : Time} (hk : ∀ k' < k, tr.time k' ≤ b) :
    ∃ E ∈ tr.HonestBlocksAt H, E.root = a.T ∧ OnOriginChainWithin tr H E b := by
  have hd := hrun.time_nonneg k
  obtain ⟨E, hE, hEr, hEc⟩ := Compose.row_on_chain_upTo (hrun.upTo hd) (hnc.upTo _) hx
    ((RunTrace.upTo_signAt tr).2 ⟨le_rfl, h⟩) hk
  exact ⟨E, upTo_subset hrun hd hE, hEr, onOriginChainWithin_of_upTo hrun hd hEc⟩

/-- **`Σ.F` and `Σ.J` are on the chain of the origins within `b`**: the state of `y` before cut
`i`, read at `t ∈ [0, b]` at or after every earlier cut, with `y` honest at `t` and `2 f_t < n`
(a target quorum has a member honest at `t`, Lemma Q at the reading time). -/
theorem caches_on_chain_at {ini} (hrun : Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    {y : Fin sp.n} {i : Nat} {t b : Time} (ht0 : 0 ≤ t) (hi : ∀ k < i, tr.time k ≤ t)
    (htb : t ≤ b) (hy : y ∈ H t) (hf : 2 * (H t)ᶜ.ncard < sp.n) :
    OnOriginChainWithin tr H (tr.state y i).fg.F b ∧
      OnOriginChainWithin tr H (tr.state y i).fg.J b := by
  have hst := Trace.upTo_state tr y hi
  have h := Compose.caches_on_chain_of_two (hrun.upTo ht0) (hnc.upTo _) hf hy (b := t) hi
  rw [hst] at h
  have hmono : ∀ {B}, OnOriginChainWithin tr H B t → OnOriginChainWithin tr H B b := by
    intro B hB
    rcases onOriginChainWithin_iff.1 hB with hg | ⟨C, s, hC, hBC⟩
    · exact onOriginChainWithin_iff.2 (Or.inl hg)
    · exact onOriginChainWithin_iff.2 (Or.inr ⟨C, s, hC.mono htb, hBC⟩)
  exact ⟨hmono (onOriginChainWithin_of_upTo hrun ht0 h.1),
    hmono (onOriginChainWithin_of_upTo hrun ht0 h.2)⟩

end Consensus.Goldilocks.Compose.Growing

end

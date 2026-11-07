module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Source
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Same-height rows from reports, under growing faults

The growing forms of the row services of `Healing/Outcome/Service` and of the row provenance of
`Healing/Retention/Rows`. Each node is honest at its own cut: a signer at its signing, a reporter
at its report, an origin's writer at its write. A reader of a held state is honest at an
observation time after the state's cuts. The node-local steps are the static ones on the prefix
through the node's cut; the only cross-node fact is the comparability of bounded high origins
(`ResetPremisesUpTo.origins_compatible_at`).

* `ResetPremisesUpTo.high_row_source_at`: a high attestation names the entry of a high origin's
  chain written by its signer before the signing;
* `ResetPremisesUpTo.high_entry_eq_at`, `ResetPremisesUpTo.record_entry_eq_at`: high entries and
  high record entries agree at equal height;
* `ResetPremisesUpTo.row_target_of_sign_at`, `ResetPremisesUpTo.row_of_sign_at`: a high
  signature's target, timeout and finality fields;
* `ResetPremisesUpTo.sign_of_report_at`, `ResetPremisesUpTo.row_of_report_at`: a same-height
  report supplies an actual signature by its time;
* `ResetPremisesUpTo.row_signers_of_reports_at`: same-height reports of every node honest at `d`
  yield a quorum of exact entry signatures. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a : Time}

/-! ## Pure helpers -/

/-- The block named by a source's `T_h` is held and is the entry of its own state. -/
private theorem source_entry {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) (src : NodeBlock P ACP) :
    ∃ E ∈ st.tree, E.root = (st.σ src.root).Th ∧ (st.σ E.root).Th = E.root := by
  rcases hs : st.blocks src.root with _ | X
  · have hg : (st.σ src.root).Th = P.genesisRoot := by
      rw [Healing.Store.σ_of_blocks_none hr hs]; rfl
    refine ⟨_, Healing.Store.genesis_mem hr, hg.symm, ?_⟩
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Healing.Store.σ_genesis hr]; rfl
  · have hXr : X.root = src.root := Goldilocks.Store.Reachable.blocks_root hr hs
    have hX : X ∈ st.tree := by change st.blocks X.root = some X; rw [hXr]; exact hs
    obtain ⟨⟨E, hE, hEr, -, -, hET⟩, -⟩ := Store.entry_state_of_source P ACP acp₀ _ hr X hX
    rw [← hXr]
    exact ⟨E, hE, hEr, hET.trans hEr.symm⟩

/-- `create_attestation` signs `(h, T_h)` of its input with the record's finality pair and
records it; a timeout only on a recorded timeout or another target at that height. -/
private theorem createAtt_spec {n : Nat} {Λ Λ' : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) :
    a.val = v ∧ a.h = σe.h ∧ a.T = σe.Th ∧ a.fin = Λ.finalityPair σe ∧ Λ' = Λ.recordAtt a ∧
      (a.timeout = true → Λ.timeout σe.h ≠ ∅ ∨ ∃ T', Λ.target σe.h = some T' ∧ T' ≠ σe.Th) := by
  unfold FG.Record.createAtt at h
  rcases hp : Λ.heightPair σe.h σe.Th with _ | ⟨h', T', τ⟩ <;> rw [hp] at h
  · cases h
  dsimp only at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨rfl, rfl⟩ := Healing.Store.heightPair_eq hp
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun hτ => ?_⟩
  unfold FG.Record.heightPair at hp
  split_ifs at hp with h1 h2 h3 <;> simp only [Option.some.injEq, Prod.mk.injEq] at hp
  · exact Or.inl h2
  · simp_all
  · push Not at h3
    obtain ⟨T'', hT''⟩ := Option.ne_none_iff_exists'.1 h3.1
    exact Or.inr ⟨T'', hT'', fun e => h3.2 (hT''.trans (by rw [e]))⟩

/-- `create_attestation` signs nothing only on a lock of another root at the input's height, or
a content of that height already sent. -/
private theorem createAtt_none {n : Nat} {Λ : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    (h : Λ.createAtt v σe = none) :
    (Λ.lock σe.h ≠ none ∧ Λ.lock σe.h ≠ some σe.Th) ∨ ∃ b ∈ Λ.sent, b.1 = σe.h := by
  unfold FG.Record.createAtt at h
  rcases hp : Λ.heightPair σe.h σe.Th with _ | ⟨h', T', τ⟩ <;> rw [hp] at h
  · unfold FG.Record.heightPair at hp
    split_ifs at hp with h1
    exact Or.inl h1
  · obtain ⟨rfl, -⟩ := Healing.Store.heightPair_eq hp
    dsimp only at h
    split_ifs at h with hany
    obtain ⟨b, hb, hb'⟩ := List.any_eq_true.1 hany
    exact Or.inr ⟨b, hb, (of_decide_eq_true hb').1⟩

/-- The selection of a fast-lock write is in the frame of its call. -/
private theorem fastLockAt_frame_mem {tr : GoldilocksTrace sp ro} {x : Fin sp.n} {i s : Nat}
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (h : SA.FastLockAt tr.projAC x i s D CV) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt x i ℓ) : D ∈ ℓ.frame.tree := by
  rcases h with ⟨ℓ', C, ⟨hc', -⟩, -, hD, -⟩ | ⟨ℓ', A, ⟨hc', -⟩, -, hsel, -⟩
  · obtain rfl : ℓ' = ℓ := Option.some.inj (hc'.2.symm.trans hc.2)
    exact (SA.deepest_mem hD).1.1.1
  · obtain rfl : ℓ' = ℓ := Option.some.inj (hc'.2.symm.trans hc.2)
    unfold SA.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    exact (SA.deepest_mem hsel).1.1

/-! ## The source of a signed row, on a static run -/

/-- **The source of a signed row** on a static run, without a height bound: the row names the
entry `E` of the chain of the stored block `O` of a fast-lock write of the signer at an earlier
cut `r`, joined at the write. The entry's height is the row's, so `O` is at least that high. -/
private theorem row_source_static {H₀ : Set (Fin sp.n)} {tr₀ : GoldilocksTrace sp ro}
    (hrun : Consensus.Goldilocks.GoldilocksRun proposer dg H₀ tr₀)
    (hnc : Compose.NoCollRun dg tr₀) {v : Fin sp.n} (hv : v ∈ H₀)
    {d : Nat} {att : FG.Att sp.n} (hs : tr₀.SignAt v d att) :
    ∃ r < d, ∃ l O CV ℓw D, tr₀.projAC.CallAt v r ℓw ∧ SA.FastLockAt tr₀.projAC v r l D CV ∧
      O = ℓw.frame.viableAncestor D ∧ tr₀.JoinedAt v (tr₀.time r) ∧
      O ∈ (tr₀.state v r).fg.tree ∧ att.h ≤ ((tr₀.state v r).fg.σ O.root).h ∧
      ∃ E ∈ (tr₀.state v r).fg.tree, (tr₀.state v r).fg.Anc E O ∧ E.root = att.T ∧
        ((tr₀.state v r).fg.σ E.root).h = att.h ∧ ((tr₀.state v r).fg.σ E.root).Th = E.root := by
  have hacr := Compose.goldilocks_ac_projection sp ro dg H₀ tr₀ proposer hrun hnc
  have hr := hacr.localRun
  have hU := hr.coherent
  obtain ⟨C, hcall⟩ := hs
  obtain ⟨d', rfl, ℓ, hc', hto, -, hC, hfgeq⟩ :=
    Compose.attest_source hrun.toLocalRun hv hcall
  have hpc : tr₀.projAC.CallAt v d' ℓ := Compose.projAC_callAt.mpr hc'
  have hC' : (SA.acToFG sp (tr₀.projAC.state v d') ℓ.frame (tr₀.time d')).2 = some C := by
    rw [Compose.projAC_state hrun.toLocalRun hv]
    exact hC
  obtain ⟨hCv, l, hl, hlb, hlf, -⟩ := SA.toFG_candidate hC'
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  obtain ⟨r, hrd, CV, ℓw, D, hcw, hfl, L, hL, hLr, hLO⟩ :=
    Healing.stored_fast_lock_provenance hr hv d' l₀ hl₀ hlf
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hv hpc
  obtain ⟨hΦw, -⟩ := SA.frameIn_of_callAt hr hv hcw
  have hCt : C ∈ ℓ.frame.tree := hCv.1
  obtain ⟨hvat, hva⟩ := SA.viableAncestor_anc hΦ hB₀
  obtain rfl : C = ℓ.frame.viableAncestor B₀ := hU.1 (hΦU hCt) (hΦU hvat) hlb.symm
  obtain rfl : L = B₀ := hU.1 hL (hΦU hB₀) (hLr.trans hB₀r.symm)
  set O := ℓw.frame.viableAncestor D with hO
  have hCO : Anc (tr₀.HonestBlocks H₀) (ℓ.frame.viableAncestor L) O := (hva.mono hΦU).trans hLO
  have hOt : O ∈ (tr₀.state v r).fg.tree :=
    Healing.mem_tree_of_frame hrun hv hcw
      (SA.viableAncestor_anc hΦw (fastLockAt_frame_mem hfl hcw)).1
  set st := (tr₀.state v (d' + 1)).fg with hst
  have hreach := Compose.fg_reachable hrun.toLocalRun hv (d' + 1)
  have hCst : ℓ.frame.viableAncestor L ∈ st.tree := by
    rw [hfgeq]
    exact Healing.mem_tree_of_frame hrun hv hpc hCt
  have hcut := (hrun.cutLaw v hv (d' + 1) _ hcall).1
  obtain ⟨hah, haT⟩ := Healing.Store.createAtt_eq hcut
  obtain ⟨⟨E, hE, hEr, hEC, hEh, hETh⟩, -⟩ :=
    Store.entry_state_of_source sp.toParams (Payload sp.n) _ st hreach _ hCst
  have hEh' : (st.σ E.root).h = att.h := by rw [hah, hEr]
  have hETh' : (st.σ E.root).Th = E.root := by rw [hETh, hEr]
  have hEr' : E.root = att.T := by
    rw [haT]
    change E.root = (st.σ (st.σ _).Th).Th
    rw [← hEr, hETh']
  have hOst : O ∈ st.tree := Compose.tree_mono hrun.toLocalRun hv (by omega) hOt
  have hCOst := Healing.store_anc_of_honest_anc hrun hnc hv hCO hOst
  have hσO := Healing.σ_eq_honest hrun hnc hv hv hOst hOt
  have hOh : att.h ≤ ((tr₀.state v r).fg.σ O.root).h := by
    rw [← hσO]
    have := Healing.h_le_of_store_anc hreach hCOst
    rw [← hEh] at this
    omega
  have hsub : st.tree ⊆ tr₀.HonestBlocks H₀ := fun X hX => ⟨v, hv, d' + 1, hX⟩
  have hEO : Anc (tr₀.HonestBlocks H₀) E O := (hEC.mono hsub).trans hCO
  have hEt := Healing.mem_of_honest_anc hrun hnc hv hEO hOt
  have hσE := Healing.σ_eq_honest hrun hnc hv hv hEt hE
  refine ⟨r, by omega, l₀.slot, O, CV, ℓw, D, hcw, hfl, rfl,
    Healing.joinedAt_of_fastLockAt hrun hnc hv hfl, hOt, hOh, E, hEt,
    Healing.store_anc_of_honest_anc hrun hnc hv hEO hOt, hEr', by rw [hσE, hEh'],
    by rw [hσE, hETh']⟩

/-! ## Prefix transports of the node-local record facts -/

/-- The record origin of a node honest at `t`, after every earlier cut
(`client_record_origin_of_run` on the prefix through `t`). -/
private theorem client_record_origin_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hy : y ∈ H t) (h r : Nat) :
    ((tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.h = h ∧ att.T = r) ∧
    ((tr.state y i).record.lock h = some r →
      ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.fin = some (h, r)) := by
  have hst := Trace.upTo_state tr y hle
  obtain ⟨h1, h2⟩ := Healing.client_record_origin_of_run (hrun.upTo ht0) hy h r i
  rw [hst] at h1 h2
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨k, hk, att, hs, hh⟩ := h1 hx
    exact ⟨k, hk, att, ((RunTrace.upTo_signAt _).mp hs).2, hh⟩
  · obtain ⟨k, hk, att, hs, hh⟩ := h2 hx
    exact ⟨k, hk, att, ((RunTrace.upTo_signAt _).mp hs).2, hh⟩

/-- One record step of a node honest at the step. -/
private theorem record_step_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i)) :
    (tr.state y (i + 1)).record = (tr.state y i).record ∨
      ∃ att, tr.SignAt y i att ∧
        (tr.state y (i + 1)).record = (tr.state y i).record.recordAtt att := by
  have hle1 : ∀ q < i + 1, tr.time q ≤ tr.time i := fun _ hq => hrun.time_mono (by omega)
  have hle0 : ∀ q < i, tr.time q ≤ tr.time i := fun _ hq => hrun.time_mono hq.le
  have h := Healing.record_step_of_run (hrun.upTo (hrun.time_nonneg i)) hy i
  rw [Trace.upTo_state tr y hle1, Trace.upTo_state tr y hle0] at h
  rcases h with h | ⟨att, hs, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨att, ((RunTrace.upTo_signAt _).mp hs).2, h⟩

/-- A sent content of a node honest at `t`, after every earlier cut, was signed earlier. -/
private theorem sent_origin_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hy : y ∈ H t) {b : FG.Content} (hb : b ∈ (tr.state y i).record.sent) :
    ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.content = b := by
  obtain ⟨k, hk, att, hs, he⟩ := Healing.sent_origin (hrun.upTo ht0) hy i
    (by rw [Trace.upTo_state tr y hle]; exact hb)
  exact ⟨k, hk, att, ((RunTrace.upTo_signAt _).mp hs).2, he⟩

/-- The entry of a signature of a node honest at its signing. -/
private theorem signAt_entry_at (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) {att : FG.Att sp.n}
    (hs : tr.SignAt y k att) :
    ∃ E ∈ (tr.state y k).fg.tree, E.root = att.T ∧ ((tr.state y k).fg.σ E.root).h = att.h := by
  have h := Healing.signAt_entry (hrun.upTo (hrun.time_nonneg k)) hy
    ((RunTrace.upTo_signAt _).mpr ⟨le_rfl, hs⟩)
  rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

/-- The finality pair of a signature of a node honest at its signing names a held entry below the
signed entry. -/
private theorem signed_fin_pair_entry_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) {att : FG.Att sp.n}
    (hs : tr.SignAt y k att) {h r : Nat} (hfin : att.fin = some (h, r)) :
    ∃ J ∈ (tr.state y k).fg.tree, ∃ E ∈ (tr.state y k).fg.tree, E.root = att.T ∧
      (tr.state y k).fg.Anc J E ∧ J.root = r ∧ ((tr.state y k).fg.σ J.root).h = h ∧
      ((tr.state y k).fg.σ J.root).Th = J.root := by
  have h := Healing.signed_fin_pair_entry_of_run (hrun.upTo (hrun.time_nonneg k)) hy
    ((RunTrace.upTo_signAt _).mpr ⟨le_rfl, hs⟩) hfin
  rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

namespace ResetPremisesUpTo

variable {b : Time}

/-- **The source of a high attestation**, under growing faults. An attestation of height
`≥ H_z + 1` signed at cut `d` by a node honest at its signing names the entry `E` (at its
height) of the chain of a high origin `(O, l)` written by the signer at a cut `r < d`. -/
theorem high_row_source_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {v : Fin sp.n} {d : Nat} (hv : v ∈ H (tr.time d)) {att : FG.Att sp.n}
    (hs : tr.SignAt v d att) (hh : HZ tr H g + 1 ≤ att.h) :
    ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧ ∃ E ∈ (tr.state v r).fg.tree,
      (tr.state v r).fg.Anc E O ∧ E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
      ((tr.state v r).fg.σ E.root).Th = E.root := by
  have hrun := hp.run
  have h0 := hrun.time_nonneg d
  have hs' : (tr.upTo (tr.time d)).SignAt v d att := (RunTrace.upTo_signAt _).mpr ⟨le_rfl, hs⟩
  obtain ⟨r, hrd, l, O, CV, ℓw, D, hcw, hfl, rfl, hj, hOt, hOh, E, hEt, hEO, hEr, hEh, hET⟩ :=
    row_source_static (hrun.upTo h0) (hp.noColl.upTo _) hv hs'
  have hrt : tr.time r ≤ tr.time d := hrun.time_mono hrd.le
  have hst : (tr.upTo (tr.time d)).state v r = tr.state v r :=
    RunTrace.upTo_state_of_le hrun.time_mono hrt
  rw [hst] at hOt hOh hEt hEO hEh hET
  have hcw' : tr.projAC.CallAt v r ℓw := by
    rw [RunTrace.upTo_projAC] at hcw
    exact ((Trace.upTo_callAt _).mp hcw).2
  have hfl' : SA.FastLockAt tr.projAC v r l D CV :=
    (fastLockAt_upTo_iff hrun.time_mono hrt).mp hfl
  have hj' : tr.JoinedAt v (tr.time r) := (joinedAt_upTo_iff hrt).mp hj
  refine ⟨r, hrd, l, _, ⟨hrun.antitone hrt hv, hj', ⟨CV, ℓw, D, hcw', hfl', rfl⟩, hh.trans hOh⟩,
    E, hEt, hEO, hEr, hEh, hET⟩

/-- Entries at equal height below one held block agree, at a holder honest at an observation
time after its cuts. -/
private theorem entry_root_eq_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < m, tr.time q ≤ t)
    (hz : z ∈ H t) {C Z₁ Z₂ : SA.Blk sp.n (List (FG.Att sp.n))}
    (hC : C ∈ (tr.state z m).fg.tree)
    (h₁ : Anc (tr.HonestBlocksAt H) Z₁ C) (h₂ : Anc (tr.HonestBlocksAt H) Z₂ C)
    (hh : ((tr.state z m).fg.σ Z₁.root).h = ((tr.state z m).fg.σ Z₂.root).h)
    (hT₁ : ((tr.state z m).fg.σ Z₁.root).Th = Z₁.root)
    (hT₂ : ((tr.state z m).fg.σ Z₂.root).Th = Z₂.root) : Z₁.root = Z₂.root := by
  have hr := fg_reachable_at hp.run ht hle hz
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  rcases SA.anc_total hU h₁ h₂ with h | h
  · have := Healing.Th_eq_of_anc hr (store_anc_of_honest_anc_at hp.run hp.noColl ht hle hz h
      (mem_of_honest_anc_at hp.run hp.noColl ht hle hz h₂ hC)) hh.symm
    rw [← hT₁, ← hT₂, this]
  · have := Healing.Th_eq_of_anc hr (store_anc_of_honest_anc_at hp.run hp.noColl ht hle hz h
      (mem_of_honest_anc_at hp.run hp.noColl ht hle hz h₁ hC)) hh
    rw [← hT₁, ← hT₂, this]

/-- **Historical self-entries under bounded high origins agree at equal height**, each read at a
holder honest at an observation time after its cuts. -/
theorem high_entry_eq_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {x x' : Fin sp.n}
    {i j i' j' : Nat} {B B' Z₁ Z₂ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (ho' : HighOrigin tr H g x' i' j' B') (hi'b : tr.time i' ≤ b)
    (h₁ : Anc (tr.HonestBlocksAt H) Z₁ B) (h₂ : Anc (tr.HonestBlocksAt H) Z₂ B')
    {y₁ y₂ : Fin sp.n} {m₁ m₂ : Nat} {t₁ t₂ : Time}
    (ht₁ : 0 ≤ t₁) (hle₁ : ∀ q < m₁, tr.time q ≤ t₁) (hy₁ : y₁ ∈ H t₁)
    (ht₂ : 0 ≤ t₂) (hle₂ : ∀ q < m₂, tr.time q ≤ t₂) (hy₂ : y₂ ∈ H t₂)
    (hZ₁ : Z₁ ∈ (tr.state y₁ m₁).fg.tree) (hZ₂ : Z₂ ∈ (tr.state y₂ m₂).fg.tree)
    (hh : ((tr.state y₁ m₁).fg.σ Z₁.root).h = ((tr.state y₂ m₂).fg.σ Z₂.root).h)
    (hT₁ : ((tr.state y₁ m₁).fg.σ Z₁.root).Th = Z₁.root)
    (hT₂ : ((tr.state y₂ m₂).fg.σ Z₂.root).Th = Z₂.root) : Z₁.root = Z₂.root := by
  have key : ∀ {w : Fin sp.n} {k : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))},
      w ∈ H (tr.time k) → D ∈ (tr.state w k).fg.tree → Anc (tr.HonestBlocksAt H) Z₁ D →
      Anc (tr.HonestBlocksAt H) Z₂ D → Z₁.root = Z₂.root := by
    intro w k D hw hD hZ₁D hZ₂D
    have h0 := hp.run.time_nonneg k
    have hlek : ∀ q < k, tr.time q ≤ tr.time k := fun _ hq => hp.run.time_mono hq.le
    have e₁ := σ_eq_honest_at hp.run hp.noColl ht₁ hle₁ hy₁ h0 hlek hw hZ₁
      (mem_of_honest_anc_at hp.run hp.noColl h0 hlek hw hZ₁D hD)
    have e₂ := σ_eq_honest_at hp.run hp.noColl ht₂ hle₂ hy₂ h0 hlek hw hZ₂
      (mem_of_honest_anc_at hp.run hp.noColl h0 hlek hw hZ₂D hD)
    exact entry_root_eq_at hp h0 hlek hw hD hZ₁D hZ₂D (by rw [← e₁, ← e₂, hh])
      (by rw [← e₁, hT₁]) (by rw [← e₂, hT₂])
  rcases hp.origins_compatible_at ho hib ho' hi'b with hBB' | hB'B
  · exact key ho'.1 (highOrigin_mem_at hp.run hp.noColl ho') (h₁.trans hBB') h₂
  · exact key ho.1 (highOrigin_mem_at hp.run hp.noColl ho) h₁ (h₂.trans hB'B)

/-- **A high record entry is the high-chain entry of its height**: a record of a node honest at
`t ≤ b` after its cuts, with a target, timeout or lock entry at `h ≥ H_z + 1`, names the root of
every entry at `h` below a bounded high origin. -/
theorem record_entry_eq_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b) {h r : Nat} (hh : HZ tr H g + 1 ≤ h)
    (hr : (tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h ∨
      (tr.state y i).record.lock h = some r)
    {xo : Fin sp.n} {io jo : Nat} {B E : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hiob : tr.time io ≤ b)
    (hEB : Anc (tr.HonestBlocksAt H) E B) {z : Fin sp.n} {m : Nat} {u : Time} (hu : 0 ≤ u)
    (hlez : ∀ q < m, tr.time q ≤ u) (hz : z ∈ H u) (hE : E ∈ (tr.state z m).fg.tree)
    (hEh : ((tr.state z m).fg.σ E.root).h = h)
    (hET : ((tr.state z m).fg.σ E.root).Th = E.root) : r = E.root := by
  have hrun := hp.run
  have hU := Compose.Growing.honest_blocks_coherent hrun hp.noColl
  have leC : ∀ k : Nat, ∀ q < k, tr.time q ≤ tr.time k := fun _ _ hq => hrun.time_mono hq.le
  have target : ∀ k < i, ∀ att, tr.SignAt y k att → att.h = h → att.T = r → r = E.root := by
    intro k hki att hs hah har
    have hkt : tr.time k ≤ t := hle k hki
    have hyk : y ∈ H (tr.time k) := hrun.antitone hkt hy
    obtain ⟨q, hqk, l, O, hO, X, hX, hXO, hXr, hXh, hXT⟩ :=
      hp.high_row_source_at hyk hs (hah ▸ hh)
    have hq0 := hrun.time_nonneg q
    exact har.symm.trans (hXr.symm.trans (hp.high_entry_eq_at hO
      ((hrun.time_mono hqk.le).trans (hkt.trans htb)) ho hiob
      (honest_anc_of_store_anc_at hq0 (leC q) hO.1 hXO) hEB hq0 (leC q) hO.1 hu hlez hz hX hE
      (hXh.trans (hah.trans hEh.symm)) hXT hET))
  have horig := client_record_origin_at hrun ht0 hle hy h r
  rcases hr with ht | ht | hl
  · obtain ⟨k, hki, att, hs, hah, har⟩ := horig.1 (Or.inl ht)
    exact target k hki att hs hah har
  · obtain ⟨k, hki, att, hs, hah, har⟩ := horig.1 (Or.inr ht)
    exact target k hki att hs hah har
  · obtain ⟨k, hki, att, hs, hfin⟩ := horig.2 hl
    have hkt : tr.time k ≤ t := hle k hki
    have hyk : y ∈ H (tr.time k) := hrun.antitone hkt hy
    have hk0 := hrun.time_nonneg k
    obtain ⟨J, hJ, X, hX, hXr, hJX, hJr, hJh, hJT⟩ := signed_fin_pair_entry_at hrun hyk hs hfin
    obtain ⟨X', hX', hX'r, hX'h⟩ := signAt_entry_at hrun hyk hs
    obtain rfl : X' = X := hU.1 ⟨y, k, _, hk0, leC k, hyk, hX'⟩ ⟨y, k, _, hk0, leC k, hyk, hX⟩
      (hX'r.trans hXr.symm)
    have hle' := Healing.σ_h_le_of_anc (fg_reachable_at hrun hk0 (leC k) hyk) hJX
    obtain ⟨q, hqk, l, O, hO, X'', hX'', hXO, hX''r, _, _⟩ :=
      hp.high_row_source_at hyk hs (by omega)
    have hq0 := hrun.time_nonneg q
    obtain rfl : X'' = X' := hU.1 ⟨y, q, _, hq0, leC q, hO.1, hX''⟩
      ⟨y, k, _, hk0, leC k, hyk, hX⟩ (hX''r.trans hX'r.symm)
    have hJO : Anc (tr.HonestBlocksAt H) J O :=
      (honest_anc_of_store_anc_at hk0 (leC k) hyk hJX).trans
        (honest_anc_of_store_anc_at hq0 (leC q) hO.1 hXO)
    exact hJr.symm.trans (hp.high_entry_eq_at hO
      ((hrun.time_mono hqk.le).trans (hkt.trans htb)) ho hiob
      hJO hEB hk0 (leC k) hyk hu hlez hz hJ hE (hJh.trans hEh.symm) hJT hET)

/-- The target and timeout fields of a high entry's attestation, signed by a node honest at its
signing, do not require its predecessor to be high. -/
private theorem sign_target_before_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) {att : FG.Att sp.n}
    (hs : tr.SignAt y k att) (hkb : tr.time k ≤ b) (hh : HZ tr H g + 1 ≤ att.h)
    (he : (tr.state y k).record.timeout att.h = ∅) : att.timeout = false := by
  have leC : ∀ k : Nat, ∀ q < k, tr.time q ≤ tr.time k := fun _ _ hq => hp.run.time_mono hq.le
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw y k _ hc hy).1
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨_, hah, haT, _, _, hτ⟩ := createAtt_spec hcl
  rw [← Bool.not_eq_true]
  intro hto
  rw [← hah, ← haT] at hτ
  rcases hτ hto with h' | ⟨T', hT', hne⟩
  · exact h' he
  · obtain ⟨q, hqk, l, O, hO, E, hE, hEO, hEr, hEh, hET⟩ := hp.high_row_source_at hy ⟨src, hc⟩ hh
    have hq0 := hp.run.time_nonneg q
    exact hne ((hp.record_entry_eq_at (hp.run.time_nonneg k) (leC k) hy hkb hh (Or.inl hT') hO
      ((hp.run.time_mono hqk.le).trans hkb) (honest_anc_of_store_anc_at hq0 (leC q) hO.1 hEO)
      hq0 (leC q) hO.1 hE hEh hET).trans hEr)

/-- A node honest at `t ≤ b`, after its cuts, has no recorded timeout at a high height. -/
private theorem timeout_empty_before_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {t : Time} (ht0 : 0 ≤ t) (hy : y ∈ H t) (htb : t ≤ b) :
    ∀ i, (∀ q < i, tr.time q ≤ t) → ∀ h, HZ tr H g + 1 ≤ h →
      (tr.state y i).record.timeout h = ∅
  | 0, _, h, _ => by rw [Trace.state, hp.run.init y (hp.run.antitone ht0 hy)]; rfl
  | i + 1, hle, h, hh => by
    have hle' : ∀ q < i, tr.time q ≤ t := fun q hq => hle q (by omega)
    have hit : tr.time i ≤ t := hle i (by omega)
    have hyi := hp.run.antitone hit hy
    rcases record_step_at hp.run hyi with he | ⟨att, hs, he⟩ <;> rw [he]
    · exact timeout_empty_before_at hp ht0 hy htb i hle' h hh
    · simp only [FG.Record.recordAtt]
      split_ifs with hto
      · rw [Function.update_apply]
        split_ifs with hha
        · subst hha
          have := sign_target_before_at hp hyi hs (hit.trans htb) hh
            (timeout_empty_before_at hp ht0 hy htb i hle' _ hh)
          simp_all
        · exact timeout_empty_before_at hp ht0 hy htb i hle' h hh
      · exact timeout_empty_before_at hp ht0 hy htb i hle' h hh

/-- Finite normalization of a high signature's target and timeout fields, for a signer honest
at its signing. -/
theorem row_target_of_sign_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} {j : Nat} (hz : z ∈ H (tr.time j)) {att : FG.Att sp.n}
    (hs : tr.SignAt z j att) (hjb : tr.time j ≤ b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t) (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hiob : tr.time io ≤ b)
    (hTB : Anc (tr.HonestBlocksAt H) T B) (hatt : att.h = σT.h) :
    att.val = z ∧ att.T = T.root ∧ att.timeout = false := by
  subst hσ
  have leC : ∀ k : Nat, ∀ q < k, tr.time q ≤ tr.time k := fun _ _ hq => hp.run.time_mono hq.le
  have hh : HZ tr H g + 1 ≤ att.h := hatt ▸ hhT
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw z j _ hc hz).1
  change (tr.state z j).record.createAtt z ((tr.state z j).fg.σ
    ((tr.state z j).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨hv, _, _, _, _, _⟩ := createAtt_spec hcl
  obtain ⟨q, hqj, l, O, hO, E, hE, hEO, hEr, hEh, hET⟩ := hp.high_row_source_at hz ⟨src, hc⟩ hh
  have hq0 := hp.run.time_nonneg q
  have hTr : att.T = T.root := hEr.symm.trans (hp.high_entry_eq_at hO
    ((hp.run.time_mono hqj.le).trans hjb) ho hiob
    (honest_anc_of_store_anc_at hq0 (leC q) hO.1 hEO) hTB hq0 (leC q) hO.1 ht hle hy hE hT
    (hEh.trans hatt) hET hTe)
  exact ⟨hv, hTr, sign_target_before_at hp hz ⟨src, hc⟩ hjb hh
    (timeout_empty_before_at hp (hp.run.time_nonneg j) hz hjb j (leC j) _ hh)⟩

/-- Historical signatures of a node honest at its signing carry the exact predecessor (of a
height whose previous height is justified) when that predecessor is high. -/
theorem row_of_sign_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} {j : Nat} (hz : z ∈ H (tr.time j)) {att : FG.Att sp.n}
    (hs : tr.SignAt z j att) (hjb : tr.time j ≤ b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t) (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hhj : σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hiob : tr.time io ≤ b)
    (hTB : Anc (tr.HonestBlocksAt H) T B) (hatt : att.h = σT.h) :
    att.val = z ∧ att.T = T.root ∧ att.timeout = false ∧
      (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J)) := by
  subst hσ
  have hrun := hp.run
  have leC : ∀ k : Nat, ∀ q < k, tr.time q ≤ tr.time k := fun _ _ hq => hrun.time_mono hq.le
  have hj0 := hrun.time_nonneg j
  have hU := Compose.Growing.honest_blocks_coherent hrun hp.noColl
  obtain ⟨hv, hTr, htimeout⟩ :=
    hp.row_target_of_sign_at hz hs hjb ht hle hy hT rfl hTe hhT ho hiob hTB hatt
  obtain ⟨src, hc⟩ := hs
  have hcl := (hrun.cutLaw z j _ hc hz).1
  change (tr.state z j).record.createAtt z ((tr.state z j).fg.σ
    ((tr.state z j).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨_, _, haT, hfin, _, _⟩ := createAtt_spec hcl
  refine ⟨hv, hTr, htimeout, fun hb => ?_⟩
  obtain ⟨E', hE', hE'r, hE'T⟩ := source_entry (fg_reachable_at hrun hj0 (leC j) hz) src
  have hR : ((tr.state z j).fg.σ src.root).Th = T.root := by
    rw [← hTr, haT, ← hE'r, hE'T]
  have he : E' = T := hU.1 ⟨z, j, _, hj0, leC j, hz, hE'⟩ ⟨y, m, t, ht, hle, hy, hT⟩
    (hE'r.trans hR)
  rw [he] at hE'
  rw [hfin, hR, σ_eq_honest_at hrun hp.noColl hj0 (leC j) hz ht hle hy hE' hT]
  obtain ⟨J₀, hJ₀, hJ₀T, hJ₀r, hJ₀h, hJ₀T'⟩ :=
    (Healing.chain_pairs_entry (fg_reachable_at hrun ht hle hy) hT).1 hb.1
  have heq := fun r hr => (hp.record_entry_eq_at hj0 (leC j) hz hjb (hhj hb) (i := j) (r := r)
    hr ho hiob ((honest_anc_of_store_anc_at ht hle hy hJ₀T).trans hTB) ht hle hy hJ₀ hJ₀h
    hJ₀T').trans hJ₀r
  have hperm : (tr.state z j).record.permits ((tr.state y m).fg.σ T.root).hj
      ((tr.state y m).fg.σ T.root).J := by
    refine ⟨?_, fun r hr => Finset.mem_singleton.2 (heq r (Or.inr (Or.inl hr))), ?_⟩
    · rcases ht' : (tr.state z j).record.target _ with _ | r
      exacts [Or.inl rfl, Or.inr (by rw [heq r (Or.inl ht')])]
    · rcases hl : (tr.state z j).record.lock _ with _ | r
      exacts [Or.inl rfl, Or.inr (by rw [heq r (Or.inr (Or.inr hl))])]
  unfold FG.Record.finalityPair
  simp only [hb, hperm, ↓reduceIte]

/-- A bounded same-height report of a node honest at the report supplies a signature of it by
the report's time, including the case where previously signed content suppresses the call. -/
theorem sign_of_report_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} {r : Nat} (hz : z ∈ H (tr.time r))
    {ell : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC z r ell C) (hrb : tr.time r ≤ b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t) (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hTC : Anc (tr.HonestBlocksAt H) T C)
    (hCh : ((tr.state z r).fg.σ C.root).h = σT.h)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hiob : tr.time io ≤ b)
    (hTB : Anc (tr.HonestBlocksAt H) T B) :
    ∃ j att, tr.SignAt z j att ∧ tr.time j ≤ tr.time r ∧ att.h = σT.h := by
  subst hσ
  have hrun := hp.run
  have hnc := hp.noColl
  have h0 := hrun.time_nonneg r
  have leR : ∀ q < r, tr.time q ≤ tr.time r := fun _ hq => hrun.time_mono hq.le
  have leR1 : ∀ q < r + 1, tr.time q ≤ tr.time r := fun _ hq => hrun.time_mono (by omega)
  have hCt := toFG_mem_tree_at hrun hz hrep
  obtain ⟨hpc, hcall, hC⟩ := hrep
  have hTt := mem_of_honest_anc_at hrun hnc h0 leR hz hTC hCt
  have hσT := σ_eq_honest_at hrun hnc h0 leR hz ht hle hy hTt hT
  have hCTh : ((tr.state z r).fg.σ C.root).Th = T.root := by
    rw [Healing.Th_eq_of_anc (fg_reachable_at hrun h0 leR hz)
      (store_anc_of_honest_anc_at hrun hnc h0 leR hz hTC hCt)
      (by rw [hCh, hσT]), hσT, hTe]
  rw [Obligations.Growing.projAC_state_at hrun hz] at hC
  have hpc' : (tr.upTo (tr.time r)).CallAt z r (.ac ell) :=
    (Trace.upTo_callAt_of_le _ le_rfl).mpr (Compose.projAC_callAt.1 hpc)
  have hst0 : (tr.upTo (tr.time r)).state z r = tr.state z r :=
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl
  have hst1 : (tr.upTo (tr.time r)).state z (r + 1) = tr.state z (r + 1) :=
    Trace.upTo_state tr z leR1
  obtain ⟨s, hs, hts, hfg⟩ := Healing.toFG_attest (hrun.upTo h0).toLocalRun hz hpc' hcall
    (by rw [hst0]; exact hC)
  rw [hst0, hst1] at hfg
  have hs' : tr.CallAt z (r + 1) (.fg (.attest C s)) := ((Trace.upTo_callAt _).mp hs).2
  have hts' : tr.time (r + 1) = tr.time r := hts
  have hz1 : z ∈ H (tr.time (r + 1)) := hts' ▸ hz
  have hσe : (tr.state z (r + 1)).fg.σ ((tr.state z (r + 1)).fg.σ C.root).Th =
      (tr.state y m).fg.σ T.root := by rw [hfg, hCTh, hσT]
  cases s with
  | some att =>
    have hcl := (hrun.cutLaw z _ _ hs' hz1).1
    change (tr.state z (r + 1)).record.createAtt z ((tr.state z (r + 1)).fg.σ
      ((tr.state z (r + 1)).fg.σ C.root).Th) = some (att, _) at hcl
    exact ⟨r + 1, att, ⟨C, hs'⟩, hts'.le, by rw [(createAtt_spec hcl).2.1, hσe]⟩
  | none =>
    have hcl := (hrun.cutLaw z _ _ hs' hz1).1
    change (tr.state z (r + 1)).record.createAtt z ((tr.state z (r + 1)).fg.σ
      ((tr.state z (r + 1)).fg.σ C.root).Th) = none at hcl
    rw [hσe] at hcl
    rcases createAtt_none hcl with ⟨hl, hl'⟩ | ⟨c, hc, _⟩
    · obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists'.1 hl
      have := hp.record_entry_eq_at h0 leR1 hz hrb hhT (Or.inr (Or.inr hr'))
        ho hiob hTB ht hle hy hT rfl hTe
      exact absurd (by rw [hr', this, hTe]) hl'
    · obtain ⟨k, hk, att, hsk, rfl⟩ := sent_origin_at hrun h0 leR1 hz hc
      exact ⟨k, att, hsk, (hrun.time_mono hk.le).trans hts'.le, by assumption⟩

/-- A bounded same-height report of a node honest at the report supplies the exact entry
attestation, with historical finality permission checked at the actual signing cut. -/
theorem row_of_report_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} {r : Nat} (hz : z ∈ H (tr.time r))
    {ell : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC z r ell C) (hrb : tr.time r ≤ b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t) (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hhj : σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj)
    (hTC : Anc (tr.HonestBlocksAt H) T C)
    (hCh : ((tr.state z r).fg.σ C.root).h = σT.h) :
    ∃ j att, tr.SignAt z j att ∧ tr.time j ≤ tr.time r ∧ att.val = z ∧
      att.h = σT.h ∧ att.T = T.root ∧ att.timeout = false ∧
      (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J)) := by
  obtain ⟨io, _, jo, O, _, _, ho, hiob, _, hCO, _⟩ := hp.high_report_origin_at hz hrep hrb
    (by rw [hCh]; exact hhT)
  have hTO := hTC.trans hCO
  obtain ⟨j, att, hs, htj, hh⟩ :=
    hp.sign_of_report_at hz hrep hrb ht hle hy hT hσ hTe hhT hTC hCh ho hiob hTO
  obtain ⟨hv, hroot, htimeout, hfin⟩ := hp.row_of_sign_at (hp.run.antitone htj hz) hs
    (htj.trans hrb) ht hle hy hT hσ hTe hhT hhj ho hiob hTO hh
  exact ⟨j, att, hs, htj, hv, hh, hroot, htimeout, hfin⟩

/-- Same-height reports, by `d`, from every node honest at `d` yield a quorum of nodes honest at
`d` with exact entry signatures by `d`. Historical reports count without any freshness
assumption. -/
theorem row_signers_of_reports_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t) (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hhj : σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj)
    {d : Time} (hd : 0 ≤ d) (hdb : d ≤ b)
    (hreports : ∀ z, z ∈ H d → ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ d ∧
      Anc (tr.HonestBlocksAt H) T C ∧ ((tr.state z r).fg.σ C.root).h = σT.h) :
    ∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
      ∀ z ∈ ids, z ∈ H d ∧ ∃ att j, tr.SignAt z j att ∧ att.val = z ∧
        att.h = σT.h ∧ att.T = T.root ∧ att.timeout = false ∧ tr.time j ≤ d ∧
        (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J)) := by
  classical
  refine ⟨Finset.univ.filter (· ∈ H d), ?_, ?_⟩
  · have hcard : (Finset.univ.filter (· ∈ H d)).card = (H d).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext z
      simp
    rw [hcard]
    have hn : (H d).ncard + (H d)ᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hf := hp.faults d hd hdb
    change (2 * sp.n + 2) / 3 ≤ _
    omega
  · intro z hz
    have hzH := (Finset.mem_filter.1 hz).2
    obtain ⟨r, ell, C, hr, hrd, hTC, hh⟩ := hreports z hzH
    obtain ⟨j, att, hs, htj, hv, hah, hroot, htimeout, hfin⟩ :=
      hp.row_of_report_at (hp.run.antitone hrd hzH) hr (hrd.trans hdb) ht hle hy hT hσ hTe hhT
        hhj hTC hh
    exact ⟨hzH, att, j, hs, hv, hah, hroot, htimeout, htj.trans hrd, hfin⟩

end ResetPremisesUpTo

end Consensus.Goldilocks.Healing.Growing

end

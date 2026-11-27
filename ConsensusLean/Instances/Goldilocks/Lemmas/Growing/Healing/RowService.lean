module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.DeepQuarantine
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SourceCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Lift
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Source
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.ClientSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Healed
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Attest

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
  yield a quorum, of nodes still honest at a later `e ≤ b`, of exact entry signatures by `d`. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n} {g ΔF a : Time}

/-! ## Pure helpers -/

/-! ## The source of a signed row, on a static run -/

/-- **The source of a signed row** on a static run, without a height bound: the row names the
entry `E` of the chain of the stored block `O` of a fast-lock write of the signer at an earlier
cut `r`, joined at the write. The entry's height is the row's, so `O` is at least that high.
The row's source must be a fast-lock candidate (`hfast`, read at the source's own height, which is
at least the row's); a deep source need not sit below a fast lock. -/
private theorem row_source_static {H₀ : Set (Fin sp.n)} {tr₀ : GoldilocksTrace sp}
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.GoldilocksRun proposer dg H₀ tr₀ ini)
    (hnc : Compose.NoCollRun dg tr₀) {v : Fin sp.n} (hv : v ∈ H₀)
    {d : Nat} {att : FG.Att sp.n} (hs : tr₀.SignAt v d att)
    (hfast : ∀ d' ℓ C, d' < d → AC.ToFGAt tr₀.projAC v d' ℓ C →
      att.h ≤ ((tr₀.state v d').fg.σ C.root).h →
      C ∈ AC.toFGCandidates sp (tr₀.projAC.state v d') ℓ.frame (tr₀.time d')) :
    ∃ r < d, ∃ l O CV ℓw D, tr₀.projAC.CallAt v r ℓw ∧ AC.FastLockAt tr₀.projAC v r l D CV ∧
      O = ℓw.frame.viableAncestor D ∧ tr₀.JoinedAt v (tr₀.time r) ∧
      O ∈ (tr₀.state v r).fg.tree ∧ att.h ≤ ((tr₀.state v r).fg.σ O.root).h ∧
      ∃ E ∈ (tr₀.state v r).fg.tree, (tr₀.state v r).fg.Anc E O ∧ E.root = att.T ∧
        ((tr₀.state v r).fg.σ E.root).h = att.h ∧ ((tr₀.state v r).fg.σ E.root).Th = E.root := by
  have hacr := Compose.goldilocks_ac_projection_from hrun hnc
  have hr := hacr.localRun
  have hU := hr.coherent
  obtain ⟨C, hcall⟩ := hs
  obtain ⟨d', rfl, ℓ, hc', hto, -, hC, hfgeq⟩ :=
    Compose.attest_source hrun.toLocalRun hv hcall
  have hpc : tr₀.projAC.CallAt v d' ℓ := Compose.projAC_callAt.mpr hc'
  have hC' : (AC.acToFG sp (tr₀.projAC.state v d') ℓ.frame (tr₀.time d')).2 = some C := by
    rw [Compose.projAC_state hrun.toLocalRun hv]
    exact hC
  obtain ⟨hΦ, hΦU⟩ := AC.frameIn_of_callAt hr hv hpc
  have hCt : C ∈ ℓ.frame.tree := (AC.toFG_source hC').1.1
  -- the signed entry, read at the source's state
  set st := (tr₀.state v (d' + 1)).fg with hst
  have hreach := Compose.fg_reachable hrun.toLocalRun hv (d' + 1)
  have hCst : C ∈ st.tree := by
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
  -- the source is a fast-lock candidate: it is at least as high as the row
  have hCh : att.h ≤ ((tr₀.state v d').fg.σ C.root).h := by
    have := Healing.h_le_of_store_anc hreach hEC
    rw [hEh'] at this
    rwa [← hfgeq]
  obtain ⟨hCv, l, hl, hlb, hlf, -⟩ := hfast d' ℓ C (by omega) ⟨hpc, hto, hC'⟩ hCh
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  obtain ⟨r, hrd, CV, ℓw, D, hcw, hfl, L, hL, hLr, hLO⟩ :=
    Healing.stored_fast_lock_provenance hr hacr.vstart hv d' l₀ hl₀ hlf
  obtain ⟨hΦw, -⟩ := AC.frameIn_of_callAt hr hv hcw
  obtain ⟨hvat, hva⟩ := AC.viableAncestor_anc hΦ hB₀
  obtain rfl : C = ℓ.frame.viableAncestor B₀ := hU.1 (hΦU hCt) (hΦU hvat) hlb.symm
  obtain rfl : L = B₀ := hU.1 hL (hΦU hB₀) (hLr.trans hB₀r.symm)
  set O := ℓw.frame.viableAncestor D with hO
  have hCO : Anc (tr₀.HonestBlocks H₀) (ℓ.frame.viableAncestor L) O := (hva.mono hΦU).trans hLO
  have hOt : O ∈ (tr₀.state v r).fg.tree :=
    Healing.mem_tree_of_frame hrun hv hcw
      (AC.viableAncestor_anc hΦw (fastLockAt_frame_mem hfl hcw)).1
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
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
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
private theorem record_step_at {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
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
private theorem sent_origin_at {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hy : y ∈ H t) {b : FG.Content} (hb : b ∈ (tr.state y i).record.sent) :
    ∃ k < i, ∃ att, tr.SignAt y k att ∧ att.content = b := by
  obtain ⟨k, hk, att, hs, he⟩ := Healing.sent_origin_from (hrun.upTo ht0).toLocalRun hy i
    (by rw [Trace.upTo_state tr y hle]; exact hb)
  exact ⟨k, hk, att, ((RunTrace.upTo_signAt _).mp hs).2, he⟩

/-- The entry of a signature of a node honest at its signing. -/
private theorem signAt_entry_at {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) {att : FG.Att sp.n}
    (hs : tr.SignAt y k att) :
    ∃ E ∈ (tr.state y k).fg.tree, E.root = att.T ∧ ((tr.state y k).fg.σ E.root).h = att.h := by
  have h := Healing.signAt_entry (hrun.upTo (hrun.time_nonneg k)) hy
    ((RunTrace.upTo_signAt _).mpr ⟨le_rfl, hs⟩)
  rwa [RunTrace.upTo_state_of_le hrun.time_mono le_rfl] at h

/-- The finality pair of a signature of a node honest at its signing names a held entry below the
signed entry. -/
private theorem signed_fin_pair_entry_at
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
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
variable {hold : Time}

/-- **The source of a high attestation**, under growing faults. An attestation of height
`≥ H_z + 1` signed at cut `d` by a node honest at its signing and at `c_z` names the entry `E`
(at its height) of the chain of a high origin `(O, l)` written by the signer at a cut `r < d`.
The signing is before the deep quarantine ends (`hq`), so the row's high source is a fast-lock
candidate (`KernelProof.high_toFG_fast_at`). -/
theorem high_row_source_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {v : Fin sp.n} {d : Nat} (hvz : v ∈ H (max (cutZ sp.toParams g) (tr.time d)))
    {att : FG.Att sp.n}
    (hs : tr.SignAt v d att) (hh : HZ tr H g + 1 ≤ att.h)
    (hq : ∀ D, sp.deepDepth = some D → tr.time d ≤ cutZ sp.toParams g + 4 * D * sp.Δ) :
    ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧ ∃ E ∈ (tr.state v r).fg.tree,
      (tr.state v r).fg.Anc E O ∧ E.root = att.T ∧ ((tr.state v r).fg.σ E.root).h = att.h ∧
      ((tr.state v r).fg.σ E.root).Th = E.root := by
  have hrun := hp.run
  have h0 := hrun.time_nonneg d
  have hv := hrun.antitone (le_max_right _ _) hvz
  have hs' : (tr.upTo (tr.time d)).SignAt v d att := (RunTrace.upTo_signAt _).mpr ⟨le_rfl, hs⟩
  -- a source of the row before `d`, at least as high as the row, is a fast-lock candidate
  have hfast : ∀ d' ℓ C, d' < d → AC.ToFGAt (tr.upTo (tr.time d)).projAC v d' ℓ C →
      att.h ≤ (((tr.upTo (tr.time d)).state v d').fg.σ C.root).h →
      C ∈ AC.toFGCandidates sp ((tr.upTo (tr.time d)).projAC.state v d') ℓ.frame
        ((tr.upTo (tr.time d)).time d') := by
    intro d' ℓ C hd' hto hCh
    have hd't : tr.time d' ≤ tr.time d := hrun.time_mono hd'.le
    have hto' := (toFGAt_upTo_iff hrun.time_mono hd't).mp hto
    rw [RunTrace.upTo_state_of_le hrun.time_mono hd't] at hCh
    have hv' : v ∈ H (max (cutZ sp.toParams g) (tr.time d')) :=
      hrun.antitone (max_le_max le_rfl hd't) hvz
    have hc := KernelProof.high_toFG_fast_at hrun hp.noColl
      (hp.snapshot.imp fun _ h => h.1) hv' hto' (hh.trans hCh)
      (fun D hD => hd't.trans (hq D hD))
    rw [RunTrace.upTo_projAC, Trace.upTo_state tr.projAC v
      (fun _ hk => (hrun.time_mono hk.le).trans hd't),
      Compose.Growing.projAC_state_at hrun (hrun.antitone (le_max_right _ _) hv'), Trace.upTo_time]
    exact hc
  obtain ⟨r, hrd, l, O, CV, ℓw, D, hcw, hfl, rfl, hj, hOt, hOh, E, hEt, hEO, hEr, hEh, hET⟩ :=
    row_source_static (hrun.upTo h0) (hp.noColl.upTo _) hv hs' hfast
  have hrt : tr.time r ≤ tr.time d := hrun.time_mono hrd.le
  have hst : (tr.upTo (tr.time d)).state v r = tr.state v r :=
    RunTrace.upTo_state_of_le hrun.time_mono hrt
  rw [hst] at hOt hOh hEt hEO hEh hET
  have hcw' : tr.projAC.CallAt v r ℓw := by
    rw [RunTrace.upTo_projAC] at hcw
    exact ((Trace.upTo_callAt _).mp hcw).2
  have hfl' : AC.FastLockAt tr.projAC v r l D CV :=
    (fastLockAt_upTo_iff hrun.time_mono hrt).mp hfl
  have hj' : tr.JoinedAt v (tr.time r) := (joinedAt_upTo_iff hrt).mp hj
  refine ⟨r, hrd, l, _, ⟨hrun.antitone (max_le_max le_rfl hrt) hvz, hj',
    ⟨CV, ℓw, D, hcw', hfl', rfl⟩, hh.trans hOh⟩, E, hEt, hEO, hEr, hEh, hET⟩

/-- Entries at equal height below one held block agree, at a holder honest at an observation
time after its cuts. -/
private theorem entry_root_eq_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {z : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < m, tr.time q ≤ t)
    (hz : z ∈ H t) {C Z₁ Z₂ : AC.Blk sp.n (List (FG.Att sp.n))}
    (hC : C ∈ (tr.state z m).fg.tree)
    (h₁ : Anc (tr.HonestBlocksAt H) Z₁ C) (h₂ : Anc (tr.HonestBlocksAt H) Z₂ C)
    (hh : ((tr.state z m).fg.σ Z₁.root).h = ((tr.state z m).fg.σ Z₂.root).h)
    (hT₁ : ((tr.state z m).fg.σ Z₁.root).Th = Z₁.root)
    (hT₂ : ((tr.state z m).fg.σ Z₂.root).Th = Z₂.root) : Z₁.root = Z₂.root := by
  have hr := fg_reachable_at hp.run ht hle hz
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  rcases AC.anc_total hU h₁ h₂ with h | h
  · have := Healing.Th_eq_of_anc hr (store_anc_of_honest_anc_at hp.run hp.noColl ht hle hz h
      (mem_of_honest_anc_at hp.run hp.noColl ht hle hz h₂ hC)) hh.symm
    rw [← hT₁, ← hT₂, this]
  · have := Healing.Th_eq_of_anc hr (store_anc_of_honest_anc_at hp.run hp.noColl ht hle hz h
      (mem_of_honest_anc_at hp.run hp.noColl ht hle hz h₁ hC)) hh
    rw [← hT₁, ← hT₂, this]

/-- **Historical self-entries under bounded high origins agree at equal height**, each read at a
holder honest at an observation time after its cuts. -/
theorem high_entry_eq_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) {x x' : Fin sp.n}
    {i j i' j' : Nat} {B B' Z₁ Z₂ : AC.Blk sp.n (List (FG.Att sp.n))}
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
  have key : ∀ {w : Fin sp.n} {k : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))},
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
  · exact key (hp.run.antitone (le_max_right _ _) ho'.1) (highOrigin_mem_at hp.run hp.noColl ho')
      (h₁.trans hBB') h₂
  · exact key (hp.run.antitone (le_max_right _ _) ho.1) (highOrigin_mem_at hp.run hp.noColl ho) h₁
      (h₂.trans hB'B)

private theorem sourceChain_down {B C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hBC : Anc (tr.HonestBlocksAt H) B C) (hC : HighOrCovered tr H g a b C) :
    HighOrCovered tr H g a b B := by
  rw [highOrCovered_iff] at hC ⊢
  rcases hC with ⟨x, i, s, O, ho, hib, hCO⟩ | ⟨hc, hC⟩
  · exact Or.inl ⟨x, i, s, O, ho, hib, hBC.trans hCO⟩
  · obtain ⟨O, s, ho, hCO⟩ := Compose.Growing.onHealedChain_iff.mp hC
    exact Or.inr ⟨hc, Compose.Growing.onHealedChain_iff.mpr ⟨O, s, ho, hBC.trans hCO⟩⟩

private theorem sourceChain_pair {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    (B C : AC.Blk sp.n (List (FG.Att sp.n)))
    (hB : HighOrCovered tr H g a b B) (hC : HighOrCovered tr H g a b C) :
    Compatible (tr.HonestBlocksAt H) B C := by
  have hU := Compose.Growing.honestBlocksAt_coherent hp.run hp.noColl
  rw [highOrCovered_iff] at hB hC
  rcases hB with ⟨x, i, s, O, ho, hib, hBO⟩ | ⟨hc, hB⟩ <;>
    rcases hC with ⟨y, j, s', O', ho', hjb, hCO⟩ | ⟨hc', hC⟩
  · exact (Compose.Growing.compatible_of_anc_left hU hCO
      (Compose.Growing.compatible_of_anc_left hU hBO
        (hp.origins_compatible_at ho hib ho' hjb)).symm).symm
  · exact Compose.Growing.compatible_of_anc_left hU hBO
      (Compose.Growing.healed_source_compatible_highOrigin_at hp.run hp.noColl
        hc'.s1 hC hib ho).symm
  · exact (Compose.Growing.compatible_of_anc_left hU hCO
      (Compose.Growing.healed_source_compatible_highOrigin_at hp.run hp.noColl
        hc.s1 hB hjb ho').symm).symm
  · exact Compose.Growing.healed_sources_compatible_at hp.run hp.noColl hc.s1 hB hC

private theorem report_sourceChain_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {i : Nat} {ell : ACLabel (goldilocksNode sp)}
    {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hy : y ∈ H (max (cutZ sp.toParams g) (tr.time i)))
    (hr : AC.ToFGAt tr.projAC y i ell C) (hib : tr.time i ≤ b)
    (hh : HZ tr H g + 1 ≤ ((tr.state y i).fg.σ C.root).h) :
    HighOrCovered tr H g a b C := by
  exact hp.high_or_covered_at hy hr hib hh

private theorem signed_sourceChain_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} {att : FG.Att sp.n}
    (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time k))) (hs : tr.SignAt y k att)
    (hkb : tr.time k ≤ b) (hh : HZ tr H g + 1 ≤ att.h) :
    ∃ E ∈ (tr.state y k).fg.tree, HighOrCovered tr H g a b E ∧ E.root = att.T ∧
      ((tr.state y k).fg.σ E.root).h = att.h ∧ ((tr.state y k).fg.σ E.root).Th = E.root := by
  have hy := hp.run.antitone (le_max_right _ _) hyz
  obtain ⟨C, hcall⟩ := hs
  obtain ⟨i, rfl, ell, hc, hto, htime, hret, hfg⟩ := Compose.Growing.attest_source hp.run hy hcall
  have hrep : AC.ToFGAt tr.projAC y i ell C := by
    refine ⟨Compose.projAC_callAt.mpr hc, hto, ?_⟩
    rwa [Compose.Growing.projAC_state_at hp.run (htime ▸ hy)]
  have hC : C ∈ (tr.state y (i + 1)).fg.tree := by
    rw [hfg]
    exact toFG_mem_tree_at hp.run (htime ▸ hy) hrep
  have hreach := fg_reachable_at hp.run (hp.run.time_nonneg (i + 1))
    (fun _ hq => hp.run.time_mono hq.le) hy
  have hcut := (hp.run.cutLaw y (i + 1) _ hcall hy).1
  obtain ⟨hah, haT⟩ := Healing.Store.createAtt_eq hcut
  obtain ⟨⟨E, hE, hEr, hEC, hEh, hET⟩, -⟩ :=
    Store.entry_state_of_source sp.toParams (Payload sp.n) _ _ hreach _ hC
  have hEh' : ((tr.state y (i + 1)).fg.σ E.root).h = att.h := by rw [hah, hEr]
  have hET' : ((tr.state y (i + 1)).fg.σ E.root).Th = E.root := by rw [hET, hEr]
  have hEr' : E.root = att.T := by
    rw [haT]
    rw [← hEr, hET']
  have hCh := Healing.h_le_of_store_anc hreach hEC
  rw [hEh', hfg] at hCh
  have hCy := report_sourceChain_at hp (htime ▸ hyz) hrep (htime ▸ hkb) (hh.trans hCh)
  exact ⟨E, hE, sourceChain_down (honest_anc_of_store_anc_at (hp.run.time_nonneg (i + 1))
    (fun _ hq => hp.run.time_mono hq.le) hy hEC) hCy, hEr', hEh', hET'⟩

private theorem source_entry_eq_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {B B' E E' : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocksAt H) (hB' : B' ∈ tr.HonestBlocksAt H)
    (hchain : HighOrCovered tr H g a b B) (hchain' : HighOrCovered tr H g a b B')
    (hEB : Anc (tr.HonestBlocksAt H) E B) (hEB' : Anc (tr.HonestBlocksAt H) E' B')
    {y z : Fin sp.n} {i j : Nat} {t u : Time}
    (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t) (hy : y ∈ H t)
    (hu : 0 ≤ u) (hle' : ∀ q < j, tr.time q ≤ u) (hz : z ∈ H u)
    (hE : E ∈ (tr.state y i).fg.tree) (hE' : E' ∈ (tr.state z j).fg.tree)
    (hh : ((tr.state y i).fg.σ E.root).h = ((tr.state z j).fg.σ E'.root).h)
    (hT : ((tr.state y i).fg.σ E.root).Th = E.root)
    (hT' : ((tr.state z j).fg.σ E'.root).Th = E'.root) : E.root = E'.root := by
  have key : ∀ D ∈ tr.HonestBlocksAt H, Anc (tr.HonestBlocksAt H) E D →
      Anc (tr.HonestBlocksAt H) E' D → E.root = E'.root := by
    rintro D ⟨w, k, v, hv, hlev, hw, hD⟩ hED hE'D
    have e₁ := σ_eq_honest_at hp.run hp.noColl ht hle hy hv hlev hw hE
      (mem_of_honest_anc_at hp.run hp.noColl hv hlev hw hED hD)
    have e₂ := σ_eq_honest_at hp.run hp.noColl hu hle' hz hv hlev hw hE'
      (mem_of_honest_anc_at hp.run hp.noColl hv hlev hw hE'D hD)
    exact entry_root_eq_at hp hv hlev hw hD hED hE'D (by rw [← e₁, ← e₂, hh])
      (by rw [← e₁, hT]) (by rw [← e₂, hT'])
  rcases sourceChain_pair hp B B' hchain hchain' with h | h
  · exact key B' hB' (hEB.trans h) hEB'
  · exact key B hB hEB (hEB'.trans h)

/-- **A high record entry is the high-chain entry of its height**: a record of a node honest at
`t ≤ b` after its cuts and at `c_z`, with a target, timeout or lock entry at `h ≥ H_z + 1`, names
the root of every entry at `h` below a bounded high origin. -/
theorem record_entry_eq_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hyz : y ∈ H (max (cutZ sp.toParams g) t)) (htb : t ≤ b) {h r : Nat} (hh : HZ tr H g + 1 ≤ h)
    (hr : (tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h ∨
      (tr.state y i).record.lock h = some r)
    {B E : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrCovered tr H g a b B) (hB : B ∈ tr.HonestBlocksAt H)
    (hEB : Anc (tr.HonestBlocksAt H) E B) {z : Fin sp.n} {m : Nat} {u : Time} (hu : 0 ≤ u)
    (hlez : ∀ q < m, tr.time q ≤ u) (hz : z ∈ H u) (hE : E ∈ (tr.state z m).fg.tree)
    (hEh : ((tr.state z m).fg.σ E.root).h = h)
    (hET : ((tr.state z m).fg.σ E.root).Th = E.root) : r = E.root := by
  have hrun := hp.run
  have hy := hrun.antitone (le_max_right _ _) hyz
  have hU := Compose.Growing.honest_blocks_coherent hrun hp.noColl
  have leC : ∀ k : Nat, ∀ q < k, tr.time q ≤ tr.time k := fun _ _ hq => hrun.time_mono hq.le
  have target : ∀ k < i, ∀ att, tr.SignAt y k att → att.h = h → att.T = r → r = E.root := by
    intro k hki att hs hah har
    have hkt : tr.time k ≤ t := hle k hki
    have hyk := hrun.antitone hkt hy
    obtain ⟨X, hX, hchainX, hXr, hXh, hXT⟩ := signed_sourceChain_at hp
      (hrun.antitone (max_le_max le_rfl hkt) hyz) hs (hkt.trans htb) (hah ▸ hh)
    exact har.symm.trans (hXr.symm.trans (source_entry_eq_at hp
      ⟨y, k, _, hrun.time_nonneg k, leC k, hyk, hX⟩ hB hchainX ho
      .refl hEB (hrun.time_nonneg k) (leC k) hyk hu hlez hz hX hE
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
    have hle' := Healing.h_le_of_store_anc (fg_reachable_at hrun hk0 (leC k) hyk) hJX
    obtain ⟨X'', hX'', hchainX, hX''r, _, _⟩ := signed_sourceChain_at hp
      (hrun.antitone (max_le_max le_rfl hkt) hyz) hs (hkt.trans htb) (by omega)
    obtain rfl : X'' = X' := hU.1 ⟨y, k, _, hk0, leC k, hyk, hX''⟩
      ⟨y, k, _, hk0, leC k, hyk, hX⟩ (hX''r.trans hX'r.symm)
    exact hJr.symm.trans (source_entry_eq_at hp
      ⟨y, k, _, hk0, leC k, hyk, hX⟩ hB hchainX ho
      (honest_anc_of_store_anc_at hk0 (leC k) hyk hJX) hEB hk0 (leC k) hyk hu hlez hz hJ hE
      (hJh.trans hEh.symm) hJT hET)

/-- The target and timeout fields of a high entry's attestation, signed by a node honest at its
signing and at `c_z`, do not require its predecessor to be high. -/
private theorem sign_target_before_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time k)))
    {att : FG.Att sp.n}
    (hs : tr.SignAt y k att) (hkb : tr.time k ≤ b) (hh : HZ tr H g + 1 ≤ att.h)
    (he : (tr.state y k).record.timeout att.h = ∅) : att.timeout = false := by
  have leC : ∀ k : Nat, ∀ q < k, tr.time q ≤ tr.time k := fun _ _ hq => hp.run.time_mono hq.le
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw y k _ hc (hp.run.antitone (le_max_right _ _) hyz)).1
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨_, hah, haT, _, _, hτ⟩ := createAtt_fields hcl
  rw [← Bool.not_eq_true]
  intro hto
  rw [← hah, ← haT] at hτ
  rcases hτ hto with h' | ⟨T', hT', hne⟩
  · exact h' he
  · obtain ⟨E, hE, hchain, hEr, hEh, hET⟩ := signed_sourceChain_at hp hyz ⟨src, hc⟩ hkb hh
    have hy := hp.run.antitone (le_max_right _ _) hyz
    exact hne ((hp.record_entry_eq_at (hp.run.time_nonneg k) (leC k) hyz hkb hh (Or.inl hT')
      hchain ⟨y, k, _, hp.run.time_nonneg k, leC k, hy, hE⟩ .refl
      (hp.run.time_nonneg k) (leC k) hy hE hEh hET).trans hEr)

/-- A node honest at `t ≤ b`, after its cuts, and at `c_z` has no recorded timeout at a high
height. -/
private theorem timeout_empty_before_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {t : Time} (ht0 : 0 ≤ t) (hyz : y ∈ H (max (cutZ sp.toParams g) t))
    (htb : t ≤ b) :
    ∀ i, (∀ q < i, tr.time q ≤ t) → ∀ h, HZ tr H g + 1 ≤ h →
      (tr.state y i).record.timeout h = ∅
  | 0, _, h, _ => by
    rw [Trace.state, hp.run.init y (hp.run.antitone (ht0.trans (le_max_right _ _)) hyz)]; rfl
  | i + 1, hle, h, hh => by
    have hle' : ∀ q < i, tr.time q ≤ t := fun q hq => hle q (by omega)
    have hit : tr.time i ≤ t := hle i (by omega)
    have hyiz := hp.run.antitone (max_le_max le_rfl hit) hyz
    have hyi := hp.run.antitone (le_max_right _ _) hyiz
    rcases record_step_at hp.run hyi with he | ⟨att, hs, he⟩ <;> rw [he]
    · exact timeout_empty_before_at hp ht0 hyz htb i hle' h hh
    · simp only [FG.Record.recordAtt]
      split_ifs with hto
      · rw [Function.update_apply]
        split_ifs with hha
        · subst hha
          have := sign_target_before_at hp hyiz hs (hit.trans htb) hh
            (timeout_empty_before_at hp ht0 hyz htb i hle' _ hh)
          simp_all
        · exact timeout_empty_before_at hp ht0 hyz htb i hle' h hh
      · exact timeout_empty_before_at hp ht0 hyz htb i hle' h hh

/-- Finite normalization of a high signature's target and timeout fields, for a signer honest
at its signing and at `c_z`. -/
theorem row_target_of_sign_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {z : Fin sp.n} {j : Nat} (hzz : z ∈ H (max (cutZ sp.toParams g) (tr.time j)))
    {att : FG.Att sp.n}
    (hs : tr.SignAt z j att) (hjb : tr.time j ≤ b)
    {T : AC.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t) (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h)
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrCovered tr H g a b B) (hB : B ∈ tr.HonestBlocksAt H)
    (hTB : Anc (tr.HonestBlocksAt H) T B) (hatt : att.h = σT.h) :
    att.val = z ∧ att.T = T.root ∧ att.timeout = false := by
  subst hσ
  have leC : ∀ k : Nat, ∀ q < k, tr.time q ≤ tr.time k := fun _ _ hq => hp.run.time_mono hq.le
  have hh : HZ tr H g + 1 ≤ att.h := hatt ▸ hhT
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw z j _ hc (hp.run.antitone (le_max_right _ _) hzz)).1
  change (tr.state z j).record.createAtt z ((tr.state z j).fg.σ
    ((tr.state z j).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨hv, _, _, _, _, _⟩ := createAtt_fields hcl
  obtain ⟨E, hE, hchain, hEr, hEh, hET⟩ := signed_sourceChain_at hp hzz ⟨src, hc⟩ hjb hh
  have hj0 := hp.run.time_nonneg j
  have hz := hp.run.antitone (le_max_right _ _) hzz
  have hTr : att.T = T.root := hEr.symm.trans (source_entry_eq_at hp
    ⟨z, j, _, hj0, leC j, hz, hE⟩ hB hchain ho .refl hTB hj0 (leC j) hz ht hle hy hE hT
    (hEh.trans hatt) hET hTe)
  exact ⟨hv, hTr, sign_target_before_at hp hzz ⟨src, hc⟩ hjb hh
    (timeout_empty_before_at hp (hp.run.time_nonneg j) hzz hjb j (leC j) _ hh)⟩

/-- Historical signatures of a node honest at its signing and at `c_z` carry the exact
predecessor (of a height whose previous height is justified) when that predecessor is high. -/
theorem row_of_sign_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {z : Fin sp.n} {j : Nat} (hzz : z ∈ H (max (cutZ sp.toParams g) (tr.time j)))
    {att : FG.Att sp.n}
    (hs : tr.SignAt z j att) (hjb : tr.time j ≤ b)
    {T : AC.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t) (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hhj : σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj)
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrCovered tr H g a b B) (hB : B ∈ tr.HonestBlocksAt H)
    (hTB : Anc (tr.HonestBlocksAt H) T B) (hatt : att.h = σT.h) :
    att.val = z ∧ att.T = T.root ∧ att.timeout = false ∧
      (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J)) := by
  subst hσ
  have hrun := hp.run
  have hz := hrun.antitone (le_max_right _ _) hzz
  have leC : ∀ k : Nat, ∀ q < k, tr.time q ≤ tr.time k := fun _ _ hq => hrun.time_mono hq.le
  have hj0 := hrun.time_nonneg j
  have hU := Compose.Growing.honest_blocks_coherent hrun hp.noColl
  obtain ⟨hv, hTr, htimeout⟩ :=
    hp.row_target_of_sign_at hzz hs hjb ht hle hy hT rfl hTe hhT ho hB hTB hatt
  obtain ⟨src, hc⟩ := hs
  have hcl := (hrun.cutLaw z j _ hc hz).1
  change (tr.state z j).record.createAtt z ((tr.state z j).fg.σ
    ((tr.state z j).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨_, _, haT, hfin, _, _⟩ := createAtt_fields hcl
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
  have heq := fun r hr => (hp.record_entry_eq_at hj0 (leC j) hzz hjb (hhj hb) (i := j) (r := r)
    hr ho hB ((honest_anc_of_store_anc_at ht hle hy hJ₀T).trans hTB) ht hle hy hJ₀ hJ₀h
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

/-- A bounded same-height report of a node honest at the report and at `c_z` supplies a signature
of it by the report's time, including the case where previously signed content suppresses the
call. -/
theorem sign_of_report_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {z : Fin sp.n} {r : Nat} (hzz : z ∈ H (max (cutZ sp.toParams g) (tr.time r)))
    {ell : ACLabel (goldilocksNode sp)} {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrep : AC.ToFGAt tr.projAC z r ell C) (hrb : tr.time r ≤ b)
    {T : AC.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t) (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hTC : Anc (tr.HonestBlocksAt H) T C)
    (hCh : ((tr.state z r).fg.σ C.root).h = σT.h)
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrCovered tr H g a b B) (hB : B ∈ tr.HonestBlocksAt H)
    (hTB : Anc (tr.HonestBlocksAt H) T B) :
    ∃ j att, tr.SignAt z j att ∧ tr.time j ≤ tr.time r ∧ att.h = σT.h := by
  subst hσ
  have hrun := hp.run
  have hnc := hp.noColl
  have hz := hrun.antitone (le_max_right _ _) hzz
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
    exact ⟨r + 1, att, ⟨C, hs'⟩, hts'.le, by rw [(createAtt_fields hcl).2.1, hσe]⟩
  | none =>
    have hcl := (hrun.cutLaw z _ _ hs' hz1).1
    change (tr.state z (r + 1)).record.createAtt z ((tr.state z (r + 1)).fg.σ
      ((tr.state z (r + 1)).fg.σ C.root).Th) = none at hcl
    rw [hσe] at hcl
    rcases createAtt_refused hcl with ⟨hl, hl'⟩ | ⟨c, hc, _⟩
    · obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists'.1 hl
      have := hp.record_entry_eq_at h0 leR1 hzz hrb hhT (Or.inr (Or.inr hr'))
        ho hB hTB ht hle hy hT rfl hTe
      exact absurd (by rw [hr', this, hTe]) hl'
    · obtain ⟨k, hk, att, hsk, rfl⟩ := sent_origin_at hrun h0 leR1 hz hc
      exact ⟨k, att, hsk, (hrun.time_mono hk.le).trans hts'.le, by assumption⟩

/-- A bounded same-height report of a node honest at the report and at `c_z` supplies the exact
entry attestation, with historical finality permission checked at the actual signing cut. -/
theorem row_of_report_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {z : Fin sp.n} {r : Nat} (hzz : z ∈ H (max (cutZ sp.toParams g) (tr.time r)))
    {ell : ACLabel (goldilocksNode sp)} {C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hrep : AC.ToFGAt tr.projAC z r ell C) (hrb : tr.time r ≤ b)
    {T : AC.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t) (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hhj : σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj)
    (hTC : Anc (tr.HonestBlocksAt H) T C)
    (hCh : ((tr.state z r).fg.σ C.root).h = σT.h) :
    ∃ j att, tr.SignAt z j att ∧ tr.time j ≤ tr.time r ∧ att.val = z ∧
      att.h = σT.h ∧ att.T = T.root ∧ att.timeout = false ∧
      (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J)) := by
  have ho := hp.high_or_covered_at hzz hrep hrb (by rw [hCh]; exact hhT)
  have hC : C ∈ tr.HonestBlocksAt H := ⟨z, r, _, hp.run.time_nonneg r,
    (fun _ hq => hp.run.time_mono hq.le), hp.run.antitone (le_max_right _ _) hzz,
    toFG_mem_tree_at hp.run (hp.run.antitone (le_max_right _ _) hzz) hrep⟩
  obtain ⟨j, att, hs, htj, hh⟩ :=
    hp.sign_of_report_at hzz hrep hrb ht hle hy hT hσ hTe hhT hTC hCh ho hC hTC
  obtain ⟨hv, hroot, htimeout, hfin⟩ :=
    hp.row_of_sign_at (hp.run.antitone (max_le_max le_rfl htj) hzz) hs
    (htj.trans hrb) ht hle hy hT hσ hTe hhT hhj ho hC hTC hh
  exact ⟨j, att, hs, htj, hv, hh, hroot, htimeout, hfin⟩

/-- Same-height reports, by `d`, from every node honest at `d` and at `c_z` yield a quorum of
nodes honest at a later `e ∈ [d, b]` and at `c_z` with exact entry signatures by `d`. The fault
bound at `e` gives the quorum. Historical reports count without any freshness assumption. -/
theorem row_signers_of_reports_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {T : AC.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t) (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hhj : σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj)
    {d e : Time} (hd : 0 ≤ d) (hde : d ≤ e) (heb : e ≤ b)
    (hreports : ∀ z, z ∈ H (max (cutZ sp.toParams g) d) → ∃ r ell C, AC.ToFGAt tr.projAC z r ell C ∧
      tr.time r ≤ d ∧ Anc (tr.HonestBlocksAt H) T C ∧ ((tr.state z r).fg.σ C.root).h = σT.h) :
    ∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
      ∀ z ∈ ids, z ∈ H (max (cutZ sp.toParams g) e) ∧ ∃ att j, tr.SignAt z j att ∧ att.val = z ∧
        att.h = σT.h ∧ att.T = T.root ∧ att.timeout = false ∧ tr.time j ≤ d ∧
        (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J)) := by
  classical
  let d' := max (cutZ sp.toParams g) e
  refine ⟨Finset.univ.filter (· ∈ H d'), ?_, ?_⟩
  · have hcard : (Finset.univ.filter (· ∈ H d')).card = (H d').ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext z
      simp
    rw [hcard]
    have hn : (H d').ncard + (H d')ᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    obtain ⟨j, hj, hjb⟩ := hp.snapshot
    have hf := hp.faults d' ((hd.trans hde).trans (le_max_right _ _))
      (max_le (hj.2.le.trans hjb) heb)
    change (2 * sp.n + 2) / 3 ≤ _
    omega
  · intro z hz
    have hzH := (Finset.mem_filter.1 hz).2
    obtain ⟨r, ell, C, hr, hrd, hTC, hh⟩ :=
      hreports z (hp.run.antitone (max_le_max le_rfl hde) hzH)
    obtain ⟨j, att, hs, htj, hv, hah, hroot, htimeout, hfin⟩ :=
      hp.row_of_report_at (hp.run.antitone (max_le_max le_rfl (hrd.trans hde)) hzH) hr
        ((hrd.trans hde).trans heb) ht
        hle hy hT hσ hTe hhT hhj hTC hh
    exact ⟨hzH, att, j, hs, hv, hah, hroot, htimeout, htj.trans hrd, hfin⟩

/-! ## Explicit post-drain source and compatibility premises

These consumers sit below Continuation. Their source and compatibility premises are discharged
above that layer, so they do not import the healed-frontier bridge or reconstruct a fast lock.
-/

/-- Transport a report cover to the signed self-entry at the following cut. The cover only
needs to be closed under ancestry; in particular it may include slow-lock healed members. -/
private theorem signed_entry_of_report_cover_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {chain : AC.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hdown : ∀ B C, Anc (tr.HonestBlocksAt H) B C → chain C → chain B)
    (hcover : ∀ y i ell C, y ∈ H (max (cutZ sp.toParams g) (tr.time i)) →
      AC.ToFGAt tr.projAC y i ell C → tr.time i ≤ b →
      HZ tr H g + 1 ≤ ((tr.state y i).fg.σ C.root).h → chain C)
    {y : Fin sp.n} {k : Nat} {att : FG.Att sp.n}
    (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time k))) (hs : tr.SignAt y k att)
    (hkb : tr.time k ≤ b) (hh : HZ tr H g + 1 ≤ att.h) :
    ∃ E ∈ (tr.state y k).fg.tree, chain E ∧ E.root = att.T ∧
      ((tr.state y k).fg.σ E.root).h = att.h ∧ ((tr.state y k).fg.σ E.root).Th = E.root := by
  have hy := hp.run.antitone (le_max_right _ _) hyz
  obtain ⟨C, hcall⟩ := hs
  obtain ⟨i, rfl, ell, hc, hto, htime, hret, hfg⟩ := Compose.Growing.attest_source hp.run hy hcall
  have hrep : AC.ToFGAt tr.projAC y i ell C := by
    refine ⟨Compose.projAC_callAt.mpr hc, hto, ?_⟩
    rwa [Compose.Growing.projAC_state_at hp.run (htime ▸ hy)]
  have hC : C ∈ (tr.state y (i + 1)).fg.tree := by
    rw [hfg]
    exact toFG_mem_tree_at hp.run (htime ▸ hy) hrep
  have hreach := fg_reachable_at hp.run (hp.run.time_nonneg (i + 1))
    (fun _ hq => hp.run.time_mono hq.le) hy
  have hcut := (hp.run.cutLaw y (i + 1) _ hcall hy).1
  obtain ⟨hah, haT⟩ := Healing.Store.createAtt_eq hcut
  obtain ⟨⟨E, hE, hEr, hEC, hEh, hET⟩, -⟩ :=
    Store.entry_state_of_source sp.toParams (Payload sp.n) _ _ hreach _ hC
  have hEh' : ((tr.state y (i + 1)).fg.σ E.root).h = att.h := by rw [hah, hEr]
  have hET' : ((tr.state y (i + 1)).fg.σ E.root).Th = E.root := by rw [hET, hEr]
  have hEr' : E.root = att.T := by
    rw [haT]
    rw [← hEr, hET']
  have hCh := Healing.h_le_of_store_anc hreach hEC
  rw [hEh', hfg] at hCh
  have hCy := hcover y i ell C (htime ▸ hyz) hrep (htime ▸ hkb) (hh.trans hCh)
  exact ⟨E, hE, hdown E C (honest_anc_of_store_anc_at (hp.run.time_nonneg (i + 1))
    (fun _ hq => hp.run.time_mono hq.le) hy hEC) hCy, hEr', hEh', hET'⟩

/-- Equal-height self-entries below compatible held blocks agree. The covering blocks need
not have fast-lock provenance. -/
private theorem entry_eq_of_compatible_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {B B' E E' : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocksAt H) (hB' : B' ∈ tr.HonestBlocksAt H)
    (hcomp : Compatible (tr.HonestBlocksAt H) B B')
    (hEB : Anc (tr.HonestBlocksAt H) E B) (hEB' : Anc (tr.HonestBlocksAt H) E' B')
    {y z : Fin sp.n} {i j : Nat} {t u : Time}
    (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t) (hy : y ∈ H t)
    (hu : 0 ≤ u) (hle' : ∀ q < j, tr.time q ≤ u) (hz : z ∈ H u)
    (hE : E ∈ (tr.state y i).fg.tree) (hE' : E' ∈ (tr.state z j).fg.tree)
    (hh : ((tr.state y i).fg.σ E.root).h = ((tr.state z j).fg.σ E'.root).h)
    (hT : ((tr.state y i).fg.σ E.root).Th = E.root)
    (hT' : ((tr.state z j).fg.σ E'.root).Th = E'.root) : E.root = E'.root := by
  have key : ∀ D ∈ tr.HonestBlocksAt H, Anc (tr.HonestBlocksAt H) E D →
      Anc (tr.HonestBlocksAt H) E' D → E.root = E'.root := by
    rintro D ⟨w, k, v, hv, hlev, hw, hD⟩ hED hE'D
    have e₁ := σ_eq_honest_at hp.run hp.noColl ht hle hy hv hlev hw hE
      (mem_of_honest_anc_at hp.run hp.noColl hv hlev hw hED hD)
    have e₂ := σ_eq_honest_at hp.run hp.noColl hu hle' hz hv hlev hw hE'
      (mem_of_honest_anc_at hp.run hp.noColl hv hlev hw hE'D hD)
    exact entry_root_eq_at hp hv hlev hw hD hED hE'D (by rw [← e₁, ← e₂, hh])
      (by rw [← e₁, hT]) (by rw [← e₂, hT'])
  rcases hcomp with h | h
  · exact key B' hB' (hEB.trans h) hEB'
  · exact key B hB hEB (hEB'.trans h)

/-- The record consumer with an explicit source cover and pairwise compatibility. In the
healed application `chain` is `OnHealedChain`, source cover comes from the post-drain reports,
and pairwise compatibility is S1. -/
private theorem record_entry_eq_of_sources_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {chain : AC.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hpair : ∀ B B', chain B → chain B' → Compatible (tr.HonestBlocksAt H) B B')
    (hsource : ∀ y k att, y ∈ H (max (cutZ sp.toParams g) (tr.time k)) →
      tr.SignAt y k att → tr.time k ≤ b → HZ tr H g + 1 ≤ att.h →
      ∃ E ∈ (tr.state y k).fg.tree, chain E ∧ E.root = att.T ∧
        ((tr.state y k).fg.σ E.root).h = att.h ∧ ((tr.state y k).fg.σ E.root).Th = E.root)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht0 : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hyz : y ∈ H (max (cutZ sp.toParams g) t)) (htb : t ≤ b)
    {h r : Nat} (hh : HZ tr H g + 1 ≤ h)
    (hr : (tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h ∨
      (tr.state y i).record.lock h = some r)
    {B E : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ tr.HonestBlocksAt H) (hchain : chain B)
    (hEB : Anc (tr.HonestBlocksAt H) E B) {z : Fin sp.n} {m : Nat} {u : Time}
    (hu : 0 ≤ u) (hlez : ∀ q < m, tr.time q ≤ u) (hz : z ∈ H u)
    (hE : E ∈ (tr.state z m).fg.tree) (hEh : ((tr.state z m).fg.σ E.root).h = h)
    (hET : ((tr.state z m).fg.σ E.root).Th = E.root) : r = E.root := by
  have hrun := hp.run
  have hy := hrun.antitone (le_max_right _ _) hyz
  have leC : ∀ k : Nat, ∀ q < k, tr.time q ≤ tr.time k := fun _ _ hq => hrun.time_mono hq.le
  have target : ∀ k < i, ∀ att, tr.SignAt y k att → att.h = h → att.T = r → r = E.root := by
    intro k hki att hs hah har
    have hkt := hle k hki
    have hyk := hrun.antitone hkt hy
    obtain ⟨X, hX, hchainX, hXr, hXh, hXT⟩ := hsource y k att
      (hrun.antitone (max_le_max le_rfl hkt) hyz) hs (hkt.trans htb) (hah ▸ hh)
    exact har.symm.trans (hXr.symm.trans (entry_eq_of_compatible_at hp
      ⟨y, k, _, hrun.time_nonneg k, leC k, hyk, hX⟩ hB (hpair X B hchainX hchain)
      .refl hEB (hrun.time_nonneg k) (leC k) hyk hu hlez hz hX hE
      (hXh.trans (hah.trans hEh.symm)) hXT hET))
  have horig := client_record_origin_at hrun ht0 hle hy h r
  rcases hr with ht | ht | hl
  · obtain ⟨k, hki, att, hs, hah, har⟩ := horig.1 (Or.inl ht)
    exact target k hki att hs hah har
  · obtain ⟨k, hki, att, hs, hah, har⟩ := horig.1 (Or.inr ht)
    exact target k hki att hs hah har
  · obtain ⟨k, hki, att, hs, hfin⟩ := horig.2 hl
    have hkt := hle k hki
    have hyk := hrun.antitone hkt hy
    have hk0 := hrun.time_nonneg k
    obtain ⟨J, hJ, X, hX, hXr, hJX, hJr, hJh, hJT⟩ := signed_fin_pair_entry_at hrun hyk hs hfin
    obtain ⟨X', hX', hX'r, hX'h⟩ := signAt_entry_at hrun hyk hs
    have hU := Compose.Growing.honest_blocks_coherent hrun hp.noColl
    obtain rfl : X' = X := hU.1 ⟨y, k, _, hk0, leC k, hyk, hX'⟩
      ⟨y, k, _, hk0, leC k, hyk, hX⟩ (hX'r.trans hXr.symm)
    have hle' := Healing.h_le_of_store_anc (fg_reachable_at hrun hk0 (leC k) hyk) hJX
    obtain ⟨X'', hX'', hchainX, hX''r, _, _⟩ := hsource y k att
      (hrun.antitone (max_le_max le_rfl hkt) hyz) hs (hkt.trans htb) (by omega)
    obtain rfl : X'' = X' := hU.1 ⟨y, k, _, hk0, leC k, hyk, hX''⟩
      ⟨y, k, _, hk0, leC k, hyk, hX⟩ (hX''r.trans hX'r.symm)
    exact hJr.symm.trans (entry_eq_of_compatible_at hp
      ⟨y, k, _, hk0, leC k, hyk, hX⟩ hB (hpair _ B hchainX hchain)
      (honest_anc_of_store_anc_at hk0 (leC k) hyk hJX) hEB hk0 (leC k) hyk hu hlez hz hJ hE
      (hJh.trans hEh.symm) hJT hET)

section SourceConsumers

variable {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
  (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
  {chain : AC.Blk sp.n (List (FG.Att sp.n)) → Prop}
  (hpair : ∀ B B', chain B → chain B' → Compatible (tr.HonestBlocksAt H) B B')
  (hsource : ∀ y k att, y ∈ H (max (cutZ sp.toParams g) (tr.time k)) →
    tr.SignAt y k att → tr.time k ≤ b → HZ tr H g + 1 ≤ att.h →
    ∃ E ∈ (tr.state y k).fg.tree, chain E ∧ E.root = att.T ∧
      ((tr.state y k).fg.σ E.root).h = att.h ∧ ((tr.state y k).fg.σ E.root).Th = E.root)

include hp hpair hsource

private theorem sign_target_of_sources_at
    {y : Fin sp.n} {k : Nat} (hyz : y ∈ H (max (cutZ sp.toParams g) (tr.time k)))
    {att : FG.Att sp.n} (hs : tr.SignAt y k att) (hkb : tr.time k ≤ b)
    (hh : HZ tr H g + 1 ≤ att.h) (he : (tr.state y k).record.timeout att.h = ∅) :
    att.timeout = false := by
  have hk0 := hp.run.time_nonneg k
  have hy := hp.run.antitone (le_max_right _ _) hyz
  have leC : ∀ q < k, tr.time q ≤ tr.time k := fun _ hq => hp.run.time_mono hq.le
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw y k _ hc hy).1
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨_, hah, haT, _, _, hτ⟩ := createAtt_fields hcl
  rw [← Bool.not_eq_true]
  intro hto
  rw [← hah, ← haT] at hτ
  rcases hτ hto with h' | ⟨T', hT', hne⟩
  · exact h' he
  · obtain ⟨E, hE, hchain, hEr, hEh, hET⟩ := hsource y k att hyz ⟨src, hc⟩ hkb hh
    exact hne ((record_entry_eq_of_sources_at hp hpair hsource hk0 leC hyz hkb hh
      (Or.inl hT') ⟨y, k, _, hk0, leC, hy, hE⟩ hchain .refl hk0 leC hy hE hEh hET).trans hEr)

private theorem timeout_empty_of_sources_at
    {y : Fin sp.n} {t : Time} (ht0 : 0 ≤ t) (hyz : y ∈ H (max (cutZ sp.toParams g) t))
    (htb : t ≤ b) :
    ∀ i, (∀ q < i, tr.time q ≤ t) → ∀ h, HZ tr H g + 1 ≤ h →
      (tr.state y i).record.timeout h = ∅
  | 0, _, h, _ => by
    rw [Trace.state, hp.run.init y (hp.run.antitone (ht0.trans (le_max_right _ _)) hyz)]; rfl
  | i + 1, hle, h, hh => by
    have hle' : ∀ q < i, tr.time q ≤ t := fun q hq => hle q (by omega)
    have hit : tr.time i ≤ t := hle i (by omega)
    have hyiz := hp.run.antitone (max_le_max le_rfl hit) hyz
    have hyi := hp.run.antitone (le_max_right _ _) hyiz
    rcases record_step_at hp.run hyi with he | ⟨att, hs, he⟩ <;> rw [he]
    · exact timeout_empty_of_sources_at ht0 hyz htb i hle' h hh
    · simp only [FG.Record.recordAtt]
      split_ifs with hto
      · rw [Function.update_apply]
        split_ifs with hha
        · subst hha
          have := sign_target_of_sources_at hp hpair hsource hyiz hs (hit.trans htb) hh
            (timeout_empty_of_sources_at ht0 hyz htb i hle' _ hh)
          simp_all
        · exact timeout_empty_of_sources_at ht0 hyz htb i hle' h hh
      · exact timeout_empty_of_sources_at ht0 hyz htb i hle' h hh

/-- Normalize a signature against a compatible source family, including the healed family. -/
private theorem row_target_of_sources_at
    {z : Fin sp.n} {j : Nat} (hzz : z ∈ H (max (cutZ sp.toParams g) (tr.time j)))
    {att : FG.Att sp.n} (hs : tr.SignAt z j att) (hjb : tr.time j ≤ b)
    {T B : AC.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t)
    (hT : T ∈ (tr.state y m).fg.tree) {σT : FG.ChainState sp.n}
    (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hB : B ∈ tr.HonestBlocksAt H) (hchain : chain B)
    (hTB : Anc (tr.HonestBlocksAt H) T B) (hatt : att.h = σT.h) :
    att.val = z ∧ att.T = T.root ∧ att.timeout = false := by
  subst hσ
  have hj0 := hp.run.time_nonneg j
  have hz := hp.run.antitone (le_max_right _ _) hzz
  have leC : ∀ q < j, tr.time q ≤ tr.time j := fun _ hq => hp.run.time_mono hq.le
  have hh : HZ tr H g + 1 ≤ att.h := hatt ▸ hhT
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw z j _ hc hz).1
  change (tr.state z j).record.createAtt z ((tr.state z j).fg.σ
    ((tr.state z j).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨hv, _, _, _, _, _⟩ := createAtt_fields hcl
  obtain ⟨E, hE, hchainE, hEr, hEh, hET⟩ := hsource z j att hzz ⟨src, hc⟩ hjb hh
  have hTr : att.T = T.root := hEr.symm.trans (entry_eq_of_compatible_at hp
    ⟨z, j, _, hj0, leC, hz, hE⟩ hB (hpair E B hchainE hchain) .refl hTB
    hj0 leC hz ht hle hy hE hT (hEh.trans hatt) hET hTe)
  exact ⟨hv, hTr, sign_target_of_sources_at hp hpair hsource hzz ⟨src, hc⟩ hjb hh
    (timeout_empty_of_sources_at hp hpair hsource hj0 hzz hjb j leC _ hh)⟩

/-- Exact finality permission from the compatible source family, including historical lock
entries below the current signed entry. -/
private theorem row_of_sources_at
    {z : Fin sp.n} {j : Nat} (hzz : z ∈ H (max (cutZ sp.toParams g) (tr.time j)))
    {att : FG.Att sp.n} (hs : tr.SignAt z j att) (hjb : tr.time j ≤ b)
    {T B : AC.Blk sp.n (List (FG.Att sp.n))} {y : Fin sp.n} {m : Nat} {t : Time}
    (ht : 0 ≤ t) (hle : ∀ q < m, tr.time q ≤ t) (hy : y ∈ H t)
    (hT : T ∈ (tr.state y m).fg.tree) {σT : FG.ChainState sp.n}
    (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hhj : σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj)
    (hB : B ∈ tr.HonestBlocksAt H) (hchain : chain B)
    (hTB : Anc (tr.HonestBlocksAt H) T B) (hatt : att.h = σT.h) :
    att.val = z ∧ att.T = T.root ∧ att.timeout = false ∧
      (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J)) := by
  subst hσ
  have hz := hp.run.antitone (le_max_right _ _) hzz
  have hj0 := hp.run.time_nonneg j
  have leC : ∀ q < j, tr.time q ≤ tr.time j := fun _ hq => hp.run.time_mono hq.le
  obtain ⟨hv, hTr, htimeout⟩ := row_target_of_sources_at hp hpair hsource hzz hs hjb ht hle hy
    hT rfl hTe hhT hB hchain hTB hatt
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw z j _ hc hz).1
  change (tr.state z j).record.createAtt z ((tr.state z j).fg.σ
    ((tr.state z j).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨_, _, haT, hfin, _, _⟩ := createAtt_fields hcl
  refine ⟨hv, hTr, htimeout, fun hb => ?_⟩
  obtain ⟨E', hE', hE'r, hE'T⟩ := source_entry (fg_reachable_at hp.run hj0 leC hz) src
  have hR : ((tr.state z j).fg.σ src.root).Th = T.root := by
    rw [← hTr, haT, ← hE'r, hE'T]
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have he : E' = T := hU.1 ⟨z, j, _, hj0, leC, hz, hE'⟩ ⟨y, m, t, ht, hle, hy, hT⟩
    (hE'r.trans hR)
  rw [he] at hE'
  rw [hfin, hR, σ_eq_honest_at hp.run hp.noColl hj0 leC hz ht hle hy hE' hT]
  obtain ⟨J₀, hJ₀, hJ₀T, hJ₀r, hJ₀h, hJ₀T'⟩ :=
    (Healing.chain_pairs_entry (fg_reachable_at hp.run ht hle hy) hT).1 hb.1
  have heq := fun r hr => (record_entry_eq_of_sources_at hp hpair hsource hj0 leC hzz hjb
    (hhj hb) (i := j) (r := r) hr hB hchain
    ((honest_anc_of_store_anc_at ht hle hy hJ₀T).trans hTB) ht hle hy hJ₀ hJ₀h hJ₀T').trans hJ₀r
  have hperm : (tr.state z j).record.permits ((tr.state y m).fg.σ T.root).hj
      ((tr.state y m).fg.σ T.root).J := by
    refine ⟨?_, fun r hr => Finset.mem_singleton.2 (heq r (Or.inr (Or.inl hr))), ?_⟩
    · rcases ht' : (tr.state z j).record.target _ with _ | r
      exacts [Or.inl rfl, Or.inr (by rw [heq r (Or.inl ht')])]
    · rcases hl : (tr.state z j).record.lock _ with _ | r
      exacts [Or.inl rfl, Or.inr (by rw [heq r (Or.inr (Or.inr hl))])]
  unfold FG.Record.finalityPair
  simp only [hb, hperm, ↓reduceIte]

end SourceConsumers

end ResetPremisesUpTo

end Consensus.Goldilocks.Healing.Growing

end

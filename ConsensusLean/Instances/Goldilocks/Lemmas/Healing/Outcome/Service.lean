module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Settle
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Outcome
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Source
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion

public section

/-! # Goldilocks Healing: building blocks of C1.2, AC outcome service for honest entries

Proved pieces toward C1.2 (`Compose.OutcomeService`, claims C1.2 at goldilocks `6703bf05`),
following fradamt-agent/workbench `producer-reset-continuation.md` §17, §18 (BA) and §26. C1.2
itself is not proved here.

* **Entry rows** (`EntryRows`): for a served entry `E = (h, T, u)`, by `t_u + 6Δ` either honest
  validators of weight `q` have signed a target row for `E`, or an honest accepted block has
  justified `E` (the retained justified crossing).
* **Rows from reports** (workbench#30): the actual reports and their high origins
  (`high_report_origin`), the honest records (`high_entry_eq`, `record_entry_eq`), the rows from
  signatures and reports (`row_target_of_sign`, `row_of_sign`, `sign_of_report`) and their finite
  forms through a horizon (`ResetPremisesUpTo.row_of_report`,
  `ResetPremisesUpTo.row_signers_of_reports`).
* **The carriers**: acceptance relay reaches only the honest nodes whose `Σ.F` the carrier
  extends; a carrier below a high origin is held or above every honest `Σ.F`
  (`carrier_below_origin_before`), since HR.4 (R2) makes every honest `Σ.F` compatible with the
  origin; a higher report above an honest ready proposal lies below a high origin
  (`higher_report_window_origin_before`).
* **The finite reset service adapter**: Catch and Sync windows at the actual reset
  (`catch_window_at_reset_of_reset_catch_before`, `sync_window_at_reset_of_reset_before`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-! ## FG traces: pools, ancestry and justifications across honest stores -/

section FGTraces

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
  {tr : FGTrace P ACP}

private theorem mem_onAttestation {st : Store P ACP} {a b : FG.Att P.n}
    (h : a ∈ st.atts ∨ a = b) : a ∈ (st.onAttestation b).atts := by
  unfold Store.onAttestation
  split_ifs with hb
  · rcases h with h | rfl
    exacts [h, hb]
  · rcases h with h | rfl
    · simp [h]
    · simp

private theorem mem_addAtts {a : FG.Att P.n} :
    ∀ (l : List (FG.Att P.n)) (st : Store P ACP), a ∈ st.atts ∨ a ∈ l → a ∈ (st.addAtts l).atts
  | [], _, h => h.resolve_right List.not_mem_nil
  | b :: l, st, h => by
    rw [Store.addAtts, List.foldl_cons, ← Store.addAtts]
    refine mem_addAtts l _ ?_
    rcases h with h | h
    · exact Or.inl (mem_onAttestation (Or.inl h))
    · rcases List.mem_cons.1 h with rfl | h
      exacts [Or.inl (mem_onAttestation (Or.inr rfl)), Or.inr h]

/-- The pool of an honest node only grows. -/
private theorem pool_mono (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {k m : Nat}
    (hkm : k ≤ m) : (tr.store y k).atts ⊆ (tr.store y m).atts := by
  induction m, hkm using Nat.le_induction with
  | base => exact fun _ h => h
  | succ m _ ih =>
    intro a ha
    have ha := ih ha
    rcases Store.store_step hr hy m with he | ⟨B, -, hB⟩ | ⟨b, -, he⟩
    · rwa [he]
    · obtain ⟨pr, σ', -, -, -, -, -, he⟩ := Store.onBlock_eq_some hB
      rw [he]
      refine mem_addAtts _ _ (Or.inl ?_)
      rw [(Store.updateFinality_spec _ _).2.2.1]
      exact ha
    · rw [he]
      exact mem_onAttestation (Or.inl ha)

/-- A block of `U` whose root an honest held block names as its parent is held. -/
private theorem parent_mem (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {B Y : NodeBlock P ACP} (hB : B ∈ (tr.store y i).tree) (hY : Y ∈ U)
    (hp : B.parent = some Y.root) : Y ∈ (tr.store y i).tree := by
  rcases ((Store.accepted_tree P ACP acp₀ _ (Store.store_reachable hr hy i)).2.2.2 B
    hB).cases_tail with rfl | ⟨Z, -, hZ, -, hZp⟩
  · exact absurd hp (by simp [Params.genesisBlock])
  · obtain rfl : Z = Y := hr.coherent.1 (hr.tree_subset y hy i hZ) hY
      (Option.some.inj (hZp.symm.trans hp))
    exact hZ

/-- Ancestry inside `U` ending at an honest held block is ancestry in that store. -/
private theorem store_anc (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {A B : NodeBlock P ACP} (h : Anc U A B) (hB : B ∈ (tr.store y i).tree) :
    (tr.store y i).Anc A B := by
  induction h with
  | refl => exact .refl
  | tail _ hYB ih =>
    have hY := parent_mem hr hy hB hYB.1 hYB.2.2
    exact (ih hY).tail ⟨hY, hB, hYB.2.2⟩

/-- Ancestors of a held block are held. -/
private theorem mem_of_anc {st : Store P ACP} {A B : NodeBlock P ACP} (h : st.Anc A B)
    (hB : B ∈ st.tree) : A ∈ st.tree := by
  induction h with
  | refl => exact hB
  | tail _ hp ih => exact ih hp.1

/-- Ancestry at one honest store holds at another that holds the descendant. -/
private theorem anc_transfer (hr : FGLocalRun acp₀ H U tr) {y z : Fin P.n} (hy : y ∈ H)
    (hz : z ∈ H) {i j : Nat} {A B : NodeBlock P ACP} (h : (tr.store y i).Anc A B)
    (hB : B ∈ (tr.store z j).tree) : (tr.store z j).Anc A B :=
  store_anc hr hz (h.mono (hr.tree_subset y hy i)) hB

end FGTraces

/-! ## The first crossing of an entry before its timeout (workbench#30 §5)

As `Lemmas/FGStore/Window.lean` (`events_current`, `entry_facts`), at a reachable store. -/

section Walk

variable {P : Params} {ACP : Type} {acp₀ : ACP}

/-- The block named by a source's `T_h` is held and is the entry of its own state. -/
private theorem source_entry {st : Store P ACP} (hr : st.Reachable acp₀) (src : NodeBlock P ACP) :
    ∃ E ∈ st.tree, E.root = (st.σ src.root).Th ∧ (st.σ E.root).Th = E.root := by
  rcases hs : st.blocks src.root with _ | X
  · have hg : (st.σ src.root).Th = P.genesisRoot := by rw [Store.σ_of_blocks_none hr hs]; rfl
    refine ⟨_, Store.genesis_mem hr, hg.symm, ?_⟩
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, Store.σ_genesis hr]; rfl
  · have hXr : X.root = src.root := Goldilocks.Store.Reachable.blocks_root hr hs
    have hX : X ∈ st.tree := by change st.blocks X.root = some X; rw [hXr]; exact hs
    obtain ⟨⟨E, hE, hEr, -, -, hET⟩, -⟩ := Store.entry_state_of_source P ACP acp₀ _ hr X hX
    rw [← hXr]
    exact ⟨E, hE, hEr, hET.trans hEr.symm⟩

end Walk

/-! ## The honest client's records (workbench#30 §4) -/

section Client

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
  obtain ⟨rfl, rfl⟩ := Store.heightPair_eq hp
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
  · obtain ⟨rfl, -⟩ := Store.heightPair_eq hp
    dsimp only at h
    split_ifs at h with hany
    obtain ⟨b, hb, hb'⟩ := List.any_eq_true.1 hany
    exact Or.inr ⟨b, hb, (of_decide_eq_true hb').1⟩

end Client

/-! ## Runs: deadlines and the relay of a carrier -/

section Runs

variable {P : Params} {A : NodeAC P} {tr : RunTrace A}

private theorem lastWake_coe {y : Fin P.n} {w : Time} :
    ∀ {c : Nat}, tr.lastWake y c = (w : WithBot Time) → ∃ k ≤ c, tr.RestartAt y k ∧ tr.time k = w
  | 0, h => by
    unfold RunTrace.lastWake at h
    split_ifs at h with hr
    · exact ⟨0, le_rfl, hr, WithBot.coe_injective h⟩
    · simp at h
  | c + 1, h => by
    unfold RunTrace.lastWake at h
    split_ifs at h with hr
    · exact ⟨c + 1, le_rfl, hr, WithBot.coe_injective h⟩
    · obtain ⟨k, hk, h'⟩ := lastWake_coe h
      exact ⟨k, hk.trans (Nat.le_succ c), h'⟩

/-- With every restart of `y` at or before `a`, the deadline of `τ` is at most `max(τ, a) + Δ'`. -/
private theorem deadline_le {y : Fin P.n} {c : Nat} {a : Time}
    (h : ∀ k, tr.RestartAt y k → tr.time k ≤ a) (τ Δ' : Time) :
    tr.deadline y c τ Δ' ≤ max τ a + Δ' := by
  unfold RunTrace.deadline
  rcases hw : tr.lastWake y c with _ | w
  · change τ + Δ' ≤ max τ a + Δ'
    linarith [le_max_left τ a]
  · obtain ⟨k, -, hrk, rfl⟩ := lastWake_coe hw
    change max τ (tr.time k) + Δ' ≤ max τ a + Δ'
    linarith [max_le_max (le_refl τ) (h k hrk)]

end Runs

variable {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n}
  {tr : GoldilocksTrace sp ro} {g ΔF Gp a : Time} {cF kF : Nat}

/-! ## The actual reports (workbench#30 §3) -/

/-- A block that `ac_to_fg` returns is a candidate (as in `Retention/Rows`). -/
private theorem mem_toFGCandidates {FGP : Type} {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP}
    {t : Time} {C : SA.Blk sp.n FGP} (h : (SA.acToFG sp A Φ t).2 = some C) :
    C ∈ SA.toFGCandidates sp A Φ t := by
  unfold SA.acToFG at h
  split_ifs at h
  split at h
  · cases h
  · rename_i C' hC'
    split_ifs at h
    cases h
    exact (SA.deepest_mem hC').1

/-- The selection of a fast-lock write is in the frame of its call (as in `Retention/Rows`). -/
private theorem fastLockAt_frame_mem {x : Fin sp.n} {i s : Nat}
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (h : SA.FastLockAt tr.projAC x i s D CV) {ℓ : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt x i ℓ) : D ∈ ℓ.frame.tree := by
  rcases h with ⟨ℓ', C, ⟨hc', -⟩, -, -, hD, -⟩ | ⟨ℓ', A, ⟨hc', -⟩, -, hsel, -⟩
  · obtain rfl : ℓ' = ℓ := Option.some.inj (hc'.2.symm.trans hc.2)
    exact (SA.deepest_mem hD).1.1.1
  · obtain rfl : ℓ' = ℓ := Option.some.inj (hc'.2.symm.trans hc.2)
    unfold SA.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    exact (SA.deepest_mem hsel).1.1

/-- The block of an actual report is in the reporter's FG tree. -/
private theorem report_mem (hrun : GoldilocksRun proposer dg H tr)
    {z : Fin sp.n} (hz : z ∈ H) {r : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : SA.ToFGAt tr.projAC z r ℓ C) : C ∈ (tr.state z r).fg.tree :=
  mem_tree_of_frame hrun hz h.1 (mem_toFGCandidates h.2.2).1.1

/-- **An actual high report has a stored high origin written before it** (workbench#30 §3, the
prefix of `high_row_source`): `C` is the viable image of a live fast lock, below the stored block
`B` of an earlier fast-lock write (`stored_fast_lock_provenance`); `B` is high as `C ⪯ B` is. -/
theorem high_report_origin (hp : ResetPremises tr H proposer dg g ΔF a)
    {z : Fin sp.n} (hz : z ∈ H)
    {r : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC z r ℓ C)
    (hhC : HZ tr H g + 1 ≤ ((tr.state z r).fg.σ C.root).h) :
    ∃ io < r, ∃ jo B, HighOrigin tr H g z io jo B ∧ Anc (tr.HonestBlocks H) C B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hU := hr.coherent
  obtain ⟨hpc, -, hC'⟩ := hrep
  obtain ⟨hCv, l, hl, hlb, hlf, -⟩ := mem_toFGCandidates hC'
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  obtain ⟨io, hio, CV, ℓw, D, hcw, hfl, L, hL, hLr, hLO⟩ :=
    stored_fast_lock_provenance hr hz r l₀ hl₀ hlf
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hz hpc
  obtain ⟨hΦw, -⟩ := SA.frameIn_of_callAt hr hz hcw
  have hCt : C ∈ ℓ.frame.tree := hCv.1
  obtain ⟨hvat, hva⟩ := SA.viableAncestor_anc hΦ hB₀
  obtain rfl : C = ℓ.frame.viableAncestor B₀ := hU.1 (hΦU hCt) (hΦU hvat) hlb.symm
  obtain rfl : L = B₀ := hU.1 hL (hΦU hB₀) (hLr.trans hB₀r.symm)
  set O := ℓw.frame.viableAncestor D
  have hCO : Anc (tr.HonestBlocks H) (ℓ.frame.viableAncestor L) O := (hva.mono hΦU).trans hLO
  have hOt : O ∈ (tr.state z io).fg.tree :=
    mem_tree_of_frame hp.run hz hcw (SA.viableAncestor_anc hΦw (fastLockAt_frame_mem hfl hcw)).1
  have hOr : O ∈ (tr.state z r).fg.tree := Compose.tree_mono hp.run.toLocalRun hz hio.le hOt
  have hCOr := store_anc_of_honest_anc hp.run hp.noColl hz hCO hOr
  have hOh : HZ tr H g + 1 ≤ ((tr.state z io).fg.σ O.root).h := by
    rw [← σ_eq_honest hp.run hp.noColl hz hz hOr hOt]
    exact hhC.trans (h_le_of_store_anc (Compose.fg_reachable hp.run.toLocalRun hz r) hCOr)
  have hoO : HighOrigin tr H g z io l₀.slot O := by
    unfold HighOrigin Compose.StoredFastLockAt
    exact ⟨hz, joinedAt_of_fastLockAt hp.run hp.noColl hz hfl, ⟨CV, ℓw, D, hcw, hfl, rfl⟩, hOh⟩
  exact ⟨io, hio, l₀.slot, O, hoO, hCO⟩

/-- Bounded report provenance retains the raw fast-lock source, as well as
its stored viable image. Both cover the actual report. -/
theorem ResetPremisesUpTo.high_report_origin {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} (hz : z ∈ H)
    {r : Nat} {ell : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC z r ell C) (hrb : tr.time r ≤ b)
    (hhC : HZ tr H g + 1 ≤ ((tr.state z r).fg.σ C.root).h) :
    ∃ io < r, ∃ jo O D CV, HighOrigin tr H g z io jo O ∧ tr.time io ≤ b ∧
      SA.FastLockAt tr.projAC z io jo D CV ∧ Anc (tr.HonestBlocks H) C O ∧
      Anc (tr.HonestBlocks H) O D := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hpc, _, hC'⟩ := hrep
  obtain ⟨hCv, l, hl, hlb, hlf, _⟩ := mem_toFGCandidates hC'
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, _, rfl⟩ := hl
  obtain ⟨io, hio, CV, ellw, D, hcw, hfl, L, hL, hLr, hLO⟩ :=
    stored_fast_lock_provenance hr hz r l₀ hl₀ hlf
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hz hpc
  obtain ⟨hPhiw, hPhiwU⟩ := SA.frameIn_of_callAt hr hz hcw
  obtain ⟨hvat, hva⟩ := SA.viableAncestor_anc hPhi hB₀
  obtain rfl : C = ell.frame.viableAncestor B₀ :=
    hr.coherent.1 (hPhiU hCv.1) (hPhiU hvat) hlb.symm
  obtain rfl : L = B₀ := hr.coherent.1 hL (hPhiU hB₀) (hLr.trans hB₀r.symm)
  let O := ellw.frame.viableAncestor D
  have hCO : Anc (tr.HonestBlocks H) (ell.frame.viableAncestor L) O :=
    (hva.mono hPhiU).trans hLO
  have hOD := SA.viableAncestor_anc hPhiw (fastLockAt_frame_mem hfl hcw)
  have hOt : O ∈ (tr.state z io).fg.tree := mem_tree_of_frame hp.run hz hcw hOD.1
  have hOr := Compose.tree_mono hp.run.toLocalRun hz hio.le hOt
  have hOh : HZ tr H g + 1 ≤ ((tr.state z io).fg.σ O.root).h := by
    rw [← σ_eq_honest hp.run hp.noColl hz hz hOr hOt]
    exact hhC.trans (h_le_of_store_anc (Compose.fg_reachable hp.run.toLocalRun hz r)
      (store_anc_of_honest_anc hp.run hp.noColl hz hCO hOr))
  refine ⟨io, hio, l₀.slot, O, D, CV, ?_, (hp.run.time_mono hio.le).trans hrb,
    hfl, hCO, hOD.2.mono hPhiwU⟩
  exact ⟨hz, joinedAt_of_fastLockAt hp.run hp.noColl hz hfl, ⟨CV, ellw, D, hcw, hfl, rfl⟩, hOh⟩

/-! ## High entries and the honest records (workbench#30 §4) -/

/-- Historical self-entries under bounded high origins agree at equal height. -/
theorem ResetPremisesUpTo.high_entry_eq {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {x x' : Fin sp.n}
    {i j i' j' : Nat} {B B' Z₁ Z₂ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hib : tr.time i ≤ b)
    (ho' : HighOrigin tr H g x' i' j' B') (hi'b : tr.time i' ≤ b)
    (h₁ : Anc (tr.HonestBlocks H) Z₁ B) (h₂ : Anc (tr.HonestBlocks H) Z₂ B')
    {y₁ y₂ : Fin sp.n} (hy₁ : y₁ ∈ H) (hy₂ : y₂ ∈ H) {m₁ m₂ : Nat}
    (hZ₁ : Z₁ ∈ (tr.state y₁ m₁).fg.tree) (hZ₂ : Z₂ ∈ (tr.state y₂ m₂).fg.tree)
    (hh : ((tr.state y₁ m₁).fg.σ Z₁.root).h = ((tr.state y₂ m₂).fg.σ Z₂.root).h)
    (hT₁ : ((tr.state y₁ m₁).fg.σ Z₁.root).Th = Z₁.root)
    (hT₂ : ((tr.state y₂ m₂).fg.σ Z₂.root).Th = Z₂.root) : Z₁.root = Z₂.root := by
  have key : ∀ {w : Fin sp.n} {k : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}, w ∈ H →
      D ∈ (tr.state w k).fg.tree → Anc (tr.HonestBlocks H) Z₁ D →
      Anc (tr.HonestBlocks H) Z₂ D → Z₁.root = Z₂.root := by
    intro w k D hw hD hZ₁D hZ₂D
    have e₁ := σ_eq_honest hp.run hp.noColl hy₁ hw hZ₁ (hp.mem_tree_of_anc hw hZ₁D hD)
    have e₂ := σ_eq_honest hp.run hp.noColl hy₂ hw hZ₂ (hp.mem_tree_of_anc hw hZ₂D hD)
    exact hp.entry_root_eq hw hD hZ₁D hZ₂D (by rw [← e₁, ← e₂, hh])
      (by rw [← e₁, hT₁]) (by rw [← e₂, hT₂])
  obtain ⟨CV, hs⟩ := ho.2.2.1
  obtain ⟨CV', hs'⟩ := ho'.2.2.1
  rcases hp.origins_compatible ho hib ho' hi'b with hBB' | hB'B
  · exact key ho'.1 (storedFastLock_mem hp.run hp.noColl ho'.1 hs').1 (h₁.trans hBB') h₂
  · exact key ho.1 (storedFastLock_mem hp.run hp.noColl ho.1 hs).1 h₁ (h₂.trans hB'B)

/-- **Two high-chain entries of one height are one block**: below two high origins, comparable
(R1), they sit below the larger, held by its writer, where `entry_root_eq` applies. -/
private theorem high_entry_eq (hp : ResetPremises tr H proposer dg g ΔF a) {x x' : Fin sp.n}
    {i j i' j' : Nat} {B B' Z₁ Z₂ : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (ho' : HighOrigin tr H g x' i' j' B')
    (h₁ : Anc (tr.HonestBlocks H) Z₁ B) (h₂ : Anc (tr.HonestBlocks H) Z₂ B')
    {y₁ y₂ : Fin sp.n} (hy₁ : y₁ ∈ H) (hy₂ : y₂ ∈ H) {m₁ m₂ : Nat}
    (hZ₁ : Z₁ ∈ (tr.state y₁ m₁).fg.tree) (hZ₂ : Z₂ ∈ (tr.state y₂ m₂).fg.tree)
    (hh : ((tr.state y₁ m₁).fg.σ Z₁.root).h = ((tr.state y₂ m₂).fg.σ Z₂.root).h)
    (hT₁ : ((tr.state y₁ m₁).fg.σ Z₁.root).Th = Z₁.root)
    (hT₂ : ((tr.state y₂ m₂).fg.σ Z₂.root).Th = Z₂.root) : Z₁.root = Z₂.root := by
  have key : ∀ {w : Fin sp.n} {k : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}, w ∈ H →
      D ∈ (tr.state w k).fg.tree → Anc (tr.HonestBlocks H) Z₁ D →
      Anc (tr.HonestBlocks H) Z₂ D → Z₁.root = Z₂.root := by
    intro w k D hw hD hZ₁D hZ₂D
    have e₁ := σ_eq_run hp hy₁ hw hZ₁ (mem_tree_of_anc hp hw hZ₁D hD)
    have e₂ := σ_eq_run hp hy₂ hw hZ₂ (mem_tree_of_anc hp hw hZ₂D hD)
    exact entry_root_eq hp hw hD hZ₁D hZ₂D (by rw [← e₁, ← e₂, hh]) (by rw [← e₁, hT₁])
      (by rw [← e₂, hT₂])
  obtain ⟨CV, hs⟩ := ho.2.2.1
  obtain ⟨CV', hs'⟩ := ho'.2.2.1
  rcases (height_scoped_retention sp ro proposer dg H tr g ΔF hp.run hp.healthy hp.noColl a
    hp.reset).comparable x i j B x' i' j' B' ho ho' with hBB' | hB'B
  · exact key ho'.1 (storedFastLock_mem hp.run hp.noColl ho'.1 hs').1 (h₁.trans hBB') h₂
  · exact key ho.1 (storedFastLock_mem hp.run hp.noColl ho.1 hs).1 h₁ (h₂.trans hB'B)

/-- **A high record entry is the high-chain entry of its height**: an honest record's target,
timeout or lock entry at `h ≥ H_z + 1` is the root of every entry at `h` below a high origin. -/
theorem ResetPremisesUpTo.record_entry_eq {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {i h r : Nat} (hib : tr.time i ≤ b)
    (hh : HZ tr H g + 1 ≤ h)
    (hr : (tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h ∨
      (tr.state y i).record.lock h = some r)
    {xo : Fin sp.n} {io jo : Nat} {B E : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hiob : tr.time io ≤ b)
    (hEB : Anc (tr.HonestBlocks H) E B) {z : Fin sp.n}
    (hz : z ∈ H) {m : Nat} (hE : E ∈ (tr.state z m).fg.tree)
    (hEh : ((tr.state z m).fg.σ E.root).h = h)
    (hET : ((tr.state z m).fg.σ E.root).Th = E.root) : r = E.root := by
  have target : ∀ k < i, ∀ att, tr.SignAt y k att → att.h = h → att.T = r → r = E.root := by
    intro k hki att hs hah har
    obtain ⟨q, hqk, l, O, hO, X, hX, hXO, hXr, hXh, hXT⟩ :=
      hp.high_row_source hy hs (hah ▸ hh)
    exact har.symm.trans (hXr.symm.trans (hp.high_entry_eq hO
      ((hp.run.time_mono (hqk.le.trans hki.le)).trans hib) ho hiob
      (hXO.mono fun D hD => ⟨y, hy, q, hD⟩) hEB hy hz hX hE
      (hXh.trans (hah.trans hEh.symm)) hXT hET))
  rcases hr with ht | ht | hl
  · obtain ⟨k, hki, att, hs, hah, har⟩ :=
      (client_record_origin_of_run hp.run hy h r i).1 (Or.inl ht)
    exact target k hki att hs hah har
  · obtain ⟨k, hki, att, hs, hah, har⟩ :=
      (client_record_origin_of_run hp.run hy h r i).1 (Or.inr ht)
    exact target k hki att hs hah har
  · obtain ⟨k, hki, att, hs, hfin⟩ := (client_record_origin_of_run hp.run hy h r i).2 hl
    obtain ⟨J, hJ, X, hX, hXr, hJX, hJr, hJh, hJT⟩ := signed_fin_pair_entry_of_run hp.run hy hs hfin
    obtain ⟨X', hX', hX'r, hX'h⟩ := signAt_entry hp.run hy hs
    obtain rfl : X' = X := hp.honest_coherent.1 ⟨y, hy, k, hX'⟩ ⟨y, hy, k, hX⟩
      (hX'r.trans hXr.symm)
    have hle := σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun hy k) hJX
    obtain ⟨q, hqk, l, O, hO, X'', hX'', hXO, hX''r, _, _⟩ := hp.high_row_source hy hs (by omega)
    obtain rfl : X'' = X' := hp.honest_coherent.1 ⟨y, hy, q, hX''⟩ ⟨y, hy, k, hX⟩
      (hX''r.trans hX'r.symm)
    have hJO : Anc (tr.HonestBlocks H) J O :=
      (hJX.mono (show (tr.state y k).fg.tree ⊆ tr.HonestBlocks H from
        fun D hD => ⟨y, hy, k, hD⟩)).trans
        (hXO.mono fun D hD => ⟨y, hy, q, hD⟩)
    exact hJr.symm.trans (hp.high_entry_eq hO
      ((hp.run.time_mono (hqk.le.trans hki.le)).trans hib) ho hiob
      hJO hEB hy hz hJ hE (hJh.trans hEh.symm) hJT hET)

private theorem record_entry_eq (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H)
    {i h r : Nat} (hh : HZ tr H g + 1 ≤ h)
    (hr : (tr.state y i).record.target h = some r ∨ r ∈ (tr.state y i).record.timeout h ∨
      (tr.state y i).record.lock h = some r)
    {xo : Fin sp.n} {io jo : Nat} {B E : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hEB : Anc (tr.HonestBlocks H) E B) {z : Fin sp.n}
    (hz : z ∈ H) {m : Nat} (hE : E ∈ (tr.state z m).fg.tree)
    (hEh : ((tr.state z m).fg.σ E.root).h = h)
    (hET : ((tr.state z m).fg.σ E.root).Th = E.root) : r = E.root := by
  obtain ⟨x, i', j, B', ho', Z, hZB', rfl, w, hw, k, hZ, hZh, hZT⟩ := high_record_entry hp
    (height_scoped_retention sp ro proposer dg H tr g ΔF
      hp.run hp.healthy hp.noColl a hp.reset).rows
    hy hh hr
  exact high_entry_eq hp ho' ho hZB' hEB hw hz hZ hE (hZh.trans hEh.symm) hZT hET

/-- **The first-timeout step**: with no timeout recorded at its height, an honest high row is a
target: another recorded target there is the high-chain entry, the row's own. -/
private theorem sign_target (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {att : FG.Att sp.n} (hs : tr.SignAt y k att) (hh : HZ tr H g + 1 ≤ att.h)
    (he : (tr.state y k).record.timeout att.h = ∅) : att.timeout = false := by
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw y hy k _ hc).1
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨-, hah, haT, -, -, hτ⟩ := createAtt_spec hcl
  rw [← Bool.not_eq_true]
  intro hto
  rw [← hah, ← haT] at hτ
  rcases hτ hto with h' | ⟨T', hT', hne⟩
  · exact h' he
  · obtain ⟨_, -, l, O, hO, E, hE, hEO, hEr, hEh, hET⟩ := high_row_source hp hy ⟨src, hc⟩ hh
    exact hne ((record_entry_eq hp hy hh (Or.inl hT') hO (hEO.mono fun X hX => ⟨y, hy, _, hX⟩)
      hy hE hEh hET).trans hEr)

/-- **No honest high timeout** (workbench#30 §4, first-timeout induction): the timeout sets of an
honest record at the heights `≥ H_z + 1` stay empty. -/
private theorem timeout_empty (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) :
    ∀ i h, HZ tr H g + 1 ≤ h → (tr.state y i).record.timeout h = ∅
  | 0, h, _ => by
    rw [Trace.state, hp.run.init y hy]
    rfl
  | i + 1, h, hh => by
    rcases record_step_of_run hp.run hy i with he | ⟨att, hs, he⟩ <;> rw [he]
    · exact timeout_empty hp hy i h hh
    · simp only [FG.Record.recordAtt]
      split_ifs with hto
      · rw [Function.update_apply]
        split_ifs with hha
        · subst hha
          have := sign_target hp hy hs hh (timeout_empty hp hy i _ hh)
          simp_all
        · exact timeout_empty hp hy i h hh
      · exact timeout_empty hp hy i h hh

/-- The target and timeout fields of a high entry's row do not require its
predecessor to be high. -/
private theorem sign_target_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {att : FG.Att sp.n}
    (hs : tr.SignAt y k att) (hkb : tr.time k ≤ b) (hh : HZ tr H g + 1 ≤ att.h)
    (he : (tr.state y k).record.timeout att.h = ∅) : att.timeout = false := by
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw y hy k _ hc).1
  change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
    ((tr.state y k).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨_, hah, haT, _, _, hτ⟩ := createAtt_spec hcl
  rw [← Bool.not_eq_true]
  intro hto
  rw [← hah, ← haT] at hτ
  rcases hτ hto with h' | ⟨T', hT', hne⟩
  · exact h' he
  · obtain ⟨q, hqk, l, O, hO, E, hE, hEO, hEr, hEh, hET⟩ := hp.high_row_source hy ⟨src, hc⟩ hh
    exact hne ((hp.record_entry_eq hy hkb hh (Or.inl hT') hO
      ((hp.run.time_mono hqk.le).trans hkb) (hEO.mono fun X hX => ⟨y, hy, q, hX⟩)
      hy hE hEh hET).trans hEr)

private theorem timeout_empty_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) :
    ∀ i, tr.time i ≤ b → ∀ h, HZ tr H g + 1 ≤ h → (tr.state y i).record.timeout h = ∅
  | 0, _, h, _ => by rw [Trace.state, hp.run.init y hy]; rfl
  | i + 1, hib, h, hh => by
    have hib' := (hp.run.time_mono (Nat.le_succ i)).trans hib
    rcases record_step_of_run hp.run hy i with he | ⟨att, hs, he⟩ <;> rw [he]
    · exact timeout_empty_before hp hy i hib' h hh
    · simp only [FG.Record.recordAtt]
      split_ifs with hto
      · rw [Function.update_apply]
        split_ifs with hha
        · subst hha
          have := sign_target_before hp hy hs hib' hh (timeout_empty_before hp hy i hib' _ hh)
          simp_all
        · exact timeout_empty_before hp hy i hib' h hh
      · exact timeout_empty_before hp hy i hib' h hh

/-- Finite normalization of a high signature's target and timeout fields. -/
theorem ResetPremisesUpTo.row_target_of_sign {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} (hz : z ∈ H)
    {j : Nat} {att : FG.Att sp.n} (hs : tr.SignAt z j att) (hjb : tr.time j ≤ b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))}
    {y : Fin sp.n} (hy : y ∈ H) {m : Nat} (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hiob : tr.time io ≤ b)
    (hTB : Anc (tr.HonestBlocks H) T B) (hatt : att.h = σT.h) :
    att.val = z ∧ att.T = T.root ∧ att.timeout = false := by
  subst hσ
  have hh : HZ tr H g + 1 ≤ att.h := hatt ▸ hhT
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw z hz j _ hc).1
  change (tr.state z j).record.createAtt z ((tr.state z j).fg.σ
    ((tr.state z j).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨hv, _, _, _, _, _⟩ := createAtt_spec hcl
  obtain ⟨q, hqj, l, O, hO, E, hE, hEO, hEr, hEh, hET⟩ := hp.high_row_source hz ⟨src, hc⟩ hh
  have hTr : att.T = T.root := hEr.symm.trans (hp.high_entry_eq hO
    ((hp.run.time_mono hqj.le).trans hjb) ho hiob
    (hEO.mono fun X hX => ⟨z, hz, q, hX⟩) hTB hz hy hE hT (hEh.trans hatt) hET hTe)
  exact ⟨hv, hTr, sign_target_before hp hz ⟨src, hc⟩ hjb hh (timeout_empty_before hp hz j hjb _ hh)⟩

theorem row_target_of_sign (hp : ResetPremises tr H proposer dg g ΔF a)
    {z : Fin sp.n} (hz : z ∈ H)
    {j : Nat} {att : FG.Att sp.n} (hs : tr.SignAt z j att) {T : SA.Blk sp.n (List (FG.Att sp.n))}
    {y : Fin sp.n} (hy : y ∈ H) {m : Nat} (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hTB : Anc (tr.HonestBlocks H) T B) (hatt : att.h = σT.h) :
    att.val = z ∧ att.T = T.root ∧ att.timeout = false := by
  subst hσ
  have hh : HZ tr H g + 1 ≤ att.h := hatt ▸ hhT
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw z hz j _ hc).1
  change (tr.state z j).record.createAtt z ((tr.state z j).fg.σ
    ((tr.state z j).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨hv, -, -, -, -, -⟩ := createAtt_spec hcl
  obtain ⟨_, -, l, O, hO, E, hE, hEO, hEr, hEh, hET⟩ := high_row_source hp hz ⟨src, hc⟩ hh
  have hTr : att.T = T.root := hEr.symm.trans (high_entry_eq hp hO ho
    (hEO.mono fun X hX => ⟨z, hz, _, hX⟩) hTB hz hy hE hT (hEh.trans hatt) hET hTe)
  exact ⟨hv, hTr, sign_target hp hz ⟨src, hc⟩ hh (timeout_empty hp hz j _ hh)⟩

/-- Historical signatures carry the exact predecessor (of a height whose previous height is
justified) when that predecessor is high; permission is proved at the original signing cut. -/
theorem ResetPremisesUpTo.row_of_sign {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} (hz : z ∈ H)
    {j : Nat} {att : FG.Att sp.n} (hs : tr.SignAt z j att) (hjb : tr.time j ≤ b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))}
    {y : Fin sp.n} (hy : y ∈ H) {m : Nat} (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hhj : σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hiob : tr.time io ≤ b)
    (hTB : Anc (tr.HonestBlocks H) T B) (hatt : att.h = σT.h) :
    att.val = z ∧ att.T = T.root ∧ att.timeout = false ∧
      (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J)) := by
  subst hσ
  obtain ⟨hv, hTr, htimeout⟩ := hp.row_target_of_sign hz hs hjb hy hT rfl hTe hhT ho hiob hTB hatt
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw z hz j _ hc).1
  change (tr.state z j).record.createAtt z ((tr.state z j).fg.σ
    ((tr.state z j).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨_, _, haT, hfin, _, _⟩ := createAtt_spec hcl
  refine ⟨hv, hTr, htimeout, fun hb => ?_⟩
  obtain ⟨E', hE', hE'r, hE'T⟩ := source_entry (Compose.fg_reachable hp.run.toLocalRun hz j) src
  have hR : ((tr.state z j).fg.σ src.root).Th = T.root := by
    rw [← hTr, haT, ← hE'r, hE'T]
  have he : E' = T := hp.honest_coherent.1 ⟨z, hz, j, hE'⟩ ⟨y, hy, m, hT⟩ (hE'r.trans hR)
  rw [he] at hE'
  rw [hfin, hR, σ_eq_honest hp.run hp.noColl hz hy hE' hT]
  obtain ⟨J₀, hJ₀, hJ₀T, hJ₀r, hJ₀h, hJ₀T'⟩ :=
    (chain_pairs_entry (Compose.fg_reachable hp.run.toLocalRun hy m) hT).1 hb.1
  have hsub : (tr.state y m).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, m, hX⟩
  have heq := fun r hr => (hp.record_entry_eq hz hjb (hhj hb) (i := j) (r := r) hr ho hiob
    ((hJ₀T.mono hsub).trans hTB) hy hJ₀ hJ₀h hJ₀T').trans hJ₀r
  have hperm : (tr.state z j).record.permits ((tr.state y m).fg.σ T.root).hj
      ((tr.state y m).fg.σ T.root).J := by
    refine ⟨?_, fun r hr => Finset.mem_singleton.2 (heq r (Or.inr (Or.inl hr))), ?_⟩
    · rcases ht : (tr.state z j).record.target _ with _ | r
      exacts [Or.inl rfl, Or.inr (by rw [heq r (Or.inl ht)])]
    · rcases hl : (tr.state z j).record.lock _ with _ | r
      exacts [Or.inl rfl, Or.inr (by rw [heq r (Or.inr (Or.inr hl))])]
  unfold FG.Record.finalityPair
  simp only [hb, hperm, ↓reduceIte]

/-- **An honest row of a high entry's height is its target row, with the predecessor at an entry
whose previous height is justified** (workbench#30 §4): it names `T` (`high_entry_eq`), is no
timeout (`timeout_empty`), and its `finality_pair` of `σ[T]` is `(h_j, J)`, which the high records
permit (`record_entry_eq`). -/
theorem row_of_sign (hp : ResetPremises tr H proposer dg g ΔF a)
    {z : Fin sp.n} (hz : z ∈ H)
    {j : Nat} {att : FG.Att sp.n} (hs : tr.SignAt z j att) {T : SA.Blk sp.n (List (FG.Att sp.n))}
    {y : Fin sp.n} (hy : y ∈ H) {m : Nat} (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hhj : σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hTB : Anc (tr.HonestBlocks H) T B) (hatt : att.h = σT.h) :
    att.val = z ∧ att.T = T.root ∧ att.timeout = false ∧
      (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J)) := by
  subst hσ
  obtain ⟨hv, hTr, htimeout⟩ := row_target_of_sign hp hz hs hy hT rfl hTe hhT ho hTB hatt
  obtain ⟨src, hc⟩ := hs
  have hcl := (hp.run.cutLaw z hz j _ hc).1
  change (tr.state z j).record.createAtt z ((tr.state z j).fg.σ
    ((tr.state z j).fg.σ src.root).Th) = some (att, _) at hcl
  obtain ⟨-, -, haT, hfin, -, -⟩ := createAtt_spec hcl
  refine ⟨hv, hTr, htimeout, fun hb => ?_⟩
  obtain ⟨E', hE', hE'r, hE'T⟩ := source_entry (Compose.fg_reachable hp.run.toLocalRun hz j) src
  have hR : ((tr.state z j).fg.σ src.root).Th = T.root := by
    rw [← hTr, haT, ← hE'r, hE'T]
  have hE'eq : E' = T := (honest_coherent hp).1 ⟨z, hz, j, hE'⟩ ⟨y, hy, m, hT⟩ (hE'r.trans hR)
  rw [hE'eq] at hE'
  rw [hfin, hR, σ_eq_run hp hz hy hE' hT]
  -- the records permit the predecessor: each high record entry at `h_j` is `J`'s block
  obtain ⟨J₀, hJ₀, hJ₀T, hJ₀r, hJ₀h, hJ₀T'⟩ :=
    (chain_pairs_entry (Compose.fg_reachable hp.run.toLocalRun hy m) hT).1 hb.1
  have hsub : (tr.state y m).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, m, hX⟩
  have heq := fun r hr => (record_entry_eq hp hz (hhj hb) (i := j) (r := r) hr ho
    ((hJ₀T.mono hsub).trans hTB) hy hJ₀ hJ₀h hJ₀T').trans hJ₀r
  have hperm : (tr.state z j).record.permits ((tr.state y m).fg.σ T.root).hj
      ((tr.state y m).fg.σ T.root).J := by
    refine ⟨?_, fun r hr => Finset.mem_singleton.2 (heq r (Or.inr (Or.inl hr))), ?_⟩
    · rcases ht : (tr.state z j).record.target _ with _ | r
      exacts [Or.inl rfl, Or.inr (by rw [heq r (Or.inl ht)])]
    · rcases hl : (tr.state z j).record.lock _ with _ | r
      exacts [Or.inl rfl, Or.inr (by rw [heq r (Or.inr (Or.inr hl))])]
  unfold FG.Record.finalityPair
  simp only [hb, hperm, ↓reduceIte]

/-- **A same-height report gives a row of the entry's height by then** (workbench#30 §4): the
client call after it (`toFG_attest`) reads `σ[T]`; it signs, or (no foreign lock,
`record_entry_eq`) already sent a content of that height, signed earlier (`sent_origin`). -/
theorem sign_of_report (hp : ResetPremises tr H proposer dg g ΔF a)
    {z : Fin sp.n} (hz : z ∈ H)
    {r : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC z r ℓ C) {T : SA.Blk sp.n (List (FG.Att sp.n))}
    {y : Fin sp.n} (hy : y ∈ H) {m : Nat} (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hTC : Anc (tr.HonestBlocks H) T C)
    (hCh : ((tr.state z r).fg.σ C.root).h = σT.h)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hTB : Anc (tr.HonestBlocks H) T B) :
    ∃ j att, tr.SignAt z j att ∧ tr.time j ≤ tr.time r ∧ att.h = σT.h := by
  subst hσ
  have hCt := report_mem hp.run hz hrep
  obtain ⟨hpc, hcall, hC⟩ := hrep
  have hTt := mem_tree_of_anc hp hz hTC hCt
  have hσT := σ_eq_run hp hz hy hTt hT
  have hCTh : ((tr.state z r).fg.σ C.root).Th = T.root := by
    rw [Th_eq_of_anc (Compose.fg_reachable hp.run.toLocalRun hz r) (anc_tree_of_anc hp hz hTC hCt)
      (by rw [hCh, hσT]), hσT, hTe]
  rw [Compose.projAC_state hp.run.toLocalRun hz] at hC
  obtain ⟨s, hs, hts, hfg⟩ :=
    toFG_attest hp.run.toLocalRun hz (Compose.projAC_callAt.1 hpc) hcall hC
  -- the entry state of the client call is `σ[T]`
  have hσe : (tr.state z (r + 1)).fg.σ ((tr.state z (r + 1)).fg.σ C.root).Th =
      (tr.state y m).fg.σ T.root := by
    rw [hfg, hCTh, hσT]
  cases s with
  | some att =>
    have hcl := (hp.run.cutLaw z hz _ _ hs).1
    change (tr.state z (r + 1)).record.createAtt z ((tr.state z (r + 1)).fg.σ
      ((tr.state z (r + 1)).fg.σ C.root).Th) = some (att, _) at hcl
    exact ⟨r + 1, att, ⟨C, hs⟩, hts.le, by rw [(createAtt_spec hcl).2.1, hσe]⟩
  | none =>
    have hcl := (hp.run.cutLaw z hz _ _ hs).1
    change (tr.state z (r + 1)).record.createAtt z ((tr.state z (r + 1)).fg.σ
      ((tr.state z (r + 1)).fg.σ C.root).Th) = none at hcl
    rw [hσe] at hcl
    rcases createAtt_none hcl with ⟨hl, hl'⟩ | ⟨b, hb, hb1⟩
    · obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists'.1 hl
      have := record_entry_eq hp hz hhT (Or.inr (Or.inr hr')) ho hTB hy hT rfl hTe
      exact absurd (by rw [hr', this, hTe]) hl'
    · obtain ⟨k, hk, att, hsk, rfl⟩ := sent_origin hp.run hz (r + 1) hb
      exact ⟨k, att, hsk, (hp.run.time_mono hk.le).trans hts.le, hb1⟩

/-! ## A higher report: the same first crossing and its origin (workbench#30 §5) -/

/-- A bounded same-height report supplies an actual signature by its timestamp,
including the case where a previously signed content suppresses the new call. -/
theorem ResetPremisesUpTo.sign_of_report {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} (hz : z ∈ H)
    {r : Nat} {ell : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC z r ell C) (hrb : tr.time r ≤ b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))}
    {y : Fin sp.n} (hy : y ∈ H) {m : Nat} (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hTC : Anc (tr.HonestBlocks H) T C)
    (hCh : ((tr.state z r).fg.σ C.root).h = σT.h)
    {xo : Fin sp.n} {io jo : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g xo io jo B) (hiob : tr.time io ≤ b)
    (hTB : Anc (tr.HonestBlocks H) T B) :
    ∃ j att, tr.SignAt z j att ∧ tr.time j ≤ tr.time r ∧ att.h = σT.h := by
  subst hσ
  have hCt := report_mem hp.run hz hrep
  obtain ⟨hpc, hcall, hC⟩ := hrep
  have hTt := hp.mem_tree_of_anc hz hTC hCt
  have hσT := σ_eq_honest hp.run hp.noColl hz hy hTt hT
  have hCTh : ((tr.state z r).fg.σ C.root).Th = T.root := by
    rw [Th_eq_of_anc (Compose.fg_reachable hp.run.toLocalRun hz r)
      (store_anc_of_honest_anc hp.run hp.noColl hz hTC hCt)
      (by rw [hCh, hσT]), hσT, hTe]
  rw [Compose.projAC_state hp.run.toLocalRun hz] at hC
  obtain ⟨s, hs, hts, hfg⟩ :=
    toFG_attest hp.run.toLocalRun hz (Compose.projAC_callAt.1 hpc) hcall hC
  have hσe : (tr.state z (r + 1)).fg.σ ((tr.state z (r + 1)).fg.σ C.root).Th =
      (tr.state y m).fg.σ T.root := by rw [hfg, hCTh, hσT]
  cases s with
  | some att =>
    have hcl := (hp.run.cutLaw z hz _ _ hs).1
    change (tr.state z (r + 1)).record.createAtt z ((tr.state z (r + 1)).fg.σ
      ((tr.state z (r + 1)).fg.σ C.root).Th) = some (att, _) at hcl
    exact ⟨r + 1, att, ⟨C, hs⟩, hts.le, by rw [(createAtt_spec hcl).2.1, hσe]⟩
  | none =>
    have hcl := (hp.run.cutLaw z hz _ _ hs).1
    change (tr.state z (r + 1)).record.createAtt z ((tr.state z (r + 1)).fg.σ
      ((tr.state z (r + 1)).fg.σ C.root).Th) = none at hcl
    rw [hσe] at hcl
    rcases createAtt_none hcl with ⟨hl, hl'⟩ | ⟨c, hc, _⟩
    · obtain ⟨r', hr'⟩ := Option.ne_none_iff_exists'.1 hl
      have := hp.record_entry_eq hz (hts.le.trans hrb) hhT (Or.inr (Or.inr hr'))
        ho hiob hTB hy hT rfl hTe
      exact absurd (by rw [hr', this, hTe]) hl'
    · obtain ⟨k, hk, att, hsk, rfl⟩ := sent_origin hp.run hz (r + 1) hc
      exact ⟨k, att, hsk, (hp.run.time_mono hk.le).trans hts.le, by assumption⟩

/-- A bounded same-height report supplies the exact entry row, with historical
finality permission checked at the actual signing cut. -/
theorem ResetPremisesUpTo.row_of_report {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {z : Fin sp.n} (hz : z ∈ H)
    {r : Nat} {ell : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hrep : SA.ToFGAt tr.projAC z r ell C) (hrb : tr.time r ≤ b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))}
    {y : Fin sp.n} (hy : y ∈ H) {m : Nat} (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hhj : σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj)
    (hTC : Anc (tr.HonestBlocks H) T C)
    (hCh : ((tr.state z r).fg.σ C.root).h = σT.h) :
    ∃ j att, tr.SignAt z j att ∧ tr.time j ≤ tr.time r ∧ att.val = z ∧
      att.h = σT.h ∧ att.T = T.root ∧ att.timeout = false ∧
      (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J)) := by
  obtain ⟨io, _, jo, O, _, _, ho, hiob, _, hCO, _⟩ := hp.high_report_origin hz hrep hrb
    (by rw [hCh]; exact hhT)
  have hTO := hTC.trans hCO
  obtain ⟨j, att, hs, ht, hh⟩ := hp.sign_of_report hz hrep hrb hy hT hσ hTe hhT hTC hCh ho hiob hTO
  obtain ⟨hv, hroot, htimeout, hfin⟩ :=
    hp.row_of_sign hz hs (ht.trans hrb) hy hT hσ hTe hhT hhj ho hiob hTO hh
  exact ⟨j, att, hs, ht, hv, hh, hroot, htimeout, hfin⟩

/-- Same-height reports from every honest node yield an identity quorum of exact
entry signatures. Historical reports count without any freshness assumption. -/
theorem ResetPremisesUpTo.row_signers_of_reports {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {T : SA.Blk sp.n (List (FG.Att sp.n))}
    {y : Fin sp.n} (hy : y ∈ H) {m : Nat} (hT : T ∈ (tr.state y m).fg.tree)
    {σT : FG.ChainState sp.n} (hσ : (tr.state y m).fg.σ T.root = σT) (hTe : σT.Th = T.root)
    (hhT : HZ tr H g + 1 ≤ σT.h) (hhj : σT.previousHeightJustified → HZ tr H g + 1 ≤ σT.hj)
    {d : Time} (hdb : d ≤ b)
    (hreports : ∀ z ∈ H, ∃ r ell C, SA.ToFGAt tr.projAC z r ell C ∧ tr.time r ≤ d ∧
      Anc (tr.HonestBlocks H) T C ∧ ((tr.state z r).fg.σ C.root).h = σT.h) :
    ∃ ids : Finset (Fin sp.n), sp.toParams.fg.q ≤ ids.card ∧
      ∀ z ∈ ids, z ∈ H ∧ ∃ att j, tr.SignAt z j att ∧ att.val = z ∧
        att.h = σT.h ∧ att.T = T.root ∧ att.timeout = false ∧ tr.time j ≤ d ∧
        (σT.previousHeightJustified → att.fin = some (σT.hj, σT.J)) := by
  classical
  refine ⟨Finset.univ.filter (· ∈ H), ?_, ?_⟩
  · have hcard : (Finset.univ.filter (· ∈ H)).card = H.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext z
      simp
    rw [hcard]
    have hn : H.ncard + Hᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hf := hp.faults
    change (2 * sp.n + 2) / 3 ≤ _
    omega
  · intro z hz
    have hzH := (Finset.mem_filter.1 hz).2
    obtain ⟨r, ell, C, hr, hrd, hTC, hh⟩ := hreports z hzH
    obtain ⟨j, att, hs, ht, hv, hah, hroot, htimeout, hfin⟩ :=
      hp.row_of_report hzH hr (hrd.trans hdb) hy hT hσ hTe hhT hhj hTC hh
    exact ⟨hzH, att, j, hs, hv, hah, hroot, htimeout, ht.trans hrd, hfin⟩

/-! ## The carriers -/

/-- **C0.3 at an honest proposal**: the own block of an honest proposal is accepted at its cut,
and it includes every row of the proposer's pool that is valid against its parent's state and not
on its parent's chain (`proposal_attestations`). -/
private theorem proposal_accepted (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    {w : Fin sp.n} (hw : w ∈ H) {kw : Nat} {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : tr.ProposesAt w kw W) :
    tr.AcceptAt w kw W ∧ ∀ Pr ∈ (tr.state w kw).fg.tree, W.parent = some Pr.root →
      ∀ r ∈ (tr.state w kw).fg.atts, ((tr.state w kw).fg.σ Pr.root).validAtt r →
        ¬ (tr.state w kw).fg.OnChain Pr r → r ∈ W.fgPayload := by
  obtain ⟨⟨⟨acc, hc⟩, hpos⟩, -, -⟩ := hP
  rcases Compose.blockCall_cases hrun.toLocalRun hw hc with hg |
    ⟨j, x, rfl, hg, hpr, d, p, hdp, rfl, -, -, -, hfg⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  have hreq : (goldilocksNode sp ro).Requirements :=
    ⟨(SA.interface_requirements sp _ ro).1, (SA.interface_requirements sp _ ro).2.1,
      (SA.interface_requirements sp _ ro).2.2.1, (SA.interface_requirements sp _ ro).2.2.2,
      SA.proposal_payload_valid sp _ ro⟩
  obtain ⟨hacc, -⟩ :=
    own_block_accepted hrun.toLocalRun hreq hrun.genesis_root_ok hnc hw hg hpr hdp
  have he := hc.2.symm.trans hacc.2
  simp only [Option.some.injEq, Cut.fg.injEq, FGLabel.block.injEq] at he
  obtain rfl := he.2
  refine ⟨hc, fun Pr hPr hpar r hr hv hn => ?_⟩
  rw [hfg] at hPr hr hv hn
  have hroot : d.head.root = Pr.root := Option.some.inj hpar
  change r ∈ (tr.state w j).fg.proposalAttestations d.head
  simp only [Store.proposalAttestations, List.mem_filter, decide_eq_true_eq]
  refine ⟨hr, by rw [hroot]; exact hv, fun ⟨X, hX, hXd, hrX⟩ => hn ⟨X, hX, ?_, hrX⟩⟩
  have hd : d.head ∈ (tr.state w j).fg.tree := by
    rcases eq_or_ne X d.head with rfl | hne
    exacts [hX, (hXd.mem hne).2]
  have e : (tr.state w j).fg.blocks d.head.root = some Pr := by rw [hroot]; exact hPr
  obtain rfl : d.head = Pr := Option.some.inj (hd.symm.trans e)
  exact hXd

/-- The FG projection of a Goldilocks run under the HS shared premises is an FG trace with its
contract (C0.5 (c)). -/
private theorem fg_run (hrun : GoldilocksRun proposer dg H tr) (hsh : HSShared tr H dg g ΔF) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload H (tr.HonestBlocks H) tr.projFG :=
  Compose.fg_projection _ _ dg H _ tr proposer
    ⟨(SA.interface_requirements sp _ ro).1, (SA.interface_requirements sp _ ro).2.1,
      (SA.interface_requirements sp _ ro).2.2.1, (SA.interface_requirements sp _ ro).2.2.2,
      SA.proposal_payload_valid sp _ ro⟩
    hsh.genesisRoot hrun.toLocalRun hsh.noColl

/-- Catch before GST and acceptance relay after GST give Catch at the actual reset,
without awake or service obligations beyond the finite observation horizon. -/
theorem catch_window_at_reset_of_reset_catch_before {b t : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) (htb : t ≤ b) :
    CatchACWindowBefore tr.projAC H (tr.HonestBlocks H) a (2 * sp.Δ) t := by
  have hca := cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨k, hk, -⟩ := hp.snapshot; exact ⟨k, hk⟩) hp.reset
  have hga : SA.gbar g < a := by linarith [lt_cutZ sp g, sp.toParams.hΔ]
  have hra : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ a := by
    apply le_trans _ hca.le
    rw [cutZ_eq]
    exact (SA.ts_le_iff sp).mpr (by omega)
  constructor
  intro x hx i B ha hi y hy j ell hj ht hjt hF
  change a + 2 * sp.Δ ≤ tr.time j at ht
  change tr.time j ≤ t at hjt
  by_cases hgi : tr.projAC.time i < SA.gbar g
  · obtain ⟨k, hk, hak, hkt⟩ := projection_catch_of_run hp.run hc x hx i B ha hgi
      y hy j ell hj (by change SA.gbar g + 2 * sp.Δ ≤ tr.time j; linarith) hF
    exact ⟨k, hk, hak, by linarith⟩
  · obtain ⟨i', rfl, ha', hti⟩ := fg_accept_before hp.run.toLocalRun hx ha
    change tr.time (i' + 1) < a at hi
    change ¬ tr.time (i' + 1) < SA.gbar g at hgi
    have hia : tr.time i' < a := by simpa only [hti] using hi
    have hgg : g ≤ tr.time i' := (SA.le_gbar g).trans (by
      simpa only [hti] using le_of_not_gt hgi)
    have hmax : max (tr.time i') g = tr.time i' := max_eq_left hgg
    have hdeadline : ∀ k ≤ j, tr.deadline y k (tr.time i') sp.Δ ≤ a + sp.Δ := by
      intro k hkj
      apply le_trans (Compose.deadline_le_of_restarts (a := a) (fun r hr hrest =>
        (restart_le_before hp hy hrest
          ((hp.run.time_mono (hr.trans hkj)).trans (hjt.trans htb))).trans hra) _ _)
      rw [max_eq_right hia.le]
    obtain ⟨k, hk, hak, hkt⟩ := hp.sync.relay x hx i' B ha' hgg y hy j
      ⟨_, Compose.projAC_callAt.mp hj⟩ (by
        rw [hmax]
        exact (hdeadline j le_rfl).trans (by linarith [sp.toParams.hΔ]))
      (by rwa [Compose.frame_of_projAC hp.run hy hj] at hF)
    obtain ⟨hak', htk, -⟩ := ac_block_after hp.run.toLocalRun hy hak
    have hkj : k < j := by
      rcases hk.lt_or_eq with hk | rfl
      · exact hk
      · exact absurd (hak.2.symm.trans (Compose.projAC_callAt.mp hj).2) (by simp)
    refine ⟨k + 1, hkj, hak', ?_⟩
    change tr.time (k + 1) < a + 2 * sp.Δ
    rw [htk]
    rw [hmax] at hkt
    exact lt_of_lt_of_le hkt ((hdeadline k hk).trans (by linarith [sp.toParams.hΔ]))

/-- Finite reset service supplies AC synchrony from the actual reset, retaining the
recipient deadline cutoff and strict processing deadlines. -/
theorem sync_window_at_reset_of_reset_before {b t : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (htb : t ≤ b) :
    SyncACWindowBefore H (tr.HonestBlocks H) a t tr.projAC := by
  have hca := cutZ_lt_reset_of_snapshot hp.run
    (by obtain ⟨k, hk, -⟩ := hp.snapshot; exact ⟨k, hk⟩) hp.reset
  have hga : g ≤ a := by
    have := SA.le_gbar g
    have := lt_cutZ sp g
    linarith [sp.toParams.hΔ]
  have hs := hp.sync.syncAC (hi := b) hp.run hga
  have hsource : ∀ y j (u : Time), u ≤ tr.projAC.deadline y j u := by
    intro y j u
    unfold ACTrace.deadline
    have hΔ : 0 < sp.Δ := sp.toParams.hΔ
    cases tr.projAC.lastWake y j with
    | bot => change u ≤ u + sp.Δ; linarith
    | coe w =>
      change u ≤ max u w + sp.Δ
      have := le_max_left u w
      linarith
  constructor
  · intro x hx i m hm hi y hy j ell hj ht hd
    exact hs.1 x hx i m hm hi ((hsource y j _).trans (ht.trans htb))
      y hy j ell hj hd
  · intro x hx i B hB hi y hy j ell hj ht hd hF
    exact hs.2 x hx i B hB hi ((hsource y j _).trans (ht.trans htb))
      y hy j ell hj hd hF

end Consensus.Goldilocks.Healing

end

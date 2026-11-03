module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Induction
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Boot
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Cut
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.PivotOldSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Service
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset

public section

/-! # Goldilocks Recovery: `Rec` from permanent high finality (O.1, lane B)

Under the reset premises, no honest restart after `ḡ`, and `HighFinalityFrom T` (every honest
pre-call `Σ.F` has state height `≥ H_z + 1` from `T ≥ ḡ` on), `Rec` holds from `T + 12Δ`
(`rec_of_high_finality`, packaged as `recoveryFromHighFinality`):

* R1 `late_write_high`: a stored fast write after `T + 12Δ` by a joined honest writer, from
  either origin (a regular update, vetoed or not, or an optimistic confirmation), is a high
  origin of a slot starting after `T`.
* R2 `high_origin_clean`: such an origin is `Clean` for every later slot. (K0) `Σ.F` by
  finalized/high-origin compatibility; `Σ.J` at `t_s` is high (the `Σ.F` at the node's next call
  is), so its quorum carries no honest row naming a conflicting high entry
  (`no_honest_row_conflicting`). (K1) an excluded entry strictly extends a high `Σ.F`, so it is
  high and only faulty validators name it. (K2) `vote_height_lead` at each honest vote.
* R3 `late_sources_compatible`: sources from `T` on are high and below high origins.
* R4 `late_entry_high`: an ancestral entry of a late source whose slot starts after `T + 4Δ` is
  above the high `Σ.F₀` of the node's tick in `(T, T + 4Δ]`, at every height.
* R5 `late_entry_records`: the record entries at such an entry name only it
  (`ResetPremisesUpTo.record_entry_eq`). The first-source premise of `Rec.records` is not used. -/

namespace Consensus.Goldilocks.Healing.Recovery

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF a T : Time}

/-- The state before a cut equals the state before the node's next call. -/
theorem state_eq_next_call {y : Fin sp.n} {j k : Nat} (hjk : j ≤ k)
    (hno : ∀ m, j ≤ m → m < k → ¬ tr.IsCall y m) : tr.state y j = tr.state y k := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hjk ih =>
    rw [ih (fun m h1 h2 => hno m h1 (by omega))]
    simp only [Trace.state]
    split_ifs with h
    · exact absurd ⟨_, h.1, (Option.ne_none_iff_exists'.1 h.2).choose_spec⟩ (hno k hjk (by omega))
    · rfl

/-- **`Σ.F` is high at the first cut from a slot start after `T`.** -/
theorem high_F_firstCut (hp : ResetPremises tr H proposer dg g ΔF a) (hgT : gbar g ≤ T)
    (hF : HighFinalityFrom tr H g T) {y : Fin sp.n} (hy : y ∈ H) {s j : Nat} (hs : T < sp.ts s)
    (hj : tr.FirstCutFrom j (sp.ts s)) :
    HZ tr H g + 1 ≤ ((tr.state y j).fg.σ (tr.state y j).fg.F.root).h := by
  have h0 : 0 ≤ sp.ts s := le_trans (le_trans (SA.gbar_nonneg g) hgT) hs.le
  have hpub : sp.toParams.IsPublic (sp.ts s) := ⟨4 * (s : Int), by unfold SAParams.ts; ring⟩
  have haw : tr.awake y (sp.ts s) := hp.healthy.2.1 y hy _ (max_le
    (le_trans (le_trans (le_gbar g) hgT) hs.le) h0)
  obtain ⟨j', x, hg⟩ := hp.run.tick_of_awake y hy _ h0 hpub haw
  obtain ⟨hne, hk, -⟩ := hg
  obtain ⟨hn, ht, -, -, hl⟩ := hk 0 (List.length_pos_of_ne_nil hne)
  rw [Nat.add_zero] at hn ht hl
  have hcall : tr.IsCall y j' := ⟨_, hn, hl⟩
  have hjj' : j ≤ j' := by
    by_contra h
    exact absurd (hj.2 j' (by omega)) (by rw [ht]; exact lt_irrefl _)
  classical
  let k := Nat.find (p := fun k => j ≤ k ∧ tr.IsCall y k) ⟨j', hjj', hcall⟩
  have hk : j ≤ k ∧ tr.IsCall y k := Nat.find_spec (p := fun k => j ≤ k ∧ tr.IsCall y k) _
  have hmin : ∀ m, j ≤ m → m < k → ¬ tr.IsCall y m := fun m h1 h2 h3 =>
    Nat.find_min (p := fun k => j ≤ k ∧ tr.IsCall y k) _ h2 ⟨h1, h3⟩
  rw [state_eq_next_call hk.1 hmin]
  exact hF.at_call y hy k hk.2 (le_trans hs.le (le_trans hj.1 (hp.run.time_mono hk.1)))


/-- An honest row of a held entry `E` that conflicts with the high origin `B` cannot exist: a
high row names an entry below a high origin, and every high origin is comparable with `B`. -/
theorem no_honest_row_conflicting (hp : ResetPremises tr H proposer dg g ΔF a)
    {x : Fin sp.n} {i s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i s B) {z : Fin sp.n} (hz : z ∈ H) {m : Nat}
    {E : SA.Blk sp.n (List (FG.Att sp.n))} (hE : E ∈ (tr.state z m).fg.tree)
    (hEh : HZ tr H g + 1 ≤ ((tr.state z m).fg.σ E.root).h)
    (hnc : ¬ Compatible (tr.HonestBlocks H) E B)
    {v : Fin sp.n} (hv : v ∈ H) {d : Nat} {att : FG.Att sp.n} (hsd : tr.SignAt v d att)
    (haT : att.T = E.root) : False := by
  have hU := honest_coherent hp
  obtain ⟨E', hE', hE'r, hE'h⟩ := signAt_entry hp.run hv hsd
  obtain rfl : E' = E := hU.1 ⟨_, hv, d, hE'⟩ ⟨_, hz, m, hE⟩ (hE'r.trans haT)
  have hatt : HZ tr H g + 1 ≤ att.h := by
    rw [← hE'h, σ_eq_run hp hv hz hE' hE]; exact hEh
  obtain ⟨xo, io, jo, O, hoO, E₀, hE₀, hE₀O, hE₀r, -⟩ := high_rows hp v hv d att hsd
    (reset_le_of_high hp.run hp.healthy hp.reset hv hsd hatt) hatt
  obtain rfl : E₀ = E' := hU.1 ⟨_, hoO.1, io, hE₀⟩ ⟨_, hv, d, hE'⟩ (hE₀r.trans hE'r.symm)
  have hEO : Anc (tr.HonestBlocks H) E₀ O := hE₀O.mono fun X hX => ⟨_, hoO.1, io, hX⟩
  rcases (height_scoped_retention sp ro proposer dg H tr g ΔF hp.run hp.healthy hp.noColl a
    hp.reset).comparable xo io jo O x i s B hoO ho with hOB | hBO
  · exact hnc (Or.inl (hEO.trans hOB))
  · exact hnc (SA.anc_total hU hEO hBO)

/-- **(K0) at `t_s` for a high origin of a slot after `T`.** -/
theorem clean_caches (hp : ResetPremises tr H proposer dg g ΔF a) (hgT : gbar g ≤ T)
    (hF : HighFinalityFrom tr H g T) {x : Fin sp.n} {i s : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i s B) (hs : T < sp.ts s) :
    ∀ y ∈ H, ∀ j, tr.FirstCutFrom j (sp.ts s) →
      Compatible (tr.HonestBlocks H) (tr.state y j).fg.F B ∧
        Compatible (tr.HonestBlocks H) (tr.state y j).fg.J B := by
  intro y hy j hj
  refine ⟨finalized_compatible_high_origin_at_any_cut hp hy ho, ?_⟩
  have hU := honest_coherent hp
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy j
  have hsub : (tr.state y j).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, j, hX⟩
  obtain ⟨-, hJm, hFJ, ⟨Bj, hBj, hBjJ, hBjhj⟩, -⟩ := Store.cache_invariants _ _ _ _ hreach
  obtain ⟨E, hE, hEr, -, hcase⟩ := Store.J_entry_of_reachable hreach hBj
  obtain rfl : E = (tr.state y j).fg.J := hU.1 (hsub hE) (hsub hJm) (hEr.trans hBjJ)
  obtain ⟨-, -, -, -, -, -, -, -, -, hBx⟩ := highOrigin_mem hp ho
  have hgB := ((Store.accepted_tree _ _ _ _
    (Compose.fg_reachable hp.run.toLocalRun ho.1 i)).2.2.2 B hBx).mono
      (fun X hX => (⟨x, ho.1, i, hX⟩ : X ∈ tr.HonestBlocks H))
  rcases hcase with he | ⟨hEh, -⟩
  · rw [he]; exact Or.inl hgB
  have hhigh : HZ tr H g + 1 ≤ (tr.state y j).fg.hj := by
    have h1 := high_F_firstCut hp hgT hF hy hs hj
    have h2 := σ_h_le_of_anc hreach hFJ
    omega
  have hrow : ∀ E ∈ (tr.state y j).fg.tree,
      HZ tr H g + 1 ≤ ((tr.state y j).fg.σ E.root).h →
      ((tr.state y j).fg.σ E.root).Th = E.root → ¬ Compatible (tr.HonestBlocks H) E B →
      ∀ W ∈ (tr.state y j).fg.tree, ∀ att ∈ W.fgPayload, att.T = E.root → att.val ∉ H := by
    intro E hE hEh _ hnc W hW att ha haT haH
    rcases Compose.tree_cases hp.run.toLocalRun hy hW with rfl | ⟨i', -, hA⟩
    · cases ha
    obtain ⟨d, -, hsd⟩ :=
      hp.run.att_unforgeable y hy i' att (Or.inr ⟨W, ⟨true, hA⟩, ha⟩) haH
    exact no_honest_row_conflicting hp ho hy hE hEh hnc haH hsd haT
  exact Store.J_compatible_of_rows hreach (faulty_lt_q hp.healthy) hU hsub hgB hrow hhigh

/-- **(K1) for a high origin of a slot after `T`**: an excluded entry strictly extends a high
`Σ.F`, so it is high, and no honest validator names it. -/
theorem clean_rowCut (hp : ResetPremises tr H proposer dg g ΔF a) (hgT : gbar g ≤ T)
    (hF : HighFinalityFrom tr H g T) {x : Fin sp.n} {i s : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i s B) (hs : T < sp.ts s) (T₀ : Time) :
    ∀ E' ∈ Compose.excludedEntries tr H s B,
      (Store.namers sp.toParams (Payload sp.n) H tr.projFG T₀ E').ncard <
        sp.toParams.fg.q := by
  rintro E' ⟨hnc, y, hy, j, hj, hFE, -⟩
  refine lt_of_le_of_lt (Set.ncard_le_ncard (fun v hv => ?_) (Set.toFinite _))
    (faulty_lt_q hp.healthy)
  rcases hv with hv | ⟨d, att, hs', -, hT⟩
  · exact hv
  intro hvH
  have hsd := signAt_of_projFG hs'
  obtain ⟨E₁, hE₁, hE₁r, -⟩ := signAt_entry hp.run hvH hsd
  have hU := honest_coherent hp
  have hE'U : E' ∈ tr.HonestBlocks H := by
    rcases hFE.cases_tail with h | ⟨Z, -, hZ⟩
    · rw [h]; exact ⟨y, hy, j, (Store.cache_invariants _ _ _ _
        (Compose.fg_reachable hp.run.toLocalRun hy j)).1⟩
    · exact hZ.2.1
  obtain rfl : E₁ = E' := hU.1 ⟨_, hvH, d, hE₁⟩ hE'U (hE₁r.trans hT)
  have hFm := (Store.cache_invariants _ _ _ _ (Compose.fg_reachable hp.run.toLocalRun hy j)).1
  have hFv := mem_tree_of_anc hp hvH hFE hE₁
  have hh := σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun hvH d)
    (anc_tree_of_anc hp hvH hFE hE₁)
  rw [← σ_eq_run hp hy hvH hFm hFv] at hh
  exact no_honest_row_conflicting hp ho hvH hE₁
    ((high_F_firstCut hp hgT hF hy hs hj).trans hh) hnc hvH hsd hT

/-- **(K2) for a high origin**: R5 (`vote_height_lead`) at every honest vote of a later slot. -/
theorem clean_heightLead (hp : ResetPremises tr H proposer dg g ΔF a)
    {x : Fin sp.n} {i s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i s B) (m : Nat) :
    ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot → e.msg.slot ≤ m →
      (∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B D ∧ (tr.state y k).fg.IsViable D) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot :=
  fun _ hy k _ _ hc hj _ => vote_height_lead hp k (fun k' _ => retention_inv hp k') ho hy hc hj

/-- **R2: a high origin of a slot after `T` is clean** for every later slot. -/
theorem high_origin_clean (hp : ResetPremises tr H proposer dg g ΔF a) (hgT : gbar g ≤ T)
    (hF : HighFinalityFrom tr H g T) {x : Fin sp.n} {i s : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i s B) (hs : T < sp.ts s) :
    ∀ m, s < m → Compose.Clean tr H s m B := fun m _ =>
  ⟨clean_caches hp hgT hF ho hs, clean_rowCut hp hgT hF ho hs _, clean_heightLead hp ho m⟩


/-- **R1: a late stored fast write is a high origin of a slot after `T`.** -/
theorem late_write_high (hp : ResetPremises tr H proposer dg g ΔF a) (hgT : gbar g ≤ T)
    (hnr : NoRestartAfter tr H (gbar g)) (hF : HighFinalityFrom tr H g T)
    {x : Fin sp.n} {i s : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hwrite : Compose.StoredFastLockAt tr x i s B CV) (hx : x ∈ H)
    (ht : T + 12 * sp.Δ < tr.time i)
    (hjoin : SA.joined sp (tr.state x i).ac (tr.time i)) :
    T < sp.ts s ∧ HighOrigin tr H g x i s B := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨ℓ, D, hc, hfl, rfl⟩ := hwrite
  have hcall : tr.IsCall x i := ⟨_, Compose.projAC_callAt.1 hc⟩
  have h0 : 0 ≤ tr.time i := hp.run.time_nonneg i
  -- the slot starts after `T`
  have hts : T < sp.ts s := by
    rcases hfl with ⟨ℓ', C, ⟨-, -, htu, -⟩, -⟩ | ⟨ℓ', A, -, hsl, -⟩
    · change tr.time i = sp.ts s + 6 * sp.Δ at htu
      linarith
    · have hlt : tr.time i < sp.ts ((s + 1 : Nat) : Int) := by
        by_contra hle
        have := (SA.ts_le_iff_le_slot sp h0 _).1 (not_lt.1 hle)
        change sp.slot (tr.time i) = s at hsl
        omega
      have : sp.ts ((s + 1 : Nat) : Int) = sp.ts s + 4 * sp.Δ := by
        unfold SAParams.ts; push_cast; ring
      linarith
  refine ⟨hts, hx, ?_, ⟨CV, ℓ, D, hc, hfl, rfl⟩, ?_⟩
  · -- joined at the write
    have hnrx : ¬ tr.RestartAt x i := fun h => by
      have := hnr x hx i h
      linarith [SA.gbar_nonneg g]
    exact ((Compose.joined_projection sp ro dg H tr proposer hp.run x hx (tr.time i)).2.1 i
      hcall hnrx rfl).2 hjoin
  · -- the stored block is above the high `Σ.F` of the writer
    obtain ⟨ℓ', hc', hD⟩ := fastLock_mem hfl
    obtain rfl : ℓ = ℓ' := Option.some.inj (hc.2.symm.trans hc'.2)
    obtain ⟨hB, -⟩ := SA.viableAncestor_anc (SA.frameIn_of_callAt hr hx hc).1 hD
    rw [Compose.frame_of_projAC hp.run hx hc] at hB
    obtain ⟨hBt, hFB⟩ := hB
    have h1 := hF.at_call x hx i hcall (by linarith)
    have h2 := σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun hx i) hFB
    rw [Compose.frame_of_projAC hp.run hx hc]
    exact h1.trans h2


/-- The block that `ac_to_fg` returns is in the frame of the call. -/
private theorem toFG_mem_frame {FGP : Type} {A : SA.SAState sp.n} {Φ : SA.Frm sp.n FGP}
    {t : Time} {C : SA.Blk sp.n FGP} (h : (SA.acToFG sp A Φ t).2 = some C) : C ∈ Φ.tree := by
  unfold SA.acToFG at h
  split_ifs at h
  split at h
  · cases h
  · rename_i C' hC'
    split_ifs at h
    cases h
    exact (SA.deepest_mem hC').1.1.1

/-- A source at an honest call from `T` on is high and below a high origin. -/
theorem late_source_origin (hp : ResetPremises tr H proposer dg g ΔF a)
    (hF : HighFinalityFrom tr H g T) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hC : SA.ToFGAt tr.projAC y k ell C) (ht : T ≤ tr.time k) :
    HZ tr H g + 1 ≤ ((tr.state y k).fg.σ C.root).h ∧
      ∃ io < k, ∃ jo B, HighOrigin tr H g y io jo B ∧ Anc (tr.HonestBlocks H) C B := by
  have hCm := toFG_mem_frame hC.2.2
  rw [Compose.frame_of_projAC hp.run hy hC.1] at hCm
  have hh := (hF.at_call y hy k ⟨_, Compose.projAC_callAt.1 hC.1⟩ ht).trans
    (σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun hy k) hCm.2)
  exact ⟨hh, high_report_origin hp hy hC hh⟩

/-- **R3: late sources are compatible.** -/
theorem late_sources_compatible (hp : ResetPremises tr H proposer dg g ΔF a)
    (hF : HighFinalityFrom tr H g T) {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {k j : Nat}
    {ell ell' : ACLabel (goldilocksNode sp ro)} {C D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hC : SA.ToFGAt tr.projAC y k ell C) (hD : SA.ToFGAt tr.projAC z j ell' D)
    (htC : T ≤ tr.time k) (htD : T ≤ tr.time j) :
    Compatible (tr.HonestBlocks H) C D := by
  have hU := honest_coherent hp
  obtain ⟨_, _, _, _, B, hoB, hCB⟩ := late_source_origin hp hF hy hC htC
  obtain ⟨_, _, _, _, B', hoB', hDB'⟩ := late_source_origin hp hF hz hD htD
  rcases (height_scoped_retention sp ro proposer dg H tr g ΔF hp.run hp.healthy hp.noColl a
    hp.reset).comparable _ _ _ B _ _ _ B' hoB hoB' with hBB' | hB'B
  · exact SA.anc_total hU (hCB.trans hBB') hDB'
  · exact SA.anc_total hU hCB (hDB'.trans hB'B)


/-- A block of an honest tree before cut `j` is not of a later slot than `j`'s time. -/
theorem tree_slot_le (hp : ResetPremises tr H proposer dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H)
    {j : Nat} {X : SA.Blk sp.n (List (FG.Att sp.n))} (hX : X ∈ (tr.state y j).fg.tree) :
    X.slot ≤ sp.slot (tr.time j) := by
  rcases Compose.tree_cases hp.run.toLocalRun hy hX with rfl | ⟨k, hk, hacc⟩
  · exact Nat.zero_le _
  · exact ((hp.run.cutLaw y hy k _ hacc).1).trans
      (SA.slot_mono sp (hp.run.time_nonneg k) (hp.run.time_mono hk.le))

/-- An honest node has a call with a high `Σ.F` in `(T, T + 4Δ]`: its tick at the next slot
start. -/
theorem high_F_call_soon (hp : ResetPremises tr H proposer dg g ΔF a) (hgT : gbar g ≤ T)
    (hF : HighFinalityFrom tr H g T) {y : Fin sp.n} (hy : y ∈ H) :
    ∃ j, tr.IsCall y j ∧ T < tr.time j ∧ tr.time j ≤ T + 4 * sp.Δ ∧
      tr.time j = sp.ts (sp.slot T + 1 : Nat) ∧
      HZ tr H g + 1 ≤ ((tr.state y j).fg.σ (tr.state y j).fg.F.root).h := by
  have hT0 : 0 ≤ T := le_trans (SA.gbar_nonneg g) hgT
  set t₀ := sp.ts (sp.slot T + 1 : Nat) with ht₀
  have hlt : T < t₀ := by
    by_contra hle
    have := (SA.ts_le_iff_le_slot sp hT0 _).1 (not_lt.1 hle)
    push_cast at this; omega
  have hle : t₀ ≤ T + 4 * sp.Δ := by
    have h1 := (SA.ts_le_iff_le_slot sp hT0 (sp.slot T : Int)).2 le_rfl
    have : t₀ = sp.ts (sp.slot T : Int) + 4 * sp.Δ := by
      rw [ht₀]; unfold SAParams.ts; push_cast; ring
    linarith
  have h0 : 0 ≤ t₀ := by linarith
  have hpub : sp.toParams.IsPublic t₀ := ⟨4 * ((sp.slot T + 1 : Nat) : Int), by
    rw [ht₀]; unfold SAParams.ts; ring⟩
  have haw : tr.awake y t₀ := hp.healthy.2.1 y hy _ (max_le
    (by linarith [le_gbar g]) h0)
  obtain ⟨j, x, hne, hk, -⟩ := hp.run.tick_of_awake y hy _ h0 hpub haw
  obtain ⟨hn, ht, -, -, hl⟩ := hk 0 (List.length_pos_of_ne_nil hne)
  rw [Nat.add_zero] at hn ht hl
  exact ⟨j, ⟨_, hn, hl⟩, by rw [ht]; exact hlt, by rw [ht]; exact hle, ht,
    hF.at_call y hy j ⟨_, hn, hl⟩ (by rw [ht]; exact hlt.le)⟩

/-- **R4: a new ancestral entry of a late source is high.** The source's node had a high `Σ.F₀`
at its tick in `(T, T + 4Δ]`, which is below the source and of a slot before the entry's, so the
entry is above `F₀`. -/
theorem late_entry_high (hp : ResetPremises tr H proposer dg g ΔF a) (hgT : gbar g ≤ T)
    (hF : HighFinalityFrom tr H g T) {y : Fin sp.n} (hy : y ∈ H) {k h : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {C E : SA.Blk sp.n (List (FG.Att sp.n))}
    (hC : SA.ToFGAt tr.projAC y k ell C) (ht : T + 4 * sp.Δ < tr.time k)
    (hE : EntryOf (tr.state y k).fg C E h) (hslot : T + 4 * sp.Δ < sp.ts E.slot) :
    HZ tr H g + 1 ≤ h := by
  have hU := honest_coherent hp
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy k
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, k, hX⟩
  obtain ⟨⟨hEt, -⟩, rfl, hEC⟩ := hE
  obtain ⟨j₀, -, -, hj₀T, -, hF₀⟩ := high_F_call_soon hp hgT hF hy
  have hj₀k : j₀ ≤ k := by
    by_contra hc
    have := hp.run.time_mono (show k ≤ j₀ by omega)
    linarith
  have hF₀k := Healing.run_F_mono hp.run.toLocalRun hy hj₀k
  have hCm := toFG_mem_frame hC.2.2
  rw [Compose.frame_of_projAC hp.run hy hC.1] at hCm
  have hF₀C := hF₀k.trans (hCm.2.mono hsub)
  set F₀ := (tr.state y j₀).fg.F
  have hF₀m : F₀ ∈ (tr.state y j₀).fg.tree :=
    (Store.cache_invariants _ _ _ _ (Compose.fg_reachable hp.run.toLocalRun hy j₀)).1
  rcases SA.anc_total hU (hEC.mono hsub) hF₀C with hEF | hFE
  · -- `E ⪯ F₀` is impossible: `F₀`'s slot starts by `T + 4Δ`, before `E`'s
    exfalso
    have h1 := Anc.slot_le hU hEF
    have h2 := tree_slot_le hp hy hF₀m
    have h0 : 0 ≤ tr.time j₀ := hp.run.time_nonneg j₀
    have h3 := (SA.ts_le_iff_le_slot sp h0 (sp.slot (tr.time j₀) : Int)).2 le_rfl
    have h4 : sp.ts E.slot ≤ sp.ts (sp.slot (tr.time j₀) : Int) :=
      (SA.ts_le_iff sp).2 (by exact_mod_cast h1.1.trans h2)
    linarith
  · have hF₀y := mem_tree_of_anc hp hy hFE hEt
    have hh := σ_h_le_of_anc hreach (anc_tree_of_anc hp hy hFE hEt)
    rw [← σ_eq_run hp hy hy hF₀m hF₀y] at hh
    exact hF₀.trans hh


/-- **R5: the record at a new high entry names only that entry.** -/
theorem late_entry_records (hp : ResetPremises tr H proposer dg g ΔF a) (hgT : gbar g ≤ T)
    (hF : HighFinalityFrom tr H g T) {y : Fin sp.n} (hy : y ∈ H) {k h : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {C E : SA.Blk sp.n (List (FG.Att sp.n))}
    (hC : SA.ToFGAt tr.projAC y k ell C) (ht : T + 4 * sp.Δ < tr.time k)
    (hE : EntryOf (tr.state y k).fg C E h) (hslot : T + 4 * sp.Δ < sp.ts E.slot) :
    ((tr.state y k).record.target h = none ∨ (tr.state y k).record.target h = some E.root) ∧
      (∀ r ∈ (tr.state y k).record.timeout h, r = E.root) ∧
      ((tr.state y k).record.lock h = none ∨ (tr.state y k).record.lock h = some E.root) := by
  have hh := late_entry_high hp hgT hF hy hC ht hE hslot
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, k, hX⟩
  obtain ⟨_, io, -, jo, B, ho, hCB⟩ := late_source_origin hp hF hy hC (by linarith [sp.toParams.hΔ])
  obtain ⟨⟨hEt, hET⟩, hEh, hEC⟩ := hE
  have hEB := (hEC.mono hsub).trans hCB
  set b := max (max a (tr.time k)) (tr.time io)
  have hp' := hp.toUpTo tr H (show a ≤ b from (le_max_left _ _).trans (le_max_left _ _))
  have key : ∀ r, ((tr.state y k).record.target h = some r ∨ r ∈ (tr.state y k).record.timeout h ∨
      (tr.state y k).record.lock h = some r) → r = E.root := fun r hr =>
    hp'.record_entry_eq hy ((le_max_right _ _).trans (le_max_left _ _)) hh hr ho
      (le_max_right _ _) hEB hy hEt hEh hET
  refine ⟨?_, fun r hr => key r (Or.inr (Or.inl hr)), ?_⟩
  · rcases ht' : (tr.state y k).record.target h with _ | r
    · exact Or.inl rfl
    · exact Or.inr (by rw [key r (Or.inl ht')])
  · rcases hl : (tr.state y k).record.lock h with _ | r
    · exact Or.inl rfl
    · exact Or.inr (by rw [key r (Or.inr (Or.inr hl))])


/-- **Recovery from permanent high finality**: `Rec` from `T + 12Δ` on. -/
theorem rec_of_high_finality (hp : ResetPremises tr H proposer dg g ΔF a) (hgT : gbar g ≤ T)
    (hnr : NoRestartAfter tr H (gbar g)) (hF : HighFinalityFrom tr H g T) :
    Rec tr H (T + 12 * sp.Δ) := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  refine ⟨fun x hx i s B CV hw ht hj m hsm => ?_, fun y hy z hz k ℓ C k' ℓ' C' hC hC' ht ht' => ?_,
    fun y hy k ℓ C E h hC ht hE hs _ => ?_⟩
  · obtain ⟨hts, ho⟩ := late_write_high hp hgT hnr hF hw hx ht hj
    exact high_origin_clean hp hgT hF ho hts m hsm
  · exact late_sources_compatible hp hF hy hz hC hC' (by linarith) (by linarith)
  · exact late_entry_records hp hgT hF hy hC (by linarith) hE (by linarith)

/-- Lane B's interface obligation, from `rec_of_high_finality`. -/
theorem recoveryFromHighFinality :
    RecoveryFromHighFinality tr H proposer dg g ΔF a T :=
  ⟨fun hp hgT hnr hF => rec_of_high_finality hp hgT hnr hF⟩

end Consensus.Goldilocks.Healing.Recovery

end

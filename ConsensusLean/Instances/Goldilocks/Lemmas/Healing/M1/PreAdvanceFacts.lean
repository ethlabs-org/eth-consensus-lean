module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireClient

public section

/-! # M1′ A2 and A3: honest locks before the advance (LH, F3-lock, O1-L)

All lemmas hold at every honest cut; only the
F3-lock lemma uses the NoAdvance premise.

* `hj_ge_of_lock` (LH): an honest record lock at height `h` gives own `h_j ≥ h`.
* `lock_root_eq_J` (kind J): a lock at `h = h_j` names `Σ.J`.
* `lock_none_of_noAdvance` (F3-lock): before the advance there is no lock at `H_z`.
* `client_progress_of_lock` (A-item 3): `client_progress` with the lock premise as a
  hypothesis, in place of `HSShared` and `PhaseOn`.
* `lock_free_or_entry_of_frame` and `client_signs_of_frame` (O1-L): in kind F
  (`h_j < h`) or kind J (`h_j = h`, `Σ.J ⪯ C`) the lock at the source height is free or the
  entry, so the client signs the attestation now or signed it before. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

private theorem fg_run (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr) :
    FGLocalRun (goldilocksNode sp ro).genesisPayload H (tr.HonestBlocks H) tr.projFG := by
  have hreq := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  exact Compose.fg_projection _ _ dg H _ tr proposer
    ⟨hreq.1, hreq.2.1, hreq.2.2.1, hreq.2.2.2, SA.proposal_payload_valid sp _ ro⟩
    hrun.genesis_root_ok hrun.toLocalRun hnc

/-- An ancestor of genesis in a store is genesis. -/
private theorem eq_genesis_of_anc {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    {X : NodeBlock P ACP} (h : st.Anc X (P.genesisBlock acp₀)) : X = P.genesisBlock acp₀ := by
  rcases h.cases_tail with rfl | ⟨Y, -, hY⟩
  · rfl
  · exact absurd hY.2.2 (by simp [Params.genesisBlock])

/-- The state height of `Σ.F` is at most `h_j`, or `Σ.F` is genesis. -/
private theorem F_h_le_hj (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n} (hy : y ∈ H)
    (k : Nat) :
    (tr.state y k).fg.F = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload ∨
      ((tr.state y k).fg.σ (tr.state y k).fg.F.root).h ≤ (tr.state y k).fg.hj := by
  have hR := Compose.fg_reachable hrun.toLocalRun hy k
  obtain ⟨hFm, hJm, hFJ, ⟨Bj, hBj, hBjJ, hBjhj⟩, -⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hR
  obtain ⟨E, hE, hEr, -, hEg⟩ := Store.J_entry_of_reachable hR hBj
  have hEJ : E.root = (tr.state y k).fg.J.root := hEr.trans hBjJ
  have hFh := h_le_of_store_anc hR hFJ
  rcases hEg with rfl | ⟨hEh, -⟩
  · left
    have h1 : (tr.state y k).fg.blocks
        (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).root =
        some (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload) := hE
    have h2 : (tr.state y k).fg.blocks (tr.state y k).fg.J.root =
        some (tr.state y k).fg.J := hJm
    rw [hEJ] at h1
    rw [Option.some.inj (h2.symm.trans h1)] at hFJ
    exact eq_genesis_of_anc hFJ
  · right
    rw [← hEJ, hEh, hBjhj] at hFh
    exact hFh

/-- **Lemma LH.** An honest record lock at height `h` gives own `h_j ≥ h`. Premises:
the run, no collision and `f < 2q − n`. -/
theorem hj_ge_of_lock (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) {y : Fin sp.n} (hy : y ∈ H) {k h r : Nat}
    (hl : (tr.state y k).record.lock h = some r) : h ≤ (tr.state y k).fg.hj := by
  obtain ⟨k', hk', att, hsa, hfin⟩ := (record_facts hrun hy k).2.2 h r hl
  obtain ⟨B, hB, hBj, hBJ⟩ := signed_fin_justified hrun hy hsa hfin
  refine le_trans ?_ (hj_mono hrun hy hk'.le)
  have hR := Compose.fg_reachable hrun.toLocalRun hy k'
  by_contra hlt
  have hlt' : (tr.state y k').fg.hj < ((tr.state y k').fg.σ B.root).h := by
    have := Store.hj_lt_h hR hB
    omega
  have hFB := store_anc_of_honest_anc hrun hnc hy (F_anc_of_hj_lt hrun hnc hf hy hy hB hlt') hB
  obtain ⟨E, hE, hEr, hEB, -⟩ := Store.J_entry_of_reachable hR hB
  have hEh := Store.J_height_le hR hB hE hEr
  have hcoh : Coherent (tr.state y k').fg.tree :=
    (Compose.honest_blocks_coherent hrun.toLocalRun hnc).mono
      fun X hX => (⟨y, hy, k', hX⟩ : X ∈ tr.HonestBlocks H)
  have hjmax := (jMax_iff _).1 (jMax_of_reachable hR) B hB E hE hEr
  have hgE : (tr.state y k').fg.Anc
      (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload) E :=
    (Goldilocks.Store.accepted_tree _ _ _ _ hR).2.2.2 _ hE
  rcases Anc.total hcoh hFB hEB with hFE | hEF
  · have := hjmax hFE
    omega
  · rcases F_h_le_hj hrun hy k' with hFg | hFh
    · have := hjmax (hFg ▸ hgE)
      omega
    · have := h_le_of_store_anc hR hEF
      omega

/-- **O1-L, kind F.** Without a justification at `h` (`h_j < h`), the lock at `h` is free. -/
theorem lock_none_of_hj_lt (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {k h : Nat} (hlt : (tr.state y k).fg.hj < h) :
    (tr.state y k).record.lock h = none := by
  rcases hl : (tr.state y k).record.lock h with _ | r
  · rfl
  · have := hj_ge_of_lock hrun hnc hf hy hl
    omega

/-- **O1-L, kind J.** A lock at `h = h_j` names `Σ.J` (the lock's carrier and the cache justify
at the same height; PhaseCount (a)). -/
theorem lock_root_eq_J (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) {y : Fin sp.n} (hy : y ∈ H) {k h r : Nat}
    (hl : (tr.state y k).record.lock h = some r) (hj : (tr.state y k).fg.hj = h) :
    r = (tr.state y k).fg.J.root := by
  obtain ⟨k', -, att, hsa, hfin⟩ := (record_facts hrun hy k).2.2 h r hl
  obtain ⟨B, hB, hBj, hBJ⟩ := signed_fin_justified hrun hy hsa hfin
  obtain ⟨-, -, -, ⟨Bj, hBjt, hBjJ, hBjhj⟩, -⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ (Compose.fg_reachable hrun.toLocalRun hy k)
  have he := J_eq_of_hj_eq (fg_run hrun hnc) hf hy hy (i := k') (j := k) (B := B) (B' := Bj)
    (by rw [store_eq_fg hrun hy]; exact hB) (by rw [store_eq_fg hrun hy]; exact hBjt)
    (by rw [store_eq_fg hrun hy, store_eq_fg hrun hy, hBj, hBjhj, hj])
  rw [store_eq_fg hrun hy, store_eq_fg hrun hy, hBJ, hBjJ] at he
  exact he

/-- **F3-lock.** Before the advance (no honest signature of height `> H_z` at a time
`< T`), an honest node has no lock at `H_z` at a cut before `T`: such a lock is the finality
pair of a signed attestation of height `> H_z` (well-formedness). -/
theorem lock_none_of_noAdvance (hrun : GoldilocksRun proposer dg H tr) {g T : Time}
    (hna : ∀ v ∈ H, ∀ k att, tr.SignAt v k att → tr.time k < T → att.h ≤ HZ tr H g)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (hkT : tr.time k < T) :
    (tr.state y k).record.lock (HZ tr H g) = none := by
  rcases hl : (tr.state y k).record.lock (HZ tr H g) with _ | r
  · rfl
  obtain ⟨k', hk', att, hsa, hfin⟩ := (record_facts hrun hy k).2.2 _ r hl
  have hwf := signAt_wellFormed hrun hy hsa
  have hT := hna y hy k' att hsa (lt_of_le_of_lt (hrun.time_mono hk'.le) hkT)
  have := hwf.2 (HZ tr H g, r) (by simp [hfin])
  omega

/-- **A-item 3.** `client_progress` with the lock premise as a hypothesis (no `HSShared`, no
phase): at an honest `fg_attest(C)` with `C` of state height `h` and entry `E`, if the lock at
`h` is free or `E`, the client signs an attestation `(h, E)` now or signed one at an earlier cut. -/
theorem client_progress_of_lock (hrun : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))} {signed : Option (FG.Att sp.n)}
    (hc : tr.CallAt y k (.fg (.attest C signed))) {E : SA.Blk sp.n (List (FG.Att sp.n))} {h : Nat}
    (hE : EntryOf (tr.state y k).fg C E h) (hCh : ((tr.state y k).fg.σ C.root).h = h)
    (hlock : (tr.state y k).record.lock h = none ∨
      (tr.state y k).record.lock h = some E.root) :
    (∃ att, signed = some att ∧ att.h = h ∧ att.T = E.root) ∨
      ∃ k' < k, ∃ att, tr.SignAt y k' att ∧ att.h = h ∧ att.T = E.root := by
  have hr := Compose.fg_reachable hrun.toLocalRun hy k
  obtain ⟨⟨-, hETh⟩, hEh, hEC⟩ := hE
  have hCTh : ((tr.state y k).fg.σ C.root).Th = E.root := by
    rw [Th_eq_of_anc hr hEC (hCh.trans hEh.symm), hETh]
  have hσe : (tr.state y k).fg.σ ((tr.state y k).fg.σ C.root).Th =
      (tr.state y k).fg.σ E.root := by rw [hCTh]
  have he₁ : ((tr.state y k).fg.σ E.root).h = h := hEh
  have he₂ : ((tr.state y k).fg.σ E.root).Th = E.root := hETh
  have hlaw := hrun.cutLaw y hy k _ hc
  cases signed with
  | some a =>
    have hcl := hlaw.1
    change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
      ((tr.state y k).fg.σ C.root).Th) = some (a, _) at hcl
    rw [hσe] at hcl
    obtain ⟨-, hah, haT, -⟩ := Client.createAtt_some hcl
    exact Or.inl ⟨a, rfl, hah.trans he₁, haT.trans he₂⟩
  | none =>
    have hcl := hlaw.1
    change (tr.state y k).record.createAtt y ((tr.state y k).fg.σ
      ((tr.state y k).fg.σ C.root).Th) = none at hcl
    rw [hσe] at hcl
    rcases Client.createAtt_none hcl with ⟨h1, h2⟩ | ⟨b, hb, hbh, hbT⟩
    · simp only [he₁, he₂] at h1 h2
      rcases hlock with hl | hl
      · exact absurd hl h1
      · exact absurd hl h2
    simp only [he₁, he₂] at hbh hbT
    obtain ⟨hok, hsent, -⟩ := record_facts hrun hy k
    have hbT' : b.2.1 = E.root := by
      rcases hbT with hbT | ⟨hto, htg⟩
      · exact hbT
      obtain ⟨h1, h2⟩ := (Client.sentOK_iff _).1 hok b hb
      cases hτ : b.2.2.1
      · have := h2 hτ
        rw [hbh] at this
        rcases htg with htg | htg <;> rw [htg] at this
        · cases this
        · exact (Option.some.inj this).symm
      · have := h1 hτ
        rw [hbh, hto] at this
        simp at this
    obtain ⟨k', hk', att, hsa, rfl⟩ := hsent b hb
    exact Or.inr ⟨k', hk', att, hsa, hbh, hbT'⟩

/-- **O1-L, the lock.** At an honest cut, let `C` have state height `h` and entry `E`.
In kind F (`h_j < h`) the lock at `h` is free. In kind J (`h_j = h` and `Σ.J ⪯ C`) it is free
or `E`. -/
theorem lock_free_or_entry_of_frame (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {C E : SA.Blk sp.n (List (FG.Att sp.n))} {h : Nat}
    (hE : EntryOf (tr.state y k).fg C E h) (hCh : ((tr.state y k).fg.σ C.root).h = h)
    (hkind : (tr.state y k).fg.hj < h ∨
      ((tr.state y k).fg.hj = h ∧ (tr.state y k).fg.Anc (tr.state y k).fg.J C)) :
    (tr.state y k).record.lock h = none ∨ (tr.state y k).record.lock h = some E.root := by
  rcases hkind with hlt | ⟨hj, hJC⟩
  · exact Or.inl (lock_none_of_hj_lt hrun hnc hf hy hlt)
  rcases hl : (tr.state y k).record.lock h with _ | r
  · exact Or.inl rfl
  refine Or.inr (congrArg some ?_)
  rw [lock_root_eq_J hrun hnc hf hy hl hj]
  have hr := Compose.fg_reachable hrun.toLocalRun hy k
  obtain ⟨⟨-, hETh⟩, hEh, hEC⟩ := hE
  obtain ⟨-, hJm, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hr
  have hJh := Store.J_height_le hr hBj hJm hBjJ.symm
  have hJCh := h_le_of_store_anc hr hJC
  obtain ⟨E', hE', hE'r, -, hE'g⟩ := Store.J_entry_of_reachable hr hBj
  have hE'J : E' = (tr.state y k).fg.J := by
    have h1 : (tr.state y k).fg.blocks E'.root = some E' := hE'
    have h2 : (tr.state y k).fg.blocks (tr.state y k).fg.J.root =
      some (tr.state y k).fg.J := hJm
    rw [hE'r, hBjJ] at h1
    exact Option.some.inj (h1.symm.trans h2)
  subst hE'J
  have hJTh : ((tr.state y k).fg.σ (tr.state y k).fg.J.root).Th = (tr.state y k).fg.J.root := by
    rcases hE'g with he | ⟨-, hTh⟩
    · have hg : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).root =
          sp.toParams.genesisRoot := rfl
      rw [he, hg, Store.σ_genesis hr]
      rfl
    · exact hTh
  -- `σ[J].h = h`: `h ≤ σ[J].h ≤ σ[C].h = h`
  have hJeq : ((tr.state y k).fg.σ C.root).h =
      ((tr.state y k).fg.σ (tr.state y k).fg.J.root).h := by omega
  have h1 := Th_eq_of_anc hr hJC hJeq
  have h2 := Th_eq_of_anc hr hEC (hCh.trans hEh.symm)
  rw [hJTh] at h1
  rw [hETh] at h2
  exact h1.symm.trans h2

/-- **O1-L, the attestation.** At an honest `fg_attest(C)` with `C` of state height `h` and
entry `E`, in kind F or kind J, the client signs `(h, E)` now or signed it before. -/
theorem client_signs_of_frame (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {C : SA.Blk sp.n (List (FG.Att sp.n))}
    {signed : Option (FG.Att sp.n)} (hc : tr.CallAt y k (.fg (.attest C signed)))
    {E : SA.Blk sp.n (List (FG.Att sp.n))} {h : Nat}
    (hE : EntryOf (tr.state y k).fg C E h) (hCh : ((tr.state y k).fg.σ C.root).h = h)
    (hkind : (tr.state y k).fg.hj < h ∨
      ((tr.state y k).fg.hj = h ∧ (tr.state y k).fg.Anc (tr.state y k).fg.J C)) :
    (∃ att, signed = some att ∧ att.h = h ∧ att.T = E.root) ∨
      ∃ k' < k, ∃ att, tr.SignAt y k' att ∧ att.h = h ∧ att.T = E.root :=
  client_progress_of_lock hrun hy hc hE hCh
    (lock_free_or_entry_of_frame hrun hnc hf hy hE hCh hkind)

/-- **The attestation at `H_z` before the advance (ROW-sign, h = H_z).** -/
theorem client_signs_HZ_of_noAdvance (hrun : GoldilocksRun proposer dg H tr) {g T : Time}
    (hna : ∀ v ∈ H, ∀ k att, tr.SignAt v k att → tr.time k < T → att.h ≤ HZ tr H g)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (hkT : tr.time k < T)
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {signed : Option (FG.Att sp.n)}
    (hc : tr.CallAt y k (.fg (.attest C signed))) {E : SA.Blk sp.n (List (FG.Att sp.n))}
    (hE : EntryOf (tr.state y k).fg C E (HZ tr H g))
    (hCh : ((tr.state y k).fg.σ C.root).h = HZ tr H g) :
    (∃ att, signed = some att ∧ att.h = HZ tr H g ∧ att.T = E.root) ∨
      ∃ k' < k, ∃ att, tr.SignAt y k' att ∧ att.h = HZ tr H g ∧ att.T = E.root :=
  client_progress_of_lock hrun hy hc hE hCh (Or.inl (lock_none_of_noAdvance hrun hna hy hkT))

end Consensus.Goldilocks.Healing

end

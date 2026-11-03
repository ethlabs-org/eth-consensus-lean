module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting

public section

/-! # Goldilocks Healing: trivial frames, the honest batch, and fast-origin transfer (T1 §3)

Over a `StandaloneRun` (H.1's premises), with `r = r_AC(ḡ)` (a slot `j` is `≥ r` exactly when
`ḡ + 4Δ ≤ t_j`):

* **trivial frames** (claims H.1 proof shape, "Viability and Carry come from relay and
  `Catch`"): acceptance relay before a deadline (`relay_accept`), block stamps
  (`blockStamp_cases`, `accepted_of_blockStamp_lt`), viability at a vote (`trivial_viable`) and
  `Carry` (`carry_of_sent`, `trivial_carry_update`, `trivial_carry_fastLock`,
  `trivial_carry_votes`);
* **the honest batch** (`honest_voters_half`): in a slot `≥ r` every honest node votes;
* **T1 §3 for the votes**: `votes_continue` (A1.3 by induction on slots) and
  `fast_origin_transfer_votes` (A1.2/A1.4 at the next slot by the first bad vote). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {proposer : Nat → Fin sp.n}

/-! ## Helpers -/

/-- The walk of a subtree of a well-formed frame ends in the frame's tree. -/
theorem getHead_mem' {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {T : Set (Blk sp.n FGP)}
    (hT : T ⊆ Φ.tree) (A : SAState sp.n) (t : Time) (V : View sp.n) (σ : Int) :
    getHead sp A Φ t T V σ ∈ Φ.tree := by
  have ha : getAnchor sp A Φ t ∈ Φ.tree := by
    unfold getAnchor
    cases hd : deepest Φ (liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot}) with
    | none => exact hΦ.fcRoot_mem
    | some D =>
      rcases (deepest_mem hd).1 with h | h
      · exact h.1
      · exact (Set.mem_singleton_iff.1 h) ▸ hΦ.fcRoot_mem
  obtain h | h := eq_or_ne (getAnchor sp A Φ t) (getHead sp A Φ t T V σ)
  · exact h ▸ ha
  · exact (Anc.mem (C := getHead sp A Φ t T V σ) (anc_ghost hT _ ha) h).2

private theorem bs_admitVote (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).blockStamp = A.blockStamp := by
  unfold admitVote; split_ifs <;> rfl

private theorem bs_optimistic (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).blockStamp = A.blockStamp := by
  unfold optimisticConfirmation updateLatestConfirmed; split
  · rfl
  · split_ifs <;> rfl

private theorem lastWake_cases (y : Fin sp.n) : ∀ c, tr.lastWake y c = ⊥ ∨
    ∃ k ≤ c, tr.RestartAt y k ∧ tr.lastWake y c = (tr.time k : WithBot Time)
  | 0 => by
    unfold ACTrace.lastWake
    split_ifs with h
    · exact Or.inr ⟨0, le_rfl, h, rfl⟩
    · exact Or.inl rfl
  | c + 1 => by
    unfold ACTrace.lastWake
    split_ifs with h
    · exact Or.inr ⟨c + 1, le_rfl, h, rfl⟩
    · rcases lastWake_cases y c with h' | ⟨k, hk, hrk, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨k, hk.trans (Nat.le_succ c), hrk, h'⟩

/-- Under `Healthy(g)`, the delivery deadline of an object of time `τ` at an honest node is at
most `max(τ, ḡ) + Δ` (no restart after `ḡ`). -/
theorem HealthyBase.deadline_le (hS : HealthyBase tr H U proposer g) {y : Fin sp.n} (hy : y ∈ H)
    (c : Nat) (τ : Time) : tr.deadline y c τ ≤ max τ (gbar g) + sp.Δ := by
  unfold ACTrace.deadline
  rcases lastWake_cases (tr := tr) y c with h | ⟨k, -, hrk, h⟩
  · rw [h]
    change τ + sp.Δ ≤ _
    linarith [le_max_left τ (gbar g)]
  · rw [h]
    change max τ (tr.time k) + sp.Δ ≤ _
    linarith [max_le_max_left τ (hS.restart_le hy hrk)]

/-- Under trivial frames, `Φ.F` is the same block at every honest call. -/
theorem trivial_F_eq (hS : StandaloneRun tr H U proposer g) {y z : Fin sp.n} (hy : y ∈ H)
    (hz : z ∈ H) {i j : Nat} {ℓ ℓ' : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ)
    (hc' : tr.CallAt z j ℓ') : ℓ.frame.F = ℓ'.frame.F := by
  have hr := hS.run.localRun
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
  obtain ⟨hΦ', hΦ'U⟩ := frameIn_of_callAt hr hz hc'
  exact hr.coherent.1 (hΦU hΦ.rooted.1) (hΦ'U hΦ'.rooted.1)
    ((hS.trivial y hy i ℓ hc).1.trans (hS.trivial z hz j ℓ' hc').1.symm)

/-! ## Trivial frames: viability and `Carry` -/

/-! ## Trivial frames: blocks, stamps, relay and held votes -/

private theorem etime_lt {a b : Time} : ETime.of a < ETime.of b ↔ a < b := by
  simp [ETime.of]

private theorem etime_le {a b : Time} : ETime.of a ≤ ETime.of b ↔ a ≤ b := by
  simp [ETime.of]

private theorem ts_succ (s : Nat) : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
  simp only [SAParams.ts]; push_cast; ring

/-- Under trivial frames, an ancestor (inside `U`) of a block of an honest node's frame is
`Φ.F` (genesis) or a block the node accepted by then. -/
theorem trivial_anc_mem (hS : StandaloneRun tr H U proposer g) {x : Fin sp.n} (hx : x ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x k ℓ) {Hv X : Blk sp.n FGP}
    (hHv : Hv ∈ ℓ.frame.tree) (hX : Anc U X Hv) :
    X = ℓ.frame.F ∨ ∃ k' ≤ k, tr.AcceptAt x k' X := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  obtain ⟨hF, -, -, htree⟩ := hS.trivial x hx k ℓ hc
  rcases anc_total hU hX ((hΦ.rooted.2 Hv hHv).mono hΦU) with h | h
  · left
    obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_call sp hr hx k ℓ hc
    have hFG : ℓ.frame.F = G := hU.1 (hΦU hΦ.rooted.1) hGU (hF.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h with h | ⟨c, -, hp⟩
    · exact h.symm
    · have := hp.2.2
      rw [hFG, hGp] at this
      exact absurd this (by simp)
  · have hXt := frame_mem_of_between sp hU hΦ hΦU hHv hX h
    rw [htree] at hXt
    exact Set.mem_insert_iff.1 hXt

/-- **Acceptance relay before a deadline** (`Healthy(g)` from `g` on, `Catch(2Δ)` before): a
block an honest `z` accepted before `T ≥ ḡ + Δ`, extending `Φ.F`, is accepted by every honest
`y` before `T + Δ`, read at any call of `y` from `T + Δ` on. -/
theorem relay_accept (hS : StandaloneRun tr H U proposer g) {z : Fin sp.n} (hz : z ∈ H) {k : Nat}
    {X : Blk sp.n FGP} (hacc : tr.AcceptAt z k X) {T : Time} (hkT : tr.time k < T)
    (hT : gbar g + sp.Δ ≤ T) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) (hi : T + sp.Δ ≤ tr.time i)
    (hF : Anc U ℓ.frame.F X) : ∃ k' ≤ i, tr.AcceptAt y k' X ∧ tr.time k' < T + sp.Δ := by
  have hΔ := sp.toParams.hΔ
  have hmax : max (tr.time k) (gbar g) < T := max_lt hkT (by linarith)
  by_cases hgk : g ≤ tr.time k
  · obtain ⟨k', hk'i, hacc', hlt⟩ := hS.healthy.2.1 z hz k X hacc hgk y hy i ℓ hc
      (by linarith [hS.deadline_le hy i (tr.time k)]) hF
    exact ⟨k', hk'i, hacc', by linarith [hS.deadline_le hy k' (tr.time k)]⟩
  · obtain ⟨k', hk'i, hacc', hlt⟩ := hS.catchUp z hz k X hacc
      (lt_of_lt_of_le (not_le.1 hgk) (le_gbar g)) y hy i ℓ hc (by linarith) hF
    exact ⟨k', hk'i, hacc', by linarith⟩

/-- **Block stamps under trivial frames**: the stamp of a root at an honest node before cut `i`
is unset, or the root is genesis, or it is at least the time at which the node accepted a block
of that root at an earlier cut (a restart's replay stamps only frame blocks, accepted before). -/
theorem blockStamp_cases (hS : StandaloneRun tr H U proposer g) {y : Fin sp.n}
    (hy : y ∈ H) (r : Nat) :
    ∀ i, (tr.state y i).blockStamp r = ⊤ ∨ r = sp.genesisRoot ∨
      ∃ k < i, ∃ X : Blk sp.n FGP, X.root = r ∧ tr.AcceptAt y k X ∧
        ETime.of (tr.time k) ≤ (tr.state y i).blockStamp r := by
  have hr := hS.run.localRun
  intro i
  induction i with
  | zero =>
    have h0 : tr.state y 0 = SAState.initial sp.genesisRoot := hr.init y hy
    rw [h0]
    by_cases hg : r = sp.genesisRoot
    · exact Or.inr (Or.inl hg)
    · left; simp [SAState.initial, hg]
  | succ i ih =>
    have weak : ∀ st : ETime, (st = ⊤ ∨ r = sp.genesisRoot ∨ ∃ k < i, ∃ X : Blk sp.n FGP,
        X.root = r ∧ tr.AcceptAt y k X ∧ ETime.of (tr.time k) ≤ st) →
        st = ⊤ ∨ r = sp.genesisRoot ∨ ∃ k < i + 1, ∃ X : Blk sp.n FGP, X.root = r ∧
          tr.AcceptAt y k X ∧ ETime.of (tr.time k) ≤ st :=
      fun st h => h.imp_right (Or.imp_right fun ⟨k, hk, X, h1, h2, h3⟩ =>
        ⟨k, hk.trans (Nat.lt_succ_self i), X, h1, h2, h3⟩)
    by_cases hn : tr.node i = y ∧ tr.label i ≠ none
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hn.2
      have hc : tr.CallAt y i ℓ := ⟨hn.1, hℓ⟩
      have hst : tr.state y (i + 1) = tr.post i := by
        simp only [Trace.state]; exact ite_eq_left hn
      have he := hr.exec i ℓ hℓ (hn.1 ▸ hy)
      rw [hn.1] at he
      have hpost : tr.post i =
          ((goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i) ℓ.call).1 := by
        rw [he]
      have hΦ := (frameIn_of_callAt hr hy hc).1
      obtain ⟨hblk, -, hoth⟩ := step_blockStamp_eq ro y (tr.state y i) hΦ (hr.time_nonneg i)
        ℓ.call
      rw [hst, hpost]
      by_cases hb : ∃ B, ℓ.call = .block B
      · obtain ⟨B, hB⟩ := hb
        rw [hblk B hB, Function.update_apply]
        split_ifs with hrB
        · exact Or.inr (Or.inr ⟨i, Nat.lt_succ_self i, B, hrB.symm, ⟨ℓ, hc, hB⟩, le_rfl⟩)
        · exact weak _ ih
      simp only [not_exists] at hb
      by_cases hrs : ℓ.call = .restart
      · have hR := (restart_state sp) FGP ro y (tr.state y i) ℓ.frame (tr.time i) hΦ
          (hr.time_nonneg i)
        have hq := hR.2.2.2.2.2.2.2.2.2.2 r
        have hcall : (goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i) ℓ.call =
            acRestart sp ro y (tr.state y i) ℓ.frame (tr.time i) := by rw [hrs]; rfl
        rw [hcall]
        rcases hq with hq | ⟨hq, hne, X, hX, hXr⟩
        · rw [hq]
          by_cases hg : r = sp.genesisRoot
          · exact Or.inr (Or.inl hg)
          · left; simp [SAState.initial, hg]
        · rw [hq]
          rcases Set.mem_insert_iff.1 ((hS.trivial y hy i ℓ hc).2.2.2 ▸ hX) with hXF | ⟨k, hk, hacc⟩
          · exact Or.inr (Or.inl (hXr ▸ hXF ▸ (hS.trivial y hy i ℓ hc).1))
          · have hki : k ≠ i := by
              rintro rfl
              obtain ⟨ℓ', hc', hcall'⟩ := hacc
              have : ℓ' = ℓ := Option.some.inj (hc'.2.symm.trans hc.2)
              rw [this, hrs] at hcall'
              exact absurd hcall' (by simp)
            exact Or.inr (Or.inr ⟨k, by omega, X, hXr, hacc, etime_le.2 (hr.time_mono hk)⟩)
      · rw [hoth hb hrs]
        exact weak _ ih
    · have hst : tr.state y (i + 1) = tr.state y i := by
        simp only [Trace.state]; exact ite_eq_right hn
      rw [hst]
      exact weak _ ih

/-- A stamp before `T` at an honest node: the root is genesis, or the node accepted a block of
that root before `T`. -/
theorem accepted_of_blockStamp_lt (hS : StandaloneRun tr H U proposer g) {y : Fin sp.n} (hy : y ∈ H)
    {i r : Nat} {T : Time} (h : (tr.state y i).blockStamp r < ETime.of T) :
    r = sp.genesisRoot ∨ ∃ k < i, ∃ X : Blk sp.n FGP, X.root = r ∧ tr.AcceptAt y k X ∧
      tr.time k < T := by
  rcases blockStamp_cases hS hy r i with h' | h' | ⟨k, hk, X, hX, hacc, hle⟩
  · rw [h'] at h; exact absurd h (not_lt.2 le_top)
  · exact Or.inl h'
  · exact Or.inr ⟨k, hk, X, hX, hacc, etime_lt.1 (lt_of_le_of_lt hle h)⟩

/-- A vote an honest node holds at cut `a` is held at every later cut `b` with no restart in
between, with a stamp before `T` when every cut before `a`, every own vote of its slot and every
restart are before `T`. -/
theorem stamp_lt_of_held_of_run (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H)
    {a b : Nat} (hab : a ≤ b) {w : Vote sp.n} (hw : w ∈ (tr.state y a).pool w.slot) {T : Time}
    (hta : ∀ k < a, tr.time k < T) (hwT : sp.ts w.slot + sp.Δ < T)
    (hrestart : ∀ k < b, tr.RestartAt y k → tr.time k < T)
    (hnr : ∀ k, a ≤ k → k < b → ¬ tr.RestartAt y k) :
    w ∈ (tr.state y b).pool w.slot ∧ (tr.state y b).voteStamp w < ETime.of T := by
  have hmem := pool_mono hr hy hab hnr w.slot hw
  refine ⟨hmem, ?_⟩
  rcases pool_origin hr hy b w hmem with ⟨k, hk, hsend, hst, -⟩ | ⟨k, hk, ℓ, hc, hcall, hst, -⟩
  · rw [hst, etime_lt]
    by_cases hka : k < a
    · exact hta k hka
    obtain ⟨ℓ, hc, ⟨e, he, rfl⟩ | ⟨-, hnh, -⟩⟩ := hsend
    · obtain ⟨-, hsl, -, -⟩ := castAt_spec hr hy ⟨hc, he⟩
      have := vote_time_le hr hy ⟨ℓ, hc, he⟩
      rw [← hsl] at this
      linarith
    · exact absurd (pool_mono hr hy (not_lt.1 hka) (fun k' h1 h2 => hnr k' h1 (h2.trans hk))
        _ hw) hnh
  · rw [hst, etime_lt]
    exact hrestart k hk ⟨ℓ, hc, hcall⟩

/-- Whole-run specialization of bounded-cut stamp retention. -/
theorem stamp_lt_of_held (hS : HealthyBase tr H U proposer g) {y : Fin sp.n} (hy : y ∈ H)
    {a b : Nat} (hab : a ≤ b) {w : Vote sp.n} (hw : w ∈ (tr.state y a).pool w.slot) {T : Time}
    (hta : ∀ k < a, tr.time k < T) (hwT : sp.ts w.slot + sp.Δ < T) (hgT : gbar g < T)
    (hnr : ∀ k, a ≤ k → k < b → ¬ tr.RestartAt y k) :
    w ∈ (tr.state y b).pool w.slot ∧ (tr.state y b).voteStamp w < ETime.of T :=
  stamp_lt_of_held_of_run hS.run.localRun hy hab hw hta hwT
    (fun _ _ hk => (hS.restart_le hy hk).trans_lt hgT) hnr

private theorem admitVote_pool_ne {A : SAState sp.n} {t : Time} {v : Vote sp.n} {σ : Nat}
    (h : v.slot ≠ σ) : (admitVote sp A t v).pool σ = A.pool σ := by
  unfold admitVote
  split_ifs
  · rfl
  · rfl
  · exact Function.update_of_ne (Ne.symm h) _ _

private theorem admitVote_stamp_ne {A : SAState sp.n} {t : Time} {v w : Vote sp.n}
    (h : w ≠ v) : (admitVote sp A t v).voteStamp w = A.voteStamp w := by
  unfold admitVote
  split_ifs
  · rfl
  · rfl
  · exact Function.update_of_ne h _ _

private theorem optimistic_pool_stamp (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).pool = A.pool ∧
      (optimisticConfirmation sp A Φ t).voteStamp = A.voteStamp := by
  unfold optimisticConfirmation updateLatestConfirmed; split
  · exact ⟨rfl, rfl⟩
  · split_ifs <;> exact ⟨rfl, rfl⟩

/-- A vote of another slot that the state after an honest cast holds, it held at the read
point, with its stamp. -/
theorem heldBefore_readPoint (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) {w : Vote sp.n} (hne : e.msg.slot ≠ w.slot) {T : Time}
    (h : w ∈ (tr.state y (i + 1)).pool w.slot ∧ (tr.state y (i + 1)).voteStamp w < ETime.of T) :
    HeldBefore e.readPoint w T := by
  have hst : tr.state y (i + 1) = tr.post i := by simp [Trace.state, hc.1.1, hc.1.2]
  rw [hst, post_of_castAt hr hy hc, (optimistic_pool_stamp _ _ _).1,
    (optimistic_pool_stamp _ _ _).2, admitVote_pool_ne hne,
    admitVote_stamp_ne fun h' => hne (by rw [h'])] at h
  exact h

/-- **`Carry` from early sends** (under trivial frames): slot-`s` votes (`s ≥ r`) that honest
nodes sent or admitted in `[t_s, t_s + 2Δ)`, with heads that are genesis or blocks of the
sender's frame before `t_s + 2Δ`, are carried by every honest slot-`(s+1)` vote. -/
theorem carry_of_sent (hS : StandaloneRun tr H U proposer g) {s : Nat}
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) {CV : Set (Vote sp.n)}
    (hCV : ∀ v ∈ CV, v.slot = s ∧ ∃ x ∈ H, ∃ k, tr.SendOrAdmit x k v ∧ sp.ts s ≤ tr.time k ∧
      tr.time k < sp.ts s + 2 * sp.Δ ∧ ∃ Hv ∈ U, Hv.root = v.head ∧ (Hv.root = sp.genesisRoot ∨
        ∃ k₁, ∃ ℓ₁ : ACLabel (goldilocksSA sp FGP ro), tr.CallAt x k₁ ℓ₁ ∧
          tr.time k₁ < sp.ts s + 2 * sp.Δ ∧ Hv ∈ ℓ₁.frame.tree)) :
    Carry tr H U s CV := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  intro y hy i e ⟨ℓ, hc, he⟩ hes
  have hca : CastAt tr y i ℓ e := ⟨hc, he⟩
  obtain ⟨-, hsl, hj, -⟩ := castAt_spec hr hy hca
  have hti : sp.ts s + 4 * sp.Δ ≤ tr.time i := by
    rw [← ts_succ]
    exact (ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [← hsl, hes])
  obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_call sp hr hy i ℓ hc
  refine ⟨hr.awake_of_call y hy i ℓ hc, hj, fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨-, x, hx, -, -, -, -, Hv, hHvU, hHvr, hHv⟩ := hCV v hv
    refine ⟨Hv, hHvU, hHvr, fun X hX => ?_⟩
    rcases hHv with hgen | ⟨k₁, ℓ₁, hc₁, ht₁, hHv₁⟩
    · have hHvG : Hv = G := hU.1 hHvU hGU (hgen.trans hGr.symm)
      left
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hX with h | ⟨c, -, hp⟩
      · rw [← h]; exact hgen
      · have := hp.2.2
        rw [hHvG, hGp] at this
        exact absurd this (by simp)
    · rcases trivial_anc_mem hS hx hc₁ hHv₁ hX with hXF | ⟨k', hk', hacc⟩
      · left; rw [hXF]; exact (hS.trivial x hx k₁ ℓ₁ hc₁).1
      · right
        obtain ⟨hΦ₁, hΦ₁U⟩ := frameIn_of_callAt hr hx hc₁
        have hX₁ : X ∈ ℓ₁.frame.tree := by
          rw [(hS.trivial x hx k₁ ℓ₁ hc₁).2.2.2]
          exact Set.mem_insert_of_mem _ ⟨k', hk', hacc⟩
        have hF : Anc U ℓ.frame.F X := by
          rw [trivial_F_eq hS hy hx hc hc₁]
          exact (hΦ₁.rooted.2 X hX₁).mono hΦ₁U
        obtain ⟨k'', -, hacc'', hlt⟩ := relay_accept hS hx hacc (T := sp.ts s + 2 * sp.Δ)
          (lt_of_le_of_lt (hr.time_mono hk') ht₁) (by linarith) hy hc (by linarith) hF
        exact ⟨k'', hacc'', by linarith⟩
  · obtain ⟨hvs, x, hx, k, hsend, hk1, hk2, -⟩ := hCV v hv
    have hgk : gbar g ≤ tr.time k := by linarith
    have hmax : max (tr.time k) g = tr.time k := max_eq_left ((le_gbar g).trans hgk)
    have hdk : ∀ c, tr.deadline y c (tr.time k) ≤ tr.time k + sp.Δ := fun c =>
      (hS.deadline_le hy c _).trans (by rw [max_eq_left hgk])
    obtain ⟨k', hk'i, hkk', hproc, hk'dl⟩ := hS.healthy.1 x hx k v hsend y hy i ℓ hc
      (by rw [hmax]; linarith [hdk i])
    rw [hmax] at hk'dl
    have hk'T : tr.time k' < sp.ts s + 3 * sp.Δ := by linarith [hdk k']
    have hsl' : sp.slot (tr.time k') = s :=
      slot_of_mem sp s (by linarith) (by rw [ts_succ]; linarith)
    have hk'lt : k' < i := lt_of_le_of_ne hk'i (by rintro rfl; linarith)
    have hT : ∀ w : Vote sp.n, w.slot = s → w ∈ (tr.state y (k' + 1)).pool s →
        HeldBefore e.readPoint w (sp.ts s + 3 * sp.Δ) := by
      intro w hws hw
      refine heldBefore_readPoint hr hy hca (by rw [hes, hws]; omega) ?_
      refine stamp_lt_of_held hS.toHealthyBase hy (by omega) (hws ▸ hw)
        (fun c hc' => lt_of_le_of_lt (hr.time_mono (Nat.lt_succ_iff.1 hc')) hk'T)
        (by rw [hws]; linarith) (by linarith) fun c hc1 _ hrc => ?_
      have := hS.restart_le hy hrc
      have := hr.time_mono (show k' ≤ c by omega)
      linarith
    have hheld := held_of_processAt hr hy hproc (by rw [hsl', hvs]; omega) (by rw [hsl', hvs])
    rw [hvs] at hheld
    by_cases hv0 : v ∈ (tr.state y (k' + 1)).pool s
    · exact Or.inl (hT v hvs hv0)
    · rcases hheld with h | ⟨a, ha, b, hb, hab, hav, hbv⟩
      · exact absurd h hv0
      · have has := state_pool_slot sp hr hy (k' + 1) s a ha
        have hbs := state_pool_slot sp hr hy (k' + 1) s b hb
        exact Or.inr ⟨a, b, hab, fun h => hv0 (h ▸ ha), fun h => hv0 (h ▸ hb), hav, hbv, has,
          hbs, hT a has ha, hT b hbs hb⟩

/-- **Viability at a vote from acceptance before the freeze** (under trivial frames): a block of
`U` that is genesis, or that an honest voter of slot `σ + 1` (`σ ≥ r`) accepted before the vote
freeze `t_σ + 3Δ`, is in the viable tree of its voter block tree (or is `fc_root`). -/
theorem viable_of_accepted (hS : StandaloneRun tr H U proposer g) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) {σ : Nat}
    (hes : e.msg.slot = σ + 1) (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {B : Blk sp.n FGP}
    (hBU : B ∈ U) (hB : AcceptedBefore tr y B (sp.ts σ + 3 * sp.Δ)) :
    ViableAtVote ℓ e (σ + 1) B := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc.1
  obtain ⟨hFy, hfcy, hvhy, htreey⟩ := hS.trivial y hy i ℓ hc.1
  have hσ1 : ((σ + 1 : Nat) : Int) - 1 = σ := by push_cast; ring
  have hts1 : sp.ts (σ + 1 : Nat) = sp.ts σ + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hti : sp.ts σ + 4 * sp.Δ ≤ tr.time i := by
    obtain ⟨-, hsl, -, -⟩ := castAt_spec hr hy hc
    rw [← hts1]
    exact (ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [← hsl, hes])
  rcases hB with hg | ⟨k', hacc', hlt⟩
  · right
    rw [hU.1 hBU (hΦU hΦ.rooted.1) (hg.trans hFy.symm), hfcy]
    exact Relation.ReflTransGen.refl
  have hk'i : k' ≤ i := by
    by_contra h
    have := hr.time_mono (le_of_lt (not_le.1 h))
    linarith
  have hBy : B ∈ ℓ.frame.tree := by
    rw [htreey]; exact Set.mem_insert_of_mem _ ⟨k', hk'i, hacc'⟩
  have hst := blockStamp_lt_of_acceptedBefore sp hr hy hc.1 hBy (Or.inr ⟨k', hacc', hlt⟩)
    (fun k'' _ hr'' => lt_of_le_of_lt (hS.restart_le hy hr'') (by linarith))
    (Or.inl (by linarith))
  -- the read point's stamps are those after the call, which keeps `B`'s
  have hrp : e.readPoint.blockStamp B.root = (tr.state y i).blockStamp B.root := by
    have h1 : (tr.post i).blockStamp = e.readPoint.blockStamp := by
      rw [post_of_castAt hr hy hc, bs_optimistic, bs_admitVote]
    rw [← h1]
    have he := hr.exec i ℓ hc.1.2 (hc.1.1 ▸ hy)
    rw [hc.1.1] at he
    have hpost : tr.post i =
        ((goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i) ℓ.call).1 := by
      rw [he]
    obtain ⟨hblk, -, hoth⟩ := step_blockStamp_eq ro y (tr.state y i) hΦ (hr.time_nonneg i)
      ℓ.call
    rw [hpost]
    by_cases hb : ∃ B', ℓ.call = .block B'
    · obtain ⟨B', hB'⟩ := hb
      rw [hblk B' hB', Function.update_apply]
      split_ifs with hr'
      swap
      · rfl
      exfalso
      have hB'U : B' ∈ U := hΦU ((accept_new sp hr hy ⟨ℓ, hc.1, hB'⟩).1 ℓ hc.1)
      have := hU.1 (hΦU hBy) hB'U hr'
      subst this
      have := accept_unique sp hr hy hacc' ⟨ℓ, hc.1, hB'⟩
      subst this
      linarith
    · simp only [not_exists] at hb
      rw [hoth hb fun hrs => by
        have := hS.restart_le hy ⟨ℓ, hc.1, hrs⟩
        linarith]
  have hvbt : B ∈ voterBlockTree sp e.readPoint ℓ.frame (σ + 1) := by
    refine ⟨hBy, Or.inl ?_⟩
    rw [hrp, freeze, hσ1]
    exact hst
  left
  refine ⟨hvbt, ?_, B, hvbt, by rw [hvhy]; exact hBy, Relation.ReflTransGen.refl⟩
  rw [hfcy]
  exact hΦ.rooted.2 B hBy


/-- **Viability under trivial frames.** A block `B` extended by an honest vote of a slot
`σ ≥ r` is in the viable voter block tree of every honest slot-`(σ+1)` vote, or is genesis
(`Φ.fc_root`): the voter accepted it before the vote freeze `t_σ + 3Δ`, by acceptance relay or
`Catch(2Δ)`. -/
theorem trivial_viable (hS : StandaloneRun tr H U proposer g) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) {σ : Nat}
    (hes : e.msg.slot = σ + 1) (hσ : gbar g + 4 * sp.Δ ≤ sp.ts σ) {B : Blk sp.n FGP}
    (hB : ∃ z ∈ H, ∃ j e', VoteAt tr z j e' ∧ e'.msg.slot = σ ∧ VoteExtends U e'.msg B) :
    ViableAtVote ℓ e (σ + 1) B := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  obtain ⟨z, hz, j, e', ⟨ℓz, hcz, hez⟩, hs', Hd, hHdU, hHdr, hBHd⟩ := hB
  obtain ⟨hΦz, hΦzU⟩ := frameIn_of_callAt hr hz hcz
  obtain ⟨-, -, -, htreez⟩ := hS.trivial z hz j ℓz hcz
  obtain ⟨-, hfcy, -, -⟩ := hS.trivial y hy i ℓ hc.1
  have hFF := trivial_F_eq hS hz hy hcz hc.1
  -- the head of `z`'s vote is in its tree
  obtain ⟨-, hslz, -, hhead⟩ := castAt_spec hr hz ⟨hcz, hez⟩
  have hHdt : Hd ∈ ℓz.frame.tree := by
    have hm := getHead_mem' hΦz (fun _ hX => (voteDomain_subset_tree hX.1)) e'.readPoint (tr.time j)
      (mergedVoteView sp e'.readPoint ℓz.frame e'.msg.slot) ((e'.msg.slot : Int) - 1)
      (T := ℓz.frame.viableTree (voteDomain sp e'.readPoint ℓz.frame e'.msg.slot))
    rwa [hU.1 hHdU (hΦzU hm) (hHdr.trans hhead)]
  -- `B` is genesis, or `z` accepted it by its vote
  have hgen : ∀ X, Anc U X ℓz.frame.F → X = ℓz.frame.F := by
    intro X hX
    obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_call sp hr hz j ℓz hcz
    have hFG : ℓz.frame.F = G :=
      hU.1 (hΦzU hΦz.rooted.1) hGU ((hS.trivial z hz j ℓz hcz).1.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hX with h | ⟨c, -, hp⟩
    · exact h.symm
    · have := hp.2.2
      rw [hFG, hGp] at this
      exact absurd this (by simp)
  have hcase : B = ℓz.frame.F ∨ ∃ k ≤ j, tr.AcceptAt z k B := by
    rcases anc_total hU hBHd ((hΦz.rooted.2 Hd hHdt).mono hΦzU) with h | h
    · exact Or.inl (hgen B h)
    · have hBz := frame_mem_of_between sp hU hΦz hΦzU hHdt hBHd h
      rw [htreez] at hBz
      rcases hBz with h | h
      · exact Or.inl h
      · exact Or.inr h
  rcases hcase with hBF | ⟨k, hkj, hacc⟩
  · right
    rw [hBF, hFF, hfcy]
    exact Relation.ReflTransGen.refl
  -- times: `z` accepted `B` by `t_σ + Δ`; `y` votes from `t_{σ+1}`
  have hts1 : sp.ts (σ + 1 : Nat) = sp.ts σ + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have htk : tr.time k ≤ sp.ts σ + sp.Δ := by
    have := vote_time_le hr hz ⟨ℓz, hcz, hez⟩
    rw [← hslz, hs'] at this
    exact (hr.time_mono hkj).trans this
  have hti : sp.ts σ + 4 * sp.Δ ≤ tr.time i := by
    obtain ⟨-, hsl, -, -⟩ := castAt_spec hr hy hc
    rw [← hts1]
    exact (ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [← hsl, hes])
  have hg0 := gbar_nonneg g
  have hF : Anc U ℓ.frame.F B := by
    have hBz : B ∈ ℓz.frame.tree := by
      rw [htreez]; exact Set.mem_insert_of_mem _ ⟨k, hkj, hacc⟩
    rw [← hFF]
    exact (hΦz.rooted.2 B hBz).mono hΦzU
  -- `y` accepted `B` before the freeze `t_σ + 3Δ`
  obtain ⟨k', hk'i, hacc', hlt⟩ :
      ∃ k' ≤ i, tr.AcceptAt y k' B ∧ tr.time k' < sp.ts σ + 3 * sp.Δ := by
    by_cases hgk : g ≤ tr.time k
    · have hmax : max (tr.time k) (gbar g) ≤ sp.ts σ + sp.Δ := max_le htk (by linarith)
      obtain ⟨k', hk'i, hacc', hlt⟩ := hS.healthy.2.1 z hz k B hacc hgk y hy i ℓ hc.1
        (by linarith [hS.deadline_le hy i (tr.time k)]) hF
      exact ⟨k', hk'i, hacc', by linarith [hS.deadline_le hy k' (tr.time k)]⟩
    · obtain ⟨k', hk'i, hacc', hlt⟩ := hS.catchUp z hz k B hacc
        (lt_of_lt_of_le (not_le.1 hgk) (le_gbar g)) y hy i ℓ hc.1 (by linarith) hF
      exact ⟨k', hk'i, hacc', by linarith⟩
  exact viable_of_accepted hS hy hc hes hσ (hΦzU (by
    rw [htreez]; exact Set.mem_insert_of_mem _ ⟨k, hkj, hacc⟩)) (Or.inr ⟨k', hacc', hlt⟩)

/-- A slot-`s` vote (`s ≥ r`) of an honest node's pool was admitted, not replayed by a restart,
at a time in `[t_s, …)`, which is its stamp. -/
private theorem admitted_of_pool (hS : StandaloneRun tr H U proposer g) {x : Fin sp.n} (hx : x ∈ H)
    {s : Nat} (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) :
    ∀ c, ∀ v ∈ (tr.state x c).pool s, ∃ k < c, tr.SendOrAdmit x k v ∧
      sp.ts s ≤ tr.time k ∧ (tr.state x c).voteStamp v = ETime.of (tr.time k) := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  intro c v hv
  have hvs := state_pool_slot sp hr hx c s v hv
  rcases pool_origin hr hx c v (hvs ▸ hv) with ⟨k, hk, hsend, hst, hsl⟩ |
    ⟨k, -, ℓk, hck, hcall, -, B', hB', hvB'⟩
  · exact ⟨k, hk, hsend,
      (ts_le_iff_le_slot sp (hr.time_nonneg k) _).2 (by rw [← hvs]; exact_mod_cast hsl), hst⟩
  · exfalso
    have h1 := (frame_validPayload sp hr hx hck B' hB').1 v hvB'
    have h2 := frame_slot_le sp hr hx hck B' hB'
    have h3 := hS.restart_le hx ⟨ℓk, hck, hcall⟩
    have h4 : sp.slot (tr.time k) < s := by
      by_contra h
      have := (ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega)
      linarith
    omega

/-- **`Carry` for the counted votes of an update under trivial frames**: at an honest update of
slot `s ≥ r`, the votes `fastCounted` counts for any block `X` (resolved before `t_s + 2Δ`,
of validators with no second vote) are carried by every honest slot-`(s+1)` vote. -/
theorem trivial_carry_update (hS : StandaloneRun tr H U proposer g) {x : Fin sp.n} (hx : x ∈ H)
    {i₀ s : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr x i₀ s ℓ)
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) (X : Blk sp.n FGP) :
    Carry tr H U s (fastCounted sp (tr.state x i₀) ℓ.frame s X) := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hadm := admitted_of_pool hS hx hs
  obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr hx hupd.1
  refine carry_of_sent hS hs fun v hv => ?_
  obtain ⟨hvp, -, hres, -⟩ := hv
  have hvs := state_pool_slot sp hr hx i₀ s v hvp
  unfold resolutionTime at hres
  split at hres
  · exact absurd hres (by simp [ETime.of])
  rename_i Hd hl
  obtain ⟨hHd, hHdr⟩ := lookup_eq_some hl
  split_ifs at hres
  · exact absurd hres (not_lt.2 le_top)
  obtain ⟨h1, h2⟩ := max_lt_iff.1 hres
  obtain ⟨k, -, hsend, hk1, hst⟩ := hadm i₀ v hvp
  rw [hst, etime_lt] at h1
  refine ⟨hvs, x, hx, k, hsend, hk1, h1, Hd, hΦU hHd, hHdr, ?_⟩
  rw [← hHdr] at h2
  rcases accepted_of_blockStamp_lt hS hx h2 with hg | ⟨k₁, -, Y, hYr, ⟨ℓ₁, hc₁, hcall₁⟩, hlt⟩
  · exact Or.inl hg
  · have hY := (accept_new sp hr hx ⟨ℓ₁, hc₁, hcall₁⟩).1 ℓ₁ hc₁
    have hYd : Y = Hd := hU.1 ((frameIn_of_callAt hr hx hc₁).2 hY) (hΦU hHd) hYr
    exact Or.inr ⟨k₁, ℓ₁, hc₁, hlt, hYd ▸ hY⟩

/-- **`Carry` for a fast origin under trivial frames** (claims H.1 proof shape, "Carry comes from
relay and `Catch`"). For an honest fast lock of slot `s ≥ r` with counted votes `CV`, every
honest slot-`(s+1)` vote carries `CV`: each counted vote was admitted by the writer in
`[t_s, t_s + 2Δ)` and its head (with its ancestors) accepted by then, so by `Healthy(g)` and
`Catch(2Δ)` the voter holds it (or two other votes of its validator) and has accepted the head
and its ancestors before `t_s + 3Δ`. -/
theorem trivial_carry_fastLock (hS : StandaloneRun tr H U proposer g) {x : Fin sp.n} (hx : x ∈ H)
    {i₀ s : Nat} {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : FastLockAt tr x i₀ s B CV)
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) : Carry tr H U s CV := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  have hadm := admitted_of_pool hS hx hs
  rcases hfl with ⟨ℓ, C, ⟨hc, hc'⟩, -, -, -, rfl⟩ | ⟨ℓ, A, hpt, hsl, hsel, rfl⟩
  · exact trivial_carry_update hS hx ⟨hc, hc'⟩ hs B
  · obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr hx hpt.1
    have ht0 : tr.time i₀ < sp.ts s + 2 * sp.Δ ∧ sp.ts s ≤ tr.time i₀ := by
      unfold optimisticSelect at hsel
      dsimp only at hsel
      split_ifs at hsel with hg
      rw [hsl] at hg
      exact ⟨not_le.1 fun h => hg (Or.inr (Or.inr h)),
        (ts_le_iff_le_slot sp (hr.time_nonneg i₀) _).2 (by rw [hsl])⟩
    refine carry_of_sent hS hs fun v hv => ?_
    obtain ⟨hv, R, hR, hRr, -⟩ := hv
    have hvs := optimisticPoint_pool_slot hr hx hpt hv
    have hhead : ∃ Hv ∈ U, Hv.root = v.head ∧ (Hv.root = sp.genesisRoot ∨
        ∃ k₁, ∃ ℓ₁ : ACLabel (goldilocksSA sp FGP ro), tr.CallAt x k₁ ℓ₁ ∧
          tr.time k₁ < sp.ts s + 2 * sp.Δ ∧ Hv ∈ ℓ₁.frame.tree) :=
      ⟨R, hΦU hR, hRr, Or.inr ⟨i₀, ℓ, hpt.1, ht0.1, hR⟩⟩
    refine ⟨hvs, x, hx, ?_⟩
    by_cases hv0 : v ∈ (tr.state x i₀).pool s
    · obtain ⟨k, hk, hsend, hk1, -⟩ := hadm i₀ v hv0
      exact ⟨k, hsend, hk1, lt_of_le_of_lt (hr.time_mono hk.le) ht0.1, hhead⟩
    · have hpost : v ∈ (tr.post i₀).pool v.slot := by
        have := optimisticPoint_pool_post hr hx hpt s hv
        rwa [show tr.state x (i₀ + 1) = tr.post i₀ by simp [Trace.state, hpt.1.1, hpt.1.2],
          ← hvs] at this
      refine ⟨i₀, ⟨ℓ, hpt.1, Or.inr ⟨fun hrs => ?_, fun h => hv0 (hvs ▸ h), hpost⟩⟩, ht0.2,
        ht0.1, hhead⟩
      have := hS.restart_le hx ⟨ℓ, hpt.1, hrs⟩
      linarith

/-- **`Carry` for the honest votes of a slot under trivial frames** (claims H.1 proof shape;
A1.3's premise): every honest slot-`(m+1)` vote carries the honest slot-`m` votes, for
`m ≥ r`. Each is cast in `[t_m, t_m + Δ]` on a head its voter accepted, so as for
`trivial_carry_fastLock`. -/
theorem trivial_carry_votes (hS : StandaloneRun tr H U proposer g) {m : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) :
    Carry tr H U m {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = m} := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  refine carry_of_sent hS hm fun v hv => ?_
  obtain ⟨x, hx, j, e', ⟨ℓ, hc, he⟩, rfl, hvs⟩ := hv
  obtain ⟨-, hsl, -, hhead⟩ := castAt_spec hr hx ⟨hc, he⟩
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  have htj := vote_time_le hr hx ⟨ℓ, hc, he⟩
  rw [← hsl, hvs] at htj
  have htj' : sp.ts m ≤ tr.time j :=
    (ts_le_iff_le_slot sp (hr.time_nonneg j) _).2 (by rw [← hsl, hvs])
  have hG := getHead_mem' hΦ (fun _ hX => (voteDomain_subset_tree hX.1)) e'.readPoint (tr.time j)
    (mergedVoteView sp e'.readPoint ℓ.frame e'.msg.slot) ((e'.msg.slot : Int) - 1)
    (T := ℓ.frame.viableTree (voteDomain sp e'.readPoint ℓ.frame e'.msg.slot))
  exact ⟨hvs, x, hx, j, ⟨ℓ, hc, Or.inl ⟨e', he, rfl⟩⟩, htj', by linarith, _, hΦU hG, hhead.symm,
    Or.inr ⟨j, ℓ, hc, by linarith, hG⟩⟩

/-- Every honest node has an actual vote by the bounded slot deadline. Restart bounds
are required only before that deadline, at the join threshold for this slot. -/
theorem honest_votes_in_slot_before {b : Time} (hS : HealthyBaseUpTo tr H U proposer g b)
    {m : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) (hmb : sp.ts m + sp.Δ ≤ b)
    (hrestart : ∀ x ∈ H, ∀ r, tr.time r ≤ sp.ts m + sp.Δ → tr.RestartAt x r →
      tr.time r ≤ sp.ts ((m : Int) - 1)) :
    ∀ x ∈ H, ∃ j e, VoteAt tr x j e ∧ e.msg.slot = m ∧ tr.time j ≤ sp.ts m + sp.Δ := by
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  intro x hx
  have hslot : sp.slot (sp.ts m + sp.Δ) = m := by
    apply slot_of_mem sp m (by linarith)
    simp only [SAParams.ts]; push_cast; linarith
  obtain ⟨c, ell, hc, hcall, htc⟩ := hS.driven.tick x hx (sp.ts m + sp.Δ) (by linarith)
    ⟨4 * m + 1, by simp only [SAParams.ts]; ring⟩ (hS.awake x hx _ (by linarith) hmb)
  have hj : joined sp (tr.state x c) (tr.time c) := by
    unfold joined
    rcases restartTime_state hr hx c with h | ⟨r, hrc, hrs, h⟩
    · rw [h]; exact bot_le
    · rw [h]
      apply WithBot.coe_le_coe.mpr
      rw [htc, hslot]
      exact hrestart x hx r ((hr.time_mono hrc.le).trans htc.le) hrs
  by_cases hv : (tr.state x c).votedSlot = (sp.slot (tr.time c) : Int)
  · obtain ⟨j, hjc, e, he, hes⟩ := vote_of_votedSlot hr hx c _ hv
    exact ⟨j, e, he, by rw [hes, htc, hslot], (hr.time_mono hjc.le).trans htc.le⟩
  · have hT : tr.time c = sp.ts (sp.slot (tr.time c)) + sp.Δ := by rw [htc, hslot]
    obtain ⟨e, hem, hes⟩ := tryVote_votes x ell.frame hj hv hT
    have he := hr.exec c ell hc.2 (hc.1 ▸ hx)
    rw [hc.1, hcall] at he
    have h2 : (acOnTick sp x (tr.state x c) ell.frame (tr.time c)).2 = ell.emits :=
      congrArg Prod.snd he
    have h3 : (acOnTick sp x (tr.state x c) ell.frame (tr.time c)).2 =
        (tryVote sp x (tr.state x c) ell.frame (tr.time c)).2 := by
      unfold acOnTick
      dsimp only
      split_ifs
      all_goals first | rfl | exact absurd hj ‹_›
    exact ⟨c, e, ⟨ell, hc, h2 ▸ h3 ▸ hem⟩, by rw [hes, htc, hslot], htc.le⟩

/-- The bounded actual honest vote batch occupies at least half the committee. -/
theorem honest_voters_half_before {b : Time} (hS : HealthyBaseUpTo tr H U proposer g b)
    {m : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) (hmb : sp.ts m + sp.Δ ≤ b)
    (hrestart : ∀ x ∈ H, ∀ r, tr.time r ≤ sp.ts m + sp.Δ → tr.RestartAt x r →
      tr.time r ≤ sp.ts ((m : Int) - 1)) :
    sp.n ≤ 2 * {x | x ∈ H ∧ ∃ j e, VoteAt tr x j e ∧ e.msg.slot = m ∧
      tr.time j ≤ sp.ts m + sp.Δ}.ncard := by
  have hall := honest_votes_in_slot_before hS hm hmb hrestart
  have hle := Set.ncard_le_ncard (s := H)
    (t := {x | x ∈ H ∧ ∃ j e, VoteAt tr x j e ∧ e.msg.slot = m ∧
      tr.time j ≤ sp.ts m + sp.Δ}) fun x hx => ⟨hx, hall x hx⟩
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have := hS.faults
  omega

/-- **Every honest node votes** in a slot `m ≥ r` (T1 §3, "the honest batch"): it is awake and
joined at `t_m + Δ`, runs its tick there (`Driven`), and `try_vote` votes unless it voted in slot
`m` already. -/
theorem honest_votes_in_slot (hS : HealthyBase tr H U proposer g) {m : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) : ∀ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = m := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  intro x hx
  have hslot : sp.slot (sp.ts m + sp.Δ) = m := by
    refine slot_of_mem sp m (by linarith) ?_
    rw [show sp.ts (m + 1 : Nat) = sp.ts m + 4 * sp.Δ by simp only [SAParams.ts]; push_cast; ring]
    linarith
  obtain ⟨c, ℓ, hc, hcall, htc⟩ := hS.driven.tick x hx (sp.ts m + sp.Δ) (by linarith)
    ⟨4 * m + 1, by simp only [SAParams.ts]; ring⟩ (hS.awake hx (by linarith))
  have hj := hS.joined_state hx c (by rw [htc, hslot, ts_sub_one]; linarith)
  by_cases hv : (tr.state x c).votedSlot = (sp.slot (tr.time c) : Int)
  · obtain ⟨j, -, e, he, hes⟩ := vote_of_votedSlot hr hx c _ hv
    exact ⟨j, e, he, by rw [hes, htc, hslot]⟩
  · have hT : tr.time c = sp.ts (sp.slot (tr.time c)) + sp.Δ := by rw [htc, hslot]
    obtain ⟨e, hem, hes⟩ := tryVote_votes x ℓ.frame hj hv hT
    have he := hr.exec c ℓ hc.2 (hc.1 ▸ hx)
    rw [hc.1, hcall] at he
    have h2 : (acOnTick sp x (tr.state x c) ℓ.frame (tr.time c)).2 = ℓ.emits :=
      congrArg Prod.snd he
    have h3 : (acOnTick sp x (tr.state x c) ℓ.frame (tr.time c)).2 =
        (tryVote sp x (tr.state x c) ℓ.frame (tr.time c)).2 := by
      unfold acOnTick
      dsimp only
      split_ifs
      all_goals first | rfl | exact absurd hj ‹_›
    exact ⟨c, e, ⟨ℓ, hc, h2 ▸ h3 ▸ hem⟩, by rw [hes, htc, hslot]⟩

/-- **The honest batch** (T1 §3, "the honest batch has `n − f > n/2` seats"): in a slot
`m ≥ r` every honest node votes (it is awake and joined at `t_m + Δ`, runs its tick there
(`Driven`), and `try_vote` votes unless it voted in slot `m` already), so the honest voters of
slot `m` are at least half of the committee. -/
theorem honest_voters_half (hS : HealthyBase tr H U proposer g) {m : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) :
    sp.n ≤ 2 * {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = m}.ncard := by
  have hall := honest_votes_in_slot hS hm
  have hle := Set.ncard_le_ncard (s := H)
    (t := {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = m}) fun x hx => ⟨hx, hall x hx⟩
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have := hS.two_faulty_lt
  omega

/-- A fast lock of an honest node is extended by an honest vote of its slot: the fast test
counts at least `n/2` non-equivocating supporters, an optimistic confirmation `3n/4` voters,
and `f < n/2`. -/
theorem fastLock_honest_vote (hrun : ACRun proposer tr H U) (hf : 2 * Hᶜ.ncard < sp.n)
    {x : Fin sp.n}
    (hx : x ∈ H) {i₀ s : Nat} {B : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (hfl : FastLockAt tr x i₀ s B CV) :
    ∃ z ∈ H, ∃ j e, VoteAt tr z j e ∧ e.msg.slot = s ∧ VoteExtends U e.msg B := by
  sorry

/-! ## T1 §3: a fast origin of label `≥ r` transfers -/

/-- **T1 §3, continuation** ("Induction on slots proves permanent vote support"; A1.3): if every
honest vote of a slot `m ≥ r` extends `B`, so does every honest vote of every later slot. -/
theorem votes_continue (hS : StandaloneRun tr H U proposer g) {m : Nat}
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) {B : Blk sp.n FGP}
    (hB : ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = m → VoteExtends U e.msg B) :
    VotesExtendAfter tr H U m B := by
  have hrun := hS.run
  have hr := hrun.localRun
  have hΔ := sp.toParams.hΔ
  have hpos : 0 < sp.n := sp.toParams.hn
  rw [votesExtendAfter_iff]
  suffices h : ∀ d : Nat, ∀ x ∈ H, ∀ j e, VoteAt tr x j e → e.msg.slot = m + d →
      VoteExtends U e.msg B by
    intro x hx j e hv hs
    exact h (e.msg.slot - m) x hx j e hv (by omega)
  intro d
  induction d with
  | zero => exact hB
  | succ d ih =>
    have hmd : gbar g + 4 * sp.Δ ≤ sp.ts (m + d : Nat) :=
      hm.trans ((ts_le_iff sp).2 (by push_cast; omega))
    have hhalf := honest_voters_half hS.toHealthyBase hmd
    obtain ⟨z, hz, jz, ez, hvz, hsz⟩ := Set.nonempty_of_ncard_ne_zero
      (s := {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = m + d}) (by omega)
    have hcarry := trivial_carry_votes hS hmd
    suffices h : ∀ j, ∀ x ∈ H, ∀ e, VoteAt tr x j e → e.msg.slot = m + (d + 1) →
        VoteExtends U e.msg B from fun x hx j e hv hs => h j x hx e hv hs
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ihj =>
      intro x hx e ⟨ℓ, hc, he⟩ hes
      have hca : CastAt tr x j ℓ e := ⟨hc, he⟩
      obtain ⟨-, hsl, -, -⟩ := castAt_spec hr hx hca
      have hT : gbar g ≤ sp.ts ((sp.slot (tr.time j) : Int) - 1) := by
        rw [← hsl, hes, show ((m + (d + 1) : Nat) : Int) - 1 = ((m + d : Nat) : Int) by
          push_cast; ring]
        linarith
      exact next_transfer sp FGP ro H U tr proposer hrun (m + d) x j B ℓ e hx hca (by omega)
        ih hhalf
        (hcarry x hx j e ⟨ℓ, hc, he⟩ (by omega)) (hS.faultBound (hr.time_nonneg j) hT)
        (hS.syncAC (by linarith) _)
        (trivial_viable hS hx hca (by omega) hmd ⟨z, hz, jz, ez, hvz, hsz, ih z hz jz ez hvz hsz⟩)
        (fun z' hz' j' hj' e' hv' hs' => ihj j' hj' z' hz' e' hv' (by omega))

/-- **T1 §3, a fast origin transfers to the votes** (A1.2/A1.4 at slot `s + 1`, the first bad
vote by induction on cuts, then `votes_continue`): every honest vote of a slot after the label
`s ≥ r` of an honest fast lock extends its block. -/
theorem fast_origin_transfer_votes (hS : StandaloneRun tr H U proposer g) {x : Fin sp.n}
    (hx : x ∈ H)
    {i₀ s : Nat} {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : FastLockAt tr x i₀ s B CV)
    (hs : gbar g + 4 * sp.Δ ≤ sp.ts s) : VotesExtendAfter tr H U s B := by
  have hrun := hS.run
  have hr := hrun.localRun
  have hΔ := sp.toParams.hΔ
  have hvB := fastLock_honest_vote hrun hS.two_faulty_lt hx hfl
  have hcarry := trivial_carry_fastLock hS hx hfl hs
  have hnext : ∀ i, ∀ y ∈ H, ∀ e, VoteAt tr y i e → e.msg.slot = s + 1 →
      VoteExtends U e.msg B := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro y hy e ⟨ℓ, hc, he⟩ hes
      have hca : CastAt tr y i ℓ e := ⟨hc, he⟩
      obtain ⟨-, hsl, -, -⟩ := castAt_spec hr hy hca
      have hT : gbar g ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) := by
        rw [← hsl, hes, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by push_cast; ring]
        linarith
      exact first_transfer sp FGP ro H U tr proposer hrun s x y i₀ i B CV ℓ e hx hfl hy hca hes
        (hS.syncAC (by linarith) _) (hcarry y hy i e ⟨ℓ, hc, he⟩ hes)
        (hS.faultBound (hr.time_nonneg i) hT) (trivial_viable hS hy hca hes hs hvB)
        (fun z hz j hj e' hv' hs' => ih j hj z hz e' hv' hs')
  have hs1 : gbar g + 4 * sp.Δ ≤ sp.ts (s + 1 : Nat) :=
    hs.trans ((ts_le_iff sp).2 (by push_cast; omega))
  have hcont := votes_continue hS hs1 fun y hy i e hv hs => hnext i y hy e hv hs
  rw [votesExtendAfter_iff]
  intro y hy i e hv hlt
  rcases Nat.lt_or_ge (s + 1) e.msg.slot with h | h
  · exact votesExtendAfter_iff.1 hcont y hy i e hv h
  · exact hnext i y hy e hv (by omega)

end Consensus.Goldilocks.SA

end

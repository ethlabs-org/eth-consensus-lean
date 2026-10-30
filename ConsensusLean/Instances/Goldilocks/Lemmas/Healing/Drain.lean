module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainCommon
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainProvenance

public section

/-! # Goldilocks Healing, HS.2: clean-lock transfer and the two-window drain

`hs234-exact-interface.md` §3, under the settled context `Γ` of §1 (`DrainCommon`).

* **Extension** (proved from §2's contracts): every in-phase honest vote of a slot `> j` extends
  a clean origin's stored block `B` (`clean_fast_extends`, `clean_slow_extends`), by induction on
  the cut of the vote (the first violating event): a vote whose `fc_root` is above `B` extends it;
  a slot-`(j+1)` vote by A1.2 for a fast origin (`first_transfer_stored`, with `Carry` and frozen
  viability from §2.1 and `Sync` from `GST(g)` after `ḡ ≤ t_j`) or by the slow first transfer
  (`clean_slow_first_extends`, open) for a slow one; a later vote by A1.3 (`next_transfer`) from
  the preceding honest batch (half of the committee and `f < h_t` after `c_z`, its `Carry` by
  §2.1).
* **HS.2 (1), (2)** at the next slot and later (`clean_fast_next`, `clean_fast_later`,
  `clean_slow_next`, `clean_slow_later`): extension with §2.1's viability and `Carry`.
* **HS.2 (3), the drain** (`live_lock_clean`, proved): a lock live at a time `≥ r` keeps its
  label `l` with `slot(now) ≤ l + k`, so `l ≥ a + k + 2`.
* **HS.2 (3), the proposal boundary** (`live_lock_below_proposal`, proved from the open
  `clean_fast_proposal`, `clean_slow_proposal`, with `stored_slow_lock_provenance`): a live lock of
  a slot-`s` voter is the viable ancestor of a stored lock, below the stored block of the voter's
  own clean origin of its label (the drain), which the honest slot-`s` proposal extends unless it
  is at or below the voter's `fc_root`. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF Gp w : Time} {i₀ m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}

/-! ### Contracts of §3 (open) and stored slow-lock provenance -/

/-- **First transfer of a clean slow origin** (`hs234-exact-interface.md` §3, the slow helper;
§2.2's ancestor-target score lemma with RR/RO): under `Γ`, at an in-phase honest slot-`(j+1)`
vote whose `fc_root` is not above the stored block `B` of a clean slow lock of label `j`, given
`Carry` of the writer's result votes, the frozen viability of `B`, and the earlier in-phase honest
votes of slots `> j` extending `B`, the vote extends `B`: every saved result of the window extends
the raw slow selection `S ⪰ B`, every surviving live lock compares with `S` by RR/RO (exempt labels
`j` and `j + 1` separately), and the score walk reaches `S`. -/
theorem clean_slow_first_extends (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : StoredSlowLockAt tr x i j B)
    (hj : w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1)) (hi : PhaseOn tr.projFG H i₀ i m c)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    (he : e.msg.slot = j + 1) (hk : PhaseOn tr.projFG H i₀ k m c)
    (hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B)
    (hroot : ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot)
    (hcarry : ∀ C CV, SA.ResultAt tr.projAC x i j C CV →
      SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV)
    (hviab : B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot)) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  sorry

/-- **Proposal-boundary transfer of a clean fast origin** (`hs234-exact-interface.md` §2.2 last
paragraph, §3 last paragraph): under `Γ`, let `P` be the honest proposal of a slot `s > j` with
`t_s ≥ r`, and `y` an honest slot-`s` voter in the phase after the write of a clean fast lock with
stored block `B`, before which every in-phase honest vote of a slot `> j` extends `B`. Then `P`
extends `B`, or `B` is at or below `y`'s `fc_root`: the proposal walk over the full previous-slot
pool and the full viable tree reaches `B` (first transfer at `s = j + 1`, including a retrospective
regular write; the unanimous honest batch after). -/
theorem clean_fast_proposal (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (ho : Compose.StoredFastLockAt tr x i j B CV) (hj : w + 4 * sp.Δ ≤ sp.ts j)
    (hi : PhaseOn tr.projFG H i₀ i m c) {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : HonestProposalRun tr H s P) (hr : rTime sp w ≤ sp.ts s) (hjs : j < s)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    (he : e.msg.slot = s) (hk : PhaseOn tr.projFG H i₀ k m c) (hik : i < k)
    (hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Anc (tr.HonestBlocks H) B P ∨ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  sorry

/-- **Proposal-boundary transfer of a clean slow origin** (`hs234-exact-interface.md` §2.2 last
paragraph, §3 last paragraph): as `clean_fast_proposal`, for a slow lock of label `j` with
`t_{j−k+1} ≥ w + 4Δ` and stored block `B`. -/
theorem clean_slow_proposal (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : StoredSlowLockAt tr x i j B)
    (hj : w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1)) (hi : PhaseOn tr.projFG H i₀ i m c)
    {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))} (hP : HonestProposalRun tr H s P)
    (hr : rTime sp w ≤ sp.ts s) (hjs : j < s) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.CastAt tr.projAC y k ℓ e) (he : e.msg.slot = s) (hk : PhaseOn tr.projFG H i₀ k m c)
    (hik : i < k)
    (hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    Anc (tr.HonestBlocks H) B P ∨ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  sorry

/-- **Stored slow-lock provenance** (`hs234-exact-interface.md` §3 "every lock image retains its
original label"; the slow case of HR.4's `stored_fast_lock_provenance`): every slow lock an honest
node holds before cut `k` sits below the stored block `Φ.viableAncestor D` of a slow-lock write of
its slot at an earlier cut of the node (`add_locks` stores that block; the lock functions only
move locks back; `SA.slow_lock_provenance_stored` over the AC projection). -/
theorem stored_slow_lock_provenance (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) (k : Nat) :
    ∀ l ∈ (tr.state y k).ac.locks, l.fast = false →
      ∃ r < k, ∃ B, StoredSlowLockAt tr y r l.slot B ∧
        ∃ L ∈ tr.HonestBlocks H, L.root = l.block ∧ Anc (tr.HonestBlocks H) L B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  intro l hl hf
  rw [← Compose.projAC_state hrun.toLocalRun hy] at hl
  obtain ⟨r, hrk, ℓ, D, hc, hsl, hL⟩ := SA.slow_lock_provenance_stored hr hy k l hl hf
  exact ⟨r, hrk, _, ⟨ℓ, D, hc, hsl, rfl⟩, hL⟩

/-! ### Extension by induction on the cut of the vote -/

/-- `f < h_t` at an honest vote of a slot after a clean label, on the AC projection. -/
private theorem faultBound_proj (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} (hk : cutZ sp.toParams g ≤ tr.time k) :
    SA.FaultBound tr.projAC H (tr.time k) := by
  unfold SA.FaultBound
  rw [← (Compose.joined_projection sp ro dg H tr hrun y hy (tr.time k)).2.2]
  exact faultBound_of_healthy hrun hs hk

/-- **Extension of an origin's block** (§3's event induction): given the first transfer and the
frozen viability at every in-phase honest vote of a slot `> j` (from the earlier votes), every
such vote extends `B`. -/
private theorem origin_extends (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ))
    (hw : SettledIn tr H g w i₀ m c) {j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hj : w + 4 * sp.Δ ≤ sp.ts j)
    (hfirst : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = j + 1 →
      PhaseOn tr.projFG H i₀ k m c → ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot →
      (∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
        SA.VoteExtends (tr.HonestBlocks H) e'.msg B) →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B)
    (hviab : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → j < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c →
      (∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
        SA.VoteExtends (tr.HonestBlocks H) e'.msg B) →
      B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
        Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    ∀ k, ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e → j < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr hrun hs.noColl
  have hr := hrun'.localRun
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro y hy ℓ e hv hjs hk
  have hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B :=
    fun z hz k' hk' e' ⟨ℓ', hc', he'⟩ hs' =>
      ih k' hk' z hz ℓ' e' ⟨hc', he'⟩ hs' (hk.mono_right hk'.le)
  obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, hle⟩ := Compose.cast_head_fcRoot hr hy hv
  have hΦU := (SA.frameIn_of_callAt hr hy hv.1).2
  by_cases hBf : Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot
  · exact ⟨Hd, hΦU hHd, hHdr, hBf.trans (Anc.mono hΦU hfHd)⟩
  by_cases h1 : e.msg.slot = j + 1
  · exact hfirst y hy k ℓ e hv h1 hk hBf hprior
  obtain ⟨m', hm'⟩ : ∃ m', e.msg.slot = m' + 1 := ⟨e.msg.slot - 1, by omega⟩
  have hsm' : j < m' := by omega
  have h0 := hr.time_nonneg k
  have hsl := (SA.castAt_spec hr hy hv).2.1
  have hjm : sp.ts j ≤ sp.ts m' := (SA.ts_le_iff sp).2 (by exact_mod_cast hsm'.le)
  have htk : sp.ts e.msg.slot ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp h0 _).2 (by rw [hsl])
  have hmk : sp.ts m' ≤ tr.time k := ((SA.ts_le_iff sp).2 (by omega)).trans htk
  have hsync := syncRun_of_gst (b := sp.ts e.msg.slot + sp.Δ) hs.healthy.1
    ((le_gbar g).trans (gbar_le_of_clean hw (hj.trans hjm)))
  have hsync0 := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr ΔF _ _ hrun.toLocalRun hsync
  have hall : ∀ z ∈ H, ∀ k' e', SA.VoteAt tr.projAC z k' e' → e'.msg.slot = m' →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B := by
    intro z hz k' e' hv' hs'
    have hk' : k' < k := by
      by_contra hkk
      obtain ⟨ℓ', hc', he'⟩ := hv'
      have h₁ := (SA.castAt_spec hr hz ⟨hc', he'⟩).2.1
      have h₂ := SA.slot_mono sp h0 (hr.time_mono (not_lt.mp hkk))
      omega
    exact hprior z hz k' hk' e' hv' (by omega)
  refine SA.next_transfer sp _ ro H _ tr.projAC hrun' m' y k B ℓ e hy hv hm' hall
    (half_committee_of_healthy hrun hs (cutZ_le_of_clean hw (hj.trans hjm)))
    (honest_batch_carry hrun hs hc hw (hj.trans hjm) hall hy hv hm'
      (hviab y hy k ℓ e hv hjs hk hprior) hBf)
    (faultBound_proj hrun hs hy ((cutZ_le_of_clean hw hj).trans (hjm.trans hmk)))
    (Compose.syncAC_mono hsync0 le_rfl hle) ?_ ?_
  · rw [← hm']
    exact Or.inl ((hviab y hy k ℓ e hv hjs hk hprior).resolve_right hBf)
  · rw [← hm']
    exact fun z hz j' hj' e' hv' hsl' => hprior z hz j' hj' e' hv' (hsl' ▸ hjs)

/-- **Extension of a clean fast origin** (§3): every in-phase honest vote of a slot `> j`
extends the stored block `B`. -/
theorem clean_fast_extends (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (ho : Compose.StoredFastLockAt tr x i j B CV) (hj : w + 4 * sp.Δ ≤ sp.ts j)
    (hi : PhaseOn tr.projFG H i₀ i m c) :
    ∀ k, ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e → j < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr hrun hs.noColl
  have hr := hrun'.localRun
  refine origin_extends hrun hs hc hw hj (fun y hy k ℓ e hv h1 hk hBf hprior => ?_)
    (fun y hy k ℓ e hv hjs hk hprior =>
      clean_fast_viable hrun hs hc hp hw hx ho hj hi hy hv hjs hk hprior)
  have hviab := (clean_fast_viable hrun hs hc hp hw hx ho hj hi hy hv (by omega) hk
    hprior).resolve_right hBf
  obtain ⟨-, hle⟩ := Compose.cast_head_fcRoot hr hy hv
  have h0 := hr.time_nonneg k
  have htk : sp.ts e.msg.slot ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp h0 _).2 (by rw [(SA.castAt_spec hr hy hv).2.1])
  have hjk : sp.ts j ≤ tr.time k := ((SA.ts_le_iff sp).2 (by omega)).trans htk
  have hsync := syncRun_of_gst (b := sp.ts e.msg.slot + sp.Δ) hs.healthy.1
    ((le_gbar g).trans (gbar_le_of_clean hw hj))
  have hsync0 := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr ΔF _ _ hrun.toLocalRun hsync
  have hcarry := clean_fast_carry hrun hs hc hp hw hx ho hj hi hy hv h1 hk hprior hBf
  obtain ⟨ℓw, D, hcw, hflD, hBD⟩ := ho
  have hΦwU := (SA.frameIn_of_callAt hr hx hcw).2
  refine SA.first_transfer_stored sp hrun' hx hflD
    (hBD ▸ Anc.mono hΦwU (SA.anc_viableAncestor ℓw.frame D)) hy hv h1
    (Compose.syncAC_mono hsync0 le_rfl hle) hcarry
    (faultBound_proj hrun hs hy ((cutZ_le_of_clean hw hj).trans hjk)) ?_ ?_
  · rw [← h1]
    exact Or.inl hviab
  · rw [← h1]
    exact fun z hz j' hj' e' hv' hsl' => hprior z hz j' hj' e' hv' (by omega)

/-- A clean slow label `j` (`t_{j−k+1} ≥ w + 4Δ`) is itself clean (`t_j ≥ w + 4Δ`). -/
private theorem clean_of_slow {j : Nat} (hj : w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1)) :
    w + 4 * sp.Δ ≤ sp.ts j :=
  hj.trans ((SA.ts_le_iff sp).2 (by have := sp.two_le_k; omega))

/-- **Extension of a clean slow origin** (§3): every in-phase honest vote of a slot `> j`
extends the stored block `B`. -/
theorem clean_slow_extends (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : StoredSlowLockAt tr x i j B)
    (hj : w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1)) (hi : PhaseOn tr.projFG H i₀ i m c) :
    ∀ k, ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e → j < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg B :=
  origin_extends hrun hs hc hw (clean_of_slow hj)
    (fun _ hy _ _ _ hv h1 hk hBf hprior =>
      clean_slow_first_extends hrun hs hc hp hw hx ho hj hi hy hv h1 hk hprior hBf
        (fun _ _ hC => clean_slow_carry hrun hs hc hp hw hx ho hj hi hy hv h1 hk hprior hC hBf)
        ((clean_slow_viable hrun hs hc hp hw hx ho hj hi hy hv (by omega) hk
          hprior).resolve_right hBf))
    (fun _ hy _ _ _ hv hjs hk hprior =>
      clean_slow_viable hrun hs hc hp hw hx ho hj hi hy hv hjs hk hprior)

/-! ### HS.2 (1), (2) -/

/-- **HS.2 (1) at the next slot** (`hs234-exact-interface.md` §3 `clean_fast_next`). -/
theorem clean_fast_next (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (ho : Compose.StoredFastLockAt tr x i j B CV) (hj : w + 4 * sp.Δ ≤ sp.ts j)
    (hi : PhaseOn tr.projFG H i₀ i m c) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.CastAt tr.projAC y k ℓ e) (he : e.msg.slot = j + 1)
    (hk : PhaseOn tr.projFG H i₀ k m c) :
    VoteKeeps tr H ℓ e B ∧
      (¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot →
        SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV) := by
  have hext := clean_fast_extends hrun hs hc hp hw hx ho hj hi
  have hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B :=
    fun z hz k' hk' e' ⟨ℓ', hc', he'⟩ hs' =>
      hext k' z hz ℓ' e' ⟨hc', he'⟩ hs' (hk.mono_right hk'.le)
  exact ⟨⟨hext k y hy ℓ e hv (by omega) hk,
    clean_fast_viable hrun hs hc hp hw hx ho hj hi hy hv (by omega) hk hprior⟩,
    clean_fast_carry hrun hs hc hp hw hx ho hj hi hy hv he hk hprior⟩

/-- **HS.2 (1) at a later slot** (`hs234-exact-interface.md` §3, the propagation helper). -/
theorem clean_fast_later (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (ho : Compose.StoredFastLockAt tr x i j B CV) (hj : w + 4 * sp.Δ ≤ sp.ts j)
    (hi : PhaseOn tr.projFG H i₀ i m c) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.CastAt tr.projAC y k ℓ e) (hjs : j < e.msg.slot)
    (hk : PhaseOn tr.projFG H i₀ k m c) : VoteKeeps tr H ℓ e B := by
  have hext := clean_fast_extends hrun hs hc hp hw hx ho hj hi
  exact ⟨hext k y hy ℓ e hv hjs hk, clean_fast_viable hrun hs hc hp hw hx ho hj hi hy hv hjs hk
    fun z hz k' hk' e' ⟨ℓ', hc', he'⟩ hs' =>
      hext k' z hz ℓ' e' ⟨hc', he'⟩ hs' (hk.mono_right hk'.le)⟩

/-- **HS.2 (2) at the next slot** (`hs234-exact-interface.md` §3, the slow helper). -/
theorem clean_slow_next (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : StoredSlowLockAt tr x i j B)
    (hj : w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1)) (hi : PhaseOn tr.projFG H i₀ i m c)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    (he : e.msg.slot = j + 1) (hk : PhaseOn tr.projFG H i₀ k m c) :
    VoteKeeps tr H ℓ e B ∧
      ∀ C CV, SA.ResultAt tr.projAC x i j C CV →
        ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot →
        SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV := by
  have hext := clean_slow_extends hrun hs hc hp hw hx ho hj hi
  have hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', SA.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B :=
    fun z hz k' hk' e' ⟨ℓ', hc', he'⟩ hs' =>
      hext k' z hz ℓ' e' ⟨hc', he'⟩ hs' (hk.mono_right hk'.le)
  exact ⟨⟨hext k y hy ℓ e hv (by omega) hk,
    clean_slow_viable hrun hs hc hp hw hx ho hj hi hy hv (by omega) hk hprior⟩,
    fun _ _ hC hroot => clean_slow_carry hrun hs hc hp hw hx ho hj hi hy hv he hk hprior hC hroot⟩

/-- **HS.2 (2) at a later slot** (`hs234-exact-interface.md` §3, the propagation helper). -/
theorem clean_slow_later (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : StoredSlowLockAt tr x i j B)
    (hj : w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1)) (hi : PhaseOn tr.projFG H i₀ i m c)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hv : SA.CastAt tr.projAC y k ℓ e)
    (hjs : j < e.msg.slot) (hk : PhaseOn tr.projFG H i₀ k m c) : VoteKeeps tr H ℓ e B := by
  have hext := clean_slow_extends hrun hs hc hp hw hx ho hj hi
  exact ⟨hext k y hy ℓ e hv hjs hk, clean_slow_viable hrun hs hc hp hw hx ho hj hi hy hv hjs hk
    fun z hz k' hk' e' ⟨ℓ', hc', he'⟩ hs' =>
      hext k' z hz ℓ' e' ⟨hc', he'⟩ hs' (hk.mono_right hk'.le)⟩

/-! ### HS.2 (3): the drain and the proposal boundary -/

/-- **HS.2 (3), the two-window drain** (`hs234-exact-interface.md` §3 "the drain helper"): a
lock live at a time `t ≥ r` keeps its label `l` with `slot(t) ≤ l + k`; as
`slot(t) ≥ a + 2k + 2`, `l ≥ a + k + 2`, so the lock is clean. -/
theorem live_lock_clean {t : Time} (ht : rTime sp w ≤ t) {L : Set SA.Lock}
    {Φ : SA.Frm sp.n (List (FG.Att sp.n))} {l : SA.Lock} (hl : l ∈ SA.liveLocks sp L Φ t) :
    (l.fast = true → w + 4 * sp.Δ ≤ sp.ts l.slot) ∧
      (l.fast = false → w + 4 * sp.Δ ≤ sp.ts ((l.slot : Int) - sp.k + 1)) := by
  obtain ⟨l₀, -, B, -, -, hsl, rfl⟩ := hl
  dsimp only
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have ha := slotA_spec sp w
  have hr0 : 0 ≤ rTime sp w := mul_nonneg (by linarith) (Int.natCast_nonneg _)
  have h1 := (SA.ts_le_iff_le_slot sp (hr0.trans ht) _).1 ht
  push_cast at h1
  exact ⟨fun _ => ha.trans ((SA.ts_le_iff sp).2 (by omega)),
    fun _ => ha.trans ((SA.ts_le_iff sp).2 (by omega))⟩

/-- **HS.2 (3), the proposal boundary** (`hs234-exact-interface.md` §3 last paragraph): at an
in-phase honest slot-`s` vote, `t_s ≥ r`, every live lock of a label `< s` has its block below the
honest slot-`s` proposal `P` or at or below the voter's `fc_root`. -/
theorem live_lock_below_proposal (hrun : GoldilocksRun dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (hw : SettledIn tr H g w i₀ m c) {s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : HonestProposalRun tr H s P) (hr : rTime sp w ≤ sp.ts s) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hv : SA.CastAt tr.projAC y k ℓ e) (he : e.msg.slot = s) (hk : PhaseOn tr.projFG H i₀ k m c)
    {l : SA.Lock} (hl : l ∈ SA.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k))
    (hls : l.slot < s) {L : SA.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ ℓ.frame.tree)
    (hLr : L.root = l.block) :
    Anc (tr.HonestBlocks H) L P ∨ Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot := by
  have hr' := (Compose.goldilocks_ac_projection sp ro dg H tr hrun hs.noColl).localRun
  have hU := hr'.coherent
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr' hy hv.1
  have htk : sp.ts s ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hr'.time_nonneg k) _).2
      (by rw [← he, (SA.castAt_spec hr' hy hv).2.1])
  have hclean := live_lock_clean (hr.trans htk) hl
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  dsimp only at hls hLr hclean
  obtain ⟨hvat, hva⟩ := SA.viableAncestor_anc hΦ hB₀
  obtain rfl : L = ℓ.frame.viableAncestor B₀ := hU.1 (hΦU hL) (hΦU hvat) hLr
  have hLB₀ := Anc.mono hΦU hva
  -- the block below a stored origin `O` of the voter: `L ⪯ B₀ ⪯ O`
  have key : ∀ O : SA.Blk sp.n (List (FG.Att sp.n)),
      (∃ L' ∈ tr.HonestBlocks H, L'.root = l₀.block ∧ Anc (tr.HonestBlocks H) L' O) →
      (Anc (tr.HonestBlocks H) O P ∨ Anc (tr.HonestBlocks H) O ℓ.frame.fcRoot) →
      Anc (tr.HonestBlocks H) (ℓ.frame.viableAncestor B₀) P ∨
        Anc (tr.HonestBlocks H) (ℓ.frame.viableAncestor B₀) ℓ.frame.fcRoot := by
    rintro O ⟨L', hL', hL'r, hL'O⟩ h
    obtain rfl : L' = B₀ := hU.1 hL' (hΦU hB₀) (hL'r.trans hB₀r.symm)
    exact h.imp (hLB₀.trans hL'O).trans (hLB₀.trans hL'O).trans
  cases hf : l₀.fast
  · obtain ⟨r, hrk, O, hO, hLO⟩ :=
      stored_slow_lock_provenance hrun hs.noColl hy k l₀ hl₀ hf
    have hj := hclean.2 hf
    have hext := clean_slow_extends hrun hs hc hp hw hy hO hj (hk.mono_right hrk.le)
    exact key O hLO (clean_slow_proposal hrun hs hc hp hw hy hO hj (hk.mono_right hrk.le) hP hr
      hls hy hv he hk hrk fun z hz k' hk' e' ⟨ℓ', hc', he'⟩ hs' =>
        hext k' z hz ℓ' e' ⟨hc', he'⟩ hs' (hk.mono_right hk'.le))
  · rw [← Compose.projAC_state hrun.toLocalRun hy] at hl₀
    obtain ⟨r, hrk, CV, ℓ', D, hcw, hfl, hLO⟩ := stored_fast_lock_provenance hr' hy k l₀ hl₀ hf
    have hO : Compose.StoredFastLockAt tr y r l₀.slot (ℓ'.frame.viableAncestor D) CV :=
      ⟨ℓ', D, hcw, hfl, rfl⟩
    have hj := hclean.1 hf
    have hext := clean_fast_extends hrun hs hc hp hw hy hO hj (hk.mono_right hrk.le)
    exact key _ hLO (clean_fast_proposal hrun hs hc hp hw hy hO hj (hk.mono_right hrk.le) hP hr
      hls hy hv he hk hrk fun z hz k' hk' e' ⟨ℓ'', hc', he'⟩ hs' =>
        hext k' z hz ℓ'' e' ⟨hc', he'⟩ hs' (hk.mono_right hk'.le))

end Consensus.Goldilocks.Healing

end

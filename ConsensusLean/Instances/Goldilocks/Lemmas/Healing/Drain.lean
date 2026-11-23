module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.DrainProvenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LocksWF
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HS.2: clean-lock transfer and the two-window drain

Under the settled context `Γ` of `DrainCommon`.

* **Extension** (proved): every in-phase honest vote of a slot `> j` extends a clean origin's stored
  block `B` (`clean_fast_extends`, `clean_slow_extends`), by induction on the cut of the vote (the
  first violating event): a vote whose `fc_root` is above `B` extends it; a slot-`(j+1)` vote by
  A1.2 for a fast origin (`first_transfer_stored`, with `Carry` and frozen viability from
  `DrainCommon` and `Sync` from `GST(g)` after `ḡ ≤ t_j`) or by A1.8 for the ancestor `B` of the
  update's result for a slow one (`clean_slow_first_extends`, `result_transfer_anc`, the live locks
  compared with `B` by `slow_live_locks_anc`); a later vote by A1.3 (`next_transfer`) from the
  preceding honest batch (half of the committee and `f < h_t` after `c_z`, its `Carry` by
  `DrainCommon`).
* **HS.2 (1), (2)** at the next slot and later (`clean_fast_next`, `clean_fast_later`,
  `clean_slow_next`, `clean_slow_later`): extension with `DrainCommon`'s viability and `Carry`.
* **HS.2 (3), the drain** (`live_lock_clean`): a lock live at a time `≥ r` keeps its
  label `l` with `slot(now) ≤ l + k`, so `l ≥ a + k + 2`.
* **HS.2 (3), the proposal boundary** (`live_lock_below_proposal`): a live lock of a slot-`s`
  voter is the viable ancestor of a stored lock (`stored_fast_lock_provenance`,
  `stored_slow_lock_provenance`), below the stored block of the voter's own clean origin of its
  label (the drain), which the honest slot-`s` proposal extends (`clean_fast_proposal`,
  `clean_slow_proposal`, `DrainProposal`). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State} {g ΔF w : Time}
  {i₀ m : Nat}
  {c : PhaseCase (AC.Blk sp.n (List (FG.Att sp.n)))}

/-! ### The slow first transfer and stored slow-lock provenance -/

/-- **The live locks at a slot-`(s+1)` vote after an honest slow lock on `D`**, compared with a
block `B ⪯ D` whose earlier slot-`(s+1)` honest votes extend it (as AC/SlowLocks compares the
exempt label-`(s+1)` optimistic locks with `D` from votes extending `D`; here they extend only
`B`): a lock of a label `≤ s` sits below a stored lock,
compatible with the writer's saved result, which extends `D ⪰ B` (`slow_stored_locks_before`,
over a finite healthy base for the slot committees `K` whose honest restarts are by its start); a
lock of label `s + 1` is optimistic over three quarters of the slot-`(s+1)` committee (CS2
there), whose honest votes extend `B`. -/
private theorem slow_live_locks_anc {FGP : Type} {ro' : ReplayOrder sp FGP}
    {U : Set (AC.Blk sp.n FGP)} {T : AC.GTrace sp FGP ro'} {b : Time}
    (hS : AC.HealthyBaseUpTo K T H U proposer g b)
    (hrs : ∀ y ∈ H, ∀ k, T.RestartAt y k → T.time k ≤ b → T.time k ≤ gbar g)
    {x : Fin sp.n} (hx : x ∈ H) {i₀ s : Nat} {D B : AC.Blk sp.n FGP}
    (hsl : AC.SlowLockAt T x i₀ s D) (hBD : Anc U B D)
    (hs : gbar g ≤ sp.ts ((s : Int) - sp.k + 1)) (hsb : sp.ts s + 6 * sp.Δ ≤ b)
    {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (AC.goldilocksAC sp FGP ro')} {e : AC.Em sp FGP}
    (hc : AC.CastAt T y i ℓ e) (hes : e.msg.slot = s + 1) (hib : T.time i ≤ b)
    (hcs2 : ∀ l : Nat, s < l → 2 * (K.committee l ∩ Hᶜ).ncard < sp.committeeSize)
    (hE : AC.EarlierVotesExtend T H U i (s + 1) B) :
    ∀ L ∈ AC.liveLockBlocks sp e.readPoint.locks ℓ.frame (T.time i), Compatible U L B := by
  have hrun := hS.run
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := AC.frameIn_of_callAt hr hy hc.1
  have hsi : e.msg.slot = sp.slot (T.time i) := (AC.castAt_spec hr hy hc).2.1
  have down : ∀ {X Y}, Anc U X Y → Compatible U Y B → Compatible U X B := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact AC.anc_total hU hXY h
  rintro L ⟨hL, l, ⟨l₀, hl₀, B₀, hB₀, hB₀r, hlive₀, rfl⟩, hlL⟩
  have hlive : sp.slot (T.time i) ≤ l₀.slot + sp.k :=
    le_trans hlive₀
      ((AC.castAt_readPoint_locksWF hr hrun.vstart hy hc).cap hl₀)
  have hLe : L = ℓ.frame.viableAncestor B₀ :=
    hU.1 (hΦU hL) (hΦU (AC.viableAncestor_anc hΦ hB₀).1) hlL.symm
  subst hLe
  refine down (Anc.mono hΦU (AC.anc_viableAncestor _ B₀)) ?_
  rcases le_or_gt l₀.slot s with hle | hlt
  · obtain ⟨l₁, hl₁, hsl₁, B₁, hB₁, hB₁r, B₀', hB₀', hB₀'r, hA⟩ :=
      AC.readPoint_locks_below_stored hr hy hc (show 0 < sp.slot (T.time i) by omega) l₀ hl₀
        (show l₀.slot ≠ sp.slot (T.time i) by omega)
    obtain rfl : B₀' = B₀ := hΦ.coherent.1 hB₀' hB₀ (hB₀'r.trans hB₀r.symm)
    refine down (Anc.mono hΦU hA) ?_
    rcases AC.slow_stored_locks_before hS hrs hx hsl hs hsb hy (by omega) hib l₁ hl₁ (by omega)
        (by omega) B₁ (hΦU hB₁) hB₁r with h | h
    · exact AC.anc_total hU h hBD
    · exact Or.inr (hBD.trans h)
  · obtain ⟨Φ', A, D', -, hΦ'U, -, h34, hpool, ⟨kk, -, hAk⟩, L₀, hL₀, hL₀r, hL₀D⟩ :=
      AC.lock_origin_readPoint hrun hy hc l₀ hl₀ (by rw [hes]; push_cast; omega)
    obtain rfl : L₀ = B₀ := hU.1 hL₀ (hΦU hB₀) (hL₀r.trans hB₀r.symm)
    refine down hL₀D (AC.origin_compatible hU hΦ'U K h34
      (by rintro _ ⟨v, hv, rfl, -⟩; exact hS.hP.1 y hy (kk + 1) _ v (hAk hv))
      (hcs2 _ hlt) fun v hv hvH => ?_)
    obtain ⟨hvs, j, hj, e', hvote, rfl⟩ := hpool v hv hvH
    obtain ⟨ℓ', hcj⟩ := id hvote
    have hsj : e'.msg.slot = sp.slot (T.time j) := (AC.castAt_spec hr hvH hcj).2.1
    have : sp.slot (T.time j) ≤ sp.slot (T.time i) :=
      AC.slot_mono sp (hr.time_nonneg j) (hr.time_mono hj.le)
    exact hE _ hvH j hj e' hvote (by omega)

/-- **First transfer of a clean slow origin** (the slow helper;
the ancestor-target score lemma): under `Γ` (without `Prop⁺`), at an honest slot-`(j+1)` vote,
given `Carry` of the writer's result votes, the frozen viability of the stored block `B` and the
earlier honest votes of slots `> j` extending `B`, the vote extends `B`. This is A1.8 for the
ancestor `B ⪯ D ⪯ C` of the update's result `C` (`result_transfer_anc`: the counted supporters
of `C` support every child towards `B`): the live locks compare with `B`
(`slow_live_locks_anc`: the window's saved results by RR/RO, the exempt label-`(j+1)` optimistic
locks over earlier honest votes), and the writer's pool covers the vote's merged view
(`writer_merged`, `Sync` from `ḡ`). -/
theorem clean_slow_first_extends (hrun : GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hs : HSShared tr H K dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {x : Fin sp.n}
    (hx : x ∈ H) {i j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : StoredSlowLockAt tr x i j B) (hj : w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1))
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hv : AC.CastAt tr.projAC y k ℓ e)
    (he : e.msg.slot = j + 1)
    (hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', AC.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      AC.VoteExtends (tr.HonestBlocks H) e'.msg B)
    (hcarry : ∀ C CV, AC.ResultAt tr.projAC x i j C CV →
      AC.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV)
    (hviab : B ∈ ℓ.frame.viableTree (AC.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot)) :
    AC.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hS := healthyBase_of_hs hrun hs hc (max (tr.time k) (sp.ts j + 6 * sp.Δ))
  have hr := hS.run.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hw8 := gbar_add_le_of_settled hw
  obtain ⟨ℓw, D, hcw, hsl, rfl⟩ := ho
  obtain ⟨ℓX, C, hupd, hconf, hdeep⟩ := id hsl
  obtain rfl : ℓX = ℓw := Option.some.inj (hupd.1.2.symm.trans hcw.2)
  have hΦU := (AC.frameIn_of_callAt hr hx hcw).2
  have hBD : Anc (tr.HonestBlocks H) (ℓX.frame.viableAncestor D) D :=
    Anc.mono hΦU (AC.anc_viableAncestor _ D)
  have hDC : Anc (tr.HonestBlocks H) D C := Anc.mono hΦU (AC.deepest_mem hdeep).1.1.2.2
  have hres : AC.ResultAt tr.projAC x i j C
      (AC.fastCounted sp (tr.projAC.state x i) ℓX.frame j C) := ⟨ℓX, hupd, hconf, rfl⟩
  have hjt : w + 4 * sp.Δ ≤ sp.ts j :=
    hj.trans ((AC.ts_le_iff sp).2 (by have := sp.two_le_k; omega))
  rw [he] at hviab
  have hj1 : sp.slot (gbar g) + 1 ≤ j := slot_gbar_lt_of_cutZ_le (cutZ_le_of_clean hw hjt)
  exact AC.result_transfer_ancU sp hS.run.toU hx hres (hBD.trans hDC) hy hv he
    (hcarry _ _ hres) (Or.inl hviab)
    (slow_live_locks_anc hS (restart_le_base_of_hs hrun hs) hx hsl hBD
      ((gbar_slotAfter_add_le (by linarith)).trans' (by linarith only [hΔ]))
      (le_max_right _ _) hy hv he (le_max_left _ _) (fun l hl => hs.cs2 (by omega))
      fun z hz k' hk' e' hv' hs' => hprior z hz k' hk' e' hv' (by omega))
    (AC.writer_merged hS.run hx hupd hy hv he
      ((ResetService.of_gst tr H hs.healthy.1 (b := 0)).syncAC hrun
        ((le_gbar g).trans (gbar_le_of_clean hw hjt))))

/-- **Stored slow-lock provenance** (every lock image retains its
original label; the slow case of HR.4's `stored_fast_lock_provenance`): every slow lock an honest
node holds before cut `k` sits below the stored block `Φ.viableAncestor D` of a slow-lock write of
its slot at an earlier cut of the node (`add_locks` stores that block; the lock functions only
move locks back; `AC.slow_lock_provenance_stored` over the AC projection). -/
theorem stored_slow_lock_provenance (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) (k : Nat) :
    ∀ l ∈ (tr.state y k).ac.locks, l.fast = false →
      ∃ r < k, ∃ B, StoredSlowLockAt tr y r l.slot B ∧
        ∃ L ∈ tr.HonestBlocks H, L.root = l.block ∧ Anc (tr.HonestBlocks H) L B := by
  have hr := (Compose.goldilocks_ac_projection_from hrun hnc).localRun
  intro l hl hf
  rw [← Compose.projAC_state hrun.toLocalRun hy] at hl
  obtain ⟨r, hrk, ℓ, D, hc, hsl, hL⟩ := AC.slow_lock_provenance_stored hr hrun.vstart hy k l hl hf
  exact ⟨r, hrk, _, ⟨ℓ, D, hc, hsl, rfl⟩, hL⟩

/-! ### Extension by induction on the cut of the vote -/

/-- **Extension of an origin's block** (the event induction): given the first transfer (at the
slot-`(j+1)` votes, from the earlier votes) and the frozen viability at every in-phase honest vote
of a slot `> j + 1`, every in-phase honest vote of a slot `> j` extends `B`. -/
theorem origin_extends (hrun : GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K)) (hs : HSShared tr H K dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c)
    {j : Nat} {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hj : w + 4 * sp.Δ ≤ sp.ts j)
    (hfirst : ∀ y ∈ H, ∀ k ℓ e, AC.CastAt tr.projAC y k ℓ e → e.msg.slot = j + 1 →
      PhaseOn tr.projFG H i₀ k m c → ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot →
      (∀ z ∈ H, ∀ k' < k, ∀ e', AC.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
        AC.VoteExtends (tr.HonestBlocks H) e'.msg B) →
      AC.VoteExtends (tr.HonestBlocks H) e.msg B)
    (hviab : ∀ y ∈ H, ∀ k ℓ e, AC.CastAt tr.projAC y k ℓ e → j + 1 < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c →
      B ∈ ℓ.frame.viableTree (AC.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
        Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    ∀ k, ∀ y ∈ H, ∀ ℓ e, AC.CastAt tr.projAC y k ℓ e → j < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → AC.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hrun' := Compose.goldilocks_ac_projection_from hrun hs.noColl
  have hr := hrun'.localRun
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro y hy ℓ e hv hjs hk
  have hprior : ∀ z ∈ H, ∀ k' < k, ∀ e', AC.VoteAt tr.projAC z k' e' → j < e'.msg.slot →
      AC.VoteExtends (tr.HonestBlocks H) e'.msg B :=
    fun z hz k' hk' e' ⟨ℓ', hc', he'⟩ hs' =>
      ih k' hk' z hz ℓ' e' ⟨hc', he'⟩ hs' (hk.mono_right hk'.le)
  obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, hle⟩ := Compose.cast_head_fcRoot hr
      hrun.vstart hy hv
  have hΦU := (AC.frameIn_of_callAt hr hy hv.1).2
  by_cases hBf : Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot
  · exact ⟨Hd, hΦU hHd, hHdr, hBf.trans (Anc.mono hΦU hfHd)⟩
  by_cases h1 : e.msg.slot = j + 1
  · exact hfirst y hy k ℓ e hv h1 hk hBf hprior
  obtain ⟨m', hm'⟩ : ∃ m', e.msg.slot = m' + 1 := ⟨e.msg.slot - 1, by omega⟩
  have hsm' : j < m' := by omega
  have h0 := hr.time_nonneg k
  have hsl := (AC.castAt_spec hr hy hv).2.1
  have hjm : sp.ts j ≤ sp.ts m' := (AC.ts_le_iff sp).2 (by exact_mod_cast hsm'.le)
  have htk : sp.ts e.msg.slot ≤ tr.time k :=
    (AC.ts_le_iff_le_slot sp h0 _).2 (by rw [hsl])
  have hmk : sp.ts m' ≤ tr.time k := ((AC.ts_le_iff sp).2 (by omega)).trans htk
  have hsync := syncRun_of_gst (b := sp.ts e.msg.slot + sp.Δ) hs.healthy.1
    ((le_gbar g).trans (gbar_le_of_clean hw (hj.trans hjm)))
  have hsync0 := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF _ _ hrun.toLocalRun hsync
  have hall : ∀ z ∈ H, ∀ k' e', AC.VoteAt tr.projAC z k' e' → e'.msg.slot = m' →
      AC.VoteExtends (tr.HonestBlocks H) e'.msg B := by
    intro z hz k' e' hv' hs'
    have hk' : k' < k := by
      by_contra hkk
      obtain ⟨ℓ', hc', he'⟩ := hv'
      have h₁ := (AC.castAt_spec hr hz ⟨hc', he'⟩).2.1
      have h₂ := AC.slot_mono sp h0 (hr.time_mono (not_lt.mp hkk))
      omega
    exact hprior z hz k' hk' e' hv' (by omega)
  have hjm1 : sp.slot (gbar g) + 1 ≤ m' :=
    slot_gbar_lt_of_cutZ_le (cutZ_le_of_clean hw (hj.trans hjm))
  refine AC.next_transfer_of_carry sp hrun' K (hs.hP hrun) (hs.hT hrun) hs.hsize hy hv hm' hall
    (half_committee_of_healthy hrun hs (cutZ_le_of_clean hw (hj.trans hjm)))
    (honest_batch_carry hrun hs hc hw (hj.trans hjm) hall hy hv hm'
      (hviab y hy k ℓ e hv (by omega) hk) hBf)
    (faultBoundK_of_healthy hrun hs hjm1 ((cutZ_le_of_clean hw hj).trans (hjm.trans hmk)))
    (hs.cs2 (by omega)) ?_ ?_
  · rw [← hm']
    exact Or.inl ((hviab y hy k ℓ e hv (by omega) hk).resolve_right hBf)
  · rw [← hm']
    exact fun z hz j' hj' e' hv' hsl' => hprior z hz j' hj' e' hv' (hsl' ▸ hjs)

/-- **Extension of a clean fast origin**: every in-phase honest vote of a slot `> j`
extends the stored block `B`. -/
theorem clean_fast_extends (hrun : GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K)) (hs : HSShared tr H K dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c)
    {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (ho : Compose.StoredFastLockAt tr x i j B CV) (hj : w + 4 * sp.Δ ≤ sp.ts j) :
    ∀ k, ∀ y ∈ H, ∀ ℓ e, AC.CastAt tr.projAC y k ℓ e → j < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → AC.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hrun' := Compose.goldilocks_ac_projection_from hrun hs.noColl
  have hr := hrun'.localRun
  refine origin_extends hrun hs hc hw hj (fun y hy k ℓ e hv h1 hk hBf hprior => ?_)
    (fun _ hy _ _ _ hv hjs hk => clean_fast_viable hrun hs hc hw hx ho hj hy hv (by omega) hk)
  have hviab := (clean_fast_viable hrun hs hc hw hx ho hj hy hv (by omega) hk).resolve_right hBf
  obtain ⟨-, hle⟩ := Compose.cast_head_fcRoot hr hrun.vstart hy hv
  have h0 := hr.time_nonneg k
  have htk : sp.ts e.msg.slot ≤ tr.time k :=
    (AC.ts_le_iff_le_slot sp h0 _).2 (by rw [(AC.castAt_spec hr hy hv).2.1])
  have hjk : sp.ts j ≤ tr.time k := ((AC.ts_le_iff sp).2 (by omega)).trans htk
  have hsync := syncRun_of_gst (b := sp.ts e.msg.slot + sp.Δ) hs.healthy.1
    ((le_gbar g).trans (gbar_le_of_clean hw hj))
  have hsync0 := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF _ _ hrun.toLocalRun hsync
  have hcarry := clean_fast_carry hrun hs hc hw hx ho hj hy hv h1 hk hBf
  obtain ⟨ℓw, D, hcw, hflD, hBD⟩ := ho
  have hΦwU := (AC.frameIn_of_callAt hr hx hcw).2
  have hj1 : sp.slot (gbar g) + 1 ≤ j := slot_gbar_lt_of_cutZ_le (cutZ_le_of_clean hw hj)
  refine AC.first_transfer_storedU sp hrun'.toU K (hs.hP hrun) (hs.hT hrun) hs.hsize hx hflD
    (hBD ▸ Anc.mono hΦwU (AC.anc_viableAncestor ℓw.frame D)) hy hv h1
    (Compose.syncAC_mono hsync0 le_rfl hle) hcarry
    (faultBoundK_of_healthy hrun hs hj1 ((cutZ_le_of_clean hw hj).trans hjk))
    (hs.cs2 (by omega)) ?_ ?_
  · rw [← h1]
    exact Or.inl hviab
  · rw [← h1]
    exact fun z hz j' hj' e' hv' hsl' => hprior z hz j' hj' e' hv' (by omega)

/-- A clean slow label `j` (`t_{j−k+1} ≥ w + 4Δ`) is itself clean (`t_j ≥ w + 4Δ`). -/
private theorem clean_of_slow {j : Nat} (hj : w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1)) :
    w + 4 * sp.Δ ≤ sp.ts j :=
  hj.trans ((AC.ts_le_iff sp).2 (by have := sp.two_le_k; omega))

/-- **Extension of a clean slow origin**: every in-phase honest vote of a slot `> j`
extends the stored block `B`. -/
theorem clean_slow_extends (hrun : GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K)) (hs : HSShared tr H K dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c)
    {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ho : StoredSlowLockAt tr x i j B)
    (hj : w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1)) :
    ∀ k, ∀ y ∈ H, ∀ ℓ e, AC.CastAt tr.projAC y k ℓ e → j < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → AC.VoteExtends (tr.HonestBlocks H) e.msg B :=
  origin_extends hrun hs hc hw (clean_of_slow hj)
    (fun _ hy _ _ _ hv h1 hk hBf hprior =>
      clean_slow_first_extends hrun hs hc hw hx ho hj hy hv h1 hprior
        (fun _ _ hC => clean_slow_carry hrun hs hc hw hx ho hj hy hv h1 hk hC hBf)
        ((clean_slow_viable hrun hs hc hw hx ho hj hy hv (by omega) hk).resolve_right hBf))
    (fun _ hy _ _ _ hv hjs hk => clean_slow_viable hrun hs hc hw hx ho hj hy hv (by omega) hk)

/-! ### HS.2 (1), (2) -/

/-- **HS.2 (1) at the next slot**. -/
theorem clean_fast_next (hrun : GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K)) (hs : HSShared tr H K dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c)
    {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (ho : Compose.StoredFastLockAt tr x i j B CV) (hj : w + 4 * sp.Δ ≤ sp.ts j)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hv : AC.CastAt tr.projAC y k ℓ e) (he : e.msg.slot = j + 1)
    (hk : PhaseOn tr.projFG H i₀ k m c) :
    VoteKeeps tr H ℓ e B ∧
      (¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot →
        AC.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV) := by
  have hext := clean_fast_extends hrun hs hc hw hx ho hj
  exact ⟨⟨hext k y hy ℓ e hv (by omega) hk,
    clean_fast_viable hrun hs hc hw hx ho hj hy hv (by omega) hk⟩,
    clean_fast_carry hrun hs hc hw hx ho hj hy hv he hk⟩

/-- **HS.2 (1) at a later slot** (the propagation helper). -/
theorem clean_fast_later (hrun : GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K)) (hs : HSShared tr H K dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c)
    {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (ho : Compose.StoredFastLockAt tr x i j B CV) (hj : w + 4 * sp.Δ ≤ sp.ts j)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hv : AC.CastAt tr.projAC y k ℓ e) (hjs : j < e.msg.slot)
    (hk : PhaseOn tr.projFG H i₀ k m c) : VoteKeeps tr H ℓ e B := by
  have hext := clean_fast_extends hrun hs hc hw hx ho hj
  exact ⟨hext k y hy ℓ e hv hjs hk, clean_fast_viable hrun hs hc hw hx ho hj hy hv hjs hk⟩

/-- **HS.2 (2) at the next slot** (the slow helper). -/
theorem clean_slow_next (hrun : GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K)) (hs : HSShared tr H K dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c)
    {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ho : StoredSlowLockAt tr x i j B)
    (hj : w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1))
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hv : AC.CastAt tr.projAC y k ℓ e)
    (he : e.msg.slot = j + 1) (hk : PhaseOn tr.projFG H i₀ k m c) :
    VoteKeeps tr H ℓ e B ∧
      ∀ C CV, AC.ResultAt tr.projAC x i j C CV →
        ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot →
        AC.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV := by
  have hext := clean_slow_extends hrun hs hc hw hx ho hj
  exact ⟨⟨hext k y hy ℓ e hv (by omega) hk,
    clean_slow_viable hrun hs hc hw hx ho hj hy hv (by omega) hk⟩,
    fun _ _ hC hroot => clean_slow_carry hrun hs hc hw hx ho hj hy hv he hk hC hroot⟩

/-- **HS.2 (2) at a later slot** (the propagation helper). -/
theorem clean_slow_later (hrun : GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K)) (hs : HSShared tr H K dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c)
    {x : Fin sp.n} (hx : x ∈ H) {i j : Nat}
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (ho : StoredSlowLockAt tr x i j B)
    (hj : w + 4 * sp.Δ ≤ sp.ts ((j : Int) - sp.k + 1))
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hv : AC.CastAt tr.projAC y k ℓ e)
    (hjs : j < e.msg.slot) (hk : PhaseOn tr.projFG H i₀ k m c) : VoteKeeps tr H ℓ e B := by
  have hext := clean_slow_extends hrun hs hc hw hx ho hj
  exact ⟨hext k y hy ℓ e hv hjs hk, clean_slow_viable hrun hs hc hw hx ho hj hy hv hjs hk⟩

/-! ### HS.2 (3): the drain and the proposal boundary -/

/-- **HS.2 (3), the two-window drain**: a
lock live at a time `t ≥ r` keeps its label `l` with `slot(t) ≤ l + k`; as
`slot(t) ≥ a + 2k + 2`, `l ≥ a + k + 2`, so the lock is clean. -/
theorem live_lock_clean {t : Time} (ht : rTime sp w ≤ t) {L : Set AC.Lock}
    (hwf : AC.LocksWF sp L)
    {Φ : AC.Frm sp.n (List (FG.Att sp.n))} {l : AC.Lock} (hl : l ∈ AC.liveLocks sp L Φ t) :
    (l.fast = true → w + 4 * sp.Δ ≤ sp.ts l.slot) ∧
      (l.fast = false → w + 4 * sp.Δ ≤ sp.ts ((l.slot : Int) - sp.k + 1)) := by
  have hsl := hwf.slot_le_of_live hl
  obtain ⟨l₀, -, B, -, -, -, rfl⟩ := hl
  dsimp only at hsl ⊢
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have ha := slotA_spec sp w
  have hr0 : 0 ≤ rTime sp w := mul_nonneg (by linarith) (Int.natCast_nonneg _)
  have h1 := (AC.ts_le_iff_le_slot sp (hr0.trans ht) _).1 ht
  push_cast at h1
  exact ⟨fun _ => ha.trans ((AC.ts_le_iff sp).2 (by omega)),
    fun _ => ha.trans ((AC.ts_le_iff sp).2 (by omega))⟩

/-- **HS.2 (3), the proposal boundary**: at an
in-phase honest slot-`s` vote, `t_s ≥ r`, every live lock of a label `< s` has its block below the
honest slot-`s` proposal `P` or at or below the voter's `fc_root`. -/
theorem live_lock_below_proposal (hrun : GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hs : HSShared tr H K dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ)) (hw : SettledIn tr H g w i₀ m c) {s : Nat}
    {P : AC.Blk sp.n (List (FG.Att sp.n))} (hP : HonestProposalRun tr H proposer s P)
    (hr : rTime sp w ≤ sp.ts s) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hv : AC.CastAt tr.projAC y k ℓ e) (he : e.msg.slot = s) (hk : PhaseOn tr.projFG H i₀ k m c)
    {l : AC.Lock} (hl : l ∈ AC.liveLocks sp (tr.state y k).ac.locks ℓ.frame (tr.time k))
    (hls : l.slot < s) {L : AC.Blk sp.n (List (FG.Att sp.n))} (hL : L ∈ ℓ.frame.tree)
    (hLr : L.root = l.block) :
    Anc (tr.HonestBlocks H) L P ∨ Anc (tr.HonestBlocks H) L ℓ.frame.fcRoot := by
  have hr' := (Compose.goldilocks_ac_projection_from hrun hs.noColl).localRun
  have hU := hr'.coherent
  obtain ⟨hΦ, hΦU⟩ := AC.frameIn_of_callAt hr' hy hv.1
  have htk : sp.ts s ≤ tr.time k :=
    (AC.ts_le_iff_le_slot sp (hr'.time_nonneg k) _).2
      (by rw [← he, (AC.castAt_spec hr' hy hv).2.1])
  have hclean := live_lock_clean (hr.trans htk) (Compose.locksWF_state hrun hs.noColl hy k) hl
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩ := hl
  dsimp only at hls hLr hclean
  obtain ⟨hvat, hva⟩ := AC.viableAncestor_anc hΦ hB₀
  obtain rfl : L = ℓ.frame.viableAncestor B₀ := hU.1 (hΦU hL) (hΦU hvat) hLr
  have hLB₀ := Anc.mono hΦU hva
  -- the block below a stored origin `O` of the voter: `L ⪯ B₀ ⪯ O`
  have key : ∀ O : AC.Blk sp.n (List (FG.Att sp.n)),
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
    have hext := clean_slow_extends hrun hs hc hw hy hO hj
    exact key O hLO (Or.inl (clean_slow_proposal hrun hs hc hw hy hO hj hP hy hv he hk hrk
      fun z hz k' hk' e' ⟨ℓ', hc', he'⟩ hs' =>
        hext k' z hz ℓ' e' ⟨hc', he'⟩ hs' (hk.mono_right hk'.le)))
  · rw [← Compose.projAC_state hrun.toLocalRun hy] at hl₀
    obtain ⟨r, hrk, CV, ℓ', D, hcw, hfl, hLO⟩ :=
      stored_fast_lock_provenance hr' hrun.vstart hy k l₀ hl₀ hf
    have hO : Compose.StoredFastLockAt tr y r l₀.slot (ℓ'.frame.viableAncestor D) CV :=
      ⟨ℓ', D, hcw, hfl, rfl⟩
    have hj := hclean.1 hf
    have hext := clean_fast_extends hrun hs hc hw hy hO hj
    exact key _ hLO (Or.inl (clean_fast_proposal hrun hs hc hw hy hO hj hP hls hy hv he hk hrk
      fun z hz k' hk' e' ⟨ℓ'', hc', he'⟩ hs' =>
        hext k' z hz ℓ'' e' ⟨hc', he'⟩ hs' (hk.mono_right hk'.le)))

end Consensus.Goldilocks.Healing

end

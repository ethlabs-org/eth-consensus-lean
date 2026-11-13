module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Frontier.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Frontier.Viable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The pre-`b` frontier over AC traces: the next vote batch (`V_s` to `V_{s+1}`)

The AC content of `Compose/Sleepy/Transfer`'s finite-deadline vote step, over an AC trace with the
unlock given at a write mode and trivial frames. The unlock is read only through the unlock
relation of the trace law (`ACLocalRunU.lawful`, by `readPoint_locks_below_storedU` and
`lock_origin_readPointU`), so the oracle is any lawful one:

* **locks** (`vote_locks_compatibleAC`): at an honest slot-`(s+1)` vote at a time `≤ b`, every live
  lock block after the unlocking is compatible with a block `B` compatible with every origin within
  `b` of label at most `s`: a lock of slot at most `s` is moved back from a stored lock, which sits
  below an origin of its slot from an earlier cut (`lock_below_originU`); one of slot `s + 1` is
  optimistic over earlier honest slot-`(s+1)` votes, which extend `B`;
* **the counted batch** (`vote_extends_of_counted_batchAC`, `vote_extends_of_batchAC`, after the
  composite file's SA section, with the unlock given);
* **first transfer** (`first_transfer_stepAC`): A1.8 with the unlock given
  (`result_transfer_ancU`) for a result, A1.4 (a) (`optimistic_transfer_storedU`) for an optimistic
  selection, with the viability of trivial frames (`trivial_viableAC`) and the carry of
  `Frontier/Carry`;
* **later batch** (`later_transfer_stepAC`): the more than `f` honest slot-`s` votes extend `B`,
  are carried, and win the walk;
* `votes_below_succAC`: strong induction on the cut over the slot-`(s+1)` votes. -/

namespace Consensus.Goldilocks.SA


variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}
  {proposer : Nat → Fin sp.n} {b : Time}

/-! ### The live locks at a vote -/

/-- **The live locks at a slot-`(s+1)` vote at a time `≤ b` are compatible with `B`**, a block
compatible with every origin within `b` of label at most `s`, that the earlier honest
slot-`(s+1)` votes extend (`f < n/2`). -/
theorem vote_locks_compatibleAC
    (hrun : ACRunU wm u proposer tr H U) (hf : 2 * Hᶜ.ncard < sp.n)
    {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    {B : Blk sp.n FGP}
    (hBc : ∀ C j, OriginWithinAC tr H C j b → j ≤ s → Compatible U B C)
    (hE : EarlierVotesExtend tr H U i (s + 1) B) :
    ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L B := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc.1
  have hsi : e.msg.slot = sp.slot (tr.time i) := (castAt_specU hr hy hc).2.1
  have down : ∀ {X Y}, Anc U X Y → Compatible U Y B → Compatible U X B := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact anc_total hU hXY h
  rintro L ⟨hL, l, ⟨l₀, hl₀, B₀, hB₀, hB₀r, hlive, rfl⟩, hlL⟩
  have hLe : L = ℓ.frame.viableAncestor B₀ :=
    hU.1 (hΦU hL) (hΦU (viableAncestor_anc hΦ hB₀).1) hlL.symm
  subst hLe
  refine down (Anc.mono hΦU (anc_viableAncestor _ B₀)) ?_
  rcases le_or_gt l₀.slot s with hle | hlt
  · obtain ⟨l₁, hl₁, hsl₁, B₁, hB₁, hB₁r, B₀', hB₀', hB₀'r, hA⟩ :=
      readPoint_locks_below_storedU hr hy hc (show 0 < sp.slot (tr.time i) by omega) l₀ hl₀
        (show l₀.slot ≠ sp.slot (tr.time i) by omega)
    obtain rfl : B₀' = B₀ := hΦ.coherent.1 hB₀' hB₀ (hB₀'r.trans hB₀r.symm)
    obtain ⟨L₁, hL₁, hL₁r, O, hL₁O, k, hk, CV, hO⟩ := lock_below_originU hr hy i l₁ hl₁
    obtain rfl : L₁ = B₁ := hU.1 hL₁ (hΦU hB₁) (hL₁r.trans hB₁r.symm)
    have hOw : OriginWithinAC tr H O l₁.slot b :=
      originWithinAC_iff.2 ⟨y, hy, k, CV, (hr.time_mono hk.le).trans hib, hO⟩
    exact down ((Anc.mono hΦU hA).trans hL₁O) (hBc O l₁.slot hOw (by omega)).symm
  · obtain ⟨Φ', A, D, -, hΦ'U, -, h34, hpool, -, L₀, hL₀, hL₀r, hL₀D⟩ :=
      lock_origin_readPointU hrun hy hc l₀ hl₀ (by rw [hs]; push_cast; omega)
    obtain rfl : L₀ = B₀ := hU.1 hL₀ (hΦU hB₀) (hL₀r.trans hB₀r.symm)
    refine down hL₀D (origin_compatible hU hΦ'U (CommitteeDict.full sp.n) h34
      (fun _ _ => mem_full _ _) (by simpa only [ncard_inter_full, hrun.stock] using hf)
      fun v hv hvH => ?_)
    obtain ⟨hvs, j, hj, e', hvote, rfl⟩ := hpool v hv hvH
    obtain ⟨ℓ', hcj⟩ := id hvote
    have hsj : e'.msg.slot = sp.slot (tr.time j) := (castAt_specU hr hvH hcj).2.1
    have : sp.slot (tr.time j) ≤ sp.slot (tr.time i) :=
      slot_mono sp (hr.time_nonneg j) (hr.time_mono hj.le)
    exact hE _ hvH j hj e' hvote (by omega)

/-! ### The counted batch -/

/-- The later-batch walk for a selected honest slot-`s` batch, with the unlock given (the
composite `vote_extends_of_counted_batch`): its votes extend `B`, are carried at the read point,
and outnumber half of a set covering all merged voters. Viability and compatibility of all live
locks then make the successor vote extend `B`. -/
theorem vote_extends_of_counted_batchAC (hrun : ACRunU wm u proposer tr H U)
    {s : Nat} {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) {B : Blk sp.n FGP}
    (hviab : ViableAtVote ℓ e (s + 1) B)
    {SX W : Set (Fin sp.n)} (hSXH : SX ⊆ H)
    (hSXv : ∀ x ∈ SX, ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = s)
    (hall : ∀ x ∈ SX, ∀ j e', VoteAt tr x j e' → e'.msg.slot = s → VoteExtends U e'.msg B)
    (hW : voters (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes ⊆ W)
    (hcount : W.ncard < 2 * SX.ncard)
    (hcarry : CarryAt tr U y i e s
      {v | ∃ x ∈ SX, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s})
    (hlocks : ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L B) :
    VoteExtends U e.msg B := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨-, -, -, hhead⟩ := castAt_specU hr hy hc
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc.1
  have hσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := voteDomain_ancU hr hy hc
  rw [hs] at hdomA
  have hBt : B ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  have hsupp : SX ⊆ supporters ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s B := by
    intro w hwSX
    have hw := hSXH hwSX
    obtain ⟨j, e', hv, hvs⟩ := hSXv w hwSX
    obtain ⟨ℓw, hcw⟩ := id hv
    have hvw : e'.msg.val = w := (castAt_specU hr hw hcw).1
    have hmem : e'.msg ∈ {v | ∃ x ∈ SX, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s} :=
      ⟨w, hwSX, j, e', hv, rfl, hvs⟩
    have hheld : HeldBefore e.readPoint e'.msg (sp.ts s + 3 * sp.Δ) := by
      rcases hcarry.holds _ hmem with h | ⟨v₁, v₂, h12, h1, h2, hv₁, hv₂, hs₁, hs₂, hh₁, hh₂⟩
      · exact h
      · exfalso
        have hm : ∀ u', u'.slot = s → HeldBefore e.readPoint u' (sp.ts s + 3 * sp.Δ) →
            u' ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes := by
          intro u' hus hu
          refine Or.inl (List.mem_filter.2 ⟨?_, ?_⟩)
          · simp only [SAState.poolAt, show ¬ (((s + 1 : Nat) : Int) - 1 < 0) by omega,
              ite_false]
            simpa [hus] using hu.1
          · simpa [freeze] using hu.2
        obtain ⟨j₁, -, e₁, hv₁', he₁⟩ :=
          honest_merged_voteU hrun hy hc (hm v₁ hs₁ hh₁) (hv₁.trans hvw ▸ hw)
        have := one_vote_per_slotU sp FGP ro H U tr hr w hw j₁ j e₁ e'
          (hv₁.trans hvw ▸ hv₁') hv (by rw [he₁, hs₁, hvs])
        exact h1 (he₁ ▸ this.2 ▸ rfl)
    obtain ⟨Hv, hHv, hHvr, hacc⟩ := hcarry.heads _ hmem
    obtain ⟨Hd, hHd, hHdr, hHds⟩ := honest_headU hrun hw hv
    obtain ⟨Hd', hHd', hHd'r, hBHd'⟩ := hall w hwSX j e' hv hvs
    have h1 : Hd = Hv := hU.1 hHd hHv (hHdr.trans hHvr.symm)
    have h2 : Hd' = Hv := hU.1 hHd' hHv (hHd'r.trans hHvr.symm)
    have := carried_supporterU hrun hy hc hs hBt hvs hheld
      ⟨Hv, hHv, hHvr, h1 ▸ hvs ▸ hHds, h2 ▸ hBHd', hacc Hv Relation.ReflTransGen.refl⟩
      (honest_not_equivocatorU hrun hy hc (hvw ▸ hw))
    exact hvw ▸ this
  have hcore := anc_getHead hU hΦ hΦU e.readPoint (tr.time i)
    (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int) (fun B hB =>
        voteDomain_subset_tree hB) hdomA hviab.voteDomain
    hlocks fun X' Cx hCx hp hCxC =>
      isBest_of_majority hΦ (merged_support_subsetU hr hy hc (s + 1)) (fun B hB =>
          (voteDomain_subset_tree hB.1))
        hsupp hW hcount hCx hp hCxC
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : B = getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame (s + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
  · exact he ▸ hBt
  · exact (Anc.mem hcore he).2

/-- The full honest batch is a counted batch when it outnumbers the faulty seats (the composite
`vote_extends_of_batch`, with the unlock given). -/
theorem vote_extends_of_batchAC (hrun : ACRunU wm u proposer tr H U)
    {s : Nat} {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) {B : Blk sp.n FGP}
    (hviab : ViableAtVote ℓ e (s + 1) B)
    (hall : ∀ x ∈ H, ∀ j e', VoteAt tr x j e' → e'.msg.slot = s → VoteExtends U e'.msg B)
    (hcount : Hᶜ.ncard < {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = s}.ncard)
    (hcarry : CarryAt tr U y i e s
      {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s})
    (hlocks : ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L B) :
    VoteExtends U e.msg B := by
  let SX : Set (Fin sp.n) := {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = s}
  have hW : voters (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes ⊆ SX ∪ Hᶜ := by
    rintro w ⟨v, hv, rfl⟩
    by_cases hw : v.val ∈ H
    · obtain ⟨j, -, e', hv', he'⟩ := honest_merged_voteU hrun hy hc hv hw
      exact Or.inl ⟨hw, j, e', hv', by
        rw [he']; exact merged_vote_slotU hrun.localRun hy hc v hv⟩
    · exact Or.inr hw
  have hcount' : (SX ∪ Hᶜ).ncard < 2 * SX.ncard := by
    have := Set.ncard_union_le SX Hᶜ
    change Hᶜ.ncard < SX.ncard at hcount
    omega
  have hset : {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s} =
      {v | ∃ x ∈ SX, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s} := by
    ext v
    constructor
    · rintro ⟨x, hx, j, e', hv, rfl, hs'⟩
      exact ⟨x, ⟨hx, j, e', hv, hs'⟩, j, e', hv, rfl, hs'⟩
    · rintro ⟨x, hx, j, e', hv, he, hs'⟩
      exact ⟨x, hx.1, j, e', hv, he, hs'⟩
  rw [hset] at hcarry
  exact vote_extends_of_counted_batchAC hrun hy hc hs hviab (fun _ hx => hx.1)
    (fun _ hx => hx.2) (fun x hx => hall x hx.1) hW hcount' hcarry hlocks

/-- **The honest batch reaches a next-slot vote** at a time `≤ b` whose `Φ.F` is at or below a
block `B` that every honest slot-`s` vote extends. -/
theorem honest_batch_carryAC (hr : ACLocalRunU wm u H U tr)
    (hsy : SyncUntilAC (goldilocksSA sp FGP ro) H U b tr)
    {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b)
    {B : Blk sp.n FGP}
    (hall : ∀ x ∈ H, ∀ k e', VoteAt tr x k e' → e'.msg.slot = s → VoteExtends U e'.msg B)
    (hF : Anc U ℓ.frame.F B) :
    CarryAt tr U y i e s {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s} := by
  have hU := hr.coherent
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hone : ∀ v ∈ {v | ∃ x ∈ H, ∃ j e', VoteAt tr x j e' ∧ e'.msg = v ∧ v.slot = s},
      CarryAt tr U y i e s {v} := by
    rintro v ⟨x, hx, k, e', ⟨ℓk, hck, he'⟩, rfl, hvs⟩
    have hk := (castAt_specU hr hx ⟨hck, he'⟩).2.1
    obtain ⟨Hd, hHd, hHdr, -⟩ := honest_head_frameU hr hx ⟨hck, he'⟩
    have hkt := cast_time_leAC hr hx ⟨hck, he'⟩
    have hΦkU := (frameIn_of_callAtU hr hx hck).2
    obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hall x hx k e' ⟨ℓk, hck, he'⟩ hvs
    obtain rfl : Hd = Hv := hU.1 (hΦkU hHd) hHv (hHdr.trans hHvr.symm)
    have hkt' : tr.time k < sp.ts s + 2 * sp.Δ := by
      rw [hvs] at hkt
      exact hkt.trans_lt (add_lt_add_of_le_of_lt le_rfl (lt_mul_of_one_lt_left hΔ (by norm_num)))
    refine carryAt_of_writerAC hr hsy hx hy hc hs hib ?_
    rintro v rfl
    refine ⟨hvs, ⟨k, ⟨ℓk, hck, Or.inl ⟨e', he', rfl⟩⟩,
      (ts_le_iff_le_slot sp (hr.time_nonneg k) s).2 (by omega), hkt'⟩,
      Hd, hHv, hHvr, hF.trans hBHv, ?_⟩
    rcases Compose.frame_anc_acceptedU hr hx k ℓk hck Hd hHd Hd .refl with hg | ⟨k', hk', hacc⟩
    · exact Or.inl hg
    · exact Or.inr ⟨k', hacc, lt_of_le_of_lt (hr.time_mono hk') hkt'⟩
  exact ⟨hr.awake_of_call y hy i ℓ hc.1, (castAt_specU hr hy hc).2.2.1,
    fun v hv => (hone v hv).heads v rfl, fun v hv => (hone v hv).holds v rfl⟩

/-! ### The two transfer steps -/

/-- A block viable at an honest vote is in the vote's frame, above its `Φ.F`. -/
theorem viable_anc_FAC (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e) {σ : Nat}
    {B : Blk sp.n FGP} (hviab : ViableAtVote ℓ e σ B) : Anc U ℓ.frame.F B := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc.1
  have hBt : B ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  exact (hΦ.rooted.2 B hBt).mono hΦU

/-- **First transfer up to `b`**: an honest slot-`(s+1)` vote at a time `≤ b` extends an origin
within `b` of label `s` that the earlier honest slot-`(s+1)` votes extend. -/
theorem first_transfer_stepAC
    (hrun : ACRunU wm u proposer tr H U) (htriv : TrivialFrames tr H)
    (htick : TickDuty tr H)
    (hsy : SyncUntilAC (goldilocksSA sp FGP ro) H U b tr) (hf : 2 * Hᶜ.ncard < sp.n)
    (hJ : ∀ s : Nat, sp.ts s + sp.Δ ≤ b → FaultBound tr H (sp.ts s + sp.Δ))
    {s : Nat} (hP : OriginsBelowAC tr H U (s + 1) b) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) {C : Blk sp.n FGP}
    (hC : OriginWithinAC tr H C s b) (hE : EarlierVotesExtend tr H U i (s + 1) C) :
    VoteExtends U e.msg C := by
  have hr := hrun.localRun
  have hsv := hsy.service
  have hCc : ∀ C' j, OriginWithinAC tr H C' j b → j ≤ s → Compatible U C C' :=
    fun C' j hC' hj => originsBelowAC_iff.1 hP C s C' j (by omega) (by omega) hC hC'
  obtain ⟨x', hx', k', e', hv', -, hs', hext'⟩ := honest_supporterAC hrun htick hsv hf hJ hC
  have hvf := trivial_viableAC hr htriv hsy hy hc hs hib ⟨x', hx', k', e', hv', hs', hext'⟩
  have hlocks := vote_locks_compatibleAC hrun hf hy hc hs hib hCc hE
  have hF := viable_anc_FAC hr hy hc hvf
  obtain ⟨x, hx, i₀, CV, hi₀, hR | hO⟩ := originWithinAC_iff.1 hC
  · obtain ⟨ℓX, hupd, -, -⟩ := id hR
    exact result_transfer_ancU sp hrun hx hR .refl hy hc hs
      (result_carryAC hr hsy hx hR hy hc hs hib hF) hvf hlocks
      (writer_mergedAC hr hsv hx hupd hi₀ hy hc hs)
  · exact optimistic_transfer_storedU sp hrun (CommitteeDict.full sp.n) CommitteeP.full
      CommitteeT.full (size_binding_full hrun.stock) hx hO .refl (cs2_full hrun.stock hf)
      (cs2_full hrun.stock hf) hy hc hs
      (optimistic_carryAC hr hsy hx hO hy hc hs hib hF) hvf hE

/-- **Later batch up to `b`**: an honest slot-`(s+1)` vote at a time `≤ b` extends a block `B`
that every honest slot-`s` vote extends, compatible with every origin within `b` of label at
most `s`, and extended by the earlier honest slot-`(s+1)` votes. -/
theorem later_transfer_stepAC
    (hrun : ACRunU wm u proposer tr H U) (htriv : TrivialFrames tr H)
    (htick : TickDuty tr H)
    (hsy : SyncUntilAC (goldilocksSA sp FGP ro) H U b tr) (hf : 2 * Hᶜ.ncard < sp.n)
    (hJ : ∀ s : Nat, sp.ts s + sp.Δ ≤ b → FaultBound tr H (sp.ts s + sp.Δ))
    {s : Nat} {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1) (hib : tr.time i ≤ b) {B : Blk sp.n FGP}
    (hBc : ∀ C j, OriginWithinAC tr H C j b → j ≤ s → Compatible U B C)
    (hall : ∀ x ∈ H, ∀ k e', VoteAt tr x k e' → e'.msg.slot = s → VoteExtends U e'.msg B)
    (hE : EarlierVotesExtend tr H U i (s + 1) B) :
    VoteExtends U e.msg B := by
  have hr := hrun.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hti := (vote_restartsAC hr hy hc hs).2
  have hcount : Hᶜ.ncard <
      {x | x ∈ H ∧ ∃ j e', VoteAt tr x j e' ∧ e'.msg.slot = s}.ncard := by
    refine lt_of_lt_of_le (hJ s (by linarith)) (Set.ncard_le_ncard ?_)
    rintro x ⟨hx, hw, hj⟩
    obtain ⟨k, e', hv, hs', -⟩ := vote_of_awake_joinedAC hr htick hx hw hj
    exact ⟨hx, k, e', hv, hs'⟩
  obtain ⟨x, hx, k, e', hv, hvs⟩ :=
    (Set.ncard_pos (Set.toFinite _)).1 ((Nat.zero_le _).trans_lt hcount)
  have hvf := trivial_viableAC hr htriv hsy hy hc hs hib
    ⟨x, hx, k, e', hv, hvs, hall x hx k e' hv hvs⟩
  have hlocks := vote_locks_compatibleAC hrun hf hy hc hs hib hBc hE
  exact vote_extends_of_batchAC hrun hy hc hs hvf hall hcount
    (honest_batch_carryAC hr hsy hy hc hs hib hall (viable_anc_FAC hr hy hc hvf)) hlocks

/-- **Extending the vote frontier up to `b`**: `P_{s+1}` and `V_s` give `V_{s+1}`, by strong
induction on the cut over the honest slot-`(s+1)` votes (the first bad vote). -/
theorem votes_below_succAC
    (hrun : ACRunU wm u proposer tr H U) (htriv : TrivialFrames tr H)
    (htick : TickDuty tr H)
    (hsy : SyncUntilAC (goldilocksSA sp FGP ro) H U b tr) (hf : 2 * Hᶜ.ncard < sp.n)
    (hJ : ∀ s : Nat, sp.ts s + sp.Δ ≤ b → FaultBound tr H (sp.ts s + sp.Δ))
    {s : Nat} (hP : OriginsBelowAC tr H U (s + 1) b) (hV : VotesBelowAC tr H U s b) :
    VotesBelowAC tr H U (s + 1) b := by
  have hr := hrun.localRun
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have key : ∀ i, ∀ y ∈ H, ∀ e, VoteAt tr y i e → tr.time i ≤ b →
      e.msg.slot = s + 1 → ∀ C j, OriginWithinAC tr H C j b → j ≤ s →
        VoteExtends U e.msg C := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      rintro y hy e ⟨ℓ, hc⟩ hib hs C j hC hj
      have hE : EarlierVotesExtend tr H U i (s + 1) C :=
        fun x hx k hk e' hv hs' =>
          ih k hk x hx e' hv ((hr.time_mono hk.le).trans hib) hs' C j hC hj
      rcases hj.lt_or_eq with hj | rfl
      · have hti := (vote_restartsAC hr hy hc hs).2
        exact later_transfer_stepAC hrun htriv htick hsy hf hJ hy hc hs hib
          (fun C' j' hC' hj' => originsBelowAC_iff.1 hP C j C' j' (by omega) (by omega) hC hC')
          (fun x hx k e' hv hs' => by
            obtain ⟨ℓk, hck⟩ := id hv
            have hkt := cast_time_leAC hr hx hck
            rw [hs'] at hkt
            exact votesBelowAC_iff.1 hV C j hC x hx k e' hv (by linarith) (by omega) hs'.le) hE
      · exact first_transfer_stepAC hrun htriv htick hsy hf hJ hP hy hc hs hib hC hE
  refine votesBelowAC_iff.2 fun C j hC y hy i e hv hib hj hm => ?_
  rcases Nat.lt_or_ge e.msg.slot (s + 1) with h | h
  · exact votesBelowAC_iff.1 hV C j hC y hy i e hv hib hj (by omega)
  · exact key i y hy e hv hib (by omega) C j hC (by omega)

end Consensus.Goldilocks.SA

end

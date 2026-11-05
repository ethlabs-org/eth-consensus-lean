module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Unanimity.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: where the honest slot-`p` walks start (H.1 (i))

The anchor of an honest vote of slot `p`, and the anchor of the honest proposal of slot `p`
(`d.start`), are `fc_root` (genesis) or a live lock block. A lock of a slot below `p` is settled
(`LocksSettled` from `t_{p−1}`): every honest vote of slot `p` and the proposal head `d.head`
extend its stored block, which extends the lock block. A lock of slot `p` is written by an
optimistic confirmation on three quarters of the committee, so it is extended by an honest
slot-`p` vote; at a vote, one cast at an earlier cut (`lock_origin_readPoint`). No lock has a
later slot. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {p : Nat} {P : Blk sp.n FGP}
  {k : Nat} {ℓp : ACLabel (goldilocksSA sp FGP ro)} {d : DutyHead sp.n FGP (Payload sp.n)}
  {pay : Payload sp.n} {schedule : Nat → Fin sp.n}

/-- Under trivial frames, the anchor of a walk at an honest call is in the frame tree, and it is
`Φ.F` or the block of a stored live lock (its own viable ancestor). -/
private theorem anchor_cases (hS : StandaloneRun tr H U schedule g)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) (A : SAState sp.n) (t : Time) :
    getAnchor sp A ℓ.frame t ∈ ℓ.frame.tree ∧ (getAnchor sp A ℓ.frame t = ℓ.frame.F ∨
      ∃ l ∈ A.locks, l.LiveAt sp t ∧ (getAnchor sp A ℓ.frame t).root = l.block) := by
  obtain ⟨hΦ, -⟩ := frameIn_of_callAt hS.run.localRun hy hc
  obtain ⟨-, hfc, hvh, -⟩ := hS.trivial y hy i ℓ hc
  unfold getAnchor
  cases hd : deepest ℓ.frame (liveLockBlocks sp A.locks ℓ.frame t ∪ {ℓ.frame.fcRoot}) with
  | none => exact ⟨hΦ.fcRoot_mem, Or.inl hfc⟩
  | some D =>
    change D ∈ ℓ.frame.tree ∧ (D = ℓ.frame.F ∨ ∃ l ∈ A.locks, _ ∧ D.root = l.block)
    rcases (deepest_mem hd).1 with h | h
    · obtain ⟨hDt, -, ⟨l, hl, B₀, hB₀, hB₀r, hlive, rfl⟩, hDr⟩ := h
      have hF : ℓ.frame.Anc ℓ.frame.fcRoot B₀ := by rw [hfc]; exact hΦ.rooted.2 B₀ hB₀
      have hDB : D.root = B₀.root := by
        rw [← viableAncestor_self hΦ hB₀ (Or.inl ⟨hB₀, hF, B₀, hB₀, hvh ▸ hB₀,
          Relation.ReflTransGen.refl⟩)]
        exact hDr.symm
      exact ⟨hDt, Or.inr ⟨l, hl, hlive, hDB.trans hB₀r⟩⟩
    · rw [Set.mem_singleton_iff.1 h]
      exact ⟨hΦ.fcRoot_mem, Or.inl hfc⟩

/-- A stored lock of an honest node has a slot at most the current one: it was written by an
optimistic confirmation of its slot or by the update of its slot, at an earlier cut. -/
theorem stored_lock_slot_le (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) {l : Lock} (hl : l ∈ (tr.state y i).locks) :
    l.slot ≤ sp.slot (tr.time i) := by
  obtain ⟨j, hj, B, horig, -⟩ := lock_provenance hr hy i l hl
  have hmono := slot_mono sp (hr.time_nonneg j) (hr.time_mono hj.le)
  rcases horig with ⟨CV, ℓ, A, -, hsl, -⟩ | ⟨ℓ, -, -, htj, -⟩
  · omega
  · have : (l.slot : Int) ≤ sp.slot (tr.time j) :=
      (ts_le_iff_le_slot sp (hr.time_nonneg j) _).1 (by rw [htj]; linarith [sp.toParams.hΔ])
    omega

/-- The proposal head and every honest vote extend `Φ.F` (genesis) of an honest call. -/
private theorem genesis_extended (hs : UnanimitySetting tr H U schedule g p P k ℓp d pay)
    {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    Anc U ℓ.frame.F d.head ∧ ∀ z ∈ H, ∀ j e, VoteAt tr z j e → VoteExtends U e.msg ℓ.frame.F := by
  have hS := hs.standalone
  have hr := hS.run.localRun
  have hq := hs.proposer_mem
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hq hs.call
  refine ⟨?_, fun z hz j e ⟨ℓ', hc', he'⟩ => ?_⟩
  · have hpay := hs.payload
    unfold acProposal at hpay
    split_ifs at hpay
    simp only [Option.some.injEq, Prod.mk.injEq] at hpay
    obtain ⟨rfl, -⟩ := hpay
    rw [trivial_F_eq hS hy hq hc hs.call]
    exact (hΦ.rooted.2 _ (getHead_mem' hΦ (fun _ hB => hB.1) _ _ _ _)).mono hΦU
  · obtain ⟨hΦ', hΦ'U⟩ := frameIn_of_callAt hr hz hc'
    obtain ⟨Hd, hHd, hHdr, -⟩ := honest_head_frame hr hz ⟨hc', he'⟩
    rw [trivial_F_eq hS hy hz hc hc']
    exact ⟨Hd, hΦ'U hHd, hHdr, (hΦ'.rooted.2 Hd hHd).mono hΦ'U⟩

/-- **The anchor of an honest slot-`p` vote**: a block of `U` that every honest vote of slot
`p` and the proposal head extend, or extended by an honest slot-`p` vote of an earlier cut. -/
theorem vote_anchor_cases (hs : UnanimitySetting tr H U schedule g p P k ℓp d pay) {x : Fin sp.n}
    (hx : x ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr x j ℓ e) (hes : e.msg.slot = p) :
    getAnchor sp e.readPoint ℓ.frame (tr.time j) ∈ U ∧
      ((Anc U (getAnchor sp e.readPoint ℓ.frame (tr.time j)) d.head ∧
        ∀ z ∈ H, ∀ j' e', VoteAt tr z j' e' → e'.msg.slot = p →
          VoteExtends U e'.msg (getAnchor sp e.readPoint ℓ.frame (tr.time j))) ∨
      ∃ z ∈ H, ∃ j' < j, ∃ e', VoteAt tr z j' e' ∧ e'.msg.slot = p ∧
        VoteExtends U e'.msg (getAnchor sp e.readPoint ℓ.frame (tr.time j))) := by
  have hS := hs.standalone
  have hrun := hS.run
  have hr := hrun.localRun
  have hU := hr.coherent
  have hq := hs.proposer_mem
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc.1
  have hsl : sp.slot (tr.time j) = p := by rw [← hes]; exact (castAt_spec hr hx hc).2.1.symm
  have htj : sp.ts p ≤ tr.time j :=
    (ts_le_iff_le_slot sp (hr.time_nonneg j) _).2 (by rw [hsl])
  have hp0 : 0 < p := by
    have h0 : sp.ts 0 = 0 := by simp [SAParams.ts]
    have := hs.late
    have := gbar_nonneg g
    have := Θ_nonneg sp
    have : (0 : Int) < p := (ts_lt_iff sp).1 (by rw [h0]; linarith)
    omega
  obtain ⟨haT, ha⟩ := anchor_cases hS hx hc.1 e.readPoint (tr.time j)
  refine ⟨hΦU haT, ?_⟩
  rcases ha with ha | ⟨l, hl, hlive, hlr⟩
  · rw [ha]
    obtain ⟨h1, h2⟩ := genesis_extended hs hx hc.1
    exact Or.inl ⟨h1, fun z hz j' e' hv _ => h2 z hz j' e' hv⟩
  set a := getAnchor sp e.readPoint ℓ.frame (tr.time j)
  by_cases hlp : l.slot = p
  · -- a lock of slot `p`: three quarters of the committee voted for a block above it
    right
    obtain ⟨Φ, A, D, -, hΦ'U, -, h34, hpool, -, L, hL, hLr, hLD⟩ :=
      lock_origin_readPoint hrun hx hc l hl (by rw [hes, hlp]; omega)
    obtain rfl : L = a := hU.1 hL (hΦU haT) (hLr.trans hlr.symm)
    have hf := hS.two_faulty_lt
    have hlt : Hᶜ.ncard < (optimisticVoters sp A Φ l.slot D).ncard := by omega
    obtain ⟨u, ⟨v, hv, rfl, R, hR, hRr, hDR⟩, hu⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
    have huH : v.val ∈ H := not_not.1 hu
    obtain ⟨hvs, j', hj', e', hve, rfl⟩ := hpool v hv huH
    exact ⟨_, huH, j', hj', e', hve, hvs.trans hlp, R, hΦ'U hR, hRr,
      hLD.trans (hDR.mono hΦ'U)⟩
  · -- a lock of a lower slot: settled
    left
    obtain ⟨l₀, hl₀, hsl₀, B, hB, hBr, B', hB', hB'r, hB'B⟩ :=
      readPoint_locks_below_stored hr hx hc (by rw [hsl]; exact hp0) l hl (by rw [hsl]; exact hlp)
    obtain rfl : B' = a := hΦ.coherent.1 hB' haT (hB'r.trans hlr.symm)
    have hle := stored_lock_slot_le hr hx j hl₀
    rw [hsl] at hle
    have hlive := hlive.trans ((castAt_readPoint_locksWF hr hx hc).cap hl)
    obtain ⟨hvotes, hprops⟩ :=
      locksSettled_iff.1 hs.settled x hx j (by linarith) l₀ hl₀ (by omega) B (hΦU hB) hBr
    have haB := hB'B.mono hΦU
    refine ⟨haB.trans (proposalsExtendAfter_iff.1 hprops _ hq k ℓp p d pay hs.call
      hs.call_proposal hs.time (by omega) hs.payload), fun z hz j' e' hv hes' => ?_⟩
    obtain ⟨Hd, hHd, hHdr, hBHd⟩ := votesExtendAfter_iff.1 hvotes z hz j' e' hv (by omega)
    exact ⟨Hd, hHd, hHdr, haB.trans hBHd⟩

/-- **The anchor of the proposal**: a block of `U` that every honest vote of slot `p` extends,
or extended by some honest slot-`p` vote. -/
theorem proposal_anchor_cases (hs : UnanimitySetting tr H U schedule g p P k ℓp d pay) :
    d.start ∈ U ∧
      ((∀ z ∈ H, ∀ j e, VoteAt tr z j e → e.msg.slot = p → VoteExtends U e.msg d.start) ∨
        ∃ z ∈ H, ∃ j e, VoteAt tr z j e ∧ e.msg.slot = p ∧ VoteExtends U e.msg d.start) := by
  have hS := hs.standalone
  have hrun := hS.run
  have hr := hrun.localRun
  have hU := hr.coherent
  have hq := hs.proposer_mem
  have hΔ := sp.toParams.hΔ
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hq hs.call
  obtain ⟨-, hfc, hvh, -⟩ := hS.trivial _ hq k ℓp hs.call
  have hslot : sp.slot (tr.time k) = p := by
    rw [hs.time]; exact slot_of_mem sp p le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))
  have hpay := hs.payload
  unfold acProposal at hpay
  split_ifs at hpay
  simp only [Option.some.injEq, Prod.mk.injEq, hslot] at hpay
  obtain ⟨hd, -⟩ := hpay
  suffices h : ∀ (A : SAState sp.n) (V : View sp.n),
      A.locks = unlock sp (tr.state (schedule p) k).locks ℓp.frame (tr.time k)
        ((p : Int) - 1) V →
      getAnchor sp A ℓp.frame (tr.time k) ∈ U ∧
        ((∀ z ∈ H, ∀ j e, VoteAt tr z j e → e.msg.slot = p →
            VoteExtends U e.msg (getAnchor sp A ℓp.frame (tr.time k))) ∨
          ∃ z ∈ H, ∃ j e, VoteAt tr z j e ∧ e.msg.slot = p ∧
            VoteExtends U e.msg (getAnchor sp A ℓp.frame (tr.time k))) by
    rw [← hd]
    exact h _ _ rfl
  intro A V hA
  obtain ⟨haT, ha⟩ := anchor_cases hS hq hs.call A (tr.time k)
  refine ⟨hΦU haT, ?_⟩
  rcases ha with ha | ⟨l, hl, -, hlr⟩
  · rw [ha]
    exact Or.inl fun z hz j e hv _ => (genesis_extended hs hq hs.call).2 z hz j e hv
  set a := getAnchor sp A ℓp.frame (tr.time k)
  -- the unlocked lock comes from a stored live lock `l₂` on `B₂`, and `a ⪯ B₂`
  rw [hA] at hl
  obtain ⟨-, ⟨l₂, hl₂, B₂, hB₂, hB₂r, hlive, rfl⟩, B, hB, hBr, rfl⟩ := hl
  have hF : ℓp.frame.Anc ℓp.frame.fcRoot B₂ := by rw [hfc]; exact hΦ.rooted.2 B₂ hB₂
  have hself : ℓp.frame.viableAncestor B₂ = B₂ := viableAncestor_self hΦ hB₂
    (Or.inl ⟨hB₂, hF, B₂, hB₂, hvh ▸ hB₂, Relation.ReflTransGen.refl⟩)
  obtain rfl : B = B₂ := hΦ.coherent.1 hB hB₂ (by rw [hBr, hself])
  have haB : Anc U a B := by
    refine Anc.mono hΦU ?_
    split_ifs at hlr
    · obtain ⟨hT, hTB⟩ := unlockTarget_anc sp hΦ V ((p : Int) - 1) hB
      rw [hΦ.coherent.1 haT hT hlr]
      exact hTB
    · rw [hΦ.coherent.1 haT hB (hlr.trans hBr.symm)]
      exact Relation.ReflTransGen.refl
  have hle := stored_lock_slot_le hr hq k hl₂
  rw [hslot] at hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · -- a stored lock of a lower slot: settled
    left
    obtain ⟨hvotes, -⟩ :=
      locksSettled_iff.1 hs.settled _ hq k (by rw [hs.time]; linarith) l₂ hl₂
        (hlive.trans ((locksWF_state hr hq k).cap hl₂)) B (hΦU hB) hB₂r
    intro z hz j e hv hes
    obtain ⟨Hd, hHd, hHdr, hBHd⟩ := votesExtendAfter_iff.1 hvotes z hz j e hv (by omega)
    exact ⟨Hd, hHd, hHdr, haB.trans hBHd⟩
  · -- a stored lock of slot `p`: written by an optimistic confirmation before `t_p`
    right
    obtain ⟨j, hj, B', horig, L, hL, hLr, hLB'⟩ := lock_provenance hr hq k l₂ hl₂
    obtain rfl : L = B := hU.1 hL (hΦU hB) (hLr.trans hB₂r.symm)
    rcases horig with ⟨CV, hopt⟩ | ⟨ℓ', hupd⟩
    · obtain ⟨z, hz, j', e', hv, hes, Hd, hHd, hHdr, hB'Hd⟩ :=
        fastLock_honest_vote hrun hS.two_faulty_lt hq (Or.inr hopt)
      exact ⟨z, hz, j', e', hv, hes.trans heq, Hd, hHd, hHdr, haB.trans (hLB'.trans hB'Hd)⟩
    · exfalso
      have h1 := hupd.2.2.1
      have h2 := hr.time_mono hj.le
      rw [heq] at h1
      rw [hs.time, h1] at h2
      linarith

end Consensus.Goldilocks.SA

end

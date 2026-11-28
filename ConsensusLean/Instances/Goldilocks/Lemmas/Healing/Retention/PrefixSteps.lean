module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Order
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HR.4: the run's event order at a slot start and at its late tick

The local run facts behind the report-time bound (`Retention/Prefix`), on a run with no
collisions, with no reset, retention or service premise; the static prefix argument and its
growing-fault siblings read them on the honest prefix they need:

* **pools at a slot start** (`admit_pool_mem`, `receipt_pool_mem`, `step_pool_new`): at a slot
  start, a call other than a vote delivery takes in no vote but the node's own and those of the
  block it receives;
* **one signing per attestation** (`createAtt_spec`, `sign_unique`): an honest client refuses to
  sign a height pair it sent already;
* **the slot-start write** (`slot_start_optimistic`): an optimistic write of slot `m` before a
  signing at `t_m` counts only the signer's slot-`m` votes, so the committee size is at most one
  and the signer's own vote is at or before the write;
* **the late tick** (`vote_before_late_delivery`): a block accepted at `t_m + Δ` does not precede
  the recipient's slot-`m` vote. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload)

/-! ### Pools at a slot start -/

section Pools

variable {FGP : Type} {sp : AC.ACParams}

/-- A vote in a pool after an admission was there before, or is the admitted vote. -/
theorem admit_pool_mem {A : AC.ACState sp.n} {t : Time} {m w : AC.Vote sp.n} {s : Nat}
    (h : w ∈ (AC.admitVote sp A t m).pool s) : w ∈ A.pool s ∨ w = m := by
  unfold AC.admitVote at h
  split_ifs at h
  · exact Or.inl h
  · exact Or.inl h
  · simp only [Function.update_apply] at h
    split_ifs at h with hs
    · subst hs
      rcases List.mem_append.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_singleton.1 h)
    · exact Or.inl h

/-- A vote in a pool after a block's receipt was there before (the receipt only stamps the
block), or is a vote of the block. -/
theorem receipt_pool_mem {A : AC.ACState sp.n} {t : Time} {B : AC.Blk sp.n FGP}
    {w : AC.Vote sp.n} {s : Nat} (h : w ∈ (AC.blockReceipt sp A t B).pool s) :
    w ∈ A.pool s ∨ w ∈ AC.declaredHeadVotes B :=
  Or.inl h

private theorem tryVote_pool_mem (self : Fin sp.n) (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP)
    (t : Time) {w : AC.Vote sp.n} {s : Nat} (h : w ∈ (AC.tryVote sp self A Φ t).1.pool s) :
    w ∈ A.pool s ∨ w.val = self := by
  unfold AC.tryVote at h
  dsimp only at h
  split_ifs at h
  all_goals first
    | exact Or.inl h
    | (rw [AC.optimistic_pool] at h
       rcases admit_pool_mem h with h | rfl
       · exact Or.inl h
       · exact Or.inr rfl)

/-- At a slot start, a nondelivery call takes only own votes or votes from its input block. -/
theorem step_pool_new (self : Fin sp.n) (A : AC.ACState sp.n) (Φ : AC.Frm sp.n FGP)
    {t : Time} (ht : t = sp.ts (sp.slot t)) (hΔ : 0 < sp.Δ) (c : (AC.goldilocksAC sp FGP).Call)
    (hm : ∀ m, c ≠ .message m) (hc : c ≠ .restart) {w : AC.Vote sp.n} {s : Nat}
    (h : w ∈ ((AC.goldilocksAC sp FGP).step self A Φ t c).1.pool s) :
    w ∈ A.pool s ∨ w.val = self ∨ ∃ B, c = .block B ∧ w ∈ AC.declaredHeadVotes B := by
  cases c with
  | tick =>
    change w ∈ (AC.acOnTick sp self A Φ t).1.pool s at h
    unfold AC.acOnTick at h
    dsimp only at h
    split_ifs at h <;> first
      | exact Or.inl h
      | (exfalso; linarith)
  | proposal =>
    change w ∈ (AC.acProposal sp A Φ t).1.pool s at h
    unfold AC.acProposal at h
    dsimp only at h
    split_ifs at h <;> exact Or.inl h
  | toFG =>
    change w ∈ (AC.acToFG sp A Φ t).1.pool s at h
    unfold AC.acToFG at h
    split_ifs at h <;> exact Or.inl h
  | message m => exact absurd rfl (hm m)
  | block B =>
    change w ∈ (AC.tryVote sp self (AC.optimisticConfirmation sp (AC.blockReceipt sp A t B) Φ t)
      Φ t).1.pool s at h
    rcases tryVote_pool_mem _ _ _ _ h with h | h
    · rw [AC.optimistic_pool] at h
      rcases receipt_pool_mem h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨B, rfl, h⟩)
    · exact Or.inr (Or.inl h)
  | restart => exact absurd rfl hc

end Pools

/-! ### One signing per attestation -/

/-- `create_attestation` signs as `v`, records the attestation, and refuses a height pair whose
height (for a target) or height and entry (for a timeout) it sent already. -/
theorem createAtt_spec {n : Nat} {Λ Λ' : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) :
    a.val = v ∧ Λ' = Λ.recordAtt a ∧ ∀ b ∈ Λ.sent, ¬ (b.1 = a.h ∧ b.2.1 = a.T) := by
  unfold FG.Record.createAtt at h
  split at h
  · cases h
  · dsimp only at h
    split_ifs at h with hany
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, rfl, fun b hb hb' => hany ?_⟩
    rw [List.any_eq_true]
    exact ⟨b, hb, by simp [hb'.1, hb'.2]⟩

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp}

/-- An honest client's sent contents only grow. -/
private theorem sent_succ {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : GoldilocksRun proposer dg H tr ini)
    {v : Fin sp.n} (hv : v ∈ H)
    (c : Nat) {b : FG.Content} (hb : b ∈ (tr.state v c).record.sent) :
    b ∈ (tr.state v (c + 1)).record.sent := by
  by_cases hc : ∃ cut, tr.CallAt v c cut
  · obtain ⟨cut, hc⟩ := hc
    have hlaw := hrun.cutLaw v hv c cut hc
    rw [tr.state_succ_of_call hc]
    cases cut with
    | ac ell =>
      rw [hlaw.2.2.2]; exact hb
    | fg ell =>
      cases ell with
      | block B acc =>
        cases acc with
        | true =>
          rw [hlaw.2.2.2]; exact hb
        | false =>
          rw [hlaw.2]; exact hb
      | attestation a' =>
        rw [hlaw.2.2]; exact hb
      | attest C s =>
        cases s with
        | none =>
          rw [hlaw.2]; exact hb
        | some a' =>
          rw [(createAtt_spec hlaw.1).2.1]
          exact List.mem_append_left _ hb
  · rw [tr.state_succ_of_not fun cut hc' => hc ⟨cut, hc'⟩]
    exact hb

/-- **An honest validator signs an attestation at most once**: after signing, its content is in
the client's sent list, and `create_attestation` refuses it. -/
theorem sign_unique {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : GoldilocksRun proposer dg H tr ini)
    {v : Fin sp.n} (hv : v ∈ H)
    {d d' : Nat} {att : FG.Att sp.n} (hs : tr.SignAt v d att) (hs' : tr.SignAt v d' att) :
    d = d' := by
  have key : ∀ {d d'}, tr.SignAt v d att → tr.SignAt v d' att → d < d' → False := by
    intro d d' hs hs' hlt
    obtain ⟨C, hc⟩ := hs
    obtain ⟨C', hc'⟩ := hs'
    have hcut := hrun.cutLaw v hv d _ hc
    have hcut' := hrun.cutLaw v hv d' _ hc'
    have h₀ : att.content ∈ (tr.state v (d + 1)).record.sent := by
      rw [tr.state_succ_of_call hc, (createAtt_spec hcut.1).2.1]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have hmem : ∀ c, d + 1 ≤ c → att.content ∈ (tr.state v c).record.sent := by
      intro c hc
      induction c, hc using Nat.le_induction with
      | base => exact h₀
      | succ c _ ih => exact sent_succ hrun hv c ih
    exact (createAtt_spec hcut'.1).2.2 _ (hmem d' hlt) ⟨rfl, rfl⟩
  rcases lt_trichotomy d d' with h | h | h
  · exact (key hs hs' h).elim
  · exact h
  · exact (key hs' hs h).elim

/-! ### The slot-start write and the late tick -/

/-- A restart emits nothing. -/
private theorem restart_emits {ini}
    (hr : ACLocalRun (goldilocksNode sp) H (tr.HonestBlocks H) tr.projAC ini)
    {v : Fin sp.n} (hv : v ∈ H) {i : Nat} {ell : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt v i ell) (hcl : ell.call = .restart) : ell.emits = [] := by
  have he := hr.exec i ell hc.2 (hc.1 ▸ hv)
  rw [hc.1, hcl] at he
  have h' : ell.emits = (((AC.goldilocksAC sp (List (FG.Att sp.n))).step v
      (tr.projAC.state v i) ell.frame (tr.projAC.time i) .restart)).2 := by rw [he]
  rw [h']
  exact ((AC.restart_state sp) _ v (tr.projAC.state v i) ell.frame (tr.projAC.time i)
    (AC.frameIn_of_callAt hr hv hc).1 (hr.time_nonneg i)).1

/-- **An optimistic write of slot `m` before a signing at `t_m`** (the signing at a slot start).
The signing is in the signer's tick at `t_m`, so the write is too (before the tick, the node's
cuts at `t_m` are restarts), and so is every admission of a slot-`m` vote into the signer's pools
by then (`ac_on_tick` at `t_m` and `ac_proposal` keep the pools, a received block carries votes
of earlier slots, and no vote is delivered inside a tick): the pool of the optimistic check holds
slot-`m` votes of the signer only, so three quarters of the committee size is at most one
validator, the committee size is at most one, and the signer's own slot-`m` vote is at or before
the write. -/
theorem slot_start_optimistic {ini}
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    {v : Fin sp.n} (hv : v ∈ H) {d : Nat} {att : FG.Att sp.n}
    (hs : tr.SignAt v d att) {m : Nat} (hdt : tr.time d = sp.ts m)
    {r : Nat} (hrd : r < d) {D : AC.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (AC.Vote sp.n)} (hopt : AC.OptimisticLockAt tr.projAC v r m D CV)
    (hcs : 0 < sp.committeeSize) :
    sp.committeeSize ≤ 1 ∧ ∃ j' ≤ r, ∃ e', AC.VoteAt tr.projAC v j' e' ∧ e'.msg.slot = m := by
  have hrun' := Compose.goldilocks_ac_projection_from hrun hnc
  have hr := hrun'.localRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  obtain ⟨ellv, A, hpt, hsl, hsel, -⟩ := hopt
  have hslm : sp.slot (sp.ts m) = m := AC.slot_of_mem sp m le_rfl
    ((AC.ts_lt_iff sp).2 (by push_cast; omega))
  have hrt : tr.time r = sp.ts m := by
    refine le_antisymm (hdt ▸ hrun.time_mono hrd.le) ?_
    exact (AC.ts_le_iff_le_slot sp (hr.time_nonneg r) (m : Int)).2 (by rw [hsl])
  obtain ⟨C, hcd⟩ := hs
  obtain ⟨j, ev, kk, hg, hdj, hk⟩ := Compose.call_in_group hrun.toLocalRun hv hcd
  obtain ⟨x, rfl⟩ := @Compose.signed_only_in_ticks sp.toParams (goldilocksNode sp)
    proposer dg v _ _ _ C att (List.mem_of_getElem? hk)
  have hkk : kk < (Node.exec proposer dg v (tr.state v j) (tr.time d)
      (.tick x true)).2.length := by
    by_contra h
    rw [List.getElem?_eq_none (not_lt.mp h)] at hk
    cases hk
  have hnomsg : ∀ i, j ≤ i → i ≤ d → ∀ ell, tr.projAC.CallAt v i ell →
      ∀ mm, ell.call ≠ .message mm := by
    intro i h1 h2 ell hc mm hm
    have hl := (hg.2.1 (i - j) (by omega)).2.2.2.2
    rw [Nat.add_sub_cancel' h1, (Compose.projAC_callAt.mp hc).2] at hl
    have hmem := List.getElem_mem
      (l := (Node.exec proposer dg v (tr.state v j) (tr.time d) (.tick x true)).2)
      (n := i - j) (by omega)
    rw [← Option.some.inj hl] at hmem
    cases (exec_ac_call v _ _ _ hmem).2 mm hm
  have hpre : ∀ i < j, ∀ ell, tr.projAC.CallAt v i ell →
      tr.time i = sp.ts m → ell.call = .restart := by
    intro i hi ell hc ht
    obtain ⟨ell', he, hr'⟩ := Compose.before_tick hrun.toLocalRun hv ⟨x, true, hg⟩
      (Compose.projAC_callAt.mp hc) hi
      (by rw [ht, hdt])
    cases he
    exact hr'
  have hjr : j ≤ r := by
    by_contra hlt
    have hcl := hpre r (by omega) ellv hpt.1 hrt
    rcases hpt.2 with ⟨mm, hmm, -⟩ | ⟨B, hB, -⟩ | ⟨e₀, he₀, -⟩
    · rw [hcl] at hmm; cases hmm
    · rw [hcl] at hB; cases hB
    · rw [restart_emits hr hv hpt.1 hcl] at he₀; cases he₀
  have hQ : ∀ c ≤ d, ∀ w ∈ (tr.projAC.state v c).pool m, w.val = v := by
    intro c hc w hw
    have hws : w.slot = m := AC.state_pool_slotU sp hr.toU hrun.vstart hv c m w hw
    have hle : ∀ k₁, k₁ < c → sp.slot (tr.projAC.time k₁) ≤ m := fun k₁ hk₁ => by
      rw [← hslm, ← hdt]
      exact AC.slot_mono sp (hr.time_nonneg k₁) (hrun.time_mono (by omega))
    rcases AC.pool_origin hr hrun.vstart hv c w (by rw [hws]; exact hw) with
      ⟨k₁, hk₁, hsend, -, hsl₁⟩ | ⟨k₁, hk₁, ell₁, hc₁, -, -, B, hB, hwB⟩
    · have hsk : sp.slot (tr.projAC.time k₁) = m := le_antisymm (hle k₁ hk₁) (by omega)
      have htk : tr.time k₁ = sp.ts m := le_antisymm (hdt ▸ hrun.time_mono (by omega))
        ((AC.ts_le_iff_le_slot sp (hr.time_nonneg k₁) _).2 (by rw [hsk]))
      obtain ⟨ell₁, hc₁, ⟨e₁, he₁, rfl⟩ | ⟨hnr, hn, hh⟩⟩ := hsend
      · exact (AC.castAt_specU hr.toU hv ⟨hc₁, he₁⟩).1
      · have hjk : j ≤ k₁ := by
          by_contra h
          exact hnr (hpre k₁ (by omega) ell₁ hc₁ htk)
        have he := hr.exec k₁ ell₁ hc₁.2 (hc₁.1 ▸ hv)
        rw [hc₁.1] at he
        change w ∈ (tr.projAC.post k₁).pool w.slot at hh
        have hpost : tr.projAC.post k₁ = ((AC.goldilocksAC sp (List (FG.Att sp.n))).step v
            (tr.projAC.state v k₁) ell₁.frame (tr.projAC.time k₁) ell₁.call).1 := by rw [he]
        rw [hpost] at hh
        have hts : tr.projAC.time k₁ = sp.ts (sp.slot (tr.projAC.time k₁)) := by
          rw [hsk]; exact htk
        rcases step_pool_new v _ ell₁.frame hts hΔ ell₁.call
          (hnomsg k₁ hjk (by omega) ell₁ hc₁) hnr hh with h | h | ⟨B, hB, hwB⟩
        · exact absurd h hn
        · exact h
        · exfalso
          have hBt := (AC.accept_new sp hr hv ⟨ell₁, hc₁, hB⟩).1 ell₁ hc₁
          have h₁ := (AC.frame_validPayloadU sp hr.toU hv hc₁ B hBt).1 w hwB
          have h₂ := AC.frame_slot_leU sp hr.toU hv hc₁ B hBt
          omega
    · exfalso
      have h₁ := (AC.frame_validPayloadU sp hr.toU hv hc₁ B hB).1 w hwB
      have h₂ := AC.frame_slot_leU sp hr.toU hv hc₁ B hB
      have h₃ := hle k₁ hk₁
      omega
  have hP : ∀ w ∈ A.pool m, w.val = v := by
    intro w hw
    have hws := AC.optimisticPoint_pool_slotU hr.toU hrun.vstart hv hpt hw
    obtain ⟨hcv, hcase⟩ := hpt
    rcases hcase with ⟨mm, hmm, -⟩ | ⟨B, hB, rfl⟩ | ⟨e₀, he₀, rfl⟩
    · exact absurd hmm (hnomsg r hjr hrd.le ellv hcv mm)
    · rcases receipt_pool_mem hw with hw | hwB
      · exact hQ r hrd.le w hw
      · exfalso
        have hBt := (AC.accept_new sp hr hv ⟨ellv, hcv, hB⟩).1 ellv hcv
        have h₁ := (AC.frame_validPayloadU sp hr.toU hv hcv B hBt).1 w hwB
        have h₂ := AC.frame_slot_leU sp hr.toU hv hcv B hBt
        have h₃ : sp.slot (tr.projAC.time r) = m := hsl
        omega
    · rcases admit_pool_mem hw with hw | rfl
      · exact hQ (r + 1) hrd w (AC.readPoint_poolU hr.toU hv ⟨hcv, he₀⟩ hw).1
      · exact (AC.castAt_specU hr.toU hv ⟨hcv, he₀⟩).1
  have h34 : 3 * sp.committeeSize ≤ 4 * (AC.optimisticVoters sp A ellv.frame m D).ncard := by
    have h := hsel
    unfold AC.optimisticSelect at h
    dsimp only at h
    split_ifs at h
    have := (AC.deepest_mem h).1.2.1
    rwa [hsl] at this
  have hsub : AC.optimisticVoters sp A ellv.frame m D ⊆ {v} := by
    rintro i ⟨w, hw, rfl, -⟩
    exact hP w hw
  have hle1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_singleton] at hle1
  refine ⟨by omega, ?_⟩
  obtain ⟨i, w, hw, rfl, -⟩ :=
    Set.nonempty_of_ncard_ne_zero (s := AC.optimisticVoters sp A ellv.frame m D) (by omega)
  have hwv := hP w hw
  obtain ⟨hws, j', hj', e', hve', he'⟩ := AC.optimisticPoint_pool_voteU hrun'.toU hv hpt hw (hwv ▸
      hv)
  exact ⟨j', hj', e', hwv ▸ hve', by rw [he', hws]⟩

/-- **A delivery at `t_m + Δ` comes after the slot-`m` vote** (the
signing at `t_m + Δ`). At a public time a node's deliveries follow its tick, and its tick at
`t_m + Δ` casts its slot-`m` vote unless it voted in slot `m` already; so an honest voter of slot
`m` accepts no block at `t_m + Δ` before its vote. -/
theorem vote_before_late_delivery
    {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) {i : Nat} {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hA : tr.AcceptAt y i W) (hik : i < k) (ht : tr.time i = sp.ts e.msg.slot + sp.Δ) :
    False := by
  have hrun' := Compose.goldilocks_ac_projection_from hrun hnc
  have hr := hrun'.localRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  set u := sp.ts e.msg.slot + sp.Δ with hu
  have hm0 : 0 ≤ sp.ts e.msg.slot := by simp only [ACParams.ts]; positivity
  have htk : tr.time k = u :=
    le_antisymm (Compose.cast_head_fcRoot hr hrun.vstart hy hc).2 (ht ▸ hrun.time_mono hik.le)
  have hslot : sp.slot u = e.msg.slot := AC.slot_of_mem sp _ (by linarith)
    (by simp only [hu, ACParams.ts]; push_cast; linarith)
  have hpub : sp.toParams.IsPublic u :=
    ⟨4 * (e.msg.slot : Int) + 1, by simp only [hu, ACParams.ts]; ring⟩
  have hnprop : ¬ Node.Proposes proposer y u := by
    rintro ⟨_, hP2, _⟩
    change u = sp.toParams.slotTime (sp.slot u) at hP2
    rw [hslot, sp.slotTime_eq] at hP2
    have : u = sp.ts e.msg.slot + sp.Δ := hu
    simp only [ACParams.ts] at this
    linarith only [hΔ, hP2, this]
  obtain ⟨jt, x, fgDue, hgt⟩ := hrun.tick_of_awake y hy u
    (by linarith only [hΔ, hm0]) hpub
    (htk ▸ hrun.awake_of_call y hy k ⟨_, Compose.projAC_callAt.mp hc.1⟩)
  obtain ⟨hct', htt⟩ := tick_first_cut hgt
  let ellt : ACLabel (goldilocksNode sp) :=
    ⟨.tick, Node.frame (tr.state y jt),
      ((goldilocksNode sp).step y (tr.state y jt).ac (Node.frame (tr.state y jt)) u .tick).2⟩
  change tr.CallAt y jt (.ac ellt) at hct'
  have hcall : ellt.call = .tick := rfl
  have hjti : jt < i := by
    rcases Compose.blockCall_cases hrun.toLocalRun hy hA with hgW | ⟨j, x', f', -, -, hP, -⟩
    · rw [ht] at hgW
      rcases lt_trichotomy jt i with h | rfl | h
      · exact h
      · have := hct'.2.symm.trans hA.2
        simp at this
      · have := hrun.phase_order y hy y hy i jt u (.block W) (.tick x fgDue) hgW hgt h (.inl rfl)
        simp [Node.Event.phase] at this
    · exact absurd (ht ▸ hP) hnprop
  have hnrk : ell.call ≠ .restart := fun hcl => by
    have := hc.2
    rw [restart_emits hr hy hc.1 hcl] at this
    cases this
  have hjk : AC.joined sp (tr.projAC.state y k) u := by
    obtain ⟨-, -, hyj, -⟩ := AC.castAt_specU hr.toU hy hc
    have he := hr.exec k ell hc.1.2 (hc.1.1 ▸ hy)
    rw [hc.1.1] at he
    have h1 : (tr.projAC.post k).restartTime = (tr.projAC.state y k).restartTime := by
      have hpost : tr.projAC.post k = ((AC.goldilocksAC sp (List (FG.Att sp.n))).step y
          (tr.projAC.state y k) ell.frame (tr.projAC.time k) ell.call).1 := by rw [he]
      rw [hpost]
      exact AC.step_restartTime y _ _ _ _ hnrk
    unfold AC.joined at hyj ⊢
    rw [← h1, AC.restartTime_of_castAtU hr.toU hy hc, ← htk]
    exact hyj
  have hnr_k : ¬ tr.RestartAt y k := fun ⟨ell', hc', hr'⟩ => by
    have h := (Compose.projAC_callAt.mp hc.1).2.symm.trans hc'.2
    simp only [Option.some.injEq, Cut.ac.injEq] at h
    subst h
    exact hnrk hr'
  have hJ : tr.JoinedAt y u :=
      ((Compose.joined_projection_from hrun hy u).2.1 k
        ⟨_, Compose.projAC_callAt.mp hc.1⟩ hnr_k htk).mpr (by
    rw [← Compose.projAC_state hrun.toLocalRun hy k]
    exact hjk)
  have hpt : tr.projAC.CallAt y jt ellt := Compose.projAC_callAt.mpr hct'
  have hnrt : ¬ tr.RestartAt y jt := fun ⟨ell', hc', hr'⟩ => by
    have h := hct'.2.symm.trans hc'.2
    simp only [Option.some.injEq, Cut.ac.injEq] at h
    subst h
    rw [hcall] at hr'
    cases hr'
  have hjt : AC.joined sp (tr.projAC.state y jt) u := by
    rw [Compose.projAC_state hrun.toLocalRun hy]
    exact ((Compose.joined_projection_from hrun hy u).2.1 jt ⟨_, hct'⟩ hnrt htt).mp hJ
  have hve : AC.VoteAt tr.projAC y k e := ⟨ell, hc.1, hc.2⟩
  have hmay : (tr.projAC.state y jt).mayVote e.msg.slot = true := by
    rw [(AC.trace_mayVote hr hy jt).trans (AC.trace_mayVote hr hy k).symm]
    exact AC.mayVote_of_castAt hr hy hc
  by_cases hvs : (tr.projAC.state y jt).votedSlot = (e.msg.slot : Int)
  · rcases AC.cast_of_votedSlotU hr.toU hrun.vstart hy jt e.msg.slot hvs with
      ⟨j', hj', e', hve', hes⟩ | hmf
    · have := (AC.one_vote_per_slotU sp _ H _ tr.projAC hr.toU y hy j' k e' e hve' hve hes).1
      omega
    · exact absurd hmay (by rw [hmf]; decide)
  · have hexec := hr.exec jt ellt hpt.2 (hpt.1 ▸ hy)
    rw [hpt.1, hcall] at hexec
    have hne := Compose.acOnTick_votes y _ ellt.frame hjt
      (by rw [hslot]; exact hvs) (by rw [hslot]; exact hmay) (by rw [hslot])
    rw [show tr.projAC.time jt = u from htt] at hexec
    rw [hexec] at hne
    obtain ⟨e', he'⟩ := List.exists_mem_of_ne_nil _ hne
    have hsl' := (AC.castAt_specU hr.toU hy ⟨hpt, he'⟩).2.1
    have := (AC.one_vote_per_slotU sp _ H _ tr.projAC hr.toU y hy jt k e' e ⟨_, hpt, he'⟩ hve
      (by rw [hsl']; change sp.slot (tr.time jt) = _; rw [htt, hslot])).1
    omega

end Consensus.Goldilocks.Healing

end

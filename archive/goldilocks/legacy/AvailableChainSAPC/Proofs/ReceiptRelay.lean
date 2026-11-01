module
public import AvailableChainSAPC.Proofs.ProposalDelivery
public import AvailableChainSAPC.Proofs.CertificateValidity
public import AvailableChainSAPC.Statements.QuorumRecovery

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A later delivery has reached every earlier source clock value. -/
theorem causal_delivery_clock {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hs : ScheduleWellFormed E rho) {i j : Nat} {source reader : V}
    {a b : Wire p.n} {t t' : Time}
    (hi : rho.events[i]? = some (.deliver source a t))
    (hj : rho.events[j]? = some (.deliver reader b t')) (htt : t ≤ t') :
    (Run.stateBefore (sapc p) rho i source).base.now ≤
      (Run.stateBefore (sapc p) rho j reader).base.now := by
  have hnow := stateBefore_now_le_event p E rho hs hi source
  have ht : (Run.stateBefore (sapc p) rho i source).base.now ≤ t' := hnow.trans htt
  have hpub : PublicTime E (Run.stateBefore (sapc p) rho i source).base.now := by
    rcases stateBefore_now_source (engineClock p) rho i source with hz | ⟨k, _, hk⟩
    · change (Run.stateBefore (sapc p) rho i source).base.now = 0 at hz
      rw [hz]; exact ⟨0, by simp⟩
    · exact hs.tick_public _ _ (List.mem_of_getElem? hk)
  have hz : 0 ≤ (Run.stateBefore (sapc p) rho i source).base.now := by
    obtain ⟨k, hk⟩ := hpub
    rw [hk]
    exact mul_nonneg (Int.natCast_nonneg k) E.Δ_pos.le
  exact delivery_now_ge_public p E rho hs hj hpub hz ht

/-- A new complete signature has a seat and passes the future-label guard. -/
theorem receiveHead_new_label (p : Params) {n : Nat} (st : State n)
    (a h : HeadWire n) (hm : h ∈ (receiveHead p st a).receivedHeads) :
    h ∈ st.receivedHeads ∨ ∃ r i, h.auth = .seat r i ∧
      r ≤ (st.base.now / (4 * p.Δ)).toNat := by
  unfold receiveHead at hm
  split at hm
  · rename_i r i ha
    split at hm
    · exact Or.inl hm
    · rename_i ht
      split at hm
      · exact Or.inl hm
      · rcases List.mem_append.mp hm with hm | hm
        · exact Or.inl hm
        · have he : h = a := List.mem_singleton.mp hm
          subst h
          exact Or.inr ⟨r, i, ha, le_of_not_gt ht⟩
  · exact Or.inl hm

theorem receiveHeads_new_label (p : Params) {n : Nat} (st : State n)
    (xs : List (HeadWire n)) (h : HeadWire n)
    (hm : h ∈ (xs.foldl (receiveHead p) st).receivedHeads) :
    h ∈ st.receivedHeads ∨ ∃ r i, h.auth = .seat r i ∧
      r ≤ (st.base.now / (4 * p.Δ)).toNat := by
  induction xs generalizing st with
  | nil => exact Or.inl hm
  | cons a xs ih =>
    rcases ih _ hm with hm | hnew
    · exact receiveHead_new_label p st a h hm
    · exact Or.inr (by simpa only [receiveHead_now] using hnew)

theorem process_new_head_label (p : Params) {n : Nat} (st : State n)
    (a : Wire n) (h : HeadWire n) (hn : h ∉ st.receivedHeads)
    (hm : h ∈ (process p st a).receivedHeads) :
    ∃ r i, h.auth = .seat r i ∧ r ≤ (st.base.now / (4 * p.Δ)).toNat := by
  unfold process at hm
  split at hm
  · rw [admitHead, collectPCs_archive] at hm
    exact (receiveHead_new_label p st _ h hm).resolve_left hn
  · unfold admitProposal at hm
    split at hm
    · rw [collectPCs_archive] at hm
      have hnew := receiveHeads_new_label p _ _ h hm
      simpa only [proposalBase_now] using hnew.resolve_left hn
    · exact (hn hm).elim
  · split at hm
    · rw [collectPCs_archive] at hm
      exact (receiveHeads_new_label p st _ h hm).resolve_left hn
    · exact (hn hm).elim
  · exact (hn hm).elim

/-- Non-HEAD objects can only be handled directly. -/
theorem handles_nonhead_direct (p : Params) {n : Nat} (st : State n)
    (a o : Wire n) (hn : ∀ h, o.payload ≠ .head h) (hh : handles p st a o) : a = o := by
  rcases hh with he | hh
  · exact he
  · have hnot (xs : List (HeadWire n)) : o ∉ xs.map fromHead := by
      rintro hm
      obtain ⟨h, _, he⟩ := List.mem_map.mp hm
      exact hn h.payload (congrArg Signed.payload he.symm)
    cases ha : a.auth <;> cases hp : a.payload <;> simp only [ha, hp] at hh <;>
      first | contradiction | exact (hnot _ hh.2).elim

/-- A proposal which entered the archive passed the shared future-slot guard. -/
theorem process_proposal_slot (p : Params) {n : Nat} (st : State n)
    (o : Wire n) (b : Block) (raw support : List (HeadWire n)) (c : Option (PC n))
    (hp : o.payload = .proposal b raw support c) (hn : b ∉ st.base.blocks)
    (hm : b ∈ (process p st o).base.blocks) :
    b.slot ≤ (st.base.now / (4 * p.Δ)).toNat := by
  cases ha : o.auth <;> simp only [process, ha, hp] at hm
  all_goals first
    | exact (hn hm).elim
    | unfold admitProposal at hm
      split at hm
      · rw [collectPCs_base, receiveHeads_blocks] at hm
        unfold proposalBase GridCO.admitProposal at hm
        dsimp only at hm
        split_ifs at hm
        · exact (hn hm).elim
        · rename_i hguard
          simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
            not_or] at hguard
          exact le_of_not_gt hguard.1.1.1.1
      · exact (hn hm).elim

/-- Processing an accepted complete object at a later checked call stores it.
Complete HEADs have neither the base cap nor its lower admission window. -/
theorem accepted_handled_processed {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (i j : Nat) (source reader : V)
    (o : Wire p.n) (t t' : Time) (ha : Run.acceptsAt (sapc p) rho i source o t)
    (hh : Run.handlesAt (sapc p) rho j reader o t') (htt : t ≤ t') :
    processed p (Run.stateBefore (sapc p) rho (j + 1) reader) o = true := by
  set_option backward.isDefEq.respectTransparency false in
  obtain ⟨a, hi, hacall⟩ := ha.1
  obtain ⟨b, hj, hbcall⟩ := hh
  have hclock := causal_delivery_clock p E rho hx.toScheduleWellFormed hi hj htt
  have hcurrent' : ((Run.stateBefore (sapc p) rho i source).base.now / (4 * p.Δ)).toNat ≤
      ((Run.stateBefore (sapc p) rho j reader).base.now / (4 * p.Δ)).toNat := by
    apply Int.toNat_le_toNat
    exact Int.ediv_le_ediv (by linarith [p.deltaPos]) hclock
  have hbefore := ha.2.1
  have hafter := ha.2.2
  rw [stateBefore_succ_event hi] at hafter
  simp only [World.step, Function.update_self, sapc] at hafter
  change processed p (process p (Run.stateBefore (sapc p) rho i source) a) o = true at hafter
  change processed p (Run.stateBefore (sapc p) rho i source) o = false at hbefore
  rw [stateBefore_succ_event hj]
  simp only [World.step, Function.update_self, sapc]
  change processed p (process p (Run.stateBefore (sapc p) rho j reader) b) o = true
  cases hp : o.payload with
  | head data =>
    have hn : (⟨o.auth, data⟩ : HeadWire p.n) ∉
        (Run.stateBefore (sapc p) rho i source).receivedHeads := by
      simpa [sapc, processed, hp] using! hbefore
    have hm : (⟨o.auth, data⟩ : HeadWire p.n) ∈
        (process p (Run.stateBefore (sapc p) rho i source) a).receivedHeads := by
      simpa [processed, hp] using hafter
    obtain ⟨r, k, hk, hslot⟩ := process_new_head_label p _ a _ hn hm
    change o.auth = .seat r k at hk
    have he : o = fromHead ⟨.seat r k, data⟩ := by cases o; simp_all [fromHead]
    rw [he] at hbcall ⊢
    simpa [processed, fromHead] using! handled_head_archived p _ b r k data
      (hslot.trans hcurrent') hbcall
  | proposal target raw support c =>
    have he := handles_nonhead_direct p _ b o (by intro h; simp [hp]) hbcall
    subst b
    have he := handles_nonhead_direct p _ a o (by intro h; simp [hp]) hacall
    subst a
    have hn : target ∉ (Run.stateBefore (sapc p) rho i source).base.blocks := by
      simpa [sapc, processed, hp, GridCO.blockKnown] using! hbefore
    have hm : target ∈ (process p (Run.stateBefore (sapc p) rho i source) o).base.blocks := by
      simpa [processed, hp, GridCO.blockKnown] using hafter
    have hslot := (process_proposal_slot p _ o target raw support c hp hn hm).trans hcurrent'
    have hw := hx.wire j reader o t' hj
    have hd := hx.deps j reader o t' hj
    have hf := hx.fresh j reader o t' hj
    cases h_auth : o.auth <;> simp only [sapc, wellFormed, h_auth, hp] at hw
    all_goals first
      | contradiction
      | simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
        have hslotEq := hw.1.1.1.1.1
        have horder := hw.1.1.1.2
        have hdep : target.parent ∈ (Run.stateBefore (sapc p) rho j reader).base.blocks := by
          simpa [sapc, depsPresent, hp, GridCO.blockKnown] using hd
        have hfresh : target ∉ (Run.stateBefore (sapc p) rho j reader).base.blocks := by
          simpa [sapc, processed, hp, GridCO.blockKnown] using hf
        have he : o = ⟨.proposer target.slot, .proposal target raw support c⟩ := by
          cases o; simp_all
        subst o
        have hstored := (process_proposal_stored p _ target.slot target raw support c rfl
          hslot hdep (by simpa [hslotEq] using horder) hfresh).1
        simpa [processed, GridCO.blockKnown] using hstored
  | pc cert =>
    have he := handles_nonhead_direct p _ b o (by intro h; simp [hp]) hbcall
    subst b
    have he := handles_nonhead_direct p _ a o (by intro h; simp [hp]) hacall
    subst a
    have hw := hx.wire j reader o t' hj
    have hd := hx.deps j reader o t' hj
    have h_auth : o.auth = .none := by
      cases hauth : o.auth <;> simp_all [sapc, wellFormed]
    have hready : pcEnvelopeReady p (Run.stateBefore (sapc p) rho i source) cert = true := by
      by_contra hn
      simp only [process, h_auth, hp, ite_eq_right hn] at hafter
      exact Bool.noConfusion (hbefore.symm.trans hafter)
    have hage := (Bool.and_eq_true_iff.mp hready).2
    have hready' : pcEnvelopeReady p (Run.stateBefore (sapc p) rho j reader) cert = true := by
      simp only [pcEnvelopeReady, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨by simpa [sapc, wellFormed, h_auth, hp] using hw,
        by simpa [sapc, depsPresent, hp] using hd⟩, (of_decide_eq_true hage).trans hcurrent'⟩
    have hv := pcEnvelopeReady_valid p (Run.stateBefore (sapc p) rho j reader) cert hready'
    simp only [processed, hp, process, h_auth, hready', ↓reduceIte]
    rw [pcValid_eq_of_data p _ (cert.witnesses.foldl (receiveHead p)
      (Run.stateBefore (sapc p) rho j reader))
      (by simp only [collectPCs_base, installPC])
      (by simp only [collectPCs_archive, installPC]) cert]
    exact hv

/-- A receipt of a complete object has an acceptance after the source time.
For a duplicate carried HEAD, take its earlier first archive insertion. -/
theorem accepted_receipt_accepts_before {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (i j : Nat) (source reader : V)
    (o : Wire p.n) (t t' D : Time) (ha : Run.acceptsAt (sapc p) rho i source o t)
    (hm : processed p (Run.stateBefore (sapc p) rho (i + 1) reader) o = false)
    (hh : Run.handlesAt (sapc p) rho j reader o t') (htt : t ≤ t') (htD : t' < D) :
    ∃ u, t ≤ u ∧ u < D ∧ ∃ k, Run.acceptsAt (sapc p) rho k reader o u := by
  have hprocessed := accepted_handled_processed p E rho hx i j source reader o t t' ha hh htt
  obtain ⟨a, hi, _⟩ := ha.1
  obtain ⟨b, hj, hb⟩ := hh
  cases hp : o.payload with
  | head data =>
    have hmem : (⟨o.auth, data⟩ : HeadWire p.n) ∈
        (Run.stateBefore (sapc p) rho (j + 1) reader).receivedHeads := by
      simpa [processed, hp] using hprocessed
    obtain ⟨k, hkj, u, hk⟩ := stored_head_accepted p rho (j + 1) reader _ hmem
    have he : fromHead ⟨o.auth, data⟩ = o := by cases o; simp_all [fromHead]
    rw [he] at hk
    obtain ⟨c, hc, _⟩ := hk.1
    have hlow : t ≤ u := by
      by_contra hlt
      have hki := eventIndex_lt_of_time_lt hx.toScheduleWellFormed hc hi (lt_of_not_ge hlt)
      have hmem : (⟨o.auth, data⟩ : HeadWire p.n) ∈
          (Run.stateBefore (sapc p) rho (k + 1) reader).receivedHeads := by
        simpa [sapc, processed, hp] using hk.2.2
      have hmem := stateBefore_archive_mono p rho (show k + 1 ≤ i + 1 by omega) reader hmem
      have hfalse : (⟨o.auth, data⟩ : HeadWire p.n) ∉
          (Run.stateBefore (sapc p) rho (i + 1) reader).receivedHeads := by
        simpa [processed, hp] using hm
      exact hfalse hmem
    have hhigh : u ≤ t' := by
      by_contra hlt
      have hjk := eventIndex_lt_of_time_lt hx.toScheduleWellFormed hj hc (lt_of_not_ge hlt)
      omega
    exact ⟨u, hlow, hhigh.trans_lt htD, k, hk⟩
  | proposal target raw support cert =>
    have he := handles_nonhead_direct p _ b o (by intro h; simp [hp]) hb
    subst b
    exact ⟨t', htt, htD, j, ⟨o, hj, Or.inl rfl⟩,
      hx.fresh j reader o t' hj, hprocessed⟩
  | pc cert =>
    have he := handles_nonhead_direct p _ b o (by intro h; simp [hp]) hb
    subst b
    exact ⟨t', htt, htD, j, ⟨o, hj, Or.inl rfl⟩,
      hx.fresh j reader o t' hj, hprocessed⟩

/-- Exact complete-object relay is derived from receipt relay for SA-PC. -/
theorem receipt_acceptedRelay {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hnet : PartialSynchrony (sapc p) E rho) :
    AcceptedObjectRelay (sapc p) E rho := by
  intro source hs i o t ha reader hr hm horizon
  obtain ⟨t', htt, htD, j, hh⟩ := hnet.relay source hs i o t ha reader hr hm horizon rfl
  exact accepted_receipt_accepts_before p E rho hx i j source reader o t t' _ ha hm hh htt htD

/-- The same complete-archive bridge holds on a healthy prefix. -/
theorem receipt_healthyAcceptedRelay {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (cut : Time)
    (hnet : HealthyPrefixDelivery (sapc p) E rho cut) :
    HealthyAcceptedObjectRelay (sapc p) E rho cut := by
  intro source hs i o t ha reader hr hm deadline
  obtain ⟨t', htt, htD, j, hh⟩ := hnet.relay source hs i o t ha reader hr hm deadline rfl
  exact accepted_receipt_accepts_before p E rho hx i j source reader o t t' _ ha hm hh htt htD

theorem QuorumRecoveryRegime.acceptedRelay {V : Type} [DecidableEq V] [Fintype V]
    {p : Params} {G : Time} {E : Env V} {rho : Run V (sapc p)}
    (h : QuorumRecoveryRegime p G E rho) : AcceptedObjectRelay (sapc p) E rho :=
  receipt_acceptedRelay p E rho h.execution h.partialSynchrony

end AvailableChain.SAPC

namespace AvailableChain.Statements.Generic
open AvailableChain.Generic AvailableChain.SAPC

/-- SA-PC derives its exact archive relay; it is not a regime field. -/
theorem SleepyRegime.acceptedRelay {V : Type} [DecidableEq V] [Fintype V]
    {p : Params} {E : Env V} {I : Interface (sapc p)} {rho : Run V (sapc p)} {t : Time}
    (h : SleepyRegime (sapc p) E I rho t) : AcceptedObjectRelay (sapc p) E rho :=
  receipt_acceptedRelay p E rho h.execution h.partialSynchrony

theorem RecoveryRegime.acceptedRelay {V : Type} [DecidableEq V] [Fintype V]
    {p : Params} {E : Env V} {I : Interface (sapc p)} {C : Constants}
    {rho : Run V (sapc p)} (h : RecoveryRegime (sapc p) E I C rho) :
    AcceptedObjectRelay (sapc p) E rho :=
  receipt_acceptedRelay p E rho h.execution h.partialSynchrony

theorem OutageRegime.acceptedRelay {V : Type} [DecidableEq V] [Fintype V]
    {p : Params} {E : Env V} {I : Interface (sapc p)} {C : Constants}
    {rho : Run V (sapc p)} {T b₀ b₁ : Time} (h : OutageRegime (sapc p) E I C rho T b₀ b₁) :
    HealthyAcceptedObjectRelay (sapc p) E rho b₀ :=
  receipt_healthyAcceptedRelay p E rho h.execution b₀ h.healthy

theorem StrongArmedRegime.acceptedRelay {V : Type} [DecidableEq V] [Fintype V]
    {p : Params} {E : Env V} {I : StrongInterface (sapc p)} {f : Nat}
    {rho : Run V (sapc p)} {T b₀ : Time} (h : StrongArmedRegime (sapc p) E I f rho T b₀) :
    HealthyAcceptedObjectRelay (sapc p) E rho b₀ :=
  receipt_healthyAcceptedRelay p E rho h.execution b₀ h.healthy

end AvailableChain.Statements.Generic
end

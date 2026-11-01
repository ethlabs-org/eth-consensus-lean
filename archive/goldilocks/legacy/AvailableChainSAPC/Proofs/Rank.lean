module
public import AvailableChainSAPC.Proofs.CertificateValidity
public import AvailableChainSAPC.Proofs.Acceptance

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- The stored encoding is retained, or its target slot strictly increases.
This is a rank statement; it does not assert prefix safety. -/
def PCRankLE {n : Nat} (before after : Option (PC n)) : Prop :=
  ∀ c, before = some c → ∃ d, after = some d ∧ (d = c ∨ c.slot < d.slot)

theorem PCRankLE.refl {n : Nat} (c : Option (PC n)) : PCRankLE c c := by
  intro d hd
  exact ⟨d, hd, Or.inl rfl⟩

theorem PCRankLE.trans {n : Nat} {a b c : Option (PC n)}
    (hab : PCRankLE a b) (hbc : PCRankLE b c) : PCRankLE a c := by
  intro d hd
  obtain ⟨e, he, hde⟩ := hab d hd
  obtain ⟨f, hf, hef⟩ := hbc e he
  refine ⟨f, hf, ?_⟩
  rcases hde with rfl | hde
  · exact hef
  · rcases hef with rfl | hef
    · exact Or.inr hde
    · exact Or.inr (hde.trans hef)

theorem preferPC_rank {n : Nat} (old : Option (PC n)) (candidate : PC n) :
    PCRankLE old (preferPC old candidate) := by
  intro c hc
  rw [hc, preferPC]
  split
  · exact ⟨candidate, rfl, Or.inr (by assumption)⟩
  · exact ⟨c, rfl, Or.inl rfl⟩

theorem collectPCs_rank (p : Params) {n : Nat} (st : State n) :
    PCRankLE st.bestPC (collectPCs p st).bestPC := by
  have hf (pairs : List (Slot × Block)) (st : State n) :
      PCRankLE st.bestPC (pairs.foldl (fun acc pair =>
        match assemblePC p acc pair.1 pair.2 with
        | none => acc
        | some c => installPC acc c) st).bestPC := by
    induction pairs generalizing st with
    | nil => exact .refl _
    | cons pair pairs ih =>
        apply PCRankLE.trans (b := (match assemblePC p st pair.1 pair.2 with
          | none => st | some c => installPC st c).bestPC) ?_ (ih _)
        cases he : assemblePC p st pair.1 pair.2 with
        | none => exact .refl _
        | some c => exact preferPC_rank st.bestPC c
  exact hf _ st

theorem process_rank (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    PCRankLE st.bestPC (process p st o).bestPC := by
  unfold process
  split
  · rename_i r i data ha hp
    unfold admitHead
    have h := collectPCs_rank p (receiveHead p st ⟨o.auth, data⟩)
    simpa only [receiveHead_bestPC] using h
  · unfold admitProposal
    split
    · rename_i s b raw support c ha hp henter
      have h := collectPCs_rank p ((raw ++ pcMembers c).foldl (receiveHead p)
        { st with base := proposalBase p st o b raw support, proposals := st.proposals ++ [o] })
      rw [receiveHeads_bestPC] at h
      exact h
    · exact .refl _
  · split
    · rename_i c ha hp hready
      apply PCRankLE.trans (b := (installPC _ c).bestPC) ?_ (collectPCs_rank p _)
      have h := preferPC_rank st.bestPC c
      simpa only [installPC, receiveHeads_bestPC] using h
    · exact .refl _
  · exact .refl _

theorem stateBefore_rank {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) {i j : Nat} (hij : i ≤ j) (v : V) :
    PCRankLE (Run.stateBefore (sapc p) rho i v).bestPC
      (Run.stateBefore (sapc p) rho j v).bestPC := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]; exact .refl _
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · exact .refl _
      · apply (ih (by omega)).trans
        cases hj : rho.events[j]? with
        | none =>
            have he : Run.stateBefore (sapc p) rho (j + 1) =
                Run.stateBefore (sapc p) rho j := by
              simp [Run.stateBefore, List.take_add_one, hj]
            rw [he]; exact .refl _
        | some e =>
            rw [stateBefore_succ_event hj]
            cases e with
            | tick u t =>
                by_cases hv : v = u
                · subst u; simpa [World.step, sapc, clock_bestPC] using
                    PCRankLE.refl (Run.stateBefore (sapc p) rho j v).bestPC
                · simpa [World.step, hv] using
                    PCRankLE.refl (Run.stateBefore (sapc p) rho j v).bestPC
            | deliver u o t =>
                by_cases hv : v = u
                · subst u
                  simpa [World.step, sapc] using process_rank p
                    (Run.stateBefore (sapc p) rho j v) o
                · simpa [World.step, hv] using
                    PCRankLE.refl (Run.stateBefore (sapc p) rho j v).bestPC

/-- Rank never decreases at public reads, with no fault or delivery bound. -/
theorem read_rank {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (v : V)
    (t t' : Time) (ht : t ≤ t') :
    PCRankLE (Run.readAt (sapc p) rho t v).bestPC
      (Run.readAt (sapc p) rho t' v).bestPC := by
  rw [readAt_eq_stateBefore hs, readAt_eq_stateBefore hs]
  exact stateBefore_rank p rho (read_length_mono t t' ht) v

/-- Every public non-genesis strong read retains some certificate at
all later reads. Prefix preservation is the separate strong claim. -/
theorem strong_certificate_retained {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (v : V)
    (t t' : Time) (ht : t ≤ t') (c : PC p.n)
    (hc : (Run.readAt (sapc p) rho t v).bestPC = some c) :
    ∃ d, (Run.readAt (sapc p) rho t' v).bestPC = some d ∧ c.slot ≤ d.slot := by
  obtain ⟨d, hd, hr⟩ := read_rank p E rho hs v t t' ht c hc
  refine ⟨d, hd, ?_⟩
  rcases hr with rfl | hr
  · exact le_refl _
  · exact le_of_lt hr

end AvailableChain.SAPC
end

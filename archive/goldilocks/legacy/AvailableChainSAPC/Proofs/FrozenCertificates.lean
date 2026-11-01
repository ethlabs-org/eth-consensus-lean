module
public import AvailableChainSAPC.Proofs.CertificateValidity

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic

theorem receiveHead_frozenPC (p : Params) {n : Nat} (st : State n) (o : HeadWire n) :
    (receiveHead p st o).frozenPC = st.frozenPC := by
  unfold receiveHead
  split
  · dsimp only
    split <;> (try split_ifs) <;> rfl
  · rfl

theorem process_frozenPC (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (process p st o).frozenPC = st.frozenPC := by
  have hcollect (st : State n) : (collectPCs p st).frozenPC = st.frozenPC :=
    collectPCs_field p State.frozenPC (by intros; rfl) st
  have hfold (xs : List (HeadWire n)) (st : State n) :
      (xs.foldl (receiveHead p) st).frozenPC = st.frozenPC :=
    fold_field State.frozenPC _ (receiveHead_frozenPC p) xs st
  unfold process
  split
  · simp only [admitHead, hcollect, receiveHead_frozenPC]
  · unfold admitProposal
    split <;> simp only [hcollect, hfold]
  · split <;> simp only [hcollect, installPC, hfold]
  · rfl

/-- A clock retains the frozen list or appends the live PC at one new
label. Later receipts cannot replace this value. -/
theorem clock_frozenPC_cases (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).frozenPC = st.frozenPC ∨
      ∃ r, (clock p st t).frozenPC = st.frozenPC ++ [(r, st.bestPC)] := by
  unfold clock
  dsimp only
  split_ifs <;> simp only [gate, saveTimely]
  all_goals (try split_ifs) <;> (try simp_all only)
  all_goals first
    | exact Or.inl trivial
    | exact Or.inr ⟨((t - 3 * p.Δ) / (4 * p.Δ)).toNat, rfl⟩

def FrozenPCValid (p : Params) {n : Nat} (st : State n) : Prop :=
  ∀ r c, (r, some c) ∈ st.frozenPC → pcValid p st c = true

theorem process_frozenPC_valid (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : FrozenPCValid p st) : FrozenPCValid p (process p st o) := by
  intro r c hc
  rw [process_frozenPC] at hc
  exact pcValid_mono p st _ (process_blocks_mono p st o)
    (process_archive_mono p st o) c (h r c hc)

theorem clock_frozenPC_valid (p : Params) {n : Nat} (st : State n) (t : Time)
    (h : FrozenPCValid p st) (hlive : StoredPCValid p st) :
    FrozenPCValid p (clock p st t) := by
  intro r c hc
  have hvalid : pcValid p st c = true := by
    rcases clock_frozenPC_cases p st t with he | ⟨label, he⟩
    · exact h r c (he ▸ hc)
    · rw [he] at hc
      rcases List.mem_append.mp hc with hold | hnew
      · exact h r c hold
      · have hrow := List.mem_singleton.mp hnew
        exact hlive c (congrArg Prod.snd hrow).symm
  apply pcValid_mono p st _ ?_ ?_ c hvalid
  · rw [clock_blocks]
  · rw [clock_archive]

/-- Both stored PC sources are valid at every engine fold. -/
theorem certificates_valid_at_fold {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (sapc p).Object)) (v : V) :
    let st := (events.foldl World.step World.init) v
    StoredPCValid p st ∧ FrozenPCValid p st := by
  apply fold_invariant p (fun st => StoredPCValid p st ∧ FrozenPCValid p st)
  · simp [StoredPCValid, FrozenPCValid, initial]
  · intro st t h
    exact ⟨clock_valid p st t h.1, clock_frozenPC_valid p st t h.2 h.1⟩
  · intro st o h
    exact ⟨process_valid p st o h.1, process_frozenPC_valid p st o h.2⟩

theorem frozenPCAt_valid (p : Params) {n : Nat} (st : State n)
    (h : FrozenPCValid p st) (r : Slot) (c : PC n)
    (hc : frozenPCAt st r = some c) : pcValid p st c = true := by
  cases he : st.frozenPC.find? (fun row => row.1 == r) with
  | none => simp [frozenPCAt, he] at hc
  | some row =>
      have hm := List.mem_of_find?_eq_some he
      simp only [frozenPCAt, he, Option.map_some, Option.getD_some] at hc
      apply h row.1 c
      simpa only [← hc] using hm

theorem preferPC_cases {n : Nat} (old : Option (PC n)) (candidate chosen : PC n)
    (h : preferPC old candidate = some chosen) : old = some chosen ∨ candidate = chosen := by
  cases he : old with
  | none => exact Or.inr (by simpa [preferPC, he] using h)
  | some previous =>
      simp only [preferPC, he] at h
      split at h
      · exact Or.inr (Option.some.inj h)
      · exact Or.inl h

/-- HEAD selection uses only valid frozen or carried certificates. It
does not require the selected PC to equal the later live PC. -/
theorem selectedPC_valid (p : Params) {n : Nat} (st : State n)
    (h : FrozenPCValid p st) (r : Slot) (c : PC n)
    (hc : selectedPC p st r = some c) : pcValid p st c = true := by
  have hf (xs : List (Wire n)) (best : Option (PC n))
      (hbest : ∀ d, best = some d → pcValid p st d = true) :
      ∀ d, xs.foldl (fun best o => match o.payload with
        | .proposal b _ _ (some cert) =>
            if b.slot == r && pcValid p st cert then preferPC best cert else best
        | _ => best) best = some d → pcValid p st d = true := by
    induction xs generalizing best with
    | nil => exact hbest
    | cons o xs ih =>
        apply ih
        intro d hd
        dsimp only at hd
        split at hd
        · split at hd
          · rename_i b raw support cert hp hgood
            rcases preferPC_cases best cert d hd with hold | rfl
            · exact hbest d hold
            · exact (Bool.and_eq_true_iff.mp hgood).2
          · exact hbest d hd
        · exact hbest d hd
  exact hf st.proposals (frozenPCAt st (r - 1)) (frozenPCAt_valid p st h (r - 1)) c hc

theorem selectedPC_valid_before {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (v : V) (index : Nat) (r : Slot) (c : PC p.n)
    (h : selectedPC p (Run.stateBefore (sapc p) rho index v) r = some c) :
    pcValid p (Run.stateBefore (sapc p) rho index v) c = true :=
  selectedPC_valid p _ (certificates_valid_at_fold p _ v).2 r c h

theorem selectedPC_valid_beforeTime {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (v : V) (t : Time) (r : Slot) (c : PC p.n)
    (h : selectedPC p (Run.stateBeforeTime (sapc p) rho t v) r = some c) :
    pcValid p (Run.stateBeforeTime (sapc p) rho t v) c = true :=
  selectedPC_valid p _ (certificates_valid_at_fold p _ v).2 r c h

end AvailableChain.SAPC
end

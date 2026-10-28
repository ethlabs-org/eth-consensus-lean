module
public import ConsensusModelProofs.Canonical
public import ConsensusModelProofs.Protection

@[expose] public section

/-! # Causal runs convict nobody

In a valid run whose network is causal (every delivery is an earlier
release, as in the canonical run), every signed object anything honest saw
has an honest signer: honest nodes sign only with their own key, and carry
only what they saw. With `honestNeverSlashed`, the honest evidence convicts
nobody, faulty validators included. Realizability witnesses use this to show
that no escape or accountability conclusion is met by slashing. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

namespace Run

variable (rho : Run F E)

/-- Every signed object inside `o` has an honest signer. -/
def HonestSigned (o : (protoOf F E).Object) : Prop :=
  ∀ d, Obj.Contains o d → ∀ u, rho.signerOf d.auth = some u → u ∈ rho.honest

omit [DecidableEq V] in
/-- A tick of an honest node keeps `seen` honestly signed and releases only
honestly signed objects. -/
theorem tick_honestSigned (nd : Node (protoOf F E)) {v : V} (hv : v ∈ rho.honest) (t : Time)
    (hs : ∀ o ∈ nd.seen, rho.HonestSigned o) :
    (∀ o ∈ (rho.tick nd v t).1.seen, rho.HonestSigned o) ∧
      (∀ o ∈ (rho.tick nd v t).2, rho.HonestSigned o) := by
  unfold tick
  split
  · refine releaseAll_preserves rho.hash _
      (fun d => ∀ u, rho.signerOf d.auth = some u → u ∈ rho.honest) _ _ hs ?_
    intro o ho u hu
    rcases rho.candidates_signerOf _ v t (releaseAll_subset _ _ _ _ o ho) with h | h <;>
      rw [h] at hu
    · cases hu
    · exact Option.some.inj hu ▸ hv
  · exact ⟨hs, by simp⟩

/-- In a valid causal run, everything every node has seen is honestly
signed. -/
theorem seen_honestSigned (hv : rho.ExecutionValid) (hc : rho.Causal) (i : Nat) :
    ∀ v, ∀ o ∈ (rho.stateBefore i v).seen, rho.HonestSigned o := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    cases i with
    | zero => intro v o ho; simp [stateBefore, initWorld] at ho
    | succ k =>
      have old := ih k (Nat.lt_succ_self k)
      cases he : rho.events[k]? with
      | none =>
        have hworld : rho.stateBefore (k + 1) = rho.stateBefore k := by
          simp [stateBefore, List.take_add_one, he]
        rw [hworld]
        exact old
      | some e =>
        rw [rho.stateBefore_succ he]
        have hnode : e.node ∈ rho.honest :=
          hv.honest_only e (List.mem_of_getElem? he)
        intro w o ho
        cases e with
        | tick v t =>
          by_cases hw : w = v
          · subst w
            exact (rho.tick_honestSigned _ (v := v) hnode t (old v)).1 o (by simpa [step] using ho)
          · exact old w o (by simpa [step, hw] using ho)
        | restart v t =>
          by_cases hw : w = v
          · subst w; exact old v o (by simpa [step] using ho)
          · exact old w o (by simpa [step, hw] using ho)
        | deliver v p t =>
          by_cases hw : w = v
          · subst w
            have hm : o ∈ (rho.stateBefore k v).seen ++ [p] := by simpa [step] using ho
            rcases List.mem_append.mp hm with hm | hm
            · exact old v o hm
            · rcases List.mem_singleton.mp hm with rfl
              obtain ⟨j, u, t', hj, hju, hjo⟩ := hc k v o t he
              have hu : u ∈ rho.honest := hv.honest_only _ (List.mem_of_getElem? hju)
              simp only [releasesAt, hju] at hjo
              exact (rho.tick_honestSigned _ hu t' (ih j (by omega) u)).2 o hjo
          · exact old w o (by simpa [step, hw] using ho)

/-- In a valid causal run nobody, faulty validators included, is slashable on
what the honest nodes saw. -/
theorem not_slashable_of_causal (hv : rho.ExecutionValid) (hc : rho.Causal) (x : V) :
    ¬ rho.Slashable rho.Observed x := by
  intro hs
  have hx : x ∈ rho.honest := by
    obtain ⟨o, ⟨v, -, hov⟩, -, -, hsx, -⟩ := hs
    obtain ⟨r, hr, hro⟩ := (mem_closure_iff _ _).mp (rho.viewIdx_closure hov)
    exact rho.seen_honestSigned hv hc _ v r hr o hro x hsx
  exact rho.honestNeverSlashed hv x hx hs

end Run

/-- If nobody is slashable on what the honest nodes saw, the honest evidence
of the system run convicts nobody. -/
theorem convicted_honestEvidence_eq_empty (rho : Run F E)
    (h : ∀ x, ¬ rho.Slashable rho.Observed x) :
    (sysOf O F V).convicted ⟨E, rho⟩ ((sysOf O F V).honestEvidence ⟨E, rho⟩) = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  have hconv : (sysOf O F V).convicts ⟨E, rho⟩ ((sysOf O F V).honestEvidence ⟨E, rho⟩) x := by
    unfold System.convicted Consensus.convicted at hx
    simpa using hx
  apply h x
  obtain ⟨o, ho, o', ho', h1, h2, h3⟩ := hconv
  have hobs : ∀ q : (protoOf F E).Object,
      (⟨E, q⟩ : (sysOf O F V).Obs) ∈ (sysOf O F V).honestEvidence ⟨E, rho⟩ →
        q ∈ rho.Observed := by
    rintro q ⟨w, hw, q', hq', heq⟩
    have hqq : q = q' := eq_of_heq (Sigma.mk.inj heq).2
    exact ⟨w, hw, hqq ▸ hq'⟩
  exact ⟨o, hobs o ho, o', hobs o' ho', h1, h2, h3⟩

end Consensus.Model

end

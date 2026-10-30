module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Node

public section

/-! # Goldilocks Compose/AnyAC: the cuts of the handlers (C0.2 restart, C0.4, C0.5 cut law)

Every handler is a fixed sequence of component calls: the restart keeps `Σ` and `Λ`; a tick's
cuts are the AC's tick, the proposal cuts and the FG update cuts (C0.4); only a tick signs; and
the cuts of every handler form a `CutChain` (each AC cut executes the AC at the frame
`fg_to_ac(Σ)` and changes only `𝒜`, each FG cut executes its FG call). -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)

/-- **C0.2, the restart half.** -/
theorem restart_keeps_fg : RestartKeepsFG (A := A) self :=
  fun _ _ => ⟨rfl, rfl, rfl⟩

/-! ### C0.4 -/

private theorem proposal_cuts (st : NodeState A) (t : Time) :
    ProposalCuts self t (tickStep dg self st t .proposal).2 := by
  simp only [tickStep]
  split_ifs with hp
  · refine Or.inr ⟨hp, ⟨.proposal, frame st, []⟩, rfl, ?_⟩
    split
    · exact Or.inl rfl
    · rename_i d p _
      refine Or.inr ?_
      simp only [proposeBlock, onBlock]
      split_ifs with hf
      · exact absurd hf (by simp [mkBlock])
      · refine ⟨mkBlock dg self (Node.acProposal st t).1.fg t d.head p, rfl, rfl, ?_⟩
        split
        · exact Or.inl rfl
        · exact Or.inr ⟨_, rfl, rfl⟩
  · exact Or.inl ⟨hp, rfl⟩

private theorem update_cuts (st : NodeState A) (t : Time) :
    UpdateCuts (tickStep dg self st t .fgUpdate).2 := by
  refine ⟨⟨.toFG, frame st, []⟩, rfl, ?_⟩
  simp only [tickStep]
  split
  · exact Or.inl rfl
  · rename_i C _
    simp only [attest]
    split
    · exact Or.inr (Or.inl ⟨C, rfl⟩)
    · exact Or.inr (Or.inr ⟨C, _, rfl⟩)

/-- **C0.4.** -/
theorem tick_order : TickOrder dg self := by
  intro st t
  simp only [onTick, runSteps, tickSteps, List.foldl_cons, List.foldl_nil, List.nil_append]
  exact ⟨⟨.tick, frame st, _⟩, _, _, rfl, rfl, proposal_cuts dg self _ t,
    update_cuts dg self _ t⟩

/-! ### C0.5 (c), signing -/

/-- **C0.5 (c), signing.** -/
theorem signed_only_in_ticks : SignedOnlyInTicks dg self := by
  intro st t e C a h
  cases e with
  | tick => rfl
  | block B =>
    simp only [exec, onBlock, acCall] at h
    split_ifs at h
    · simp at h
    · split at h <;> simp at h
  | message m => simp [exec, onMessage, acCall] at h
  | attestation a' => simp [exec, onAttestation] at h
  | restart => simp [exec, restart, acCall] at h

/-! ### C0.5, the cut law -/

private theorem chain_append {t : Time} {st st₁ st₂ : NodeState A} {cs cs' : List (Cut A)}
    (h : CutChain self t st cs st₁) (h' : CutChain self t st₁ cs' st₂) :
    CutChain self t st (cs ++ cs') st₂ := by
  induction h with
  | nil => exact h'
  | cons hs _ ih => exact .cons hs (ih h')

private theorem chain_single {t : Time} {st st' : NodeState A} {c : Cut A}
    (h : CutStep self t st c st') : CutChain self t st [c] st' :=
  .cons h (.nil _)

private theorem acCall_chain (st : NodeState A) (t : Time) (c : A.Call) :
    CutChain self t st [(acCall self st t c).2] (acCall self st t c).1 :=
  chain_single self ⟨rfl, rfl, rfl, rfl⟩

private theorem onBlock_chain (st : NodeState A) (t : Time) (B : A.Blk) :
    CutChain self t st (onBlock self st t B).2 (onBlock self st t B).1 := by
  unfold onBlock
  split_ifs with hf
  · exact .nil _
  · split
    · rename_i h
      exact chain_single self ⟨h, rfl⟩
    · rename_i fg' h
      exact .cons (st₁ := { st with fg := fg' }) ⟨Nat.le_of_not_lt hf, h, rfl, rfl⟩
        (acCall_chain self _ t _)

private theorem attest_chain (st : NodeState A) (t : Time) (C : A.Blk) :
    CutChain self t st (attest self st C).2 (attest self st C).1 := by
  unfold attest
  split
  · rename_i h
    exact chain_single self ⟨h, rfl⟩
  · rename_i a Λ' h
    exact .cons (st₁ := { st with record := Λ' }) ⟨h, rfl, rfl⟩
      (chain_single self ⟨rfl, rfl, rfl⟩)

private theorem tickStep_chain (st : NodeState A) (t : Time) (s : TickStep) :
    CutChain self t st (tickStep dg self st t s).2 (tickStep dg self st t s).1 := by
  cases s with
  | acTick => exact acCall_chain self st t .tick
  | proposal =>
    simp only [tickStep]
    split_ifs
    · split
      · exact chain_single self ⟨rfl, rfl, rfl, rfl⟩
      · rename_i d p _
        exact .cons (st₁ := (Node.acProposal st t).1) ⟨rfl, rfl, rfl, rfl⟩
          (onBlock_chain self (Node.acProposal st t).1 t
            (mkBlock dg self (Node.acProposal st t).1.fg t d.head p))
    · exact .nil _
  | fgUpdate =>
    simp only [tickStep]
    split
    · exact chain_single self ⟨rfl, rfl, rfl, rfl⟩
    · rename_i C _
      exact .cons (st₁ := (Node.acToFG st t).1) ⟨rfl, rfl, rfl, rfl⟩
        (attest_chain self (Node.acToFG st t).1 t C)

private theorem runSteps_chain (st : NodeState A) (t : Time) (steps : List TickStep) :
    CutChain self t st (runSteps dg self st t steps).2 (runSteps dg self st t steps).1 := by
  unfold runSteps
  suffices h : ∀ (acc : NodeState A × List (Cut A)), CutChain self t st acc.2 acc.1 →
      CutChain self t st (steps.foldl (fun acc step =>
        let r := tickStep dg self acc.1 t step; (r.1, acc.2 ++ r.2)) acc).2
        (steps.foldl (fun acc step =>
        let r := tickStep dg self acc.1 t step; (r.1, acc.2 ++ r.2)) acc).1 from
    h _ (.nil _)
  induction steps with
  | nil => exact fun _ h => h
  | cons s l ih =>
    intro acc h
    exact ih _ (chain_append self h (tickStep_chain dg self _ t s))

/-- **C0.5, the cut law.** -/
theorem exec_is_cut_chain : ExecIsCutChain dg self := by
  intro st t e
  cases e with
  | tick => exact runSteps_chain dg self st t _
  | block B => exact onBlock_chain self st t B
  | message m => exact acCall_chain self st t _
  | attestation a => exact chain_single self ⟨rfl, rfl, rfl⟩
  | restart => exact acCall_chain self st t _

end Consensus.Goldilocks.Compose

end

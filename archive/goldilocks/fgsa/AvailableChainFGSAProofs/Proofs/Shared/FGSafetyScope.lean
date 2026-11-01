module
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient
public import AvailableChainFGSARun.Proofs.Roots

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG AvailableChain.FGCompose

/-- A proposal read names the decoded proposal body. -/
private theorem fgsa_proposalErase_some {p : Params} {o : Obj p} {b : Block}
    (h : safetyProposalErase p o = some b) :
    ∃ N, o.payload = .proposal N ∧ N.erase = b := by
  rw [fgsa_safetyProposalErase_def] at h
  cases hp : o.payload with
  | proposal N =>
      simp only [hp, Option.some.injEq] at h
      exact ⟨N, rfl, h⟩
  | _ => simp [hp] at h

/-- The FG-SA scope laws for the ancestor-closed named scope of the run. -/
theorem fgsaSafetyScopeLaws (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) :
    FGSafetyScopeLaws (fgsaCoreReads p c) (fgsaSafetyReads p c) E rho
      (RootBlockInRun p c E rho) := by
  rw [fgsaCoreReads_def, fgsaSafetyReads_def]
  refine
    { genesis_scope := fun x hx => ?_
      delivered_scope := fun x o t b hd he => ?_
      parent_scope := fun K hK hne => ?_ }
  · have hs := cstoreInv_stateBefore E rho 0 x
    exact rootBlockInRun_held E rho hx 0 ((hs.baseTree _).mpr ⟨.genesis, hs.fg.gen, rfl⟩)
  · obtain ⟨N, ho, rfl⟩ := fgsa_proposalErase_some he
    exact rootBlockInRun_delivered E rho hd ho
  · change RootBlockInRun p c E rho (eraseFG K.parent)
    rw [safetyRunBlock_def] at hK
    obtain ⟨o, b, he, hemit | hdel, hKb⟩ := hK
    · obtain ⟨N, ho, rfl⟩ := fgsa_proposalErase_some he
      change Block.Preceq (eraseFG K) N.erase at hKb
      obtain ⟨x, t, hemit⟩ := hemit
      obtain ⟨i, hp⟩ := emitted_payload_parent_base_stored E rho hemit ho
      generalize hb : N.erase = b at hKb hp
      have hparent : Block.Preceq (eraseFG K.parent) b.parent := by
        rw [← eraseFG_parent]
        have hPK : Block.Preceq (eraseFG K).parent (eraseFG K) := by
          cases K with
          | genesis => exact block_preceq_refl _
          | node P s root body rs => exact eraseFG_preceq (KitFG.preceq_parent_node _ _ _ _ _)
        by_cases he : eraseFG K = b
        · rw [he]; exact block_preceq_refl _
        cases b with
        | genesis =>
          have hg : eraseFG K = .genesis := by simpa [Block.Preceq, Block.preceq] using hKb
          exact (he hg).elim
        | node P s root body =>
          exact block_preceq_trans hPK
            ((Bool.or_eq_true_iff.mp hKb).resolve_left (by simpa using he))
      exact rootBlockInRun_stored E rho i x (stored_body_ancestor E rho i x hp hparent)
        (fun hg => hne (eraseFG_eq_genesis.mp hg))
    · obtain ⟨N, ho, rfl⟩ := fgsa_proposalErase_some he
      change Block.Preceq (eraseFG K) N.erase at hKb
      obtain ⟨x, t, hd⟩ := hdel
      apply rootBlockInRun_ancestor E rho (rootBlockInRun_delivered E rho hd ho)
      apply block_preceq_trans _ hKb
      apply eraseFG_preceq
      cases K with
      | genesis => exact KitFG.preceq_refl _
      | node P s root body rs => exact KitFG.preceq_parent_node _ _ _ _ _

/-- The named-root premise gives root injectivity on every pair of scoped FG chains. -/
theorem fgsa_safetyScopedRoots (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (hr : NamedRootCollisionFree p c E rho) :
    safetyScopedRoots (fgsaCoreReads p c) (RootBlockInRun p c E rho) := by
  rw [safetyScopedRoots_def, fgsaCoreReads_def]
  exact fun _ _ hK hW => rootInjectiveOn_run E rho hr hK hW

end AvailableChain.FGSA.Run
end

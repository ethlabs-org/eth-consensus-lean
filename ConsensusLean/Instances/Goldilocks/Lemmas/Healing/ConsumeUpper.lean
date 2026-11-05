module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AcquireSources
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HS.5: attestations at `m` for a fixed upper proposal

Keeping the chosen `Y`, over `Γ`
(`GoldilocksRun`, `HSShared`, `Catch(2Δ)`, `SettledIn … w i₀ m c`) and the client
subclaim: for an honest proposal `Y` of slot `s` with `t_s ≥ r`, state height `m`, on a protected
branch (the three clauses of `ProtectedBranch`, spelled out: `Service` imports this file) and in
the phase through `v = t_s + 6Δ`, `Y` has an entry `E` at `m` and every honest validator has signed
a matching attestation for `E` at `m` by `v` (`fixed_upper_rows_of`). No `ReadyProposal Y` is
assumed.

The assembly (proved): `Y` is held by its proposer after its cut, and its entry `E` at `m` is the
entry state of its own chain (`Store.entry_state_of_source`). Every honest node receives, in
`[t_s, v]`, a source `C ⪰ Y` (`AcquireSources.protected_sources`); at that cut (in the phase)
`C` has height `m` (`≥ ht(Y) = m` along ancestry, `≤ m` the frontier), so its entry at `m` is `E`
and it is allowed (`effAllowed_of_height`); the `fg_attest` of the same tick (`toFG_attest`,
same FG state) and the client subclaim give the matching attestation, at the same time (no extra
`Δ`).

The sources are `AcquireSources.protected_sources`, shared with HS.4. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF Gp w : Time} {i₀ m : Nat}
  {c : PhaseCase (SA.Blk sp.n (List (FG.Att sp.n)))}

/-- **Attestations at `m` for a fixed upper proposal** (the
fixed-upper-proposal step of `Service`'s `consume_continue`, with `ProtectedBranch`,
`ClientProgress` and `RowsBy` spelled out, and HS.2 as the hypothesis `hclean`). -/
theorem fixed_upper_rows_of (hrun : GoldilocksRun proposer dg H tr) (hs : HSShared tr H dg g ΔF)
    (hc : CatchRun tr H g (2 * sp.Δ))
    (hset : SettledIn tr H g w i₀ m c) (hclean : CleanLockDrain)
    (hcl : ∀ y ∈ H, ∀ k (C : SA.Blk sp.n (List (FG.Att sp.n))) (signed : Option (FG.Att sp.n)),
      tr.CallAt y k (.fg (.attest C signed)) → i₀ ≤ k → PhaseOn tr.projFG H i₀ k m c →
      ∀ E h, EntryOf (tr.state y k).fg C E h → ((tr.state y k).fg.σ C.root).h = h →
        phaseFloor m c ≤ h →
        EffAllowed (tr.state y k).fg m c C →
        (∃ att, signed = some att ∧ att.h = h ∧ att.T = E.root) ∨
        ∃ k' < k, ∃ att, tr.SignAt y k' att ∧ att.h = h ∧ att.T = E.root)
    {s kY : Nat} {Y : SA.Blk sp.n (List (FG.Att sp.n))}
    (hY : tr.ProposesAt (proposer s) kY Y)
    (hYs : Y.slot = s) (hpH : proposer s ∈ H)
    (hYh : ((tr.post kY).fg.σ Y.root).h = m) (hr : rTime sp w ≤ sp.ts s)
    (hvotes : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → e.msg.slot = s →
      e.msg.head = Y.root ∧
      (Y ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame s) ∨
        Anc (tr.HonestBlocks H) Y ℓ.frame.fcRoot))
    (hlater : ∀ y ∈ H, ∀ k ℓ e, SA.CastAt tr.projAC y k ℓ e → s < e.msg.slot →
      PhaseOn tr.projFG H i₀ k m c → SA.VoteExtends (tr.HonestBlocks H) e.msg Y)
    (hparents : ∀ (s' : Nat) (P' : SA.Blk sp.n (List (FG.Att sp.n))) (k' : Nat), s < s' →
      P'.slot = s' → tr.ProposesAt (proposer s') k' P' →
      proposer s' ∈ H → PhaseOn tr.projFG H i₀ k' m c →
      ∃ Pr, P'.parent = some Pr.root ∧ Anc (tr.HonestBlocks H) Y Pr)
    (hon : ∀ jv, FirstCutAfter tr jv (sp.ts s + 6 * sp.Δ) → PhaseOn tr.projFG H i₀ jv m c) :
    ∃ E, EntryOf (tr.post kY).fg Y E m ∧
      ∀ y ∈ H, ∃ k att, tr.SignAt y k att ∧ tr.time k ≤ sp.ts s + 6 * sp.Δ ∧ att.h = m ∧
        att.T = E.root := by
  have hnc := hs.noColl
  have hsrc := protected_sources hrun hs hc hset hclean hY hYs hpH hr hvotes hlater hparents
    hon
  obtain ⟨-, hYt, hpost⟩ := accept_of_proposesAt hrun hnc hpH hY
  rw [hpost] at hYh ⊢
  have hR := Compose.fg_reachable hrun.toLocalRun hpH (kY + 1)
  obtain ⟨⟨E, hE, hEr, hEY, hEh, hETh⟩, -⟩ :=
    Goldilocks.Store.entry_state_of_source _ _ _ _ hR Y hYt
  have hETh' : ((tr.state _ (kY + 1)).fg.σ E.root).Th = E.root := hETh.trans hEr.symm
  have hsub : ∀ {y : Fin sp.n} (_ : y ∈ H) (i : Nat),
      (tr.state y i).fg.tree ⊆ tr.HonestBlocks H := fun hy i X hX => ⟨_, hy, i, hX⟩
  refine ⟨E, ⟨⟨hE, hETh'⟩, hEh.trans hYh, hEY⟩, fun y hy => ?_⟩
  obtain ⟨k, ℓ, C, ⟨hcall, hto, hC⟩, hk₁, hk₂, hYC⟩ := hsrc y hy
  have hCt := toFG_mem_tree hrun hy ⟨hcall, hto, hC⟩
  -- the cuts `k` and `k + 1` (the `fg_attest`) lie in the phase
  have hw := add_le_rTime sp w
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  obtain ⟨jv, hjv⟩ := exists_firstCutAfter_of_healthy hrun hs hy (sp.ts s + 6 * sp.Δ)
  rw [Compose.projAC_state hrun.toLocalRun hy] at hC
  obtain ⟨sg, hatt, ht, hfg⟩ :=
    toFG_attest hrun.toLocalRun hy (Compose.projAC_callAt.1 hcall) hto hC
  have hkv : k + 1 < jv := hjv.lt_of_time_le hrun.time_mono (by rw [ht]; exact hk₂)
  have hi₀ : i₀ ≤ k := by
    by_contra hlt
    have := hset.2.1.2 k (not_le.1 hlt)
    linarith
  have hph := hon jv hjv k hi₀ (by omega)
  -- `C` has height `m` and entry `E`, and is allowed
  have hRy := Compose.fg_reachable hrun.toLocalRun hy k
  have hYt' := mem_of_honest_anc hrun hnc hy hYC hCt
  have hCh : ((tr.state y k).fg.σ C.root).h = m := by
    refine le_antisymm (h_le_of_phaseAt hrun hnc hy le_rfl hph hCt) ?_
    have := h_le_of_store_anc hRy (store_anc_of_honest_anc hrun hnc hy hYC hCt)
    rwa [σ_eq_honest hrun hnc hy hpH hYt' hYt, hYh] at this
  have hEC : Anc (tr.HonestBlocks H) E C := (hEY.mono (hsub hpH _)).trans hYC
  have hEt := mem_of_honest_anc hrun hnc hy hEC hCt
  have hσE := σ_eq_honest hrun hnc hy hpH hEt hE
  have hEnt : EntryOf (tr.state y k).fg C E m :=
    ⟨⟨hEt, by rw [hσE, hETh']⟩, by rw [hσE, hEh, hYh], store_anc_of_honest_anc hrun hnc hy hEC hCt⟩
  have hall := effAllowed_of_height hrun hy hph hCt hCh
  rw [← hfg] at hEnt hCh hall
  rcases hcl y hy (k + 1) C sg hatt (by omega)
      (fun k' h₁ h₂ => hon jv hjv k' h₁ (by omega)) E m hEnt hCh (hCh ▸ hall.2.1) hall with
    ⟨att, rfl, hah, haT⟩ | ⟨k', hk', att, hsa, hah, haT⟩
  · exact ⟨k + 1, att, ⟨C, hatt⟩, by rw [ht]; exact hk₂, hah, haT⟩
  · exact ⟨k', att, hsa, (hrun.time_mono hk'.le).trans (by rw [ht]; exact hk₂), hah, haT⟩

end Consensus.Goldilocks.Healing

end

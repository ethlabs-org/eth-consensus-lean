module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission

public section

/-! # Goldilocks SA: the writer's pool holds the voter's slot-`s` votes (A1.2, A1.8 (d))

Under `Sync[t_s, τ]`, every slot-`s` vote that an honest voter `y` of slot `s + 1` holds up to its
vote at `τ ≤ t_s + 5Δ` was admitted (and so forwarded) at a time in `[t_s, τ]`, and an honest
writer `X` whose update of slot `s` runs at `t_s + 6Δ` (joined) processed it before: it is in
`X`'s pool, or `X`'s two-vote cap refused it and the pool holds two distinct votes of its
validator (`writer_pool`). A slot-`s` vote of `y`'s merged view is in `y`'s pool, or carried by a
slot-`(s+1)` block that `y` accepted before its vote, whose receipt admitted the vote or refused
it for two other held votes of its validator (`writer_merged`, A1.8's condition (d)). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

/-- **The writer's pool, for the voter's pool.** -/
theorem writer_pool (hrun : ACRun tr H U) {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat}
    {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ s ℓX) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr) {k : Nat}
    (hk : k ≤ i) :
    ∀ v ∈ (tr.state y (k + 1)).pool s, v ∈ (tr.state X i₀).pool s ∨
      v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} := by
  sorry

/-- **The writer-pool condition** (A1.8 (d)) from `Sync[t_s, τ]`. -/
theorem writer_merged (hrun : ACRun tr H U) {X : Fin sp.n} (hX : X ∈ H) {i₀ s : Nat}
    {ℓX : ACLabel (goldilocksSA sp FGP ro)} (hupd : UpdateAt tr X i₀ s ℓX) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hs : e.msg.slot = s + 1)
    (hsync : SyncAC (goldilocksSA sp FGP ro) H U (sp.ts s) (tr.time i) tr) :
    ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s} := by
  sorry

end Consensus.Goldilocks.SA

end

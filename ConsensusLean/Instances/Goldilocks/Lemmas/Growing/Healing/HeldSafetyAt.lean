module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HeldSignedAt

public section

/-! # The held-attestation safety premise at independent honest observations

Attestations on blocks held by two readers, each observed while honest at its own time, with a
signer honest at a time after both observations, are not slashable (`held_atts_safe_at`). Each
signature is recovered at its own reader's horizon (`held_att_signed_at`) and both are charged
on the prefix up to the later time, rather than through a terminal honest cohort. This is the
safety premise of the static store-level crossing arguments (`Healing/HeldSafety`,
`Healing/M1/StoreCache`, `Healing/M1/FrameLagCore`) for the growing readers.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- **Held attestations at independently honest observations are not slashable**, for any node
run under growing faults, from any starts `ini` (`held_atts_safe_at`). -/
theorem held_atts_safe_at_local {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
    {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Time → Set (Fin P.n)}
    {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}
    (h : Consensus.Goldilocks.Growing.LocalRun proposer dg H sg tr ini)
    {y x : Fin P.n} {m i : Nat} {u t d : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t) (hud : u ≤ d) (htd : t ≤ d)
    (a b : FG.Att P.n) (ha : ∃ Y ∈ (tr.state y m).fg.tree, a ∈ Y.fgPayload)
    (hb : ∃ Y ∈ (tr.state x i).fg.tree, b ∈ Y.fgPayload) (hav : a.val ∈ H d) :
    ¬ FG.slashable a b := fun hab => by
  obtain ⟨k, hk, hka⟩ := held_att_signed_at_local h hu hytime hy ha (h.antitone hud hav)
  obtain ⟨l, hl, hlb⟩ := held_att_signed_at_local h ht hxtime hx hb
    (hab.1 ▸ h.antitone htd hav)
  rw [← hab.1] at hlb
  have hka' : (tr.upTo d).SignAt a.val k a :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hytime k hk).trans hud, hka⟩
  have hlb' : (tr.upTo d).SignAt a.val l b :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hxtime l hl).trans htd, hlb⟩
  obtain ⟨inputs, hin, hs⟩ :=
    Store.signed_run_of_exec (Compose.fg_exec (h.upTo (hu.trans hud))) hav (max k l + 1)
  exact FG.client_safety P.fg a.val inputs hin
    a (hs k (by omega) a ⟨_, Compose.projFG_callAt.mpr hka'.choose_spec⟩)
    b (hs l (by omega) b ⟨_, Compose.projFG_callAt.mpr hlb'.choose_spec⟩) hab

/-- **Held attestations at independently honest observations are not slashable.** Attestations
on blocks held by `y` (observed while honest at `u`) and by `x` (observed while honest at `t`),
with a signer honest at a time `d` after both observations, were signed by that signer's client
run on the prefix up to `d`, which client safety (G0.5) keeps free of slashable pairs. -/
theorem held_atts_safe_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y x : Fin sp.n} {m i : Nat} {u t d : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t) (hud : u ≤ d) (htd : t ≤ d)
    (a b : FG.Att sp.n) (ha : ∃ Y ∈ (tr.state y m).fg.tree, a ∈ Y.fgPayload)
    (hb : ∃ Y ∈ (tr.state x i).fg.tree, b ∈ Y.fgPayload) (hav : a.val ∈ H d) :
    ¬ FG.slashable a b :=
  held_atts_safe_at_local hrun.toLocalRun hu hytime hy ht hxtime hx hud htd a b ha hb hav

end Consensus.Goldilocks.Healing.Growing

end

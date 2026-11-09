module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client

public section

/-! # The held-attestation safety premise at independent honest observations

Attestations on blocks held by two readers, each observed while honest at its own time, with a
signer honest at a time after both observations, are not slashable (`held_atts_safe_at`). Each
signature is recovered at its own reader's horizon and both are charged on the prefix up to the
later time, rather than through a terminal honest cohort. This is the safety premise of the
static store-level crossing arguments (`Healing/HeldSafety`, `Healing/M1/StoreCache`,
`Healing/M1/FrameLagCore`) for the growing readers.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An attestation on a block held at an observation honest at `t`, with a signer honest at `t`,
was signed before the cut. -/
private theorem held_att_signed_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) {a : FG.Att sp.n}
    (ha : ∃ Y ∈ (tr.state y i).fg.tree, a ∈ Y.fgPayload) (hav : a.val ∈ H t) :
    ∃ k < i, tr.SignAt a.val k a := by
  obtain ⟨X, hX, haX⟩ := ha
  have hXt : X ∈ ((tr.upTo t).state y i).fg.tree := by rw [Trace.upTo_state tr y hle]; exact hX
  rcases Healing.tree_accepted (hrun.upTo ht).toLocalRun hy hXt with rfl | ⟨k, hk, hacc⟩
  · cases haX
  · have hacc' := ((Trace.upTo_callAt tr).mp hacc).2
    obtain ⟨k', hk', hs'⟩ := hrun.toLocalRun.att_unforgeable y k a
      (hrun.antitone (hle k hk) hy) (Or.inr ⟨X, ⟨true, hacc'⟩, haX⟩)
      (hrun.antitone (hle k hk) hav)
    exact ⟨k', hk'.trans hk, hs'⟩

/-- **Held attestations at independently honest observations are not slashable.** Attestations
on blocks held by `y` (observed while honest at `u`) and by `x` (observed while honest at `t`),
with a signer honest at a time `d` after both observations, were signed by that signer's client
run on the prefix up to `d`, which client safety (G0.5) keeps free of slashable pairs. -/
theorem held_atts_safe_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y x : Fin sp.n} {m i : Nat} {u t d : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t) (hud : u ≤ d) (htd : t ≤ d)
    (a b : FG.Att sp.n) (ha : ∃ Y ∈ (tr.state y m).fg.tree, a ∈ Y.fgPayload)
    (hb : ∃ Y ∈ (tr.state x i).fg.tree, b ∈ Y.fgPayload) (hav : a.val ∈ H d) :
    ¬ FG.slashable a b := fun hab => by
  obtain ⟨k, hk, hka⟩ := held_att_signed_at hrun hu hytime hy ha (hrun.antitone hud hav)
  obtain ⟨l, hl, hlb⟩ := held_att_signed_at hrun ht hxtime hx hb
    (hab.1 ▸ hrun.antitone htd hav)
  rw [← hab.1] at hlb
  have hr := hrun.upTo (hu.trans hud)
  have hka' : (tr.upTo d).SignAt a.val k a :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hytime k hk).trans hud, hka⟩
  have hlb' : (tr.upTo d).SignAt a.val l b :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hxtime l hl).trans htd, hlb⟩
  have hfg := Compose.fg_projection sp.toParams (goldilocksNode sp ro) dg (H d)
    (fun v => v.val) (tr.upTo d) proposer (Compose.requirements sp ro)
    hr.genesis_root_ok hr.toLocalRun (hnc.upTo _)
  obtain ⟨inputs, hin, hs⟩ := Store.signed_run hfg hav (max k l + 1)
  exact FG.client_safety sp.toParams.fg a.val inputs hin
    a (hs k (by omega) a ⟨_, Compose.projFG_callAt.mpr hka'.choose_spec⟩)
    b (hs l (by omega) b ⟨_, Compose.projFG_callAt.mpr hlb'.choose_spec⟩) hab

end Consensus.Goldilocks.Healing.Growing

end

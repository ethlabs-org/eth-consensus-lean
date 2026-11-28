module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Store
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run

public section

/-! # Client safety for honest observations

The stock FG execution theorem serializes the signer's client inputs. The two holders
need not remain honest together; the signer stays honest through both observations.
-/

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams Payload)

variable {sp : ACParams}

private theorem held_att_signed_at {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace sp} {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht : 0 ≤ t)
    (hle : ∀ k < i, tr.time k ≤ t) (hy : y ∈ H t) {a : FG.Att sp.n}
    (ha : ∃ Y ∈ (tr.state y i).fg.tree, a ∈ Y.fgPayload) (hav : a.val ∈ H t) :
    ∃ k < i, tr.SignAt a.val k a := by
  obtain ⟨X, hX, haX⟩ := ha
  have hXt : X ∈ ((tr.upTo t).state y i).fg.tree := by
    rw [Trace.upTo_state tr y hle]
    exact hX
  rcases Compose.tree_cases (hrun.upTo ht).toLocalRun hy hXt with
    rfl | ⟨k, hk, hacc⟩
  · cases haX
  · have hacc' := ((Trace.upTo_callAt tr).mp hacc).2
    obtain ⟨k', hk', hs'⟩ := hrun.att_unforgeable y k a
      (hrun.antitone (hle k hk) hy) (Or.inr ⟨X, ⟨true, hacc'⟩, haX⟩)
      (hrun.antitone (hle k hk) hav)
    exact ⟨k', hk'.trans hk, hs'⟩

/-- Client safety for two honest observations of the shadow execution. A signer remains
honest through both observations, but the two holders need not remain honest together. -/
theorem held_atts_safe_at {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace sp} {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (_hnc : Compose.NoCollRun dg tr)
    {y x : Fin sp.n} {m i : Nat} {u t d : Time}
    (hu : 0 ≤ u) (hytime : ∀ k < m, tr.time k ≤ u) (hy : y ∈ H u)
    (ht : 0 ≤ t) (hxtime : ∀ k < i, tr.time k ≤ t) (hx : x ∈ H t)
    (hud : u ≤ d) (htd : t ≤ d)
    (a b : FG.Att sp.n) (ha : ∃ Y ∈ (tr.state y m).fg.tree, a ∈ Y.fgPayload)
    (hb : ∃ Y ∈ (tr.state x i).fg.tree, b ∈ Y.fgPayload) (hav : a.val ∈ H d) :
    ¬ FG.slashable a b := fun hab => by
  obtain ⟨k, hk, hka⟩ := held_att_signed_at hrun hu hytime hy ha
    (hrun.antitone hud hav)
  obtain ⟨l, hl, hlb⟩ := held_att_signed_at hrun ht hxtime hx hb
    (hab.1 ▸ hrun.antitone htd hav)
  rw [← hab.1] at hlb
  have hka' : (tr.upTo d).SignAt a.val k a :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hytime k hk).trans hud, hka⟩
  have hlb' : (tr.upTo d).SignAt a.val l b :=
    (RunTrace.upTo_signAt tr).mpr ⟨(hxtime l hl).trans htd, hlb⟩
  have hr := hrun.upTo (hu.trans hud)
  have hfg := Compose.fg_exec hr.toLocalRun
  obtain ⟨inputs, hin, hs⟩ := Store.signed_run_of_exec hfg hav (max k l + 1)
  exact FG.client_safety sp.toParams.fg a.val inputs hin
    a (hs k (by omega) a ⟨_, Compose.projFG_callAt.mpr hka'.choose_spec⟩)
    b (hs l (by omega) b ⟨_, Compose.projFG_callAt.mpr hlb'.choose_spec⟩) hab

end Consensus.Goldilocks.Healing.Growing.Shadow

end

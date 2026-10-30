module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.AC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Steps

public section

/-! # Goldilocks Healing: H.1, AC healing standalone (trivial frames), and its corollary

H.1 over driven AC traces of the SA with trivial frames (the frame of every honest call is the
tree of the blocks the node has accepted, rooted at genesis), under `Healthy(g)`, `Catch(2Δ)`,
`NoColl` and unforgeable signatures. Proved on paper (healing-simple `t1-proof.md` §§2–6, both
reviews in `t1-t4-reviews.md`): with `r = r_AC(ḡ)`, (§2) results of one slot `≥ r` are
compatible; (§§3–4) a fast origin of label `≥ r`, and a slow origin whose window is `≥ r`,
transfers to the next slot's honest votes and every later one (A1.2, A1.4, A1.3, A1.8); (§5) every
other lock expires before `t_r + 2Θ`; (§6) at `P` the voter's tree is contained in the
proposer's and the scores agree, so every honest slot-`p` vote is `P`, and from `t_p + 6Δ` the
record extends `P`.

The steps and their assembly are in `Steps.lean` (`ac_healing_standalone_of_parent`, H.1's
conclusions for one honest proposal); H.1 rests only on the open step lemmas there.

The corollary follows from H.1 (`corollary_of_standalone`): `Prop(G_p)` gives an honest
proposer in `[t, t + G_p]`, joined there (no restart after `ḡ`), so its `ac_proposal` returns a
payload and `Driven (b)` gives its proposal. -/

namespace Consensus.Goldilocks.SA

/-- **H.1, AC healing standalone** (T1 §§2–6). -/
theorem ac_healing_standalone (sp : SAParams) : ACHealingStandalone (sp := sp) :=
  fun _ _ _ _ _ _ hrun hdr htriv hheal hcatch _ _ hpH hP hp =>
    ac_healing_standalone_of_parent ⟨⟨hrun, hdr, hheal, hcatch⟩, htriv⟩ hpH hP hp

/-- **H.1 gives its corollary**: for `t ≥ ḡ + 2Θ + 8Δ`, `Prop(G_p)` gives a slot `p` with an
honest proposer and `t ≤ t_p ≤ t + G_p`; the proposer is awake and joined at `t_p` (no restart
after `ḡ`), so `ac_proposal` returns a payload and `Driven (b)` gives the honest proposal `P`;
H.1 at `P` holds from `t_p + 6Δ ≤ t + G_p + 6Δ`. -/
theorem corollary_of_standalone (sp : SAParams) (h : ACHealingStandalone (sp := sp)) :
    ACHealingStandaloneCorollary (sp := sp) := by
  intro FGP ro H U tr g Gp hrun hdr htriv hheal hcatch hprop t ht
  have hS : StandaloneRun tr H U g := ⟨⟨hrun, hdr, hheal, hcatch⟩, htriv⟩
  have hΘ := Θ_nonneg sp
  have hΔ := sp.toParams.hΔ
  obtain ⟨p, hp1, htp, htpG, hpH⟩ := hprop t (by linarith [gbar_nonneg g])
  have hgp : gbar g + 2 * Θ sp + 8 * sp.Δ ≤ sp.ts p := ht.trans htp
  have hslot : sp.slot (sp.ts p) = p :=
    slot_of_mem sp p le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))
  have hj : gbar g ≤ sp.ts ((sp.slot (sp.ts p) : Int) - 1) := by
    rw [hslot, ts_sub_one]; linarith
  obtain ⟨k, ℓ, hc, hcall, htk, himp⟩ := hdr.proposal p (by omega) _ hpH rfl
    (hS.awake hpH (by linarith)) (hS.joinedAt hpH hj)
  have hjs := hS.joined_state hpH k (by rw [htk]; exact hj)
  obtain ⟨d, pay, hdp⟩ : ∃ d pay,
      (acProposal sp (tr.state (sp.toParams.proposer p) k) ℓ.frame (tr.time k)).2 =
        some (d, pay) := by
    unfold acProposal
    simp only [hjs, not_true_eq_false, ↓reduceIte]
    exact ⟨_, _, rfl⟩
  obtain ⟨P, hP⟩ := himp ⟨pay, hc, hcall, d, hdp⟩
  obtain ⟨-, hii⟩ := h FGP ro H U tr g hrun hdr htriv hheal hcatch p P hpH hP hgp
  refine ⟨p, P, htp, htpG, hP, fun y hy j ℓ' hc' htj htick =>
    hii y hy j ℓ' hc' (by linarith) fun heq => htick (by linarith)⟩

/-- **H.1, corollary**: H.1 at an honest proposal of `Prop(G_p)`. -/
theorem ac_healing_standalone_corollary (sp : SAParams) :
    ACHealingStandaloneCorollary (sp := sp) :=
  corollary_of_standalone sp (ac_healing_standalone sp)

end Consensus.Goldilocks.SA

end

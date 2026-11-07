module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.FG.Safety

public section

/-! # FG finalized safety for a reader honest at a read time

`Growing/FG/Safety` reads each store at a cut of a node honest at that cut's time. A ready read
`(j, t)` (every cut before `j` at a time `≤ t`, `t < time j`) has its reader honest only at `t`:
its store at `j` is made by the cuts before `j`, all at times `≤ t`. These are the forms with each
store read at such an observation, charged at the later observation:

* `FGLocalRun.finalized_chain_upTo_at` (`FGLocalRun.finalized_chain`);
* `FGLocalRun.replay_finalized_safety_upTo_at` (`FGLocalRun.replay_finalized_safety`). -/

namespace Consensus.Goldilocks.Growing

variable {P : Params} {ACP : Type} {acp₀ : ACP} {H : Time → Set (Fin P.n)}
  {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}

/-- An honest store read through `t` supplies a finalized chain and genuine signatures for
signers still honest at `t`. -/
theorem FGLocalRun.finalized_chain_upTo_at (hr : FGLocalRun acp₀ H U tr)
    {y : Fin P.n} {j : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ k < j, tr.time k ≤ t)
    (hy : y ∈ H t) :
    ∃ c σ, P.fg.chainState c = some σ ∧ σ.F = (tr.store y j).F.root ∧
      (tr.store y j).F ∈ U ∧ (∀ X ∈ U, X.root ∈ P.fg.roots c → Compatible U X (tr.store y j).F) ∧
      (∀ a ∈ P.fg.chainAtts c, a.val ∈ H t → ∃ k < j, tr.SignAt a.val k a) := by
  have hs := Trace.upTo_state tr y (i := j) hle
  obtain ⟨c, σ, hc, hF, hU, hcompat, hsign, -⟩ := Store.finalized_chain (hr.upTo ht) hy j
  simp only [FGTrace.store, hs] at hF hU hcompat
  refine ⟨c, σ, hc, hF, hU, hcompat, fun a ha hv => ?_⟩
  obtain ⟨k, hk, src, hcall⟩ := hsign a ha hv
  exact ⟨k, hk, src, ((Trace.upTo_callAt tr).mp hcall).2⟩

/-- The finalized target obtained by replaying a carrier held by a node honest at an observation
time `s` agrees with the cache of a reader honest at a read time `t`, charging certificate
intersection at `max s t`. -/
theorem FGLocalRun.replay_finalized_safety_upTo_at (hr : FGLocalRun acp₀ H U tr)
    {x y : Fin P.n} {i j : Nat} {s t : Time} (hs : 0 ≤ s) (hlx : ∀ k < i, tr.time k ≤ s)
    (hx : x ∈ H s) (ht : 0 ≤ t) (hle : ∀ k < j, tr.time k ≤ t) (hy : y ∈ H t)
    (hf : (H (max s t))ᶜ.ncard < 2 * P.fg.q - P.n)
    {B X : NodeBlock P ACP} (hB : B ∈ (tr.store x i).tree) (hX : X ∈ (tr.store x i).tree)
    (hXr : X.root = ((tr.store x i).σ B.root).F) : Compatible U X (tr.store y j).F := by
  have hsx := Trace.upTo_state tr x (i := i) hlx
  have hR : (tr.store x i).Reachable acp₀ := by
    simpa only [FGTrace.store, hsx] using
      Store.store_reachable_of_exec (hr.exec_upTo hs) hx i
  have hsub := hr.tree_subset x i s hs hlx hx
  obtain ⟨c, hc, hl, hlast, hσ⟩ := Store.chain_state_of_chain P ACP acp₀ _ hR B hB
  obtain ⟨_, hcoh, hg, _⟩ := Store.accepted_tree P ACP acp₀ _ hR
  obtain ⟨_, ⟨X', hX', hX'r, hXB⟩, _⟩ := Store.entry_state_of_source P ACP acp₀ _ hR B hB
  have he : X' = X := hr.coherent.1 (hsub hX') (hsub hX) (hX'r.trans hXr.symm)
  rw [he] at hXB
  have hanc := Store.anc_of_linked c _ hg hc hl B (by
    rcases hlast with ⟨rfl, rfl⟩ | h
    · rfl
    · simp [List.getLast?_cons, h])
  have hcompat : ∀ Z ∈ U, Z.root ∈ P.fg.roots (c.map Block.fgView) → Compatible U Z X := by
    intro Z hZU hZ
    obtain ⟨W, hW, hWZ⟩ : ∃ W ∈ P.genesisBlock acp₀ :: c, W.root = Z.root := by
      simpa [FG.FGParams.roots, Block.fgView, Params.fg, Params.genesisBlock, eq_comm] using hZ
    have hWt : W ∈ (tr.store x i).tree := by
      rcases List.mem_cons.mp hW with rfl | h
      exacts [hg, hc _ h]
    rw [← hr.coherent.1 (hsub hWt) hZU hWZ]
    exact (Goldilocks.Anc.total hcoh (hanc W hW) hXB).imp (Anc.mono hsub) (Anc.mono hsub)
  have hsig : ∀ a ∈ P.fg.chainAtts (c.map Block.fgView), a.val ∈ H s →
      ∃ k < i, tr.SignAt a.val k a := by
    intro a ha hav
    obtain ⟨_, hW, haW⟩ := List.mem_flatMap.mp ha
    obtain ⟨W, hWc, rfl⟩ := List.mem_map.mp hW
    have hWt : W ∈ (tr.store x i).tree := hc W hWc
    rw [FGTrace.store, ← hsx] at hWt
    rcases Store.tree_accepted (hr.upTo hs) hx hWt with rfl | ⟨k, hk, hacc⟩
    · cases haW
    · have hki := hlx k hk
      obtain ⟨l, hl, hs⟩ := hr.unforgeable x k a (hr.antitone hki hx)
        ⟨_, ((Trace.upTo_callAt tr).mp hacc).2, haW⟩ (hr.antitone hki hav)
      exact ⟨l, hl.trans hk, hs⟩
  by_contra hne
  obtain ⟨c₂, σ₂, h₂, hF₂, hU₂, hc₂, ha₂⟩ := hr.finalized_chain_upTo_at ht hle hy
  obtain ⟨S, hS, hSv⟩ := FG.accountable_safety P.fg _ _ _ _ hσ h₂
    (fun h => hne (hc₂ _ (hsub hX) (hXr ▸ h)))
    (fun h => hne (hcompat _ hU₂ (hF₂ ▸ h)).symm)
  obtain ⟨v, hvS, hv⟩ : ∃ v ∈ S, v ∈ H (max s t) := by
    by_contra! hS'
    have hcard := Set.ncard_le_ncard
      (s := (S : Set (Fin P.fg.n))) (t := (H (max s t))ᶜ) hS'
    rw [Set.ncard_coe_finset] at hcard
    have : ((H (max s t))ᶜ : Set (Fin P.fg.n)).ncard = ((H (max s t))ᶜ : Set (Fin P.n)).ncard :=
      rfl
    have : P.fg.n = P.n := rfl
    omega
  obtain ⟨a, ha, b, hb, rfl, hab⟩ := hSv v hvS
  have signs : ∀ z ∈ P.fg.chainAtts (c.map Block.fgView) ++ P.fg.chainAtts c₂, z.val = a.val →
      ∃ k, tr.time k ≤ max s t ∧ tr.SignAt a.val k z := by
    intro z hz hzv
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨k, hk, hs⟩ := hsig z hz (hzv ▸ hr.antitone (le_max_left _ _) hv)
      exact ⟨k, (hlx k hk).trans (le_max_left _ _), hzv ▸ hs⟩
    · obtain ⟨k, hk, hs⟩ := ha₂ z hz (hzv ▸ hr.antitone (le_max_right _ _) hv)
      exact ⟨k, (hle k hk).trans (le_max_right _ _), hzv ▸ hs⟩
  obtain ⟨k, hk, hka⟩ := signs a ha rfl
  obtain ⟨l, hl, hlb⟩ := signs b hb hab.1.symm
  exact hr.non_framing hka hlb (hr.antitone (max_le hk hl) hv) hab

end Consensus.Goldilocks.Growing

end

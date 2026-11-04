module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Walk
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Geo
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: H.2's retained heads and view comparison

Acceptance relay and catch-up retain heads above the receiving frame's finalized root.
-/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time}

/-- Relay a held block above the receiver's finalized root, including pre-GST acceptances. -/
theorem h2_relay_held (hS : HealthyBase tr H U proposer g) {z : Fin sp.n} (hz : z ∈ H)
    {k : Nat} {ℓz : ACLabel (goldilocksSA sp FGP ro)} (hcz : tr.CallAt z k ℓz)
    {X : Blk sp.n FGP} (hX : X ∈ ℓz.frame.tree) {T : Time} (hk : tr.time k ≤ T)
    (hT : gbar g + sp.Δ ≤ T) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ)
    (hi : T + sp.Δ ≤ tr.time i) (hF : Anc U ℓ.frame.F X) : X ∈ ℓ.frame.tree := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hΔ := sp.toParams.hΔ
  have hXU := (frameIn_of_callAt hr hz hcz).2 hX
  obtain ⟨hΦ, -⟩ := frameIn_of_callAt hr hy hc
  rcases Compose.frame_anc_accepted hr hz k ℓz hcz X hX X .refl with hg | ⟨a, ha, hacc⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_call sp hr hy i ℓ hc
    obtain rfl : X = G := hU.1 hXU hGU (hg.trans hGr.symm)
    rcases Relation.ReflTransGen.cases_tail hF with he | ⟨W, -, hWG⟩
    · exact he ▸ hΦ.rooted.1
    · exact False.elim ((Option.some_ne_none _) (hWG.2.2.symm.trans hGp))
  have haT := le_trans (hr.time_mono ha) hk
  obtain ⟨b, hb, haccb⟩ : ∃ b ≤ i, tr.AcceptAt y b X := by
    by_cases hga : g ≤ tr.time a
    · obtain ⟨b, hb, haccb, -⟩ := hS.healthy.2.1 z hz a X hacc hga y hy i ℓ hc
        (by
          have hdl := hS.deadline_le hy i (tr.time a)
          have hm : max (tr.time a) (gbar g) ≤ T := max_le haT (by linarith)
          linarith) hF
      exact ⟨b, hb, haccb⟩
    · obtain ⟨b, hb, haccb, -⟩ := hS.catchUp z hz a X hacc
        ((not_le.1 hga).trans_le (le_gbar g)) y hy i ℓ hc (by linarith) hF
      exact ⟨b, hb, haccb⟩
  exact mem_tree_of_acceptAt sp hr hy haccb hb hc hF

/-- A pre-freeze block of the voter above the proposer's finalized root is retained there. -/
theorem h2_frozen_mem (hS : HealthyBase tr H U proposer g) {p k : Nat} {q y : Fin sp.n}
    (hq : q ∈ H) (hy : y ∈ H) {ℓp ℓ : ACLabel (goldilocksSA sp FGP ro)}
    (hck : tr.CallAt q k ℓp) (htk : tr.time k = sp.ts p)
    (hp : gbar g + 2 * sp.Δ ≤ sp.ts p) {i : Nat} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) {X : Blk sp.n FGP} (hX : X ∈ ℓ.frame.tree)
    (hst : e.readPoint.blockStamp X.root < ETime.of (freeze sp p))
    (hF : Anc U ℓp.frame.F X) : X ∈ ℓp.frame.tree := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, -⟩ := frameIn_of_callAt hr hq hck
  rw [readPoint_blockStamp_eq hr hy hc] at hst
  rcases Healing.stamp_origin hr hy i ℓ hc.1 X hX with hg | ⟨a, -, ℓa, hca, hXa, hsta⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_call sp hr hq k ℓp hck
    obtain rfl : X = G := hU.1 ((frameIn_of_callAt hr hy hc.1).2 hX) hGU (hg.trans hGr.symm)
    rcases Relation.ReflTransGen.cases_tail hF with he | ⟨W, -, hWG⟩
    · exact he ▸ hΦ.rooted.1
    · exact False.elim ((Option.some_ne_none _) (hWG.2.2.symm.trans hGp))
  have hfz : freeze sp p = sp.ts p - sp.Δ := by unfold freeze SAParams.ts; ring
  rw [hsta, hfz] at hst
  have hat : tr.time a < sp.ts p - sp.Δ :=
    WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hst)
  exact h2_relay_held hS hy hca hXa hat.le (by linarith) hq hck (by rw [htk]; linarith) hF

/-- An honest proposal is the only block of its positive slot in honest frames. -/
theorem h2_frame_slot_eq (hS : HealthyBase tr H U proposer g) {p : Nat} (hp : 0 < p)
    (hpH : proposer p ∈ H) {P : Blk sp.n FGP}
    (hP : HonestProposal tr (proposer p) p P) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ)
    {X : Blk sp.n FGP} (hX : X ∈ ℓ.frame.tree) (hXs : X.slot = p) : X = P := by
  have hr := hS.run.localRun
  rcases frame_genesis_or_accepted sp hr hy hc X hX with h0 | ⟨j, -, hacc⟩
  · omega
  have hXp := (hS.driven.blocks y hy j X hacc (accept_ne_genesis sp hr hy hacc)).1
  obtain ⟨-, -, -, -, -, -, -, -, -, hPs, hPp, -, a, -, ⟨ℓa, hca, hcalla⟩, -⟩ := hP
  have hPa := (accept_new sp hr hpH ⟨ℓa, hca, hcalla⟩).1 ℓa hca
  exact hS.run.honest.one_block X P ⟨y, hy, i, ℓ, hc, hX⟩ ⟨_, hpH, a, ℓa, hca, hPa⟩
    (by rw [hXp, hXs]; exact hpH) (by rw [hXp, hXs, hPp]) (hXs.trans hPs.symm)

/-- Every carried support head above the voter's finalized root is retained at its read. -/
theorem h2_support_mem (hS : HealthyBase tr H U proposer g) {p k : Nat} (hp : 0 < p)
    (hpH : proposer p ∈ H) {P : Blk sp.n FGP}
    (hP : HonestProposal tr (proposer p) p P)
    {ℓp : ACLabel (goldilocksSA sp FGP ro)} (hck : tr.CallAt (proposer p) k ℓp)
    (htk : tr.time k = sp.ts p) {pay : Payload sp.n} (hpay : P.acPayload = pay)
    (hlate : gbar g + sp.Δ ≤ sp.ts p) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hes : e.msg.slot = p)
    {v : Vote sp.n} (hv : v ∈ pay.2) (hvs : v.slot + 1 = p)
    {Hd : Blk sp.n FGP} (hHd : Hd ∈ ℓp.frame.tree) (hHdr : Hd.root = v.head)
    (hF : Anc U ℓ.frame.F Hd) : Hd ∈ ℓ.frame.tree := by
  have hr := hS.run.localRun
  by_cases hearly : tr.time i < sp.ts p + sp.Δ
  · obtain ⟨Q, hQ, hQs, hsup⟩ := cast_ready hr hy hc (by rw [hes]; exact hearly)
    have hQP := h2_frame_slot_eq hS hp hpH hP hy hc.1 hQ (hQs.trans hes)
    rw [hQP, hes] at hsup
    obtain ⟨Hd', hHd', hHdr', -⟩ := hsup v (by simpa only [blockSupport, hpay] using hv)
      (by omega)
    obtain rfl : Hd' = Hd := hr.coherent.1 ((frameIn_of_callAt hr hy hc.1).2 hHd')
      ((frameIn_of_callAt hr hpH hck).2 hHd) (hHdr'.trans hHdr.symm)
    exact hHd'
  exact h2_relay_held hS hpH hck hHd htk.le hlate hy hc.1 (not_lt.1 hearly) hF

/-- The proposer and voter agree on participants, equivocators and support for common blocks,
without equating their roots or their trees. -/
theorem h2_views_agree (hS : HealthyBase tr H U proposer g) {s k : Nat}
    (hpH : proposer (s + 1) ∈ H) {P : Blk sp.n FGP}
    (hP : HonestProposal tr (proposer (s + 1)) (s + 1) P)
    {ℓp : ACLabel (goldilocksSA sp FGP ro)}
    (hck : tr.CallAt (proposer (s + 1)) k ℓp) (hcall : ℓp.call = .proposal)
    (htk : tr.time k = sp.ts (s + 1 : Nat))
    {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (hpay : (acProposal sp (tr.state (proposer (s + 1)) k) ℓp.frame (tr.time k)).2 =
      some (d, pay)) (hPpay : P.acPayload = pay) (hPs : P.slot = s + 1)
    (hlate : gbar g + 4 * sp.Δ ≤ sp.ts s) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hes : e.msg.slot = s + 1) (hPy : P ∈ ℓ.frame.tree) :
    equivocators (View.ofLists pay).votes =
        equivocators (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes ∧
      voters (View.ofLists pay).votes =
        voters (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes ∧
      ∀ X ∈ ℓp.frame.tree, X ∈ ℓ.frame.tree →
        supporters ℓp.frame (View.ofLists pay) s X =
          supporters ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s X := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  refine view_agree hS.run hpH hy rfl ⟨hck, hcall, d, hpay⟩ htk hc
    ⟨P, hPy, hPs, hPpay⟩ (hS.syncAC (by linarith) _) ?_ ?_
  · intro Hd hHd _ hst hF
    exact h2_frozen_mem hS hpH hy hck htk (by rw [hts]; linarith) hc hHd hst hF
  · intro v hv Hd hHd hHdr hF
    have hsl : sp.slot (tr.time k) = s + 1 := by
      rw [htk]; exact slot_of_mem sp (s + 1) le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))
    have hpay' := hpay
    unfold acProposal at hpay'
    split_ifs at hpay'
    simp only [Option.some.injEq, Prod.mk.injEq, hsl] at hpay'
    have hv' := hv
    rw [← hpay'.2] at hv'
    have hs : ((s + 1 : Nat) : Int) - 1 = s := by push_cast; ring
    rw [hs] at hv'
    have hvs := state_pool_slot sp hr hpH k s v
      ((mem_proposalView_votes hr hpH k s ℓp.frame v).1 (ofLists_support_subset _ _ _ _ hv'))
    exact h2_support_mem hS (by omega) hpH hP hck htk hPpay (by rw [hts]; linarith)
      hy hc hes hv (by omega) hHd hHdr hF

/-- Viable voter competitors above the proposer's root reflect into its viable tree, with the
proposal itself added. The witness is frozen (and relayed), or lies on the proposal ancestry. -/
theorem h2_competitor_reflect (hS : HealthyBase tr H U proposer g) {p k : Nat} (hp : 0 < p)
    (hpH : proposer p ∈ H) {P Q : Blk sp.n FGP}
    (hP : HonestProposal tr (proposer p) p P)
    {ℓp : ACLabel (goldilocksSA sp FGP ro)} (hck : tr.CallAt (proposer p) k ℓp)
    (hcall : ℓp.call = .proposal) (htk : tr.time k = sp.ts p)
    (hlate : gbar g + 2 * sp.Δ ≤ sp.ts p) (hgeo : Geo proposer tr H p P)
    (hPnot : P ∉ ℓp.frame.tree)
    (hQP : P.parent = some Q.root) (hQv : Q ∈ ℓp.frame.viableTree ℓp.frame.tree)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) (hes : e.msg.slot = p)
    {B : Blk sp.n FGP} (hB : B ∈ ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame p))
    (hfcB : Anc U ℓp.frame.fcRoot B) : B ∈ insert P (ℓp.frame.viableTree ℓp.frame.tree) := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  obtain ⟨hΦp, hΦpU⟩ := frameIn_of_callAt hr hpH hck
  obtain ⟨hΦy, hΦyU⟩ := frameIn_of_callAt hr hy hc.1
  have hFB := (hΦp.F_anc_fcRoot.mono hΦpU).trans hfcB
  by_cases hBP : B = P
  · exact Set.mem_insert_iff.2 (Or.inl hBP)
  right
  obtain ⟨⟨hBt, -⟩, -, W, hW, hWv, hBW⟩ := hB
  obtain ⟨Z, hZt, hZv, hBZ⟩ : ∃ Z ∈ ℓp.frame.tree, Z ∈ ℓp.frame.viableHeads ∧ Anc U B Z := by
    rcases hW.2 with hst | ⟨P', hP', hP's, hWP'⟩
    · have hWt := h2_frozen_mem hS hpH hy hck htk hlate hc hW.1 hst
        (hFB.trans (hBW.mono hΦyU))
      have hWP : W ≠ P := by
        intro he
        exact hPnot (he ▸ hWt)
      exact ⟨W, hWt, (hgeo k ℓp hck hcall htk y hy i ℓ e hc hes).2 W hW hWP |>.1 hWv,
        hBW.mono hΦyU⟩
    · obtain rfl : P' = P := h2_frame_slot_eq hS hp hpH hP hy hc.1 hP' hP's
      rcases Relation.ReflTransGen.cases_tail (hBW.trans hWP') with he | ⟨Y, hBY, hYP⟩
      · exact False.elim (hBP he.symm)
      · obtain rfl : Y = Q := hU.1 (hΦyU hYP.1) (hΦpU hQv.1)
          (Option.some.inj (hYP.2.2.symm.trans hQP))
        obtain ⟨Z, hZt, hZv, hQZ⟩ := hQv.2.2
        exact ⟨Z, hZt, hZv, (Anc.mono hΦyU hBY).trans (hQZ.mono hΦpU)⟩
  have hBp := frame_mem_of_between sp hU hΦp hΦpU hZt hBZ hFB
  exact ⟨hBp, anc_tree_of_anc_U hU hΦp hΦpU hΦp.fcRoot_mem hfcB hBp,
    Z, hZt, hZv, anc_tree_of_anc_U hU hΦp hΦpU hBp hBZ hZt⟩

/-- Every viable witness of the voter extends the proposer's root: `Geo` transfers every
witness other than the proposal into the proposer's viable heads. -/
theorem h2_witness_above_root (hS : HealthyBase tr H U proposer g) {p k : Nat}
    (hpH : proposer p ∈ H) {P : Blk sp.n FGP}
    {ℓp : ACLabel (goldilocksSA sp FGP ro)} (hck : tr.CallAt (proposer p) k ℓp)
    (hcall : ℓp.call = .proposal) (htk : tr.time k = sp.ts p)
    (hgeo : Geo proposer tr H p P) (hroot : Anc U ℓp.frame.fcRoot P)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) (hes : e.msg.slot = p)
    {W : Blk sp.n FGP} (hW : W ∈ voterBlockTree sp e.readPoint ℓ.frame p)
    (hWv : W ∈ ℓ.frame.viableHeads) : Anc U ℓp.frame.fcRoot W := by
  by_cases he : W = P
  · exact he ▸ hroot
  have hWp := (hgeo k ℓp hck hcall htk y hy i ℓ e hc hes).2 W hW he |>.1 hWv
  obtain ⟨hΦp, hΦpU⟩ := frameIn_of_callAt hS.run.localRun hpH hck
  exact (hΦp.fcRoot_anc_viableHeads W hWp).mono hΦpU

/-- A reader whose anchor is below the proposer's root reaches that root before branching. -/
theorem h2_reader_reaches_root (hS : HealthyBase tr H U proposer g) {p k : Nat}
    (hpH : proposer p ∈ H) {P : Blk sp.n FGP}
    {ℓp : ACLabel (goldilocksSA sp FGP ro)} (hck : tr.CallAt (proposer p) k ℓp)
    (hcall : ℓp.call = .proposal) (htk : tr.time k = sp.ts p)
    (hgeo : Geo proposer tr H p P) (hroot : Anc U ℓp.frame.fcRoot P)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) (hes : e.msg.slot = p)
    (hPs : P.slot = p)
    (haR : Anc U (getAnchor sp e.readPoint ℓ.frame (tr.time i)) ℓp.frame.fcRoot) :
    Anc U ℓp.frame.fcRoot
      (getHead sp e.readPoint ℓ.frame (tr.time i)
        (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame p))
        (mergedVoteView sp e.readPoint ℓ.frame p) ((p : Int) - 1)) := by
  have hr := hS.run.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc.1
  have hPv := (hgeo k ℓp hck hcall htk y hy i ℓ e hc hes).1
  have hPt := hΦ.viableHeads_subset hPv
  have hfa := fcRoot_anc_getAnchor hΦ e.readPoint (tr.time i)
  have hfR := (hfa.mono hΦU).trans haR
  have hRt := frame_mem_of_between sp hU hΦ hΦU hPt hroot
    ((hΦ.F_anc_fcRoot.mono hΦU).trans hfR)
  have hRP := anc_tree_of_anc_U hU hΦ hΦU hRt hroot hPt
  have hRtV : ℓp.frame.fcRoot ∈ ℓ.frame.viableTree
      (voterBlockTree sp e.readPoint ℓ.frame p) :=
    ⟨⟨hRt, Or.inr ⟨P, hPt, hPs, hRP⟩⟩,
      anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfR hRt,
      P, ⟨hPt, Or.inr ⟨P, hPt, hPs, .refl⟩⟩, hPv, hRP⟩
  have hat : getAnchor sp e.readPoint ℓ.frame (tr.time i) ∈ ℓ.frame.tree := by
    rcases eq_or_ne ℓ.frame.fcRoot (getAnchor sp e.readPoint ℓ.frame (tr.time i)) with he | he
    · exact he ▸ hΦ.fcRoot_mem
    · exact (Anc.mem hfa he).2
  have hclosed := voterBlockTree_anc hr hy hc
  rw [hes] at hclosed
  exact Anc.mono hΦU (h2_walk_reaches_root hΦ (fun _ h => h.1)
    (fun B hB X hXB _ => hclosed B hB X hXB) hRtV
    (anc_tree_of_anc_U hU hΦ hΦU hat haR hRt) hfa
    (fun W hW hWv => anc_tree_of_anc_U hU hΦ hΦU hRt
      (h2_witness_above_root hS hpH hck hcall htk hgeo hroot hy hc hes hW hWv) hW.1)
    _ _ _)

end Consensus.Goldilocks.SA

end

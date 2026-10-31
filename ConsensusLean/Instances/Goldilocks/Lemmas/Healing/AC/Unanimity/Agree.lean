module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Unanimity.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Trivial
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ProposalTransfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WalkEnd
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Ready

public section

/-! # Goldilocks Healing: every honest slot-`p` walk is the canonical walk (T1 §6)

At every honest vote of slot `p`, the voter walks the canonical walk: at every block, its
eligible children (in the viable voter block tree, with the merged view) are the eligible
children of the proposer's viable tree with `P` added (the proposal's view at `t_p`), with the
same scores. The voter holds `P` (its `vote_ready`, or acceptance relay by `t_p + Δ`), and `P`
is the only slot-`p` block of the honest frames (`one_block`). A child of slot below `p` of the
voter block tree was accepted before the vote freeze, so it reached the proposer by `t_p`; an
eligible child of slot below `p` of the proposer's tree has a strict majority of the voters,
all honest validators among them (`Healthy`), so an honest supporter, and reached the voter
before the freeze (`trivial_viable`); the scores and eligibility agree by `view_agree`. `P` has
no supporters in either view. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g : Time} {p : Nat} {P : Blk sp.n FGP}
  {k : Nat} {ℓp : ACLabel (goldilocksSA sp FGP ro)} {d : DutyHead sp.n FGP (Payload sp.n)}
  {pay : Payload sp.n} {schedule : Nat → Fin sp.n}

/-! ## Helpers -/

/-- The genesis block of an honest node's initial frame is in `U`, with slot `0`. -/
private theorem genesis_slot (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ {ℓ : ACLabel (goldilocksSA sp FGP ro)}, tr.CallAt y i ℓ →
      ∃ G ∈ U, G.root = sp.genesisRoot ∧ G.slot = 0 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro ℓ hc
    rcases hr.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, hroot, hslot, -⟩, ⟨-, hsub⟩, -⟩ | ⟨j, ℓ', hj, hc', -⟩
    · exact ⟨Φ₀.F, hsub (htree ▸ rfl), hroot, hslot⟩
    · exact ih j hj hc'

private theorem slot_ts (s : Nat) : sp.slot (sp.ts s) = s :=
  slot_of_mem sp s le_rfl ((ts_lt_iff sp).2 (by push_cast; omega))

/-- The slot of the proposal is positive. -/
private theorem slot_pos (hs : UnanimitySetting tr H U schedule g p P k ℓp d pay) : 0 < p := by
  have h := hs.late
  have := gbar_nonneg g
  have := Θ_nonneg sp
  have := sp.toParams.hΔ
  have h0 : sp.ts ((0 : Nat) : Int) < sp.ts (p : Int) := by
    have : sp.ts ((0 : Nat) : Int) = 0 := by simp [SAParams.ts]
    linarith
  exact_mod_cast (ts_lt_iff sp).1 h0

private theorem late_prev {s : Nat}
    (hs : UnanimitySetting tr H U schedule g (s + 1) P k ℓp d pay) :
    gbar g + 4 * sp.Δ ≤ sp.ts s ∧ gbar g + sp.Δ ≤ sp.ts (s + 1 : Nat) := by
  have h := hs.late
  have := Θ_nonneg sp
  have := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  constructor <;> linarith

/-- The payload is the proposer's view of its slot-`s` pool. -/
private theorem payload_eq {s : Nat}
    (hs : UnanimitySetting tr H U schedule g (s + 1) P k ℓp d pay) :
    pay = voteViewList (tr.state (schedule (s + 1)) k) ℓp.frame s ⊤ := by
  have h := hs.payload
  have hsl : sp.slot (tr.time k) = s + 1 := by rw [hs.time]; exact slot_ts (s + 1)
  unfold acProposal at h
  dsimp only at h
  split_ifs at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2, hsl]
  push_cast
  ring_nf

/-- The only block of slot `p` of an honest frame is `P`. -/
private theorem frame_slot_eq (hs : UnanimitySetting tr H U schedule g p P k ℓp d pay)
    {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ)
    {Q : Blk sp.n FGP} (hQ : Q ∈ ℓ.frame.tree) (hQs : Q.slot = p) : Q = P := by
  have hrun := hs.standalone.run
  have hr := hrun.localRun
  have hp := slot_pos hs
  obtain ⟨j₀, -, hacc, -⟩ := hs.accepted
  obtain ⟨ℓ₀, hc₀, -⟩ := id hacc
  have hP₀ := (accept_new sp hr hs.proposer_mem hacc).1 ℓ₀ hc₀
  have hQf : HonestFrameBlock tr H Q := ⟨y, hy, i, ℓ, hc, hQ⟩
  have hQr : Q.root ≠ sp.genesisRoot := by
    intro hg
    obtain ⟨G, hGU, hGr, hGs⟩ := genesis_slot hr hy i hc
    have := hr.coherent.1 ((frameIn_of_callAt hr hy hc).2 hQ) hGU (hg.trans hGr.symm)
    rw [this, hGs] at hQs
    omega
  have hQp := hrun.honest.proposer Q hQf hQr
  exact hrun.honest.one_block Q P hQf ⟨_, hs.proposer_mem, j₀, ℓ₀, hc₀, hP₀⟩
    (by rw [hQp, hQs]; exact hs.proposer_mem) (by rw [hQp, hQs, hs.proposer])
    (by rw [hQs, hs.slot])

/-- Acceptance relay: a block an honest node accepted by `T ≥ ḡ + Δ` is accepted by every honest
node by its calls from `T + Δ` on. -/
private theorem relay_le (hS : StandaloneRun tr H U schedule g)
    {z : Fin sp.n} (hz : z ∈ H) {a : Nat}
    {X : Blk sp.n FGP} (hacc : tr.AcceptAt z a X) {T : Time} (haT : tr.time a ≤ T)
    (hT : gbar g + sp.Δ ≤ T) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) (hi : T + sp.Δ ≤ tr.time i)
    (hF : Anc U ℓ.frame.F X) : ∃ k' ≤ i, tr.AcceptAt y k' X := by
  have hΔ := sp.toParams.hΔ
  by_cases hga : g ≤ tr.time a
  · have hmax : max (tr.time a) (gbar g) ≤ T := max_le haT (by linarith)
    obtain ⟨k', hk', hacc', -⟩ := hS.healthy.2.1 z hz a X hacc hga y hy i ℓ hc
      (by linarith [hS.deadline_le hy i (tr.time a)]) hF
    exact ⟨k', hk', hacc'⟩
  · obtain ⟨k', hk', hacc', -⟩ := hS.catchUp z hz a X hacc
      (lt_of_lt_of_le (not_le.1 hga) (le_gbar g)) y hy i ℓ hc (by linarith) hF
    exact ⟨k', hk', hacc'⟩

/-- A block of an honest frame extends the `Φ.F` of every honest call. -/
private theorem anc_F_of_mem (hS : StandaloneRun tr H U schedule g) {y z : Fin sp.n} (hy : y ∈ H)
    (hz : z ∈ H) {i i' : Nat} {ℓ ℓ' : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ)
    (hc' : tr.CallAt z i' ℓ') {X : Blk sp.n FGP} (hX : X ∈ ℓ'.frame.tree) :
    Anc U ℓ.frame.F X := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hS.run.localRun hz hc'
  rw [trivial_F_eq hS hy hz hc hc']
  exact (hΦ.rooted.2 X hX).mono hΦU

/-- Under trivial frames, `Φ.F` (genesis) has no parent. -/
private theorem F_parent (hS : StandaloneRun tr H U schedule g)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) : ℓ.frame.F.parent = none := by
  have hr := hS.run.localRun
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hy hc
  obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_call sp hr hy i ℓ hc
  rw [hr.coherent.1 (hΦU hΦ.rooted.1) hGU ((hS.trivial y hy i ℓ hc).1.trans hGr.symm), hGp]

/-- Under trivial frames, a block of the tree with a parent has its parent among the viable
heads. -/
private theorem parent_viable (hS : StandaloneRun tr H U schedule g) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) {B : Blk sp.n FGP}
    (hB : B ∈ ℓ.frame.tree) {r : Nat} (hp : B.parent = some r) :
    ∃ W ∈ ℓ.frame.viableHeads, B.parent = some W.root := by
  obtain ⟨hΦ, -⟩ := frameIn_of_callAt hS.run.localRun hy hc
  obtain ⟨-, -, hvh, -⟩ := hS.trivial y hy i ℓ hc
  rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hΦ.rooted.2 B hB) with h | ⟨W, -, hW⟩
  · rw [h, F_parent hS hy hc] at hp
    exact absurd hp (by simp)
  · exact ⟨W, by rw [hvh]; exact hW.1, hW.2.2⟩

/-- Under trivial frames, eligibility of a block of the tree with a parent is the current slot or
a strict majority. -/
private theorem eligible_iff (hS : StandaloneRun tr H U schedule g) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) {B : Blk sp.n FGP}
    (hB : B ∈ ℓ.frame.tree) {r : Nat} (hp : B.parent = some r) (t : Time) (V : View sp.n)
    (σ : Int) : goldfishEligible sp ℓ.frame t V σ B ↔
      B.slot = sp.slot t ∨ (voters V.votes).ncard < 2 * goldfishScore sp ℓ.frame V σ B := by
  have h := parent_viable hS hy hc hB hp
  unfold goldfishEligible
  constructor
  · rintro (h' | h')
    · exact absurd h h'
    · exact h'
  · exact Or.inr

/-- Under trivial frames, every block of a subset of the tree is in its viable tree. -/
private theorem mem_viableTree (hS : StandaloneRun tr H U schedule g) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ)
    {S : Set (Blk sp.n FGP)} (hsub : S ⊆ ℓ.frame.tree) {B : Blk sp.n FGP} (hB : B ∈ S) :
    B ∈ ℓ.frame.viableTree S := by
  obtain ⟨hΦ, -⟩ := frameIn_of_callAt hS.run.localRun hy hc
  obtain ⟨-, hfc, hvh, -⟩ := hS.trivial y hy i ℓ hc
  exact ⟨hB, by rw [hfc]; exact hΦ.rooted.2 B (hsub hB), B, hB, by rw [hvh]; exact hsub hB,
    Relation.ReflTransGen.refl⟩

/-- The voter holds `P`, and the heads of `P`'s support entries that the proposer holds. -/
private theorem vote_holds {s : Nat}
    (hs : UnanimitySetting tr H U schedule g (s + 1) P k ℓp d pay)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr x j ℓ e) (hes : e.msg.slot = s + 1) :
    P ∈ ℓ.frame.tree ∧ ∀ v ∈ pay.2, ∀ Hd ∈ ℓp.frame.tree, Hd.root = v.head →
      Hd ∈ ℓ.frame.tree := by
  have hS := hs.standalone
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hpH := hs.proposer_mem
  obtain ⟨-, hT⟩ := late_prev hs
  obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr hx hc.1
  obtain ⟨-, hΨU⟩ := frameIn_of_callAt hr hpH hs.call
  by_cases hearly : tr.time j < sp.ts (s + 1 : Nat) + sp.Δ
  · obtain ⟨Q, hQ, hQs, hsup⟩ := cast_ready hr hx hc (by rw [hes]; exact hearly)
    rw [hes] at hQs hsup
    have hQP := frame_slot_eq hs hx hc.1 hQ hQs
    rw [hQP] at hQ hsup
    refine ⟨hQ, fun v hv Hd hHd hHdr => ?_⟩
    have hvs : v.slot = s := by
      have hv' := hv
      rw [payload_eq hs] at hv'
      exact state_pool_slot sp hr hpH k s v ((mem_proposalView_votes hr hpH k s ℓp.frame v).1
        (ofLists_support_subset _ _ _ _ hv'))
    obtain ⟨H', hH', hH'r, -⟩ := hsup v (by rw [blockSupport, hs.acPayload]; exact hv)
      (by rw [hvs])
    rw [hU.1 (hΨU hHd) (hΦU hH') (hHdr.trans hH'r.symm)]
    exact hH'
  · have hlate : sp.ts (s + 1 : Nat) + sp.Δ ≤ tr.time j := not_lt.1 hearly
    obtain ⟨j₀, -, hacc, htj₀⟩ := hs.accepted
    obtain ⟨ℓ₀, hc₀, -⟩ := id hacc
    have hP₀ := (accept_new sp hr hpH hacc).1 ℓ₀ hc₀
    obtain ⟨a, ha, hacc'⟩ := relay_le hS hpH hacc htj₀.le hT hx hc.1 hlate
      (anc_F_of_mem hS hx hpH hc.1 hc₀ hP₀)
    refine ⟨trivial_mem_tree hS hx hc.1 ((frameIn_of_callAt hr hpH hc₀).2 hP₀)
      (Or.inr ⟨a, ha, hacc'⟩), fun v _ Hd hHd _ => ?_⟩
    have hHdU := hΨU hHd
    have hFHd := anc_F_of_mem hS hx hpH hc.1 hs.call hHd
    obtain ⟨hF, -, -, htree⟩ := hS.trivial _ hpH k ℓp hs.call
    rw [htree] at hHd
    rcases Set.mem_insert_iff.1 hHd with h | ⟨b, hbk, hacc₁⟩
    · exact trivial_mem_tree hS hx hc.1 hHdU (Or.inl (by rw [h]; exact hF))
    · obtain ⟨c, hc', hacc₂⟩ := relay_le hS hpH hacc₁
        (by rw [← hs.time]; exact hr.time_mono hbk) hT hx hc.1 hlate hFHd
      exact trivial_mem_tree hS hx hc.1 hHdU (Or.inr ⟨c, hc', hacc₂⟩)

/-- A block of the voter's tree stamped before the vote freeze is in the proposer's tree. -/
private theorem stamped_mem {s : Nat}
    (hs : UnanimitySetting tr H U schedule g (s + 1) P k ℓp d pay)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr x j ℓ e) {B : Blk sp.n FGP} (hB : B ∈ ℓ.frame.tree)
    (hst : e.readPoint.blockStamp B.root < ETime.of (freeze sp (s + 1))) :
    B ∈ ℓp.frame.tree := by
  have hS := hs.standalone
  have hr := hS.run.localRun
  have hpH := hs.proposer_mem
  obtain ⟨hσ, -⟩ := late_prev hs
  obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr hx hc.1
  have hrp : e.readPoint.blockStamp = (tr.state x (j + 1)).blockStamp := by
    rw [show tr.state x (j + 1) = tr.post j by simp [Trace.state, hc.1.1, hc.1.2],
      readPoint_blockStamp_eq hr hx hc]
  rw [hrp, freeze, show ((s + 1 : Nat) : Int) - 1 = s by push_cast; ring] at hst
  rcases accepted_of_blockStamp_lt hS hx hst with hg | ⟨a, -, X, hXr, hacc, hta⟩
  · exact trivial_mem_tree hS hpH hs.call (hΦU hB) (Or.inl hg)
  obtain ⟨ℓa, hca, -⟩ := id hacc
  obtain rfl : X = B := hr.coherent.1
    ((frameIn_of_callAt hr hx hca).2 ((accept_new sp hr hx hacc).1 ℓa hca)) (hΦU hB) hXr
  obtain ⟨b, hb, haccb⟩ := proposal_accept hS hpH hs.call hs.time hσ hx hacc hta
    (anc_F_of_mem hS hpH hx hs.call hc.1 hB)
  exact trivial_mem_tree hS hpH hs.call (hΦU hB) (Or.inr ⟨b, hb.le, haccb⟩)

/-- A block of the voter block tree is `P` or in the proposer's tree. -/
private theorem voterBlock_mem {s : Nat}
    (hs : UnanimitySetting tr H U schedule g (s + 1) P k ℓp d pay)
    {x : Fin sp.n} (hx : x ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr x j ℓ e) {B : Blk sp.n FGP}
    (hB : B ∈ voterBlockTree sp e.readPoint ℓ.frame (s + 1)) : B = P ∨ B ∈ ℓp.frame.tree := by
  have hS := hs.standalone
  have hr := hS.run.localRun
  have hU := hr.coherent
  have hpH := hs.proposer_mem
  obtain ⟨-, hΦU⟩ := frameIn_of_callAt hr hx hc.1
  obtain ⟨hΨ, hΨU⟩ := frameIn_of_callAt hr hpH hs.call
  obtain ⟨hBt, hst | ⟨P', hP', hP's, hBP'⟩⟩ := hB
  · exact Or.inr (stamped_mem hs hx hc hBt hst)
  rw [frame_slot_eq hs hx hc.1 hP' hP's] at hBP'
  rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hBP' with h | ⟨Y, hBY, hYP⟩
  · exact Or.inl h.symm
  right
  have hd : d.head ∈ ℓp.frame.tree := by
    rw [(acProposal_head hs.payload).2]
    exact getHead_mem' hΨ (fun _ h => h.1) _ _ _ _
  have hYd : Y = d.head := hU.1 (hΦU hYP.1) (hΨU hd)
    (Option.some.inj (hYP.2.2.symm.trans hs.parent))
  rw [hYd] at hBY
  rcases trivial_anc_mem hS hpH hs.call hd (Anc.mono hΦU hBY) with h | h
  · rw [h]; exact hΨ.rooted.1
  · exact trivial_mem_tree hS hpH hs.call (hΦU hBt) (Or.inr h)

/-- `P` has no supporters in the proposal's view (the proposer does not hold it yet). -/
private theorem supporters_P_proposer {s : Nat}
    (hs : UnanimitySetting tr H U schedule g (s + 1) P k ℓp d pay) :
    supporters ℓp.frame (View.ofLists pay) s P = ∅ := by
  have hr := hs.standalone.run.localRun
  obtain ⟨j₀, hkj, hacc, -⟩ := hs.accepted
  refine Set.eq_empty_of_forall_notMem fun w ⟨_, v, _, _, _, R, hR, _, hPR⟩ => ?_
  exact (accept_new sp hr hs.proposer_mem hacc).2 k hkj ℓp hs.call (mem_of_anc hPR hR)

/-- `P` has no slot-`s` supporters in the merged view: a support head has slot at most `s`. -/
private theorem supporters_P_voter {s : Nat}
    (hs : UnanimitySetting tr H U schedule g (s + 1) P k ℓp d pay) {x : Fin sp.n} (hx : x ∈ H)
    {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr x j ℓ e) :
    supporters ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s P = ∅ := by
  obtain ⟨hΦ, -⟩ := frameIn_of_callAt hs.standalone.run.localRun hx hc.1
  refine Set.eq_empty_of_forall_notMem fun w ⟨_, v, hv, _, hvs, R, hR, hRr, hPR⟩ => ?_
  have hle := (Anc.slot_le hΦ.coherent hPR).1
  rw [hs.slot] at hle
  have hRs : R.slot ≤ v.slot := by
    rcases hv with hv | ⟨-, -, -, -, -, H', hH', hH'r, hH's⟩
    · have hres := of_decide_eq_true (List.mem_filter.1 hv).2
      unfold resolutionTime at hres
      split at hres
      · exact absurd hres (not_lt.2 le_top)
      · rename_i Hd hl
        obtain ⟨hHd, hHdr⟩ := lookup_eq_some hl
        split_ifs at hres with hlt
        · exact absurd hres (not_lt.2 le_top)
        · obtain rfl : R = Hd := hΦ.coherent.1 hR hHd (hRr.trans hHdr.symm)
          omega
    · obtain rfl : R = H' := hΦ.coherent.1 hR hH' (hRr.trans hH'r.symm)
      omega
  omega

/-- A block with a strict majority in the proposal's view has an honest supporter (every honest
validator is a voter there, and none is an equivocator). -/
private theorem honest_supporter {s : Nat}
    (hs : UnanimitySetting tr H U schedule g (s + 1) P k ℓp d pay)
    {B : Blk sp.n FGP}
    (h : (voters (View.ofLists pay).votes).ncard <
      2 * goldfishScore sp ℓp.frame (View.ofLists pay) s B) :
    ∃ w ∈ H, w ∈ supporters ℓp.frame (View.ofLists pay) s B := by
  have hS := hs.standalone
  have hrun := hS.run
  have hr := hrun.localRun
  have hpH := hs.proposer_mem
  obtain ⟨hσ, -⟩ := late_prev hs
  have hpay := payload_eq hs
  subst hpay
  have hvot : H ⊆ voters (View.ofLists (voteViewList (tr.state (schedule (s + 1)) k)
      ℓp.frame s ⊤)).votes := by
    intro w hw
    obtain ⟨j', e', hv, hes⟩ := honest_votes_in_slot hS.toHealthyBase hσ w hw
    obtain ⟨ℓw, hcw, hew⟩ := id hv
    exact ⟨e'.msg, (mem_proposalView_votes hr hpH k s ℓp.frame _).2
      (honest_vote_at_proposal hS hpH hs.call hs.time hσ hw hv hes).1,
      (castAt_spec hr hw ⟨hcw, hew⟩).1⟩
  by_contra hno
  have hsub : supporters ℓp.frame (View.ofLists (voteViewList
      (tr.state (schedule (s + 1)) k) ℓp.frame s ⊤)) s B ⊆ Hᶜ :=
    fun w hw hwH => hno ⟨w, hwH, hw⟩
  have heq : equivocators (View.ofLists (voteViewList
      (tr.state (schedule (s + 1)) k) ℓp.frame s ⊤)).votes ⊆ Hᶜ :=
    fun w hw hwH => honest_not_equivocator_proposal hrun hpH k s ℓp.frame hwH hw
  have h1 := Set.ncard_le_ncard (Set.union_subset heq hsub)
  rw [Set.ncard_union_eq (Set.disjoint_left.2 fun w hw hw' => hw'.1 hw)] at h1
  have h2 := Set.ncard_le_ncard hvot
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h3 := hS.healthy.2.2.2
  unfold goldfishScore at h
  omega

/-- A child with a strict majority in the proposal's view is in the voter's viable voter block
tree: its honest supporter's slot-`s` vote extends it (`trivial_viable`). -/
private theorem supported_viable {s : Nat}
    (hs : UnanimitySetting tr H U schedule g (s + 1) P k ℓp d pay) {x : Fin sp.n} (hx : x ∈ H)
    {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr x j ℓ e)
    (hes : e.msg.slot = s + 1) {B : Blk sp.n FGP} {r : Nat} (hBp : B.parent = some r)
    (hmaj : (voters (View.ofLists pay).votes).ncard <
      2 * goldfishScore sp ℓp.frame (View.ofLists pay) s B) :
    B ∈ ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame (s + 1)) := by
  have hS := hs.standalone
  have hrun := hS.run
  have hr := hrun.localRun
  have hpH := hs.proposer_mem
  obtain ⟨hσ, -⟩ := late_prev hs
  obtain ⟨-, hΨU⟩ := frameIn_of_callAt hr hpH hs.call
  obtain ⟨w, hwH, -, v, hv, hvw, hvs, R, hR, hRr, hBR⟩ := honest_supporter hs hmaj
  rw [payload_eq hs] at hv
  have hvp := (mem_proposalView_votes hr hpH k s ℓp.frame v).1 (ofLists_support_subset _ _ _ _ hv)
  obtain ⟨j', -, e', hve, rfl⟩ := hrun.honest.pool_vote _ hpH k s v hvp (hvw ▸ hwH)
  rcases trivial_viable hS hx hc hes hσ ⟨_, hvw ▸ hwH, j', e', hve, by exact_mod_cast hvs, R,
    hΨU hR, hRr, Anc.mono hΨU hBR⟩ with h | h
  · exact h
  · exfalso
    obtain ⟨-, hfc, -, -⟩ := hS.trivial x hx j ℓ hc.1
    rw [hfc] at h
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h with h | ⟨c, -, hp⟩
    · rw [← h, F_parent hS hx hc.1] at hBp
      exact absurd hBp (by simp)
    · have := hp.2.2
      rw [F_parent hS hx hc.1] at this
      exact absurd this (by simp)

/-! ## The canonical walk -/

/-- **The voter's walk is the canonical walk**: at an honest vote of slot `p`, the eligible
children of every block, and their scores, are those of the proposer's viable tree with `P`
added. -/
theorem vote_children_eq (hs : UnanimitySetting tr H U schedule g p P k ℓp d pay) {x : Fin sp.n}
    (hx : x ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr x j ℓ e) (hes : e.msg.slot = p) (X : Blk sp.n FGP) :
    eligibleChildren (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame p))
        (goldfishEligible sp ℓ.frame (tr.time j) (mergedVoteView sp e.readPoint ℓ.frame p)
          ((p : Int) - 1)) X =
      eligibleChildren (insert P (ℓp.frame.viableTree ℓp.frame.tree))
        (goldfishEligible sp ℓp.frame (sp.ts p) (View.ofLists pay) ((p : Int) - 1)) X ∧
    ∀ B ∈ eligibleChildren (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame p))
        (goldfishEligible sp ℓ.frame (tr.time j) (mergedVoteView sp e.readPoint ℓ.frame p)
          ((p : Int) - 1)) X,
      goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame p) ((p : Int) - 1) B =
        goldfishScore sp ℓp.frame (View.ofLists pay) ((p : Int) - 1) B := by
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by have := slot_pos hs; omega⟩
  have hS := hs.standalone
  have hrun := hS.run
  have hr := hrun.localRun
  have hpH := hs.proposer_mem
  obtain ⟨hσ, -⟩ := late_prev hs
  obtain ⟨hPΦ, hpy⟩ := vote_holds hs hx hc hes
  have hsl : sp.slot (tr.time j) = s + 1 := by rw [← (castAt_spec hr hx hc).2.1, hes]
  have hslp : sp.slot (sp.ts (s + 1 : Nat)) = s + 1 := slot_ts (s + 1)
  rw [show ((s + 1 : Nat) : Int) - 1 = s by push_cast; ring]
  obtain ⟨heqv, hvot, hsupp⟩ := view_agree hrun hpH hx rfl
    ⟨hs.call, hs.call_proposal, d, hs.payload⟩ hs.time hc ⟨P, hPΦ, hs.slot, hs.acPayload⟩
    (hS.syncAC (by have := sp.toParams.hΔ; linarith) _)
    (fun Hd hHd _ hst _ => stamped_mem hs hx hc hHd hst)
    (fun v hv Hd hHd hHdr _ => hpy v hv Hd hHd hHdr)
  have hscore : ∀ B ∈ ℓ.frame.tree, B ∈ ℓp.frame.tree →
      goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s B =
        goldfishScore sp ℓp.frame (View.ofLists pay) s B := by
    intro B h1 h2
    unfold goldfishScore
    rw [heqv, hsupp B h2 h1]
  have hscoreP : goldfishScore sp ℓ.frame (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) s P =
      goldfishScore sp ℓp.frame (View.ofLists pay) s P := by
    unfold goldfishScore
    rw [heqv, supporters_P_voter hs hx hc, supporters_P_proposer hs]
  have hPel : ∀ (Φ : Frm sp.n FGP) t V (σ : Int), sp.slot t = s + 1 →
      goldfishEligible sp Φ t V σ P := fun Φ t V σ ht => by
    unfold goldfishEligible
    exact Or.inr (Or.inl (by rw [hs.slot, ht]))
  refine ⟨Set.ext fun B => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨hB, hBp, hel⟩
    by_cases hBP : B = P
    · rw [hBP] at hBp ⊢
      exact ⟨Set.mem_insert _ _, hBp, hPel _ _ _ _ hslp⟩
    have hBt : B ∈ ℓ.frame.tree := hB.1.1
    have hBΨ : B ∈ ℓp.frame.tree := (voterBlock_mem hs hx hc hB.1).resolve_left hBP
    refine ⟨Set.mem_insert_of_mem _ (mem_viableTree hS hpH hs.call subset_rfl hBΨ), hBp, ?_⟩
    rw [eligible_iff hS hx hc.1 hBt hBp, hsl] at hel
    rw [eligible_iff hS hpH hs.call hBΨ hBp, hslp, hvot, ← hscore B hBt hBΨ]
    exact hel
  · rintro ⟨hB, hBp, hel⟩
    by_cases hBP : B = P
    · rw [hBP] at hBp ⊢
      exact ⟨mem_viableTree hS hx hc.1 (fun _ h => h.1)
        ⟨hPΦ, Or.inr ⟨P, hPΦ, hs.slot, Relation.ReflTransGen.refl⟩⟩, hBp, hPel _ _ _ _ hsl⟩
    have hBΨ : B ∈ ℓp.frame.tree := ((Set.mem_insert_iff.1 hB).resolve_left hBP).1
    rw [eligible_iff hS hpH hs.call hBΨ hBp, hslp] at hel
    have hmaj := hel.resolve_left fun h => hBP (frame_slot_eq hs hpH hs.call hBΨ h)
    have hBv := supported_viable hs hx hc hes hBp hmaj
    refine ⟨hBv, hBp, ?_⟩
    rw [eligible_iff hS hx hc.1 hBv.1.1 hBp, hscore B hBv.1.1 hBΨ, ← hvot]
    exact Or.inr hmaj
  · rintro B ⟨hB, -, -⟩
    by_cases hBP : B = P
    · rw [hBP]; exact hscoreP
    · exact hscore B hB.1.1 ((voterBlock_mem hs hx hc hB.1).resolve_left hBP)

end Consensus.Goldilocks.SA

end

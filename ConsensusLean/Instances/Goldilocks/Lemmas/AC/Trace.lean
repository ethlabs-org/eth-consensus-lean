module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Invariant

public section

/-! # Goldilocks AC traces: reachability and one node's life (F.1 (c), A0.7, A0.8)

The AC trace contract gives reachable states; and, over an SA trace, a joined node has been
awake with no restart since the previous slot, erased no recent vote at its restarts, and casts
one vote per slot. -/

namespace Consensus.Goldilocks

namespace ACTrace

variable {P : Params} {FGP : Type} {A : ACInterface P FGP} (tr : ACTrace A)

/-- Before any call of `y`, its state is its initial state. -/
theorem state_of_noCall {y : Fin P.n} {i : Nat} (h : tr.NoCallBetween y 0 i) :
    tr.state y i = tr.init y := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi : tr.state y (i + 1) = tr.state y i := by
      simp only [Trace.state]
      split_ifs with hc
      · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hc.2
        exact absurd ⟨hc.1, hℓ⟩ (h i (Nat.zero_le _) (Nat.lt_succ_self _) ℓ)
      · rfl
    rw [hi]
    exact ih fun k h0 hk ℓ => h k h0 (Nat.lt_succ_of_lt hk) ℓ

/-- After a call of `y` at `j` and no call of `y` in `(j, i)`, its state is that call's
post-state. -/
theorem state_of_lastCall {y : Fin P.n} {j i : Nat} {ℓ : ACLabel A} (hc : tr.CallAt y j ℓ)
    (hji : j < i) (h : tr.NoCallBetween y (j + 1) i) : tr.state y i = tr.post j := by
  induction i with
  | zero => omega
  | succ i ih =>
    simp only [Trace.state]
    by_cases hij : i = j
    · subst hij
      have : tr.node i = y ∧ tr.label i ≠ none := ⟨hc.1, by rw [hc.2]; exact Option.some_ne_none _⟩
      split_ifs
      rfl
    · split_ifs with hn
      · obtain ⟨ℓ', hℓ'⟩ := Option.ne_none_iff_exists'.mp hn.2
        exact absurd ⟨hn.1, hℓ'⟩ (h i (by omega) (Nat.lt_succ_self _) ℓ')
      · exact ih (by omega) fun k hk hk' ℓ' => h k hk (Nat.lt_succ_of_lt hk') ℓ'

/-- Before cut `i`, `y` made no call, or a last call at some `j < i`. -/
theorem noCall_or_lastCall (y : Fin P.n) (i : Nat) :
    tr.NoCallBetween y 0 i ∨
      ∃ j < i, ∃ ℓ, tr.CallAt y j ℓ ∧ tr.NoCallBetween y (j + 1) i := by
  induction i with
  | zero => exact Or.inl fun k _ hk => absurd hk (Nat.not_lt_zero k)
  | succ i ih =>
    by_cases hc : ∃ ℓ, tr.CallAt y i ℓ
    · obtain ⟨ℓ, hℓ⟩ := hc
      exact Or.inr ⟨i, Nat.lt_succ_self _, ℓ, hℓ, fun k hk hk' => absurd hk' (by omega)⟩
    · simp only [not_exists] at hc
      have ext : ∀ a, (∀ k, a ≤ k → k < i → ∀ ℓ, ¬ tr.CallAt y k ℓ) →
          ∀ k, a ≤ k → k < i + 1 → ∀ ℓ, ¬ tr.CallAt y k ℓ := by
        intro a ha k hak hk ℓ
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact ha k hak hk ℓ
        · exact hc ℓ
      rcases ih with h | ⟨j, hj, ℓ, hℓ, h⟩
      · exact Or.inl (ext 0 h)
      · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, ℓ, hℓ, ext (j + 1) h⟩

end ACTrace

/-- The AC trace contract gives reachable states. -/
theorem localRun_reachable : LocalRunReachable := by
  intro P FGP A H U tr h y hy i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro ℓ hc
    have hexec := h.exec i ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at hexec
    have hpost : tr.post i = (A.step y (tr.state y i) ℓ.frame (tr.time i) ℓ.call).1 := by
      rw [hexec]
    rcases h.frameLaw y hy i ℓ hc with ⟨hnone, Φ₀, hinit, hin, hok⟩ | ⟨j, ℓ', hj, hc', hnb, hok⟩
    · rw [hpost, tr.state_of_noCall hnone, h.init y hy]
      exact .step ℓ.call (.init Φ₀ hinit hin) (h.time_nonneg i) hok
    · rw [hpost, tr.state_of_lastCall hc' hj hnb]
      exact .step ℓ.call (ih j hj ℓ' hc') (h.time_mono (Nat.le_of_lt hj)) hok

end Consensus.Goldilocks

namespace Consensus.Goldilocks.SA

variable (sp : SAParams) {FGP : Type}

/-- Every block of an honest node's frame passes `ac_valid_payload`: the initial frame holds
genesis, whose payload is empty, and a frame step adds only the block of an `on_block` call,
which passed the check (the input contract). -/
theorem frame_validPayload {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    ∀ B ∈ ℓ.frame.tree, validPayload B := by
  have step : ∀ (Φ Φ' : Frm sp.n FGP) (t : Time) (c : (goldilocksSA sp FGP ro).Call),
      (goldilocksSA sp FGP ro).CallOK U Φ t c Φ' → (∀ B ∈ Φ.tree, validPayload B) →
      ∀ B ∈ Φ'.tree, validPayload B := by
    intro Φ Φ' t c hok hv X hX
    obtain ⟨-, hc⟩ := hok
    cases c with
    | block B =>
      obtain ⟨hs, hB, -⟩ := hc
      rw [hs.tree_eq] at hX
      rcases hX.1 with rfl | hX
      · exact hB
      · exact hv X hX
    | message m => exact hv X (hc.1 ▸ hX)
    | tick => exact hv X (hc ▸ hX)
    | proposal => exact hv X (hc ▸ hX)
    | toFG => exact hv X (hc ▸ hX)
    | restart => exact hv X (hc ▸ hX)
  induction i using Nat.strong_induction_on generalizing ℓ with
  | _ i ih =>
    rcases h.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, -, -, -, hpay⟩, -, hok⟩ | ⟨j, ℓ', hj, hc', -, hok⟩
    · refine step Φ₀ _ _ _ hok fun B hB => ?_
      rw [htree, Set.mem_singleton_iff] at hB
      subst hB
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩ <;>
        simp [blockVotes, blockSupport, hpay] at hv
    · exact step _ _ _ _ hok (ih j hj hc')

/-- A block between `Φ.F` and a block of a well-formed frame tree (ancestry inside a coherent `U`
containing the tree) is in the tree. -/
theorem frame_mem_of_between {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {A X : Blk sp.n FGP} (hX : X ∈ Φ.tree)
    (hAX : Anc U A X) (hFA : Anc U Φ.F A) : A ∈ Φ.tree := by
  induction hAX with
  | refl => exact hX
  | @tail c d hAc e ih =>
    by_cases hdF : d = Φ.F
    · subst hdF
      have := Anc.antisymm hU (hAc.tail e) hFA
      exact this ▸ hX
    obtain rfl | ⟨p, -, hp⟩ :=
      (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hΦ.rooted.2 d hX)
    · exact absurd rfl hdF
    have hpc : p = c := hU.1 (hΦU hp.1) e.1 (Option.some_injective _ (hp.2.2.symm.trans e.2.2))
    subst hpc
    exact ih hp.1

/-- Across one lawful call, the finalized tip moves only forward (inside `U`) and a block of the
old tree that extends the new tip is in the new tree. -/
theorem callOK_retains {ro : ReplayOrder sp FGP} {U : Set (Blk sp.n FGP)} (hU : Coherent U)
    {Φ Φ' : Frm sp.n FGP} {t : Time} {c : (goldilocksSA sp FGP ro).Call}
    (hΦ : (goldilocksSA sp FGP ro).FrameIn U Φ)
    (hok : (goldilocksSA sp FGP ro).CallOK U Φ t c Φ') :
    Anc U Φ.F Φ'.F ∧ ∀ X ∈ Φ.tree, Anc U Φ'.F X → X ∈ Φ'.tree := by
  obtain ⟨hΦ', hc⟩ := hok
  cases c with
  | block B =>
    obtain ⟨hs, -, -⟩ := hc
    have hBin : B ∈ Φ'.tree := by
      rw [hs.tree_eq]; exact ⟨Set.mem_insert _ _, hs.F'_anc_B⟩
    have hins : insert B Φ.tree ⊆ U := Set.insert_subset (hΦ'.2 hBin) hΦ.2
    refine ⟨hs.F_anc_F'.mono hins, fun X hX hFX => ?_⟩
    have hF'mem : Φ'.F ∈ insert B Φ.tree := by
      have := hΦ'.1.rooted.1; rw [hs.tree_eq] at this; exact this.1
    rw [hs.tree_eq]
    refine ⟨Set.mem_insert_of_mem _ hX, ?_⟩
    rcases hF'mem with hF'B | hF'
    · rw [hF'B] at hFX
      have := frame_mem_of_between sp hU hΦ.1 hΦ.2 hX hFX
        (hF'B ▸ hs.F_anc_F'.mono hins)
      exact absurd this hs.new
    · exact (anc_tree_of_anc_U hU hΦ.1 hΦ.2 hF' hFX hX).mono (Set.subset_insert _ _)
  | message m => obtain ⟨rfl, -⟩ := hc; exact ⟨.refl, fun X hX _ => hX⟩
  | tick => subst hc; exact ⟨.refl, fun X hX _ => hX⟩
  | proposal => subst hc; exact ⟨.refl, fun X hX _ => hX⟩
  | toFG => subst hc; exact ⟨.refl, fun X hX _ => hX⟩
  | restart => subst hc; exact ⟨.refl, fun X hX _ => hX⟩

/-- **Retention between two calls of one node.** For calls of an honest node at `j ≤ i`, the
finalized tip moves forward, and a block of the frame at `j` that extends the tip at `i` is in the
frame at `i`. -/
theorem retain_between {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ℓj : ACLabel (goldilocksSA sp FGP ro)} (hcj : tr.CallAt y j ℓj) :
    ∀ i (ℓ : ACLabel (goldilocksSA sp FGP ro)), tr.CallAt y i ℓ → j ≤ i →
      Anc U ℓj.frame.F ℓ.frame.F ∧ ∀ X ∈ ℓj.frame.tree, Anc U ℓ.frame.F X → X ∈ ℓ.frame.tree := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro ℓ hc hji
    rcases Nat.eq_or_lt_of_le hji with rfl | hji
    · have : ℓ = ℓj := Option.some.inj (hc.2.symm.trans hcj.2)
      subst this
      exact ⟨.refl, fun X hX _ => hX⟩
    rcases h.frameLaw y hy i ℓ hc with ⟨hnone, -⟩ | ⟨j', ℓ', hj', hc', hnb, hok⟩
    · exact absurd hcj (hnone j (Nat.zero_le _) hji ℓj)
    have hjj' : j ≤ j' := by
      by_contra hlt
      exact hnb j (by omega) hji ℓj hcj
    obtain ⟨ihF, ihX⟩ := ih j' hj' ℓ' hc' hjj'
    have hin : (goldilocksSA sp FGP ro).FrameIn U ℓ'.frame := by
      rcases h.frameLaw y hy j' ℓ' hc' with ⟨_, _, _, _, hok'⟩ | ⟨_, _, _, _, _, hok'⟩
      · exact hok'.1
      · exact hok'.1
    obtain ⟨hF, hX⟩ := callOK_retains sp h.coherent hin hok
    exact ⟨ihF.trans hF, fun X hXj hFX => hX X (ihX X hXj (hF.trans hFX)) hFX⟩

/-- **Retention at one node.** A block that an honest node accepted is in the frame of each of its
later calls whose finalized tip it extends (inside `U`): the node's frames evolve by frame steps
inside `U` (G0.3 (frame)), so a block leaves only when `Φ.F` moves past it, and never returns. -/
theorem mem_tree_of_acceptAt {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) {k i : Nat}
    {B : Blk sp.n FGP} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hk : tr.AcceptAt y k B)
    (hki : k ≤ i) (hc : tr.CallAt y i ℓ) (hF : Anc U ℓ.frame.F B) : B ∈ ℓ.frame.tree := by
  obtain ⟨ℓk, hck, hcall⟩ := hk
  have hBk : B ∈ ℓk.frame.tree := by
    rcases h.frameLaw y hy k ℓk hck with ⟨_, _, _, _, hok⟩ | ⟨_, _, _, _, _, hok⟩ <;>
    · obtain ⟨-, hc'⟩ := hok
      rw [hcall] at hc'
      obtain ⟨hs, -, -⟩ := hc'
      rw [hs.tree_eq]; exact ⟨Set.mem_insert _ _, hs.F'_anc_B⟩
  exact (retain_between sp h hy hck i ℓ hc hki).2 B hBk hF

/-- The coherent set of an honest node's frames holds a genesis block (root `genesisRoot`, no
parent): its first call follows an initial frame. -/
theorem genesis_mem_of_call {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) :
    ∀ i (ℓ : ACLabel (goldilocksSA sp FGP ro)), tr.CallAt y i ℓ →
      ∃ G ∈ U, G.root = sp.genesisRoot ∧ G.parent = none := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro ℓ hc
    rcases h.frameLaw y hy i ℓ hc with ⟨-, Φ₀, ⟨htree, hroot, -, hpar, -⟩, hin, -⟩ |
      ⟨j, ℓ', hj, hc', -⟩
    · exact ⟨Φ₀.F, hin.2 (htree ▸ rfl), hroot, hpar⟩
    · exact ih j hj ℓ' hc'

/-- The frame of an honest `on_block(B)` call holds `B`, which is in no frame of the node's
earlier calls (it is new, and frames retain what extends their finalized tip). -/
theorem accept_new {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {B : Blk sp.n FGP} (ha : tr.AcceptAt y i B) :
    (∀ ℓ, tr.CallAt y i ℓ → B ∈ ℓ.frame.tree) ∧
      ∀ k < i, ∀ ℓk, tr.CallAt y k ℓk → B ∉ ℓk.frame.tree := by
  obtain ⟨ℓ, hc, hcall⟩ := ha
  have hok : ∃ Φ, (goldilocksSA sp FGP ro).CallOK U Φ (tr.time i) ℓ.call ℓ.frame ∧
      ((∀ k < i, ∀ ℓk, ¬ tr.CallAt y k ℓk) ∨ ∃ j < i, ∃ ℓj, tr.CallAt y j ℓj ∧
        tr.NoCallBetween y (j + 1) i ∧ Φ = ℓj.frame) := by
    rcases h.frameLaw y hy i ℓ hc with ⟨hn, Φ₀, -, -, hok⟩ | ⟨j, ℓ', hj, hc', hnb, hok⟩
    · exact ⟨Φ₀, hok, Or.inl fun k hk ℓk => hn k (Nat.zero_le _) hk ℓk⟩
    · exact ⟨ℓ'.frame, hok, Or.inr ⟨j, hj, ℓ', hc', hnb, rfl⟩⟩
  obtain ⟨Φ, hok, hprev⟩ := hok
  have hs : FrameStep Φ B ℓ.frame := by
    have := hok.2; rw [hcall] at this; exact this.1
  have hBin : B ∈ ℓ.frame.tree := by
    rw [hs.tree_eq]; exact ⟨Set.mem_insert _ _, hs.F'_anc_B⟩
  refine ⟨fun ℓ' hc' => (Option.some.inj (hc'.2.symm.trans hc.2)) ▸ hBin,
    fun k hk ℓk hck hBk => ?_⟩
  rcases hprev with hn | ⟨j, hj, ℓj, hcj, hnb, rfl⟩
  · exact hn k hk ℓk hck
  have hkj : k ≤ j := by
    by_contra hlt
    exact hnb k (by omega) hk ℓk hck
  have hinj : (goldilocksSA sp FGP ro).FrameIn U ℓj.frame := by
    rcases h.frameLaw y hy j ℓj hcj with ⟨_, _, _, _, hok'⟩ | ⟨_, _, _, _, _, hok'⟩ <;>
      exact hok'.1
  have hFF := (callOK_retains sp h.coherent hinj hok).1
  have hFB : Anc U ℓ.frame.F B := (hok.1.1.rooted.2 B hBin).mono hok.1.2
  exact hs.new ((retain_between sp h hy hck j ℓj hcj hkj).2 B hBk (hFF.trans hFB))

/-- An honest node accepts a block at most once. -/
theorem accept_unique {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) {k k' : Nat}
    {B : Blk sp.n FGP} (hk : tr.AcceptAt y k B) (hk' : tr.AcceptAt y k' B) : k = k' := by
  rcases lt_trichotomy k k' with hlt | heq | hlt
  · obtain ⟨ℓ, hc, hcl⟩ := hk
    exact absurd ((accept_new sp h hy ⟨ℓ, hc, hcl⟩).1 ℓ hc) ((accept_new sp h hy hk').2 k hlt ℓ hc)
  · exact heq
  · obtain ⟨ℓ, hc, hcl⟩ := hk'
    exact absurd ((accept_new sp h hy ⟨ℓ, hc, hcl⟩).1 ℓ hc) ((accept_new sp h hy hk).2 k' hlt ℓ hc)

/-- An honest node never accepts a block with the genesis root. -/
theorem accept_ne_genesis {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    {B : Blk sp.n FGP} (hk : tr.AcceptAt y k B) : B.root ≠ sp.genesisRoot := by
  intro hg
  obtain ⟨ℓ, hc, hcall⟩ := hk
  obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_of_call sp h hy k ℓ hc
  have hBU : B ∈ U := (by
    rcases h.frameLaw y hy k ℓ hc with ⟨_, _, _, _, hok⟩ | ⟨_, _, _, _, _, hok⟩ <;>
      exact hok.1.2 ((accept_new sp h hy ⟨ℓ, hc, hcall⟩).1 ℓ hc))
  have hBG : B = G := h.coherent.1 hBU hGU (hg.trans hGr.symm)
  have hpar : ∃ P : Blk sp.n FGP, B.parent = some P.root := by
    rcases h.frameLaw y hy k ℓ hc with ⟨_, _, _, _, hok⟩ | ⟨_, _, _, _, _, hok⟩ <;>
    · have := hok.2; rw [hcall] at this
      obtain ⟨P, -, hP⟩ := this.1.parent_mem
      exact ⟨P, hP⟩
  obtain ⟨P, hP⟩ := hpar
  rw [hBG, hGp] at hP
  exact absurd hP (by simp)

/-- Every block of an honest node's frame at a call is of slot `0` (genesis), or the node
accepted it at that call or an earlier one. -/
theorem frame_genesis_or_accepted {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    ∀ B ∈ ℓ.frame.tree, B.slot = 0 ∨ ∃ k ≤ i, tr.AcceptAt y k B := by
  induction i using Nat.strong_induction_on generalizing ℓ with
  | _ i ih =>
    have step : ∀ Φ : Frm sp.n FGP,
        (goldilocksSA sp FGP ro).CallOK U Φ (tr.time i) ℓ.call ℓ.frame →
        (∀ B ∈ Φ.tree, B.slot = 0 ∨ ∃ k ≤ i, tr.AcceptAt y k B) →
        ∀ B ∈ ℓ.frame.tree, B.slot = 0 ∨ ∃ k ≤ i, tr.AcceptAt y k B := by
      intro Φ hok hv X hX
      obtain ⟨-, hm⟩ := hok
      generalize hcall : ℓ.call = c at hm
      cases c with
      | block B =>
        rw [hm.1.tree_eq] at hX
        rcases hX.1 with rfl | hX
        · exact Or.inr ⟨i, le_rfl, ℓ, hc, hcall⟩
        · exact hv X hX
      | message m => exact hv X (hm.1 ▸ hX)
      | tick => exact hv X (hm ▸ hX)
      | proposal => exact hv X (hm ▸ hX)
      | toFG => exact hv X (hm ▸ hX)
      | restart => exact hv X (hm ▸ hX)
    rcases hr.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, -, hslot, -, -⟩, -, hok⟩ | ⟨j, ℓ', hj, hc', -, hok⟩
    · refine step Φ₀ hok fun B hB => ?_
      rw [htree, Set.mem_singleton_iff] at hB
      subst hB
      exact Or.inl hslot
    · exact step _ hok fun B hB =>
        (ih j hj hc' B hB).imp_right fun ⟨k, hk, h⟩ => ⟨k, hk.trans hj.le, h⟩

/-- The stamp of a block of an honest node's frame after a call: `−∞` (genesis), the time of the
node's acceptance of the block, or the time of one of its restarts, at or before the call. -/
private theorem stamp_cases {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) :
    ∀ i (ℓ : ACLabel (goldilocksSA sp FGP ro)), tr.CallAt y i ℓ → ∀ X ∈ ℓ.frame.tree,
      (tr.post i).blockStamp X.root = ⊥ ∨
        (∃ k ≤ i, tr.AcceptAt y k X ∧ (tr.post i).blockStamp X.root = ETime.of (tr.time k)) ∨
        (∃ r ≤ i, tr.RestartAt y r ∧ (tr.post i).blockStamp X.root = ETime.of (tr.time r)) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro ℓ hc X hX
    have hexec := h.exec i ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at hexec
    have hpost : tr.post i =
        ((goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i) ℓ.call).1 := by
      rw [hexec]
    -- the previous frame and the invariant for it, in the state before the call
    obtain ⟨Φ, hok, hpre⟩ : ∃ Φ, (goldilocksSA sp FGP ro).CallOK U Φ (tr.time i) ℓ.call ℓ.frame ∧
        ∀ X ∈ Φ.tree, (tr.state y i).blockStamp X.root = ⊥ ∨
          (∃ k ≤ i, tr.AcceptAt y k X ∧
            (tr.state y i).blockStamp X.root = ETime.of (tr.time k)) ∨
          (∃ r ≤ i, tr.RestartAt y r ∧
            (tr.state y i).blockStamp X.root = ETime.of (tr.time r)) := by
      rcases h.frameLaw y hy i ℓ hc with ⟨hn, Φ₀, ⟨htree, hroot, -, -, -⟩, -, hok⟩ |
        ⟨j, ℓ', hj, hc', hnb, hok⟩
      · refine ⟨Φ₀, hok, fun X hX => Or.inl ?_⟩
        rw [htree, Set.mem_singleton_iff] at hX
        rw [tr.state_of_noCall hn, h.init y hy, hX, hroot]
        change (if sp.genesisRoot = sp.genesisRoot then ⊥ else ⊤) = (⊥ : ETime)
        simp only [ite_true]
      · refine ⟨ℓ'.frame, hok, fun X hX => ?_⟩
        rw [tr.state_of_lastCall hc' hj hnb]
        rcases ih j hj ℓ' hc' X hX with h0 | ⟨k, hk, h1, h2⟩ | ⟨r, hr, h1, h2⟩
        · exact Or.inl h0
        · exact Or.inr (Or.inl ⟨k, hk.trans hj.le, h1, h2⟩)
        · exact Or.inr (Or.inr ⟨r, hr.trans hj.le, h1, h2⟩)
    have hΦ' := hok.1
    obtain ⟨hblk, hrst, hoth⟩ := step_blockStamp_eq ro y (tr.state y i) hΦ'.1
      (h.time_nonneg i) ℓ.call
    rw [hpost]
    generalize hcall : ℓ.call = c at hok hblk hrst hoth
    cases c with
    | block B =>
      rw [hblk B rfl, Function.update_apply]
      obtain ⟨hin, hs, -, -⟩ := hok
      split_ifs with hXB
      · have : X = B := hin.1.coherent.1 hX (by
          rw [hs.tree_eq]; exact ⟨Set.mem_insert _ _, hs.F'_anc_B⟩) hXB
        subst this
        exact Or.inr (Or.inl ⟨i, le_rfl, ⟨ℓ, hc, hcall⟩, rfl⟩)
      · rw [hs.tree_eq] at hX
        rcases hX.1 with rfl | hX'
        · exact absurd rfl hXB
        · exact hpre X hX'
    | restart =>
      rw [hrst rfl X hX]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨i, le_rfl, ⟨ℓ, hc, hcall⟩, rfl⟩)
    | tick => rw [hoth (fun _ => by simp) (by simp)]; exact hpre X (hok.2 ▸ hX)
    | proposal => rw [hoth (fun _ => by simp) (by simp)]; exact hpre X (hok.2 ▸ hX)
    | toFG => rw [hoth (fun _ => by simp) (by simp)]; exact hpre X (hok.2 ▸ hX)
    | message m => rw [hoth (fun _ => by simp) (by simp)]; exact hpre X (hok.2.1 ▸ hX)

/-- **Stamps of accepted blocks.** At an honest node's call, a block of the call's frame that the
node accepted before `T` (or genesis) has a stamp below `T` in the state before the call, when
every restart of the node up to the call was before `T` and the call does not itself accept the
block (it is at or after `T`, or not `on_block(B)`): the stamp of a block is written only when
the node accepts it (once) and by a restart's replay (A0.7). -/
theorem blockStamp_lt_of_acceptedBefore {ro : ReplayOrder sp FGP}
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) {B : Blk sp.n FGP}
    (hB : B ∈ ℓ.frame.tree) {T : Time} (hacc : AcceptedBefore tr y B T)
    (hrs : ∀ k ≤ i, tr.RestartAt y k → tr.time k < T)
    (hi : T ≤ tr.time i ∨ ℓ.call ≠ .block B) :
    (tr.state y i).blockStamp B.root < ETime.of T := by
  have hlt : ∀ t, t < T → ETime.of t < ETime.of T := fun t ht =>
    WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr ht)
  have hbot : (⊥ : ETime) < ETime.of T := WithBot.bot_lt_coe _
  -- the call does not accept `B`
  have hnot : ℓ.call ≠ .block B := by
    rcases hi with hTi | hne
    · intro hcall
      have hai : tr.AcceptAt y i B := ⟨ℓ, hc, hcall⟩
      rcases hacc with hg | ⟨k, hk, hkT⟩
      · exact accept_ne_genesis sp h hy hai hg
      · have := accept_unique sp h hy hk hai
        subst this
        exact absurd (lt_of_lt_of_le hkT hTi) (lt_irrefl _)
    · exact hne
  rcases tr.noCall_or_lastCall y i with hn | ⟨j, hj, ℓj, hcj, hnb⟩
  · -- no earlier call: the frame of the first call grows from `{genesis}`
    rw [tr.state_of_noCall hn, h.init y hy]
    rcases h.frameLaw y hy i ℓ hc with ⟨-, Φ₀, ⟨htree, hroot, -, -, -⟩, -, hok⟩ |
      ⟨j, ℓ', hj, hc', -⟩
    · have hBΦ : B ∈ Φ₀.tree := by
        obtain ⟨-, hm⟩ := hok
        generalize hcall : ℓ.call = c at hm hnot
        cases c with
        | block B' =>
          rw [hm.1.tree_eq] at hB
          rcases hB.1 with rfl | hB'
          · exact absurd rfl hnot
          · exact hB'
        | message m => exact hm.1 ▸ hB
        | tick => exact hm ▸ hB
        | proposal => exact hm ▸ hB
        | toFG => exact hm ▸ hB
        | restart => exact hm ▸ hB
      rw [htree, Set.mem_singleton_iff] at hBΦ
      rw [hBΦ, hroot]
      change (if sp.genesisRoot = sp.genesisRoot then ⊥ else ⊤) < ETime.of T
      simp only [ite_true]; exact hbot
    · exact absurd hc' (hn j (Nat.zero_le _) hj ℓ')
  · rw [tr.state_of_lastCall hcj hj hnb]
    have hBj : B ∈ ℓj.frame.tree := by
      rcases h.frameLaw y hy i ℓ hc with ⟨hn', -⟩ | ⟨j', ℓ', hj', hc', hnb', hok⟩
      · exact absurd hcj (hn' j (Nat.zero_le _) hj ℓj)
      have hjj : j' = j := by
        rcases lt_trichotomy j' j with h1 | h1 | h1
        · exact absurd hcj (hnb' j (by omega) hj ℓj)
        · exact h1
        · exact absurd hc' (hnb j' (by omega) hj' ℓ')
      subst hjj
      have : ℓ' = ℓj := Option.some.inj (hc'.2.symm.trans hcj.2)
      subst this
      obtain ⟨-, hm⟩ := hok
      generalize hcall : ℓ.call = c at hm hnot
      cases c with
      | block B' =>
        rw [hm.1.tree_eq] at hB
        rcases hB.1 with rfl | hB'
        · exact absurd rfl hnot
        · exact hB'
      | message m => exact hm.1 ▸ hB
      | tick => exact hm ▸ hB
      | proposal => exact hm ▸ hB
      | toFG => exact hm ▸ hB
      | restart => exact hm ▸ hB
    rcases stamp_cases sp h hy j ℓj hcj B hBj with h0 | ⟨k, -, hk, h1⟩ | ⟨r, hr, hrr, h1⟩
    · rw [h0]; exact hbot
    · rw [h1]
      rcases hacc with hg | ⟨k', hk', hkT⟩
      · exact absurd hg (accept_ne_genesis sp h hy hk)
      · rw [accept_unique sp h hy hk hk']; exact hlt _ hkT
    · rw [h1]; exact hlt _ (hrs r (hr.trans hj.le) hrr)

/-- **The state before a cut is initial or reachable.** The state of an honest node before cut `i`
is the initial state (no call yet), or reachable inside `U` with the frame and the time of its
last call before `i` (which is at or before the time of cut `i`). -/
theorem state_reachable {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    tr.state y i = SAState.initial sp.genesisRoot ∨
      ∃ Φ t, (goldilocksSA sp FGP ro).ReachableAt y U (tr.state y i) Φ t ∧ t ≤ tr.time i := by
  rcases tr.noCall_or_lastCall y i with hnone | ⟨j, hj, ℓ, hc, hnb⟩
  · exact Or.inl ((tr.state_of_noCall hnone).trans (h.init y hy))
  · rw [tr.state_of_lastCall hc hj hnb]
    exact Or.inr ⟨ℓ.frame, tr.time j, localRun_reachable _ _ _ _ _ tr h y hy j ℓ hc,
      h.time_mono (Nat.le_of_lt hj)⟩

/-- The slot-`σ` pool of an honest node's state before any cut holds only slot-`σ` votes. -/
theorem state_pool_slot {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) (i σ : Nat) :
    ∀ v ∈ (tr.state y i).pool σ, v.slot = σ := by
  rcases state_reachable sp h hy i with h0 | ⟨Φ, t, hr, -⟩
  · rw [h0]; intro v hv; simp [SAState.initial] at hv
  · exact (pool_cap sp FGP ro y U h.coherent _ Φ t hr σ).1

/-- The blocks of an honest call's frame are not of a future slot: the initial frame holds
genesis, of slot `0`, and a frame step adds only the block of an `on_block` call, which is not of
a future slot (the input contract); calls are at nondecreasing times from `0`. -/
theorem frame_slot_le {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    ∀ B ∈ ℓ.frame.tree, B.slot ≤ sp.slot (tr.time i) := by
  induction i using Nat.strong_induction_on generalizing ℓ with
  | _ i ih =>
    have step : ∀ (Φ : Frm sp.n FGP) (c : (goldilocksSA sp FGP ro).Call),
        (goldilocksSA sp FGP ro).CallOK U Φ (tr.time i) c ℓ.frame →
        (∀ B ∈ Φ.tree, B.slot ≤ sp.slot (tr.time i)) →
        ∀ B ∈ ℓ.frame.tree, B.slot ≤ sp.slot (tr.time i) := by
      intro Φ c hok hv X hX
      obtain ⟨-, hc'⟩ := hok
      cases c with
      | block B =>
        obtain ⟨hs, -, hB⟩ := hc'
        rw [hs.tree_eq] at hX
        rcases hX.1 with rfl | hX
        · exact hB
        · exact hv X hX
      | message m => exact hv X (hc'.1 ▸ hX)
      | tick => exact hv X (hc' ▸ hX)
      | proposal => exact hv X (hc' ▸ hX)
      | toFG => exact hv X (hc' ▸ hX)
      | restart => exact hv X (hc' ▸ hX)
    rcases h.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, -, hslot, -, -⟩, -, hok⟩ | ⟨j, ℓ', hj, hc', -, hok⟩
    · refine step Φ₀ _ hok fun B hB => ?_
      rw [htree, Set.mem_singleton_iff] at hB
      subst hB
      rw [hslot]; exact Nat.zero_le _
    · refine step _ _ hok fun B hB => ?_
      exact le_trans (ih j hj hc' B hB)
        (slot_mono sp (h.time_nonneg j) (h.time_mono (Nat.le_of_lt hj)))

/-! ### One vote per slot (A0.8)

Only `try_vote` emits, at most one vote, of slot `slot(t)`, from a joined state with
`voted_slot ≠ slot(t)`, and it writes `voted_slot ← slot(t)`; every other call keeps `voted_slot`
and `restart_time`, except the restart, which emits nothing and writes `restart_time ← t`. -/

section OneVote

variable {sp}

/-- A call from `A` at `t` that is not a restart, to `A'` with the emissions `es`: it keeps
`restart_time`, keeps `voted_slot` or sets it to `slot(t)`, and emits at most one vote, of slot
`slot(t)`, only from a joined `A` with `voted_slot ≠ slot(t)`, after which `voted_slot = slot(t)`.
-/
private def VoteStep (A A' : SAState sp.n) (es : List (Em sp FGP)) (t : Time) : Prop :=
  A'.restartTime = A.restartTime ∧
    (A'.votedSlot = A.votedSlot ∨ A'.votedSlot = sp.slot t) ∧ es.length ≤ 1 ∧
    ∀ e ∈ es, e.msg.slot = sp.slot t ∧ joined sp A t ∧ A.votedSlot ≠ sp.slot t ∧
      A'.votedSlot = sp.slot t

private theorem VoteStep.refl (A : SAState sp.n) (t : Time) :
    VoteStep (FGP := FGP) A A [] t :=
  ⟨rfl, Or.inl rfl, Nat.zero_le _, fun _ h => absurd h List.not_mem_nil⟩

private theorem VoteStep.pre {A B A' : SAState sp.n} {es : List (Em sp FGP)} {t : Time}
    (h : VoteStep B A' es t) (hv : B.votedSlot = A.votedSlot)
    (hr : B.restartTime = A.restartTime) : VoteStep A A' es t := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  refine ⟨h₁.trans hr, hv ▸ h₂, h₃, fun e he => ?_⟩
  obtain ⟨e₁, e₂, e₃, e₄⟩ := h₄ e he
  exact ⟨e₁, by unfold joined at e₂ ⊢; rwa [← hr], hv ▸ e₃, e₄⟩

private theorem VoteStep.post {A A' A'' : SAState sp.n} {es : List (Em sp FGP)} {t : Time}
    (h : VoteStep A A' es t) (hv : A''.votedSlot = A'.votedSlot)
    (hr : A''.restartTime = A'.restartTime) : VoteStep A A'' es t := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  exact ⟨hr.trans h₁, hv ▸ h₂, h₃, fun e he => hv ▸ h₄ e he⟩

private theorem admitVote_keeps (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).votedSlot = A.votedSlot ∧
      (admitVote sp A t v).restartTime = A.restartTime := by
  unfold admitVote
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem updateLatestConfirmed_keeps (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (C : Blk sp.n FGP) : (updateLatestConfirmed sp A Φ C).votedSlot = A.votedSlot ∧
      (updateLatestConfirmed sp A Φ C).restartTime = A.restartTime := by
  unfold updateLatestConfirmed
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem optimistic_keeps (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).votedSlot = A.votedSlot ∧
      (optimisticConfirmation sp A Φ t).restartTime = A.restartTime := by
  unfold optimisticConfirmation
  split
  · exact ⟨rfl, rfl⟩
  · exact updateLatestConfirmed_keeps _ _ _

private theorem updateConfirmation_keeps (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : (updateConfirmation sp A Φ t s).votedSlot = A.votedSlot ∧
      (updateConfirmation sp A Φ t s).restartTime = A.restartTime := by
  unfold updateConfirmation
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · split_ifs
    · exact ⟨rfl, rfl⟩
    · exact updateLatestConfirmed_keeps _ _ _

private theorem blockReceipt_keeps (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).votedSlot = A.votedSlot ∧
      (blockReceipt sp A t B).restartTime = A.restartTime := by
  unfold blockReceipt
  generalize blockVotes B = l
  suffices h : ∀ A' : SAState sp.n,
      (l.foldl (fun A v => admitVote sp A t v) A').votedSlot = A'.votedSlot ∧
      (l.foldl (fun A v => admitVote sp A t v) A').restartTime = A'.restartTime from
    h { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) }
  induction l with
  | nil => exact fun _ => ⟨rfl, rfl⟩
  | cons v l ih =>
    intro A'
    simp only [List.foldl_cons]
    exact ⟨(ih _).1.trans (admitVote_keeps _ _ _).1, (ih _).2.trans (admitVote_keeps _ _ _).2⟩

private theorem tryVote_voteStep (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : VoteStep A (tryVote sp self A Φ t).1 (tryVote sp self A Φ t).2 t := by
  unfold tryVote
  dsimp only
  split_ifs with h₁ h₂
  · exact VoteStep.refl A t
  · exact VoteStep.refl A t
  all_goals
    simp only [not_or, not_not, not_lt] at h₁
    obtain ⟨hj, hv, -⟩ := h₁
    have k₁ := fun A₁ v => ((optimistic_keeps (admitVote sp A₁ t v) Φ t).1.trans
      (admitVote_keeps A₁ t v).1)
    have k₂ := fun A₁ v => ((optimistic_keeps (admitVote sp A₁ t v) Φ t).2.trans
      (admitVote_keeps A₁ t v).2)
    refine ⟨k₂ _ _, Or.inr (k₁ _ _), by simp, fun e he => ?_⟩
    rw [List.mem_singleton] at he
    subst he
    exact ⟨rfl, hj, hv, k₁ _ _⟩

private theorem acOnMessage_voteStep (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (v : Vote sp.n) :
    VoteStep A (acOnMessage sp self A Φ t v).1 (acOnMessage sp self A Φ t v).2 t :=
  (tryVote_voteStep _ _ _ _).pre
    ((optimistic_keeps _ _ _).1.trans (admitVote_keeps _ _ _).1)
    ((optimistic_keeps _ _ _).2.trans (admitVote_keeps _ _ _).2)

private theorem acOnBlock_voteStep (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (B : Blk sp.n FGP) :
    VoteStep A (acOnBlock sp self A Φ t B).1 (acOnBlock sp self A Φ t B).2 t :=
  (tryVote_voteStep _ _ _ _).pre
    ((optimistic_keeps _ _ _).1.trans (blockReceipt_keeps _ _ _).1)
    ((optimistic_keeps _ _ _).2.trans (blockReceipt_keeps _ _ _).2)

private theorem acOnTick_voteStep (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : VoteStep A (acOnTick sp self A Φ t).1 (acOnTick sp self A Φ t).2 t := by
  unfold acOnTick
  dsimp only
  have hr : VoteStep A
      (if t = sp.ts (sp.slot t) + sp.Δ then tryVote sp self A Φ t else (A, [])).1
      (if t = sp.ts (sp.slot t) + sp.Δ then tryVote sp self A Φ t else (A, [])).2 t := by
    split_ifs
    · exact tryVote_voteStep _ _ _ _
    · exact VoteStep.refl A t
  generalize (if t = sp.ts (sp.slot t) + sp.Δ then tryVote sp self A Φ t else (A, [])) = r at hr ⊢
  split_ifs
  · exact hr.post (updateConfirmation_keeps _ _ _ _).1 (updateConfirmation_keeps _ _ _ _).2
  · exact hr
  · exact VoteStep.refl A t

private theorem acProposal_keeps (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acProposal sp A Φ t).1.votedSlot = A.votedSlot ∧
      (acProposal sp A Φ t).1.restartTime = A.restartTime := by
  unfold acProposal
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem acToFG_keeps (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acToFG sp A Φ t).1.votedSlot = A.votedSlot ∧
      (acToFG sp A Φ t).1.restartTime = A.restartTime := by
  unfold acToFG
  dsimp only
  split_ifs
  · split
    · exact ⟨rfl, rfl⟩
    · split_ifs <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- One call from `A` at `t ≥ 0` with a well-formed frame, to `A'` with the emissions `es`: a
restart, which emits nothing and writes `restart_time ← t`, or a `VoteStep`. -/
private theorem step_voteStep {ro : ReplayOrder sp FGP} (self : Fin sp.n) {A A' : SAState sp.n}
    {Φ : Frm sp.n FGP} {t : Time} (hΦ : FrameOK Φ) (ht : 0 ≤ t)
    (c : (goldilocksSA sp FGP ro).Call) {es : List (Em sp FGP)}
    (hs : (goldilocksSA sp FGP ro).step self A Φ t c = (A', es)) :
    (es = [] ∧ A'.restartTime = (t : WithBot Time)) ∨ VoteStep A A' es t := by
  have h₁ := congrArg Prod.fst hs
  have h₂ := congrArg Prod.snd hs
  dsimp only at h₁ h₂
  subst h₁ h₂
  cases c with
  | tick => exact Or.inr (acOnTick_voteStep _ _ _ _)
  | proposal =>
    exact Or.inr ((VoteStep.refl A t).post (acProposal_keeps _ _ _).1 (acProposal_keeps _ _ _).2)
  | toFG => exact Or.inr ((VoteStep.refl A t).post (acToFG_keeps _ _ _).1 (acToFG_keeps _ _ _).2)
  | message m => exact Or.inr (acOnMessage_voteStep _ _ _ _ _)
  | block B => exact Or.inr (acOnBlock_voteStep _ _ _ _ _)
  | restart =>
    obtain ⟨he, -, -, -, -, -, hr, -⟩ := restart_state sp FGP ro self A Φ t hΦ ht
    exact Or.inl ⟨he, hr⟩

variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
  {tr : SATrace sp FGP ro}

/-- An honest call at cut `i`: a restart at `time i` that emits nothing, or a `VoteStep`. -/
private theorem call_voteStep (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    (ℓ.emits = [] ∧ (tr.post i).restartTime = (tr.time i : WithBot Time)) ∨
      VoteStep (tr.state y i) (tr.post i) ℓ.emits (tr.time i) := by
  have hexec := h.exec i ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at hexec
  have hΦ : FrameOK ℓ.frame := by
    rcases h.frameLaw y hy i ℓ hc with ⟨-, _, -, -, hok⟩ | ⟨_, _, -, -, -, hok⟩ <;> exact hok.1.1
  exact step_voteStep y hΦ (h.time_nonneg i) ℓ.call hexec

/-- A vote of an honest node at cut `k` is of slot `slot(time k)`, from a joined state with
`voted_slot ≠ slot(time k)`, after which `voted_slot = slot(time k)`. -/
private theorem voteAt_spec (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {e : Em sp FGP} (hv : VoteAt tr y k e) :
    e.msg.slot = sp.slot (tr.time k) ∧ joined sp (tr.state y k) (tr.time k) ∧
      (tr.state y k).votedSlot ≠ sp.slot (tr.time k) ∧
      (tr.post k).votedSlot = sp.slot (tr.time k) := by
  obtain ⟨ℓ, hc, he⟩ := hv
  rcases call_voteStep h hy hc with ⟨hn, -⟩ | hs
  · rw [hn] at he; exact absurd he List.not_mem_nil
  · exact hs.2.2.2 e he

/-- After an honest vote of slot `σ` at cut `k < i`, the state of the node before cut `i` still
has `voted_slot = σ`, or cut `i` is of a later slot, or the node restarted at or after the vote. -/
private theorem after_vote (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) : ∀ k < i, ∀ e, VoteAt tr y k e →
      (tr.state y i).votedSlot = e.msg.slot ∨ e.msg.slot < sp.slot (tr.time i) ∨
        ∃ w : Time, (tr.state y i).restartTime = (w : WithBot Time) ∧ tr.time k ≤ w := by
  induction i with
  | zero => intro k hk; omega
  | succ i ih =>
    intro k hk e hv
    have hmono : sp.slot (tr.time i) ≤ sp.slot (tr.time (i + 1)) :=
      slot_mono sp (h.time_nonneg i) (h.time_mono (Nat.le_succ i))
    have hslot := (voteAt_spec h hy hv).1
    by_cases hcall : tr.node i = y ∧ tr.label i ≠ none
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hcall.2
      have hc : tr.CallAt y i ℓ := ⟨hcall.1, hℓ⟩
      have hst : tr.state y (i + 1) = tr.post i := by
        simp only [Trace.state]; exact ite_eq_left hcall
      rw [hst]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · have hki := h.time_mono (Nat.le_of_lt hk)
        rcases call_voteStep h hy hc with ⟨-, hr⟩ | ⟨hr, hv', -, -⟩
        · exact Or.inr (Or.inr ⟨_, hr, hki⟩)
        · rcases ih k hk e hv with h₁ | h₂ | ⟨w, hw, hkw⟩
          · rcases hv' with hv' | hv'
            · exact Or.inl (hv'.trans h₁)
            · have := slot_mono sp (h.time_nonneg k) hki
              rcases Nat.lt_or_eq_of_le (hslot ▸ this) with hlt | heq
              · exact Or.inr (Or.inl (lt_of_lt_of_le hlt hmono))
              · exact Or.inl (by rw [hv', heq])
          · exact Or.inr (Or.inl (lt_of_lt_of_le h₂ hmono))
          · exact Or.inr (Or.inr ⟨w, hr.trans hw, hkw⟩)
      · exact Or.inl (by rw [(voteAt_spec h hy hv).2.2.2, hslot])
    · have hst : tr.state y (i + 1) = tr.state y i := by
        simp only [Trace.state]; exact ite_eq_right hcall
      rw [hst]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rcases ih k hk e hv with h₁ | h₂ | h₃
        · exact Or.inl h₁
        · exact Or.inr (Or.inl (lt_of_lt_of_le h₂ hmono))
        · exact Or.inr (Or.inr h₃)
      · obtain ⟨ℓ, hc, -⟩ := hv
        exact absurd ⟨hc.1, by rw [hc.2]; exact Option.some_ne_none _⟩ hcall

/-- Two votes of an honest node at cuts `k < i` are of different slots. -/
private theorem vote_slot_ne (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {k i : Nat} (hki : k < i) {e e' : Em sp FGP} (hv : VoteAt tr y k e)
    (hv' : VoteAt tr y i e') : e.msg.slot ≠ e'.msg.slot := by
  intro hσ
  obtain ⟨hs', hj', hne', -⟩ := voteAt_spec h hy hv'
  have hs := (voteAt_spec h hy hv).1
  rcases after_vote h hy i k hki e hv with h₁ | h₂ | ⟨w, hw, hkw⟩
  · exact hne' (by rw [h₁, hσ, hs'])
  · omega
  · unfold joined at hj'
    rw [hw, WithBot.coe_le_coe] at hj'
    have h₁ : sp.ts (sp.slot (tr.time k)) ≤ tr.time k :=
      (ts_le_iff_le_slot sp (h.time_nonneg k) _).mpr le_rfl
    have h₂ : sp.ts ((sp.slot (tr.time i) : Int) - 1) < sp.ts (sp.slot (tr.time k)) :=
      (ts_lt_iff sp).mpr (by omega)
    exact absurd (lt_of_lt_of_le h₂ (h₁.trans (hkw.trans hj'))) (lt_irrefl _)

/-- A call that is not a restart keeps `restart_time`. -/
private theorem step_restartTime {ro : ReplayOrder sp FGP} (self : Fin sp.n) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (c : (goldilocksSA sp FGP ro).Call) (hc : c ≠ .restart) :
    ((goldilocksSA sp FGP ro).step self A Φ t c).1.restartTime = A.restartTime := by
  cases c with
  | tick => exact (acOnTick_voteStep self A Φ t).1
  | proposal => exact (acProposal_keeps A Φ t).2
  | toFG => exact (acToFG_keeps A Φ t).2
  | message m => exact (acOnMessage_voteStep self A Φ t m).1
  | block B => exact (acOnBlock_voteStep self A Φ t B).1
  | restart => exact absurd rfl hc

/-- After an honest call at `i`, `restart_time` is at least the time of every restart of the node
at a cut `≤ i`. -/
private theorem restartTime_ge (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) : ∀ i (ℓ : ACLabel (goldilocksSA sp FGP ro)), tr.CallAt y i ℓ →
      ∀ j ≤ i, tr.RestartAt y j → (tr.time j : WithBot Time) ≤ (tr.post i).restartTime := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro ℓ hc j hji hj
    have hexec := h.exec i ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at hexec
    have hΦ : FrameOK ℓ.frame := by
      rcases h.frameLaw y hy i ℓ hc with ⟨-, _, -, -, hok⟩ | ⟨_, _, -, -, -, hok⟩ <;>
        exact hok.1.1
    have hpost : tr.post i =
        ((goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i) ℓ.call).1 := by
      rw [hexec]
    by_cases hr : ℓ.call = .restart
    · rw [hpost, hr]
      obtain ⟨-, -, -, -, -, -, hrt, -⟩ :=
        restart_state sp FGP ro y (tr.state y i) ℓ.frame (tr.time i) hΦ (h.time_nonneg i)
      change (tr.time j : WithBot Time) ≤ (acRestart sp ro y _ _ _).1.restartTime
      rw [hrt]
      exact WithBot.coe_le_coe.mpr (h.time_mono hji)
    rw [hpost, step_restartTime y _ _ _ _ hr]
    rcases Nat.eq_or_lt_of_le hji with rfl | hji
    · obtain ⟨ℓj, hcj, hrj⟩ := hj
      have : ℓj = ℓ := Option.some.inj (hcj.2.symm.trans hc.2)
      exact absurd (this ▸ hrj) hr
    rcases tr.noCall_or_lastCall y i with hn | ⟨j', hj', ℓ', hc', hnb⟩
    · obtain ⟨ℓj, hcj, -⟩ := hj
      exact absurd hcj (hn j (Nat.zero_le _) hji ℓj)
    have hjj' : j ≤ j' := by
      by_contra hlt
      obtain ⟨ℓj, hcj, -⟩ := hj
      exact hnb j (by omega) hji ℓj hcj
    rw [tr.state_of_lastCall hc' hj' hnb]
    exact ih j' hj' ℓ' hc' j hjj' hj

end OneVote

/-- **F.1 (c), a joined node.** -/
theorem joined_awake : JoinedAwake sp := by
  intro FGP ro H U tr h y hy i ℓ hc hj
  have hle : ∀ j ≤ i, tr.RestartAt y j →
      tr.time j ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) := fun j hji hr =>
    WithBot.coe_le_coe.mp ((restartTime_ge h hy i ℓ hc j hji hr).trans hj)
  refine ⟨fun u hu₁ hu₂ => ?_, hle⟩
  by_contra hna
  have hlt : u < tr.time i := lt_of_le_of_ne hu₂ fun he => hna (he ▸ h.awake_of_call y hy i ℓ hc)
  obtain ⟨k, hk, hku, hki⟩ := h.restart_at_wake y hy u (tr.time i) (le_trans (le_max_left _ _) hu₁)
    hlt hna (h.awake_of_call y hy i ℓ hc)
  have hk' : k ≤ i := by
    by_contra hik
    obtain ⟨ℓk, hck, hrk⟩ := hk
    obtain ⟨u', -, hu'k, -, hbefore⟩ := h.sleep_of_restart y hy k ℓk hck hrk
    have := hbefore i (by omega) ℓ hc
    exact absurd (lt_of_lt_of_le (this.trans hu'k) hki) (lt_irrefl _)
  have h₁ := hle k hk' hk
  have h₂ := le_trans (le_max_right _ _) hu₁
  exact absurd (lt_of_lt_of_le hku (h₁.trans h₂)) (lt_irrefl _)


/-- **A0.8.** -/
theorem one_vote_per_slot : OneVotePerSlot sp := by
  intro FGP ro H U tr h y hy i j e e' hv hv' hσ
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact absurd hσ (vote_slot_ne h hy hij hv hv')
  · refine ⟨rfl, ?_⟩
    obtain ⟨ℓ, hc, he⟩ := hv
    obtain ⟨ℓ', hc', he'⟩ := hv'
    have : ℓ' = ℓ := Option.some.inj (hc'.2.symm.trans hc.2)
    subst this
    rcases call_voteStep h hy hc with ⟨hn, -⟩ | ⟨-, -, hl, -⟩
    · rw [hn] at he; exact absurd he List.not_mem_nil
    · rcases hm : ℓ'.emits with _ | ⟨a, _ | ⟨b, l⟩⟩
      · rw [hm] at he; exact absurd he List.not_mem_nil
      · rw [hm, List.mem_singleton] at he he'; exact he.trans he'.symm
      · rw [hm] at hl; simp at hl
  · exact absurd hσ.symm (vote_slot_ne h hy hji hv' hv)

end Consensus.Goldilocks.SA

end

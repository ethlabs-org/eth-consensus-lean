module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin

public section

/-! # Goldilocks SA: the locks at a voter after unlocking (A1.2–A1.4)

The vote-transfer core needs every live lock block of the voter, after its unlocking, to be
compatible with the transferred block `B`.
* Unlocking against a view in which at least half of the committee have slot-`s` support votes
  whose heads extend `B`, or equivocate, moves every lock of a slot below `s` to a block
  compatible with `B`: an ancestor that conflicts with `B` has all of them as opponents
  (`unlock_compatible`).
* A block with three quarters of the committee size in optimistic voters in a pool whose honest
  votes extend `B` is compatible with `B` when `2f < committeeSize`: one voter is honest
  (`origin_compatible`).
* At an honest slot-`(m+1)` vote, the locks of slot `m` or `m + 1` are optimistic locks written
  before the vote (`lock_origin_readPoint`); those of slot `m + 1` are compatible with `B` when
  the earlier honest slot-`(m+1)` votes extend `B`; those of slot `m` are a hypothesis, which each
  transfer node discharges with its own evidence (`locks_compatible`). -/

namespace Consensus.Goldilocks.SA

variable {wm : SA.WriteMode}

variable {FGP : Type} {sp : SAParams}

/-- **Unlocking against support for `B`.** -/
theorem unlock_compatible {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {V : View sp.n} {s : Int}
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) {S : Set (Fin sp.n)}
    (hS : ∀ w ∈ S, w ∈ equivocators V.votes ∨
      ∃ x ∈ V.support, x.val = w ∧ (x.slot : Int) = s ∧ AncR Φ B x.head)
    (hn : sp.committeeSize ≤ 2 * S.ncard) (L : Set Lock) (t : Time) :
    ∀ l ∈ unlock sp L Φ t s V, (l.slot : Int) < s → ∀ X ∈ Φ.tree, X.root = l.block →
      Compatible Φ.tree X B := by
  rintro l' ⟨l, -, B₀, -, -, rfl⟩ hlt X hX hXr
  split_ifs at hlt hXr with h
  · simp only at hXr
    -- the unlock target is in the tree, so it is `X`
    unfold unlockTarget at hXr
    rcases hd : deepest Φ {B' | B' ∈ Φ.tree ∧ Φ.Anc B' B₀ ∧ 2 * (opponents sp Φ V s B').ncard <
        sp.committeeSize} with _ | T
    · rw [hd] at hXr
      have : X = Φ.F := hΦ.coherent.1 hX hΦ.rooted.1 hXr
      subst this
      exact (compatible_F hΦ hB).symm
    · rw [hd] at hXr
      obtain ⟨⟨hT, -, hopp⟩, -⟩ := deepest_mem hd
      have : X = T := hΦ.coherent.1 hX hT hXr
      subst this
      by_contra hnc
      -- every member of `S` opposes `X`
      have hSo : S ⊆ opponents sp Φ V s X := by
        intro w hw
        obtain hw | ⟨x, hx, hxv, hxs, R, hR, hRr, hBR⟩ := hS w hw
        · exact Or.inl hw
        refine Or.inr ⟨x, hx, hxv, hxs, R, hR, hRr, ?_⟩
        rintro (hc | hc)
        · exact hnc (Or.inr (Relation.ReflTransGen.trans hBR hc))
        · exact hnc (anc_total hΦ.coherent hc hBR)
      have := Set.ncard_le_ncard hSo
      omega
  · exact absurd hlt h

/-- **Unlocking against support for `B`, for every lock rule**: a lock that the unlock relation
moves (a slot below `s`) lies at or below the parent's unlock target, which is compatible with
`B` (`unlock_compatible`), so it is compatible with `B` too. -/
theorem unlockRel_compatible {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {V : View sp.n} {s : Int}
    {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) {S : Set (Fin sp.n)}
    (hS : ∀ w ∈ S, w ∈ equivocators V.votes ∨
      ∃ x ∈ V.support, x.val = w ∧ (x.slot : Int) = s ∧ AncR Φ B x.head)
    (hn : sp.committeeSize ≤ 2 * S.ncard) {L L' : Set Lock} {t : Time}
    (hL : UnlockRel sp L Φ t s V L') :
    ∀ l ∈ L', (l.slot : Int) < s → ∀ X ∈ Φ.tree, X.root = l.block →
      Compatible Φ.tree X B := by
  intro l hl hlt X hX hXr
  obtain ⟨l₀, hl₀, B₀, hB₀, hB₀r, hlive, hs, -, -, hmv, -⟩ := hL l hl
  rw [hs] at hlt
  obtain ⟨Y, hY, hYr, hYT⟩ := hmv hlt
  obtain rfl : X = Y := hΦ.coherent.1 hX hY (hXr.trans hYr.symm)
  have hva := (viableAncestor_anc hΦ hB₀).1
  set T := unlockTarget sp Φ V s (Φ.viableAncestor B₀)
  have hT := (unlockTarget_anc sp hΦ V s hva).1
  have hmem : (⟨T.root, l₀.slot, l₀.fast, l₀.expiry⟩ : Lock) ∈ unlock sp L Φ t s V :=
    ⟨_, ⟨l₀, hl₀, B₀, hB₀, hB₀r, hlive, rfl⟩, _, hva, rfl, by rw [ite_eq_left hlt]⟩
  rcases unlock_compatible hΦ hB hS hn L t _ hmem hlt T hT rfl with h | h
  · exact Or.inl (hYT.trans h)
  · exact anc_total hΦ.coherent hYT h

variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
  {tr : SATrace sp FGP ro} {proposer : Nat → Fin sp.n}

/-- **An optimistic origin is compatible.** A block `D` of a frame inside `U` with three quarters
of the committee as optimistic voters in a pool whose honest votes extend `B` is compatible with
`B`, when `2f < committeeSize`. -/
theorem origin_compatible (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦU : Φ.tree ⊆ U)
    {A : SAState sp.n} {σ : Nat} {D B : Blk sp.n FGP}
    (h34 : 3 * sp.committeeSize ≤ 4 * (optimisticVoters sp A Φ σ D).ncard)
    (hf : 2 * Hᶜ.ncard < sp.committeeSize)
    (hext : ∀ v ∈ A.pool σ, v.val ∈ H → VoteExtends U v B) : Compatible U D B := by
  obtain ⟨x, ⟨v, hv, rfl, R, hR, hRr, hDR⟩, hxH⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard (s := Hᶜ)
      (t := optimisticVoters sp A Φ σ D) (by omega)
  obtain ⟨Hd, hHd, hHdr, hBHd⟩ := hext v hv (not_not.1 hxH)
  obtain rfl : R = Hd := hU.1 (hΦU hR) hHd (hRr.trans hHdr.symm)
  exact anc_total hU (Anc.mono hΦU hDR) hBHd

/-- `locks_compatible` with the unlock given. -/
theorem locks_compatibleU
    {u : Nat → Set Lock} (hrun : ACRunU wm u proposer tr H U) {y : Fin sp.n} (hy : y ∈ H)
    {i m : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = m + 1) {B : Blk sp.n FGP} (hB : B ∈ ℓ.frame.tree) {S : Set (Fin sp.n)}
    (hS : ∀ w ∈ S, w ∈ equivocators (mergedVoteView sp e.readPoint ℓ.frame (m + 1)).votes ∨
      ∃ x ∈ (mergedVoteView sp e.readPoint ℓ.frame (m + 1)).support,
        x.val = w ∧ x.slot = m ∧ AncR ℓ.frame B x.head)
    (hn : sp.committeeSize ≤ 2 * S.ncard) (hf : 2 * Hᶜ.ncard < sp.committeeSize)
    (hearlier : EarlierVotesExtend tr H U i (m + 1) B)
    (hm : ∀ (Φ : Frm sp.n FGP) (A : SAState sp.n) (D : Blk sp.n FGP), FrameOK Φ → Φ.tree ⊆ U →
      D ∈ Φ.tree → 3 * sp.committeeSize ≤ 4 * (optimisticVoters sp A Φ m D).ncard →
      (∀ v ∈ A.pool m, v.val ∈ H → v.slot = m ∧
        ∃ j < i, ∃ e', VoteAt tr v.val j e' ∧ e'.msg = v) →
      (∃ k ≤ i, A.pool m ⊆ (tr.state y (k + 1)).pool m) →
      Compatible U D B) :
    ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L B := by
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  -- compatibility with `B` passes to ancestors
  have down : ∀ {X Y}, Anc U X Y → Compatible U Y B → Compatible U X B := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact anc_total hU hXY h
  rintro L ⟨hL, l, ⟨l₀, hl₀, B₀, hB₀, hB₀r, -, rfl⟩, hlL⟩
  have hLe : L = ℓ.frame.viableAncestor B₀ :=
    hU.1 (hΦU hL) (hΦU (viableAncestor_anc hΦ hB₀).1) hlL.symm
  subst hLe
  refine down (Anc.mono hΦU (anc_viableAncestor _ B₀)) ?_
  rcases lt_or_ge (l₀.slot : Int) m with hlt | hge
  · -- a lock of a slot below `m` was moved by the vote's unlocking
    obtain ⟨L', hL'⟩ := readPoint_locksU hr hy hc (by omega)
    rw [hs] at hL'
    have hσ : ((m + 1 : Nat) : Int) - 1 = m := by push_cast; ring
    rw [hσ] at hL'
    rcases unlockRel_compatible hΦ hB (fun w hw => by
        rcases hS w hw with h | ⟨x, hx, hxw, hxs, hxa⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, hx, hxw, by exact_mod_cast hxs, hxa⟩) hn hL' l₀ hl₀ hlt
        B₀ hB₀ hB₀r with h | h
    · exact Or.inl (Anc.mono hΦU h)
    · exact Or.inr (Anc.mono hΦU h)
  -- a lock of slot `m` or later comes from an optimistic confirmation
  obtain ⟨Φ', A, D, hΦ', hΦ'U, hD, h34, hpool, hsub, L₀, hL₀, hL₀r, hL₀D⟩ :=
    lock_origin_readPointU hrun hy hc l₀ hl₀ (by rw [hs]; push_cast; omega)
  obtain rfl : L₀ = B₀ := hU.1 hL₀ (hΦU hB₀) (hL₀r.trans hB₀r.symm)
  refine down hL₀D ?_
  rcases (show l₀.slot = m ∨ m < l₀.slot by omega) with h | h
  · exact hm Φ' A D hΦ' hΦ'U hD (h ▸ h34) (h ▸ hpool) (h ▸ hsub)
  -- of slot `m + 1`: the honest voters' votes are earlier slot-`(m+1)` votes
  refine origin_compatible hU hΦ'U h34 hf fun v hv hvH => ?_
  obtain ⟨hvs, j, hj, e', hvote, rfl⟩ := hpool v hv hvH
  obtain ⟨ℓ', hcj⟩ := id hvote
  have hsj := (castAt_specU hr hvH hcj).2.1
  have hsi := (castAt_specU hr hy hc).2.1
  have := slot_mono sp (hr.time_nonneg j) (hr.time_mono hj.le)
  exact hearlier _ hvH j hj e' hvote (by omega)

/-- **The locks at a transfer vote.** At an honest `y`'s slot-`(m+1)` vote: if at least half of
the committee have slot-`m` support votes in `y`'s merged view whose heads extend `B`, or
equivocate there, `2f < committeeSize`, every honest slot-`(m+1)` vote at an earlier cut
extends `B`, and every optimistic origin of slot `m` (a block with three quarters of the
committee size in optimistic voters whose honest
votes were cast before the vote) is compatible with `B`, then every live lock block at the vote's
read point is compatible with `B`. -/
theorem locks_compatible (hrun : ACRun proposer tr H U) {y : Fin sp.n} (hy : y ∈ H) {i m : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = m + 1) {B : Blk sp.n FGP} (hB : B ∈ ℓ.frame.tree) {S : Set (Fin sp.n)}
    (hS : ∀ w ∈ S, w ∈ equivocators (mergedVoteView sp e.readPoint ℓ.frame (m + 1)).votes ∨
      ∃ x ∈ (mergedVoteView sp e.readPoint ℓ.frame (m + 1)).support,
        x.val = w ∧ x.slot = m ∧ AncR ℓ.frame B x.head)
    (hn : sp.committeeSize ≤ 2 * S.ncard) (hf : 2 * Hᶜ.ncard < sp.committeeSize)
    (hearlier : EarlierVotesExtend tr H U i (m + 1) B)
    (hm : ∀ (Φ : Frm sp.n FGP) (A : SAState sp.n) (D : Blk sp.n FGP), FrameOK Φ → Φ.tree ⊆ U →
      D ∈ Φ.tree → 3 * sp.committeeSize ≤ 4 * (optimisticVoters sp A Φ m D).ncard →
      (∀ v ∈ A.pool m, v.val ∈ H → v.slot = m ∧
        ∃ j < i, ∃ e', VoteAt tr v.val j e' ∧ e'.msg = v) →
      (∃ k ≤ i, A.pool m ⊆ (tr.state y (k + 1)).pool m) →
      Compatible U D B) :
    ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L B :=
  locks_compatibleU (hrun := hrun.toU) (y := y) (hy := hy) (i := i) (m := m) (ℓ := ℓ) (e := e)
      (hc := hc) (hs := hs) (B := B) (hB := hB) (S := S) (hS := hS) (hn := hn) (hf := hf)
          (hearlier := hearlier) (hm := hm)

end Consensus.Goldilocks.SA

end

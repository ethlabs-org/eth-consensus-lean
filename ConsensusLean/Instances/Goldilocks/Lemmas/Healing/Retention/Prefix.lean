module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum

public section

/-! # Goldilocks Healing, HR.4: origins before a cut and the sources of left entries

`hr4-boot-carry.md` §§3, 7; `hr4-cut-scope.md` §4.

* **Prefix comparison before a cut** (`origins_compatible_before`): with `VoteInv` at every cut
  `< k`, a high origin written before `k` is comparable with every high origin active before `k`
  (written before `k`, or whose label's votes all precede `k`). The strict-cut form of the cut
  step's `origins_compatible_prefix` (`Retention/Cut`, which imports the base-case module, so the
  base case cannot import it).
* **The entries of a chain** (`entry_at_height`): every height `1 ≤ h ≤ σ[C].h` has its entry on
  `C`'s chain; a chain that left an entry carries an honest attestation naming it
  (`honest_att_of_left`, the contrapositive of `Store.entry_kept`).
* **The source of a left high entry** (`left_entry_origin`): such an attestation, on a block of an
  honest store before cut `k`, was signed before `k`, and its entry lies below a high origin
  written by its signer before the signing (`high_row_source`).
* **The report-time bound** (`row_origin_label_lt`): that origin's label is below the slot of an
  honest vote at cut `k`; open for an optimistic origin of the vote's own slot
  (`row_origin_not_current`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- **The entry of every height of a chain**: for a held `C` and `1 ≤ h ≤ σ[C].h`, an ancestor of
`C` has state height `h` and is its own entry. -/
theorem entry_at_height {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {C : NodeBlock P ACP} (hC : C ∈ st.tree) {h : Nat} (h1 : 1 ≤ h)
    (hle : h ≤ (st.σ C.root).h) :
    ∃ Z ∈ st.tree, st.Anc Z C ∧ (st.σ Z.root).h = h ∧ (st.σ Z.root).Th = Z.root := by
  have key : ∀ {W : NodeBlock P ACP} {h : Nat}, W ∈ st.tree → (st.σ W.root).h = h →
      ∃ Z ∈ st.tree, st.Anc Z W ∧ (st.σ Z.root).h = h ∧ (st.σ Z.root).Th = Z.root := by
    intro W h hW he
    obtain ⟨⟨E, hE, hEr, hEW, hEh, hET⟩, -⟩ := Store.entry_state_of_source _ _ _ _ hr _ hW
    exact ⟨E, hE, hEW, hEh.trans he, hET.trans hEr.symm⟩
  have hA := (Store.accepted_tree _ _ _ _ hr).2.2.2 C hC
  clear hC
  induction hA generalizing h with
  | refl =>
    have hg := Store.σ_genesis hr
    have h₁ : ((st.σ (P.genesisBlock acp₀).root)).h = 1 := by
      rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, hg]; rfl
    exact key (Store.genesis_mem hr) (by omega)
  | tail _ hYW ih =>
    rcases eq_or_lt_of_le hle with he | hlt
    · exact key hYW.2.1 he.symm
    · obtain ⟨-, -, -, ht⟩ := Store.step_σ hr hYW.2.1 hYW.2.2
      obtain ⟨Z, hZ, hZY, hZh, hZT⟩ := ih h1 (by
        rcases stateTransition_bits ht with ⟨hh, -⟩ | ⟨hh, -⟩ <;> omega)
      exact ⟨Z, hZ, hZY.tail hYW, hZh, hZT⟩

/-- **A chain that left an entry carries an honest attestation naming it** (the contrapositive of
`Store.entry_kept`, G0.2 (f)): fewer than `q` faulty validators cannot leave a height. -/
theorem honest_att_of_left {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
    (hr : st.Reachable acp₀) {H : Set (Fin P.n)} (hq : Hᶜ.ncard < P.fg.q)
    {E C : NodeBlock P ACP} (hET : (st.σ E.root).Th = E.root) (hEC : st.Anc E C)
    (hlt : (st.σ E.root).h < (st.σ C.root).h) :
    ∃ W ∈ st.tree, ∃ att ∈ W.fgPayload, att.T = E.root ∧ att.val ∈ H := by
  by_contra hn
  push Not at hn
  have := (Store.entry_kept hr hq hn hEC hET).1
  omega

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- **Prefix comparison of two high origins before a cut** (`hr4-cut-scope.md` §4,
`hr4-boot-carry.md` §§3, 7). With `VoteInv` at every cut `< k`, a high origin `(B, j)` written
before `k` or whose slot-`j` votes all precede `k`, and a high origin `(O, l)` written before `k`,
are comparable: for `l < j` the honest slot-`j` votes counted by `B`'s write extend `O`; for
`j < l` those counted by `O`'s write extend `B`; for `l = j` the raw selections are compatible by
TSQ (`Sync` from `GST(g)`, `t_j ≥ g`). -/
theorem origins_compatible_before (hp : ResetPremises tr H dg g ΔF a) {k : Nat}
    (hvk : ∀ k' < k, VoteInv tr H g k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) (hg : g ≤ sp.ts j)
    (hact : i < k ∨ ∀ c, tr.time c < sp.ts (j + 1 : Nat) → c < k) {x' : Fin sp.n} {r l : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))} (ho' : HighOrigin tr H g x' r l O) (hrk : r < k) :
    Compatible (tr.HonestBlocks H) B O := by
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr hp.run hp.noColl
  have hrl := hrun'.localRun
  have hU := hrl.coherent
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have := hp.healthy.2.2
    have := Fin.pos x
    have hn : sp.n = sp.toParams.n := rfl
    omega
  obtain ⟨CV, hst⟩ := ho.2.2.1
  obtain ⟨CV', hst'⟩ := ho'.2.2.1
  obtain ⟨-, D, hfl, hBD⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
  obtain ⟨-, D', hfl', hOD'⟩ := storedFastLock_mem hp.run hp.noColl ho'.1 hst'
  have hvote : ∀ {x₀ : Fin sp.n} {i₀ j₀ : Nat} {B₀ : SA.Blk sp.n (List (FG.Att sp.n))},
      HighOrigin tr H g x₀ i₀ j₀ B₀ → ∀ z ∈ H, ∀ c < k, ∀ e, SA.VoteAt tr.projAC z c e →
        j₀ < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B₀ :=
    fun ho₀ z hz c hc e ⟨ℓ, hcl, he⟩ hsl =>
      ((voteInv_iff.1 (hvk c hc)) _ _ _ _ ho₀ z hz ℓ e ⟨hcl, he⟩ hsl).1
  rcases lt_trichotomy l j with hlt | rfl | hgt
  · have hcut : ∀ z ∈ H, ∀ c < i + 1, ∀ e, SA.VoteAt tr.projAC z c e → e.msg.slot = j →
        c < k := by
      intro z hz c hc e ⟨ℓ, hcl, he⟩ hsl
      rcases hact with hik | hts
      · omega
      refine hts c (not_le.mp fun hge => ?_)
      have h₁ := (SA.castAt_spec hrl hz ⟨hcl, he⟩).2.1
      have h₃ := (SA.ts_le_iff_le_slot sp (hrl.time_nonneg c) ((j + 1 : Nat) : Int)).mp hge
      omega
    have hDO : Compatible (tr.HonestBlocks H) D O :=
      SA.fastLock_compatible_of_votes hrun' ho.1 (Nat.lt_succ_self i) hfl hf
        fun z hz c hc e hve hsl => hvote ho' z hz c (hcut z hz c hc e hve hsl) e hve (by omega)
    by_contra hn
    exact SA.not_compatible_of_anc hU hBD (fun h => hn h.symm) hDO.symm
  · have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H
      (fun v => v.val) tr ΔF (sp.ts l) (sp.ts (l + 1 : Nat) + sp.Δ) hp.run.toLocalRun
      (syncRun_of_gst hp.healthy.1 hg)
    rcases SA.fastLock_same_slot hrun' ho.1 hfl ho'.1 hfl' hsync hf with h | h
    · exact SA.anc_total hU (hBD.trans h) hOD'
    · exact SA.anc_total hU hBD (hOD'.trans h)
  · have hD'B : Compatible (tr.HonestBlocks H) D' B :=
      SA.fastLock_compatible_of_votes hrun' ho'.1 (Nat.lt_succ_self r) hfl' hf
        fun z hz c hc e hve hsl => hvote ho z hz c (by omega) e hve (by omega)
    by_contra hn
    exact SA.not_compatible_of_anc hU hOD' hn hD'B.symm

/-- **The source of a left high entry** (`hr4-boot-carry.md` §7): a high entry `E` of an honest
store before cut `k` that a held chain has left is named by an honest attestation on a block of
that store, signed before `k`, whose entry `E` lies below a high origin written by its signer
before the signing (`high_row_source`). -/
theorem left_entry_origin (hp : ResetPremises tr H dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {E C : SA.Blk sp.n (List (FG.Att sp.n))} (hE : E ∈ (tr.state y k).fg.tree)
    (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h) (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v ∈ H, ∃ d < k, tr.SignAt v d att ∧
      att.T = E.root ∧ ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧
        Anc (tr.HonestBlocks H) E O := by
  have hU := honest_coherent hp
  obtain ⟨W, hW, att, ha, haT, haH⟩ := honest_att_of_left
    (Compose.fg_reachable hp.run.toLocalRun hy k) (faulty_lt_q hp.healthy) hET hEC hlt
  rcases tree_accepted hp.run.toLocalRun hy hW with rfl | ⟨i', hi', hA⟩
  · cases ha
  obtain ⟨d, hdi, hsd⟩ := hp.run.att_unforgeable y hy i' att (Or.inr ⟨W, ⟨true, hA⟩, ha⟩) haH
  obtain ⟨E', hE', hE'r, hE'h⟩ := signAt_entry hp.run haH hsd
  obtain rfl : E' = E := hU.1 ⟨_, haH, d, hE'⟩ ⟨y, hy, k, hE⟩ (hE'r.trans haT)
  obtain ⟨r, hrd, l, O, hoO, E₀, hE₀, hE₀O, hE₀r, -⟩ :=
    high_row_source hp haH hsd (by rw [← hE'h, σ_eq_run hp haH hy hE' hE]; exact hEh)
  obtain rfl : E₀ = E' := hU.1 ⟨_, haH, r, hE₀⟩ ⟨y, hy, k, hE⟩ (hE₀r.trans haT)
  exact ⟨W, hW, att, ha, att.val, haH, d, by omega, hsd, haT, r, hrd, l, O, hoO,
    hE₀O.mono fun X hX => ⟨_, haH, r, hX⟩⟩

/-- **No optimistic source of the vote's own slot** (`hr4-boot-carry.md` §7, "R4's report-time
argument bounds `l ≤ m − 1` before this vote"; §3, "a label-`(j+1)` optimistic source cannot be
reported before `t_{j+1} + Δ`", and the `n = 1` causal exception). An honest row carried by a
block that an honest voter holds before its slot-`m` vote is not signed after an optimistic
fast-lock write of slot `m` by its signer. Open: the report-time argument (the honest slot-`m`
votes an optimistic test of slot `m` needs, the order of the vote and the FG update in a tick,
and the order of the events within one instant). -/
theorem row_origin_not_current (hp : ResetPremises tr H dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} (hv : v ∈ H) {d : Nat} (hs : tr.SignAt v d att) {r : Nat} (hrd : r < d)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)} :
    ¬ SA.OptimisticLockAt tr.projAC v r e.msg.slot D CV := by
  sorry

/-- **The report-time bound** (`hr4-boot-carry.md` §7): the label of a high origin written by
the signer of an honest row, before the signing, where the row is carried by a block that an
honest voter holds before its vote, is below the vote's slot: a fast test of slot `l` writes at
`t_l + 6Δ ≥ t_{l+1}`, an optimistic write of slot `l` is in slot `l ≤ m`, and not of slot `m`
(`row_origin_not_current`). -/
theorem row_origin_label_lt (hp : ResetPremises tr H dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} (hv : v ∈ H) {d : Nat} (hs : tr.SignAt v d att) (hdk : d < k) {r l : Nat}
    (hrd : r < d) {O : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g v r l O) :
    l < e.msg.slot := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hp.run hp.noColl).localRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  obtain ⟨ℓw, D, CV, -, hfl, -⟩ := highOrigin_mem hp ho
  have hk := (SA.castAt_spec hr hy hc).2.1
  have htr : tr.projAC.time r ≤ tr.projAC.time k := hr.time_mono (by omega)
  rcases hfl with ⟨ℓ', C, ⟨-, -, ht, -⟩, -, -, -, -⟩ | hopt
  · have h₁ : sp.ts (l + 1 : Nat) ≤ tr.projAC.time k := by
      have : sp.ts (l + 1 : Nat) = sp.ts l + 4 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      rw [this]
      change tr.projAC.time r = sp.ts l + 6 * sp.Δ at ht
      linarith
    have := (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).mp h₁
    omega
  · have hl : l ≤ e.msg.slot := by
      obtain ⟨-, -, -, hsl, -⟩ := hopt
      rw [hk, ← hsl]
      exact SA.slot_mono sp (hr.time_nonneg r) htr
    rcases hl.lt_or_eq with hl | rfl
    · exact hl
    · exact absurd hopt (row_origin_not_current hp hy hc hW ha hv hs hrd)

end Consensus.Goldilocks.Healing

end

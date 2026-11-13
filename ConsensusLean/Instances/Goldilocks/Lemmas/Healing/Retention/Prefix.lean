module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Relay
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.PrefixSteps
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing, HR.4: origins before a cut and the sources of left entries

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
  honest vote at cut `k`. For an optimistic origin of the vote's own slot `m`
  (`row_origin_not_current`, the run's event order): the attestation is signed once
  (`sign_unique`), in a tick, at a public time in `[t_m, t_m + Δ]`; at `t_m + Δ` the voter's tick
  precedes its acceptance of the carrying block and casts its vote
  (`vote_before_late_delivery`); at `t_m` the write is in the signer's tick, whose pools hold
  slot-`m` votes of the signer only, so `n = 1` and the signer is the voter, with its vote before
  the attestation (`slot_start_optimistic`). These run facts are in `Retention/PrefixSteps`,
  which the growing-fault siblings share. -/

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
        rcases stateTransition_bits ht with ⟨hh, -⟩ | ⟨hh, -⟩ <;> (clear * - hlt hh; omega))
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
  {proposer : Nat → Fin sp.n}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- **Prefix comparison of two high origins before a cut**.
With `VoteInv` at every cut `< k`, a high origin `(B, j)` written
before `k` or whose slot-`j` votes all precede `k`, and a high origin `(O, l)` written before `k`,
are comparable: for `l < j` the honest slot-`j` votes counted by `B`'s write extend `O`; for
`j < l` those counted by `O`'s write extend `B`; for `l = j` the raw selections are compatible by
TSQ (`Sync` from `GST(g)`, `t_j ≥ g`). -/
theorem ResetPremisesUpTo.origins_compatible_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {k : Nat}
    (hvote : ∀ {x₀ : Fin sp.n} {i₀ j₀ : Nat} {B₀ : SA.Blk sp.n (List (FG.Att sp.n))},
      HighOrigin tr H g x₀ i₀ j₀ B₀ → tr.time i₀ ≤ b →
      ∀ z ∈ H, ∀ c < k, tr.time c ≤ b → ∀ e, SA.VoteAt tr.projAC z c e →
        j₀ < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B₀)
    {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) (hg : g ≤ sp.ts j)
    (hact : i < k ∨ ∀ c, tr.time c < sp.ts (j + 1 : Nat) → c < k) {x' : Fin sp.n} {r l : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))} (ho' : HighOrigin tr H g x' r l O) (hrk : r < k)
    (hib : tr.time i ≤ b) (hrb : tr.time r ≤ b) :
    Compatible (tr.HonestBlocks H) B O := by
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hrl := hrun'.localRun
  have hU := hrl.coherent
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have := hp.faults
    have := Fin.pos x
    have hn : sp.n = sp.toParams.n := rfl
    omega
  obtain ⟨CV, hst⟩ := ho.2.2.1
  obtain ⟨CV', hst'⟩ := ho'.2.2.1
  obtain ⟨-, D, hfl, hBD⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
  obtain ⟨-, D', hfl', hOD'⟩ := storedFastLock_mem hp.run hp.noColl ho'.1 hst'
  rcases lt_trichotomy l j with hlt | rfl | hgt
  · have hcut : ∀ z ∈ H, ∀ c < i + 1, ∀ e, SA.VoteAt tr.projAC z c e → e.msg.slot = j →
        c < k := by
      intro z hz c hc e ⟨ℓ, hcl, he⟩ hsl
      rcases hact with hik | hts
      · (clear * - hc hik; omega)
      refine hts c (not_le.mp fun hge => ?_)
      have h₁ := (SA.castAt_spec hrl hz ⟨hcl, he⟩).2.1
      have h₃ := (SA.ts_le_iff_le_slot sp (hrl.time_nonneg c) ((j + 1 : Nat) : Int)).mp hge
      clear * - hsl h₁ h₃; omega
    have hDO : Compatible (tr.HonestBlocks H) D O :=
      SA.fastLock_compatible_of_votes hrun' _ SA.CommitteeP.full ho.1 (Nat.lt_succ_self i) hfl
        (SA.cs2_full hp.stock hf)
        fun z hz c hc e hve hsl => hvote ho' hrb z hz c (hcut z hz c hc e hve hsl)
          ((hp.run.time_mono (by clear * - hc; omega)).trans hib) e hve (by omega)
    by_contra hn
    exact SA.not_compatible_of_anc hU hBD (fun h => hn h.symm) hDO.symm
  · have hsync := hp.sync.syncAC hp.run (hi := sp.ts (l + 1 : Nat) + sp.Δ) hg
    rcases SA.fastLock_same_slot hrun' _ SA.CommitteeP.full (SA.size_binding_full hp.stock) ho.1
      hfl ho'.1 hfl' hsync (SA.cs2_full hp.stock hf) with h | h
    · exact SA.anc_total hU (hBD.trans h) hOD'
    · exact SA.anc_total hU hBD (hOD'.trans h)
  · have hD'B : Compatible (tr.HonestBlocks H) D' B :=
      SA.fastLock_compatible_of_votes hrun' _ SA.CommitteeP.full ho'.1 (Nat.lt_succ_self r) hfl'
        (SA.cs2_full hp.stock hf)
        fun z hz c hc e hve hsl => hvote ho hib z hz c (by clear * - hrk hc; omega)
          ((hp.run.time_mono (by clear * - hc; omega)).trans hrb) e hve (by
              clear * - hgt hsl; omega)
    by_contra hn
    exact SA.not_compatible_of_anc hU hOD' hn hD'B.symm

/-- Whole-run specialization of prefix origin comparison. -/
theorem origins_compatible_before (hp : ResetPremises tr H proposer dg g ΔF a) {k : Nat}
    (hvk : ∀ k' < k, VoteInv tr H g k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) (hg : g ≤ sp.ts j)
    (hact : i < k ∨ ∀ c, tr.time c < sp.ts (j + 1 : Nat) → c < k) {x' : Fin sp.n} {r l : Nat}
    {O : SA.Blk sp.n (List (FG.Att sp.n))} (ho' : HighOrigin tr H g x' r l O) (hrk : r < k) :
    Compatible (tr.HonestBlocks H) B O := by
  apply (hp.toUpTo tr H (le_max_left a (max (tr.time i) (tr.time r)))).origins_compatible_before
    (fun ho₀ _ z hz c hc _ e ⟨ℓ, hcl, he⟩ hsl =>
      ((voteInv_iff.1 (hvk c hc)) _ _ _ _ ho₀ z hz ℓ e ⟨hcl, he⟩ hsl).1)
    ho hg hact ho' hrk
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- **The source of a left high entry**: a high entry `E` of an honest
store before cut `k` that a held chain has left is named by an honest attestation on a block of
that store, signed before `k`, whose entry `E` lies below a high origin written by its signer
before the signing (`high_row_source`). -/
theorem ResetPremisesUpTo.left_entry_origin {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {E C : SA.Blk sp.n (List (FG.Att sp.n))} (hE : E ∈ (tr.state y k).fg.tree)
    (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h) (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v ∈ H, ∃ d < k, tr.SignAt v d att ∧
      att.T = E.root ∧ ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧
        Anc (tr.HonestBlocks H) E O := by
  have hU := hp.honest_coherent
  have hq : Hᶜ.ncard < sp.toParams.fg.q := by
    have h3 := hp.faults
    have hn := sp.toParams.hn
    change 3 * Hᶜ.ncard ≤ sp.toParams.n - 1 at h3
    change Hᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    clear * - hn h3; omega
  obtain ⟨W, hW, att, ha, haT, haH⟩ := honest_att_of_left
    (Compose.fg_reachable hp.run.toLocalRun hy k) hq hET hEC hlt
  rcases tree_accepted hp.run.toLocalRun hy hW with rfl | ⟨i', hi', hA⟩
  · cases ha
  obtain ⟨d, hdi, hsd⟩ := hp.run.att_unforgeable y hy i' att (Or.inr ⟨W, ⟨true, hA⟩, ha⟩) haH
  obtain ⟨E', hE', hE'r, hE'h⟩ := signAt_entry hp.run haH hsd
  obtain rfl : E' = E := hU.1 ⟨_, haH, d, hE'⟩ ⟨y, hy, k, hE⟩ (hE'r.trans haT)
  obtain ⟨r, hrd, l, O, hoO, E₀, hE₀, hE₀O, hE₀r, -⟩ :=
    hp.high_row_source haH hsd (by rw [← hE'h, hp.σ_eq_run haH hy hE' hE]; exact hEh)
  obtain rfl : E₀ = E' := hU.1 ⟨_, haH, r, hE₀⟩ ⟨y, hy, k, hE⟩ (hE₀r.trans haT)
  exact ⟨W, hW, att, ha, att.val, haH, d, by clear * - hi' hdi; omega, hsd, haT, r, hrd, l, O, hoO,
    hE₀O.mono fun X hX => ⟨_, haH, r, hX⟩⟩

/-- Whole-run specialization of left-entry provenance. -/
theorem left_entry_origin (hp : ResetPremises tr H proposer dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {E C : SA.Blk sp.n (List (FG.Att sp.n))} (hE : E ∈ (tr.state y k).fg.tree)
    (hET : ((tr.state y k).fg.σ E.root).Th = E.root)
    (hEh : HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h) (hEC : (tr.state y k).fg.Anc E C)
    (hlt : ((tr.state y k).fg.σ E.root).h < ((tr.state y k).fg.σ C.root).h) :
    ∃ W ∈ (tr.state y k).fg.tree, ∃ att ∈ W.fgPayload, ∃ v ∈ H, ∃ d < k, tr.SignAt v d att ∧
      att.T = E.root ∧ ∃ r < d, ∃ l O, HighOrigin tr H g v r l O ∧
        Anc (tr.HonestBlocks H) E O :=
  (hp.toUpTo tr H (le_refl a)).left_entry_origin hy hE hET hEh hEC hlt

/-- **No optimistic source of the vote's own slot** (R4's report-time
argument bounds `l ≤ m − 1` before this vote; a label-`(j+1)` optimistic source cannot be
reported before `t_{j+1} + Δ`, and the `n = 1` causal exception). An honest attestation carried by
a block that an honest voter holds before its slot-`m` vote is not signed after an optimistic
fast-lock write of slot `m` by its signer: the attestation was signed once, before the voter
accepted the block, at a public time in `[t_m, t_m + Δ]` (`sign_public`); at `t_m + Δ` the voter's
tick, which casts its slot-`m` vote, precedes that acceptance (`vote_before_late_delivery`); at
`t_m` the optimistic check of slot `m` inside the signer's tick sees only the signer's own slot-`m`
vote, so `n = 1` and the signer is the voter, whose one slot-`m` vote would precede the attestation
(`slot_start_optimistic`). -/
theorem ResetPremisesUpTo.row_origin_not_current {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} (hv : v ∈ H) {d : Nat} (hs : tr.SignAt v d att) {r : Nat} (hrd : r < d)
    {D : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)} :
    ¬ SA.OptimisticLockAt tr.projAC v r e.msg.slot D CV := by
  intro hopt
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  -- the attestation was signed at `d`, before `y` accepted `W`, before the vote
  rcases tree_accepted hp.run.toLocalRun hy hW with rfl | ⟨i, hik, hA⟩
  · cases ha
  obtain ⟨C, hcd⟩ := id hs
  have hav : att.val = v := (createAtt_spec (hp.run.cutLaw v hv d _ hcd).1).1
  obtain ⟨d₀, hd₀, hs₀⟩ :=
    hp.run.att_unforgeable y hy i att (Or.inr ⟨W, ⟨true, hA⟩, ha⟩) (hav ▸ hv)
  rw [hav] at hs₀
  obtain rfl := sign_unique hp.run hv hs₀ hs
  -- `t_m ≤ time r ≤ time d ≤ time i ≤ time k ≤ t_m + Δ`, and the signing is at a public time
  have hkt : tr.time k ≤ sp.ts e.msg.slot + sp.Δ := (Compose.cast_head_fcRoot hr hy hc).2
  have hrt : sp.ts e.msg.slot ≤ tr.time r := by
    obtain ⟨-, -, -, hsl, -⟩ := hopt
    exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg r) _).2 (by rw [hsl])
  have h₁ := hp.run.time_mono hrd.le
  have h₂ := hp.run.time_mono hd₀.le
  have h₃ := hp.run.time_mono hik.le
  obtain ⟨c, hcτ⟩ := Compose.sign_public hp.run hv hcd
  have hcτ' : tr.time d₀ = sp.Δ * c := hcτ
  have hts : sp.ts e.msg.slot = sp.Δ * (4 * (e.msg.slot : Int)) := by
    simp only [SAParams.ts]; ring
  have hc₁ : 4 * (e.msg.slot : Int) ≤ c :=
    le_of_mul_le_mul_left (show sp.Δ * (4 * (e.msg.slot : Int)) ≤ sp.Δ * c by
        linarith only [hrt, hcτ, hts, h₁]) hΔ
  have hc₂ : c ≤ 4 * (e.msg.slot : Int) + 1 :=
    le_of_mul_le_mul_left (show sp.Δ * c ≤ sp.Δ * (4 * (e.msg.slot : Int) + 1) by
      rw [mul_add, mul_one]; linarith only [hkt, hcτ, hts, h₂, h₃]) hΔ
  obtain hcc | hcc : c = 4 * (e.msg.slot : Int) ∨ c = 4 * (e.msg.slot : Int) + 1 := by
    clear * - hc₁ hc₂; omega
  · -- signed at `t_m`: then `n = 1`, and the signer is the voter, with its vote before `d`
    obtain ⟨hn1, j', hj', e', hve', hes⟩ :=
      slot_start_optimistic hp.run hp.noColl hv hs (by rw [hcτ', hcc, hts]) hrd hopt hp.stock
    obtain rfl : v = y := Fin.ext (by have := v.2; have := y.2; (clear * - hn1; omega))
    have := ((SA.one_vote_per_slot sp) _ ro H _ tr.projAC hr v hy j' k e' e hve'
      ⟨ℓ, hc.1, hc.2⟩ hes).1
    clear * - hik hd₀ hrd hj' this; omega
  · -- signed at `t_m + Δ`: the voter accepted `W` at `t_m + Δ`, before its vote
    refine vote_before_late_delivery hp.run hp.noColl hy hc hA hik
      (le_antisymm (by linarith only [hkt, h₃]) ?_)
    have : tr.time d₀ = sp.ts e.msg.slot + sp.Δ := by
      rw [hcτ', hcc, hts]; ring
    linarith only [h₂, this]

/-- **The report-time bound**: the label of a high origin written by
the signer of an honest attestation, before the signing, where the attestation is carried by a block
that an honest voter holds before its vote, is below the vote's slot: a fast test of slot `l` writes
at `t_l + 6Δ ≥ t_{l+1}`, an optimistic write of slot `l` is in slot `l ≤ m`, and not of slot `m`
(`row_origin_not_current`). -/
theorem ResetPremisesUpTo.row_origin_label_lt {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} (hv : v ∈ H) {d : Nat} (hs : tr.SignAt v d att) (hdk : d < k) {r l : Nat}
    (hrd : r < d) {O : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g v r l O) :
    l < e.msg.slot := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  obtain ⟨ℓw, D, CV, -, hfl, -⟩ := hp.highOrigin_mem ho
  have hk := (SA.castAt_spec hr hy hc).2.1
  have htr : tr.projAC.time r ≤ tr.projAC.time k := hr.time_mono (by clear * - hdk hrd; omega)
  rcases hfl with ⟨ℓ', C, ⟨-, -, ht, -⟩, -, -, -, -⟩ | hopt
  · have h₁ : sp.ts (l + 1 : Nat) ≤ tr.projAC.time k := by
      have : sp.ts (l + 1 : Nat) = sp.ts l + 4 * sp.Δ := by
        simp only [SAParams.ts]; push_cast; ring
      rw [this]
      change tr.projAC.time r = sp.ts l + 6 * sp.Δ at ht
      linarith only [hΔ, htr, ht]
    have := (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).mp h₁
    clear * - hk this; omega
  · have hl : l ≤ e.msg.slot := by
      obtain ⟨-, -, -, hsl, -⟩ := hopt
      rw [hk, ← hsl]
      exact SA.slot_mono sp (hr.time_nonneg r) htr
    rcases hl.lt_or_eq with hl | rfl
    · exact hl
    · exact absurd hopt (hp.row_origin_not_current hy hc hW ha hv hs hrd)

/-- Whole-run specialization of the strict source-label bound. -/
theorem row_origin_label_lt (hp : ResetPremises tr H proposer dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y k).fg.tree) {att : FG.Att sp.n} (ha : att ∈ W.fgPayload)
    {v : Fin sp.n} (hv : v ∈ H) {d : Nat} (hs : tr.SignAt v d att) (hdk : d < k) {r l : Nat}
    (hrd : r < d) {O : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g v r l O) :
    l < e.msg.slot :=
  (hp.toUpTo tr H (le_refl a)).row_origin_label_lt hy hc hW ha hv hs hdk hrd ho

end Consensus.Goldilocks.Healing

end

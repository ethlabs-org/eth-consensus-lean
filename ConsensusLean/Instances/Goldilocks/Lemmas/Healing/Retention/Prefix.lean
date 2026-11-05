module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
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
  the attestation (`slot_start_optimistic`). -/

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
      SA.fastLock_compatible_of_votes hrun' ho.1 (Nat.lt_succ_self i) hfl hf
        fun z hz c hc e hve hsl => hvote ho' hrb z hz c (hcut z hz c hc e hve hsl)
          ((hp.run.time_mono (by clear * - hc; omega)).trans hib) e hve (by omega)
    by_contra hn
    exact SA.not_compatible_of_anc hU hBD (fun h => hn h.symm) hDO.symm
  · have hsync := hp.sync.syncAC hp.run (hi := sp.ts (l + 1 : Nat) + sp.Δ) hg
    rcases SA.fastLock_same_slot hrun' ho.1 hfl ho'.1 hfl' hsync hf with h | h
    · exact SA.anc_total hU (hBD.trans h) hOD'
    · exact SA.anc_total hU hBD (hOD'.trans h)
  · have hD'B : Compatible (tr.HonestBlocks H) D' B :=
      SA.fastLock_compatible_of_votes hrun' ho'.1 (Nat.lt_succ_self r) hfl' hf
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

/-! ### The report-time bound: pools and records at a slot start -/

section Pools

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}

private theorem optimistic_pool_eq (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP) (t : Time) :
    (SA.optimisticConfirmation sp A Φ t).pool = A.pool := by
  unfold SA.optimisticConfirmation SA.updateLatestConfirmed
  split
  · rfl
  · split_ifs <;> rfl

private theorem admit_pool_mem {A : SA.SAState sp.n} {t : Time} {m w : SA.Vote sp.n} {σ : Nat}
    (h : w ∈ (SA.admitVote sp A t m).pool σ) : w ∈ A.pool σ ∨ w = m := by
  unfold SA.admitVote at h
  split_ifs at h
  · exact Or.inl h
  · exact Or.inl h
  · simp only [Function.update_apply] at h
    split_ifs at h with hs
    · subst hs
      rcases List.mem_append.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_singleton.1 h)
    · exact Or.inl h

private theorem receipt_pool_mem {A : SA.SAState sp.n} {t : Time} {B : SA.Blk sp.n FGP}
    {w : SA.Vote sp.n} {σ : Nat} (h : w ∈ (SA.blockReceipt sp A t B).pool σ) :
    w ∈ A.pool σ ∨ w ∈ SA.blockVotes B := by
  have key : ∀ (l : List (SA.Vote sp.n)) (A₀ : SA.SAState sp.n),
      w ∈ (l.foldl (fun A v => SA.admitVote sp A t v) A₀).pool σ → w ∈ A₀.pool σ ∨ w ∈ l := by
    intro l
    induction l with
    | nil => exact fun _ h => Or.inl h
    | cons x l ih =>
      intro A₀ h
      rcases ih _ h with h | h
      · rcases admit_pool_mem h with h | rfl
        · exact Or.inl h
        · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ h)
  unfold SA.blockReceipt at h
  have h' := key _ _ h
  exact h'

private theorem tryVote_pool_mem (self : Fin sp.n) (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP)
    (t : Time) {w : SA.Vote sp.n} {σ : Nat} (h : w ∈ (SA.tryVote sp self A Φ t).1.pool σ) :
    w ∈ A.pool σ ∨ w.val = self := by
  unfold SA.tryVote at h
  dsimp only at h
  split_ifs at h
  all_goals first
    | exact Or.inl h
    | (rw [optimistic_pool_eq] at h
       rcases admit_pool_mem h with h | rfl
       · exact Or.inl h
       · exact Or.inr rfl)

/-- **At a slot start, a call other than a delivery of a vote takes in no vote** but the node's
own and those of the block it receives (`ac_on_tick` runs `try_vote` only at `t_s + Δ`, and
`ac_proposal`, `ac_to_fg` keep the pools). -/
private theorem step_pool_new (self : Fin sp.n) (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP)
    {t : Time} (ht : t = sp.ts (sp.slot t)) (hΔ : 0 < sp.Δ) (c : (SA.goldilocksSA sp FGP ro).Call)
    (hm : ∀ m, c ≠ .message m) (hc : c ≠ .restart) {w : SA.Vote sp.n} {σ : Nat}
    (h : w ∈ ((SA.goldilocksSA sp FGP ro).step self A Φ t c).1.pool σ) :
    w ∈ A.pool σ ∨ w.val = self ∨ ∃ B, c = .block B ∧ w ∈ SA.blockVotes B := by
  cases c with
  | tick =>
    change w ∈ (SA.acOnTick sp self A Φ t).1.pool σ at h
    unfold SA.acOnTick at h
    dsimp only at h
    split_ifs at h <;> first
      | exact Or.inl h
      | (exfalso; linarith)
  | proposal =>
    change w ∈ (SA.acProposal sp A Φ t).1.pool σ at h
    unfold SA.acProposal at h
    dsimp only at h
    split_ifs at h <;> exact Or.inl h
  | toFG =>
    change w ∈ (SA.acToFG sp A Φ t).1.pool σ at h
    unfold SA.acToFG at h
    split_ifs at h <;> (try split at h) <;> (try split_ifs at h) <;> exact Or.inl h
  | message m => exact absurd rfl (hm m)
  | block B =>
    change w ∈ (SA.tryVote sp self (SA.optimisticConfirmation sp (SA.blockReceipt sp A t B) Φ t)
      Φ t).1.pool σ at h
    rcases tryVote_pool_mem _ _ _ _ h with h | h
    · rw [optimistic_pool_eq] at h
      rcases receipt_pool_mem h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨B, rfl, h⟩)
    · exact Or.inr (Or.inl h)
  | restart => exact absurd rfl hc

end Pools

/-- `create_attestation` signs as `v`, records the attestation, and refuses a height pair whose
height (for a target) or height and entry (for a timeout) it sent already. -/
private theorem createAtt_spec {n : Nat} {Λ Λ' : FG.Record} {v : Fin n} {σe : FG.ChainState n}
    {a : FG.Att n} (h : Λ.createAtt v σe = some (a, Λ')) :
    a.val = v ∧ Λ' = Λ.recordAtt a ∧ ∀ b ∈ Λ.sent, ¬ (b.1 = a.h ∧ b.2.1 = a.T) := by
  unfold FG.Record.createAtt at h
  split at h
  · cases h
  · dsimp only at h
    split_ifs at h with hany
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, rfl, fun b hb hb' => hany ?_⟩
    rw [List.any_eq_true]
    exact ⟨b, hb, by simp [hb'.1, hb'.2]⟩

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- An honest client's sent contents only grow. -/
private theorem sent_succ {b : Time} (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {v : Fin sp.n} (hv : v ∈ H)
    (c : Nat) {b : FG.Content} (hb : b ∈ (tr.state v c).record.sent) :
    b ∈ (tr.state v (c + 1)).record.sent := by
  by_cases hc : ∃ cut, tr.CallAt v c cut
  · obtain ⟨cut, hc⟩ := hc
    have hlaw := hp.run.cutLaw v hv c cut hc
    rw [tr.state_succ_of_call hc]
    cases cut with
    | ac ℓ => rw [hlaw.2.2.2]; exact hb
    | fg ℓ =>
      cases ℓ with
      | block B acc =>
        cases acc with
        | true => rw [hlaw.2.2.2]; exact hb
        | false => rw [hlaw.2]; exact hb
      | attestation a' => rw [hlaw.2.2]; exact hb
      | attest C s =>
        cases s with
        | none => rw [hlaw.2]; exact hb
        | some a' =>
          rw [(createAtt_spec hlaw.1).2.1]
          exact List.mem_append_left _ hb
  · rw [tr.state_succ_of_not fun cut hc' => hc ⟨cut, hc'⟩]
    exact hb

/-- **An honest validator signs an attestation at most once**: after signing, its content is in
the client's sent list, and `create_attestation` refuses it. -/
private theorem sign_unique {b : Time} (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {v : Fin sp.n} (hv : v ∈ H)
    {d d' : Nat} {att : FG.Att sp.n} (hs : tr.SignAt v d att) (hs' : tr.SignAt v d' att) :
    d = d' := by
  have key : ∀ {d d'}, tr.SignAt v d att → tr.SignAt v d' att → d < d' → False := by
    intro d d' hs hs' hlt
    obtain ⟨C, hc⟩ := hs
    obtain ⟨C', hc'⟩ := hs'
    have h₀ : att.content ∈ (tr.state v (d + 1)).record.sent := by
      rw [tr.state_succ_of_call hc, (createAtt_spec (hp.run.cutLaw v hv d _ hc).1).2.1]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    have hmem : ∀ c, d + 1 ≤ c → att.content ∈ (tr.state v c).record.sent := by
      intro c hc
      induction c, hc using Nat.le_induction with
      | base => exact h₀
      | succ c _ ih => exact sent_succ hp hv c ih
    exact (createAtt_spec (hp.run.cutLaw v hv d' _ hc').1).2.2 _ (hmem d' hlt) ⟨rfl, rfl⟩
  rcases lt_trichotomy d d' with h | h | h
  · exact (key hs hs' h).elim
  · exact h
  · exact (key hs' hs h).elim

/-- A restart emits nothing. -/
private theorem restart_emits {b : Time} (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {v : Fin sp.n} (hv : v ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt v i ℓ)
    (hcl : ℓ.call = .restart) : ℓ.emits = [] := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have he := hr.exec i ℓ hc.2 (hc.1 ▸ hv)
  rw [hc.1, hcl] at he
  have h' : ℓ.emits = (((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step v
      (tr.projAC.state v i) ℓ.frame (tr.projAC.time i) .restart)).2 := by rw [he]
  rw [h']
  exact ((SA.restart_state sp) _ ro v (tr.projAC.state v i) ℓ.frame (tr.projAC.time i)
    (SA.frameIn_of_callAt hr hv hc).1 (hr.time_nonneg i)).1

/-- **An optimistic write of slot `m` before a signing at `t_m`** (the
signing at a slot start). The signing is in the signer's tick at `t_m`, so the write is too
(before the tick, the node's cuts at `t_m` are restarts), and so is every admission of a slot-`m`
vote into the signer's pools by then (`ac_on_tick` at `t_m` and `ac_proposal` keep the pools,
a received block carries votes of earlier slots, and no vote is delivered inside a tick): the
pool of the optimistic check holds slot-`m` votes of the signer only, so three quarters of the
committee is one validator, `n = 1`, and the signer's own slot-`m` vote is at or before the
write. -/
private theorem slot_start_optimistic {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {v : Fin sp.n}
    (hv : v ∈ H) {d : Nat} {att : FG.Att sp.n} (hs : tr.SignAt v d att) {m : Nat}
    (hdt : tr.time d = sp.ts m) {r : Nat} (hrd : r < d) {D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV : Set (SA.Vote sp.n)} (hopt : SA.OptimisticLockAt tr.projAC v r m D CV) :
    sp.n = 1 ∧ ∃ j' ≤ r, ∃ e', SA.VoteAt tr.projAC v j' e' ∧ e'.msg.slot = m := by
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun'.localRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  obtain ⟨ℓv, A, hpt, hsl, hsel, -⟩ := hopt
  have hslm : sp.slot (sp.ts m) = m := SA.slot_of_mem sp m le_rfl
    ((SA.ts_lt_iff sp).2 (by push_cast; (clear * -; omega)))
  have hrt : tr.time r = sp.ts m := by
    refine le_antisymm (hdt ▸ hp.run.time_mono hrd.le) ?_
    exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg r) (m : Int)).2 (by rw [hsl])
  -- the tick of the signing
  obtain ⟨C, hcd⟩ := hs
  obtain ⟨j, ev, kk, hg, hdj, hk⟩ := Compose.call_in_group hp.run.toLocalRun hv hcd
  obtain ⟨x, rfl⟩ := @Compose.signed_only_in_ticks sp.toParams (goldilocksNode sp ro)
    proposer dg v _ _ _ C att (List.mem_of_getElem? hk)
  have hkk : kk < (Node.exec proposer dg v (tr.state v j) (tr.time d) (.tick x)).2.length := by
    by_contra h
    rw [List.getElem?_eq_none (not_lt.mp h)] at hk
    cases hk
  have hnomsg : ∀ i, j ≤ i → i ≤ d → ∀ ℓ, tr.projAC.CallAt v i ℓ → ∀ mm, ℓ.call ≠ .message mm := by
    intro i h1 h2 ℓ hc mm hmm
    have hl := (hg.2.1 (i - j) (by clear * - hdj hkk h2; omega)).2.2.2.2
    rw [Nat.add_sub_cancel' h1, (Compose.projAC_callAt.mp hc).2] at hl
    have hmem := List.getElem_mem
      (l := (Node.exec proposer dg v (tr.state v j) (tr.time d) (.tick x)).2)
      (n := i - j) (by clear * - hdj hkk h2; omega)
    rw [← Option.some.inj hl] at hmem
    cases (exec_ac_call v _ _ _ hmem).2 mm hmm
  have hpre : ∀ i < j, ∀ ℓ, tr.projAC.CallAt v i ℓ → tr.time i = sp.ts m → ℓ.call = .restart := by
    intro i hi ℓ hc ht
    obtain ⟨ℓ', he, hr'⟩ := Compose.before_tick hp.run.toLocalRun hv ⟨x, hg⟩
      (Compose.projAC_callAt.mp hc) hi (by rw [ht, hdt])
    cases he
    exact hr'
  have hjr : j ≤ r := by
    by_contra hlt
    have hcl := hpre r (by clear * - hlt; omega) ℓv hpt.1 hrt
    rcases hpt.2 with ⟨mm, hmm, -⟩ | ⟨B, hB, -⟩ | ⟨e₀, he₀, -⟩
    · rw [hcl] at hmm; cases hmm
    · rw [hcl] at hB; cases hB
    · rw [restart_emits hp hv hpt.1 hcl] at he₀; cases he₀
  -- the slot-`m` votes of the signer's pools up to the signing are its own
  have hQ : ∀ c ≤ d, ∀ w ∈ (tr.projAC.state v c).pool m, w.val = v := by
    intro c hc w hw
    have hws : w.slot = m := SA.state_pool_slot sp hr hv c m w hw
    have hle : ∀ k₁, k₁ < c → sp.slot (tr.projAC.time k₁) ≤ m := fun k₁ hk₁ => by
      rw [← hslm, ← hdt]
      exact SA.slot_mono sp (hr.time_nonneg k₁) (hp.run.time_mono (by clear * - hc hk₁; omega))
    rcases SA.pool_origin hr hv c w (by rw [hws]; exact hw) with
      ⟨k₁, hk₁, hsend, -, hsl₁⟩ | ⟨k₁, hk₁, ℓ₁, hc₁, -, -, B, hB, hwB⟩
    · have hsk : sp.slot (tr.projAC.time k₁) = m := le_antisymm (hle k₁ hk₁) (by
        clear * - hws hsl₁; omega)
      have htk : tr.time k₁ = sp.ts m := le_antisymm (hdt ▸ hp.run.time_mono (by
          clear * - hc hk₁; omega))
        ((SA.ts_le_iff_le_slot sp (hr.time_nonneg k₁) _).2 (by rw [hsk]))
      obtain ⟨ℓ₁, hc₁, ⟨e₁, he₁, rfl⟩ | ⟨hnr, hn, hh⟩⟩ := hsend
      · exact (SA.castAt_spec hr hv ⟨hc₁, he₁⟩).1
      · have hjk : j ≤ k₁ := by
          by_contra h
          exact hnr (hpre k₁ (by clear * - h; omega) ℓ₁ hc₁ htk)
        have he := hr.exec k₁ ℓ₁ hc₁.2 (hc₁.1 ▸ hv)
        rw [hc₁.1] at he
        change w ∈ (tr.projAC.post k₁).pool w.slot at hh
        have hpost : tr.projAC.post k₁ = ((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step v
            (tr.projAC.state v k₁) ℓ₁.frame (tr.projAC.time k₁) ℓ₁.call).1 := by rw [he]
        rw [hpost] at hh
        have hts : tr.projAC.time k₁ = sp.ts (sp.slot (tr.projAC.time k₁)) := by
          rw [hsk]; exact htk
        rcases step_pool_new v _ ℓ₁.frame hts hΔ ℓ₁.call (hnomsg k₁ hjk (by
            clear * - hc hk₁; omega) ℓ₁ hc₁) hnr
          hh with h | h | ⟨B, hB, hwB⟩
        · exact absurd h hn
        · exact h
        · exfalso
          have hBt := (SA.accept_new sp hr hv ⟨ℓ₁, hc₁, hB⟩).1 ℓ₁ hc₁
          have h₁ := (SA.frame_validPayload sp hr hv hc₁ B hBt).1 w hwB
          have h₂ := SA.frame_slot_le sp hr hv hc₁ B hBt
          clear * - hws hsk h₁ h₂; omega
    · exfalso
      have h₁ := (SA.frame_validPayload sp hr hv hc₁ B hB).1 w hwB
      have h₂ := SA.frame_slot_le sp hr hv hc₁ B hB
      have h₃ := hle k₁ hk₁
      clear * - hws h₁ h₂ h₃; omega
  -- so the pool of the optimistic check holds slot-`m` votes of the signer only
  have hP : ∀ w ∈ A.pool m, w.val = v := by
    intro w hw
    have hws := SA.optimisticPoint_pool_slot hr hv hpt hw
    obtain ⟨hcv, hcase⟩ := hpt
    rcases hcase with ⟨mm, hmm, -⟩ | ⟨B, hB, rfl⟩ | ⟨e₀, he₀, rfl⟩
    · exact absurd hmm (hnomsg r hjr hrd.le ℓv hcv mm)
    · rcases receipt_pool_mem hw with hw | hwB
      · exact hQ r hrd.le w hw
      · exfalso
        have hBt := (SA.accept_new sp hr hv ⟨ℓv, hcv, hB⟩).1 ℓv hcv
        have h₁ := (SA.frame_validPayload sp hr hv hcv B hBt).1 w hwB
        have h₂ := SA.frame_slot_le sp hr hv hcv B hBt
        have h₃ : sp.slot (tr.projAC.time r) = m := hsl
        clear * - hsl hws h₁ h₂; omega
    · rcases admit_pool_mem hw with hw | rfl
      · exact hQ (r + 1) hrd w (SA.readPoint_pool hr hv ⟨hcv, he₀⟩ hw).1
      · exact (SA.castAt_spec hr hv ⟨hcv, he₀⟩).1
  have h34 : 3 * sp.n ≤ 4 * (SA.optimisticVoters sp A ℓv.frame m D).ncard := by
    have h := hsel
    unfold SA.optimisticSelect at h
    dsimp only at h
    split_ifs at h
    have := (SA.deepest_mem h).1.2.1
    rwa [hsl] at this
  have hsub : SA.optimisticVoters sp A ℓv.frame m D ⊆ {v} := by
    rintro i ⟨w, hw, rfl, -⟩
    exact hP w hw
  have hle1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_singleton] at hle1
  have hn := sp.toParams.hn
  have hn' : sp.n = sp.toParams.n := rfl
  refine ⟨by (clear * - h34 hn' hle1 hn; omega), ?_⟩
  obtain ⟨i, w, hw, rfl, -⟩ :=
    Set.nonempty_of_ncard_ne_zero (s := SA.optimisticVoters sp A ℓv.frame m D) (by
        clear * - h34 hn' hn; omega)
  have hwv := hP w hw
  obtain ⟨hws, j', hj', e', hve', he'⟩ := SA.optimisticPoint_pool_vote hrun' hv hpt hw (hwv ▸ hv)
  exact ⟨j', hj', e', hwv ▸ hve', by rw [he', hws]⟩

/-- **A delivery at `t_m + Δ` comes after the slot-`m` vote** (the
signing at `t_m + Δ`). At a public time a node's deliveries follow its tick, and its tick at
`t_m + Δ` casts its slot-`m` vote unless it voted in slot `m` already; so an honest voter of slot
`m` accepts no block at `t_m + Δ` before its vote. -/
private theorem vote_before_late_delivery {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) {i : Nat} {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hA : tr.AcceptAt y i W) (hik : i < k) (ht : tr.time i = sp.ts e.msg.slot + sp.Δ) :
    False := by
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := hrun'.localRun
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  set u := sp.ts e.msg.slot + sp.Δ with hu
  have hm0 : 0 ≤ sp.ts e.msg.slot := by simp only [SAParams.ts]; positivity
  have htk : tr.time k = u :=
    le_antisymm (Compose.cast_head_fcRoot hr hy hc).2 (ht ▸ hp.run.time_mono hik.le)
  have hslot : sp.slot u = e.msg.slot := SA.slot_of_mem sp _ (by linarith)
    (by simp only [hu, SAParams.ts]; push_cast; linarith)
  have hpub : sp.toParams.IsPublic u :=
    ⟨4 * (e.msg.slot : Int) + 1, by simp only [hu, SAParams.ts]; ring⟩
  -- the acceptance of `W` is a delivery: `t_m + Δ` is not a proposal time
  rcases Compose.blockCall_cases hp.run.toLocalRun hy hA with hgW | ⟨j, x, -, -, hP, -⟩
  swap
  · obtain ⟨-, hP2, -⟩ := hP
    rw [ht] at hP2
    change u = sp.toParams.slotTime (sp.slot u) at hP2
    rw [hslot, sp.slotTime_eq] at hP2
    have : u = sp.ts e.msg.slot + sp.Δ := hu
    simp only [SAParams.ts] at this
    linarith only [hΔ, hP2, this]
  rw [ht] at hgW
  -- the voter's tick at `t_m + Δ` precedes the delivery
  obtain ⟨jt, x, hgt⟩ := hp.run.tick_of_awake y hy u (by linarith only [hΔ, hm0]) hpub
    (htk ▸ hp.run.awake_of_call y hy k ⟨_, Compose.projAC_callAt.mp hc.1⟩)
  obtain ⟨hct, htt⟩ := tick_first_cut hgt
  have hjti : jt < i := by
    rcases lt_trichotomy jt i with h | rfl | h
    · exact h
    · have := hct.2.symm.trans hA.2
      simp [Node.acCall] at this
    · have := hp.run.phase_order y hy y hy i jt u (.block W) (.tick x) hgW hgt h
      simp [Node.Event.phase] at this
  -- joined at the tick, as at the vote
  have hnrk : ℓ.call ≠ .restart := fun hcl => by
    have := hc.2
    rw [restart_emits hp hy hc.1 hcl] at this
    cases this
  have hjk : SA.joined sp (tr.projAC.state y k) u := by
    obtain ⟨-, -, hyj, -⟩ := SA.castAt_spec hr hy hc
    have he := hr.exec k ℓ hc.1.2 (hc.1.1 ▸ hy)
    rw [hc.1.1] at he
    have h1 : (tr.projAC.post k).restartTime = (tr.projAC.state y k).restartTime := by
      have hpost : tr.projAC.post k = ((SA.goldilocksSA sp (List (FG.Att sp.n)) ro).step y
          (tr.projAC.state y k) ℓ.frame (tr.projAC.time k) ℓ.call).1 := by rw [he]
      rw [hpost]
      exact SA.step_restartTime y _ _ _ _ hnrk
    unfold SA.joined at hyj ⊢
    rw [← h1, SA.restartTime_of_castAt hr hy hc, ← htk]
    exact hyj
  have hjp := Compose.joined_projection sp ro dg H tr proposer hp.run y hy u
  have hnr_k : ¬ tr.RestartAt y k := fun ⟨ℓ', hc', hr'⟩ => by
    have h := (Compose.projAC_callAt.mp hc.1).2.symm.trans hc'.2
    simp only [Option.some.injEq, Cut.ac.injEq] at h
    subst h
    exact hnrk hr'
  have hJ : tr.JoinedAt y u := (hjp.2.1 k ⟨_, Compose.projAC_callAt.mp hc.1⟩ hnr_k htk).mpr (by
    rw [← Compose.projAC_state hp.run.toLocalRun hy k]
    exact hjk)
  obtain ⟨ℓt, hlt, hcall⟩ : ∃ ℓt : ACLabel (goldilocksNode sp ro),
      tr.label jt = some (.ac ℓt) ∧ ℓt.call = .tick := ⟨_, hct.2, rfl⟩
  have hct' : tr.CallAt y jt (.ac ℓt) := ⟨hct.1, hlt⟩
  have hpt : tr.projAC.CallAt y jt ℓt := Compose.projAC_callAt.mpr hct'
  have hnrt : ¬ tr.RestartAt y jt := fun ⟨ℓ', hc', hr'⟩ => by
    have h := hlt.symm.trans hc'.2
    simp only [Option.some.injEq, Cut.ac.injEq] at h
    subst h
    rw [hcall] at hr'
    cases hr'
  have hjt : SA.joined sp (tr.projAC.state y jt) u := by
    rw [Compose.projAC_state hp.run.toLocalRun hy]
    exact (hjp.2.1 jt ⟨_, hct'⟩ hnrt htt).mp hJ
  -- the slot-`m` vote is at or before the tick
  have hve : SA.VoteAt tr.projAC y k e := ⟨ℓ, hc.1, hc.2⟩
  by_cases hvs : (tr.projAC.state y jt).votedSlot = (e.msg.slot : Int)
  · obtain ⟨j', hj', e', hve', hes⟩ := SA.cast_of_votedSlot hr hy jt e.msg.slot hvs
    have := ((SA.one_vote_per_slot sp) _ ro H _ tr.projAC hr y hy j' k e' e hve' hve hes).1
    clear * - hik hjti hj' this; omega
  · have hexec := hr.exec jt ℓt hpt.2 (hpt.1 ▸ hy)
    rw [hpt.1, hcall] at hexec
    have hne := Compose.acOnTick_votes (ro' := ro) y _ ℓt.frame hjt
      (by rw [hslot]; exact hvs) (by rw [hslot])
    rw [show tr.projAC.time jt = u from htt] at hexec
    rw [hexec] at hne
    obtain ⟨e', he'⟩ := List.exists_mem_of_ne_nil _ hne
    have hsl' := (SA.castAt_spec hr hy ⟨hpt, he'⟩).2.1
    have := ((SA.one_vote_per_slot sp) _ ro H _ tr.projAC hr y hy jt k e' e ⟨ℓt, hpt, he'⟩ hve
      (by rw [hsl']; change sp.slot (tr.time jt) = _; rw [htt, hslot])).1
    clear * - hik hjti this; omega

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
  obtain rfl := sign_unique hp hv hs₀ hs
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
      slot_start_optimistic hp hv hs (by rw [hcτ', hcc, hts]) hrd hopt
    obtain rfl : v = y := Fin.ext (by have := v.2; have := y.2; (clear * - hn1; omega))
    have := ((SA.one_vote_per_slot sp) _ ro H _ tr.projAC hr v hy j' k e' e hve'
      ⟨ℓ, hc.1, hc.2⟩ hes).1
    clear * - hik hd₀ hrd hj' this; omega
  · -- signed at `t_m + Δ`: the voter accepted `W` at `t_m + Δ`, before its vote
    refine vote_before_late_delivery hp hy hc hA hik (le_antisymm (by linarith only [hkt, h₃]) ?_)
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

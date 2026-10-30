module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Source
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset

public section

/-! # Goldilocks Healing: HR.4, height-scoped retention

(R1)–(R4) for the reset `a_z` over a Goldilocks run under `Healthy(g)` and `NoColl`. The author's
paper results (claims HR.4, status M; `producer-reset-continuation.md` §5 (R4, R5), §10, §11
(HBoot, reviewed), §13 (JointRet, reviewed), §16 (high records); healing-simple `t1-proof.md` §9
(the base case)): C1.1's first-violating-event induction over the run's cut index, with G1.10 at
the height-scoped scope (`𝓔_B` the entries of height `≥ H_z + 1` that conflict with `B`,
`T₀ = a_z − Δ`, every row signed at `a_z` covered by HR.1 (c)). It is not an instance of C1.1:
(K0) and (K1) need not hold at `a_z`.

**The induction** (JointRet §13, over the cut index of the fixed run, as C1.1's `persist_inv`).
The invariant at cut `k` has two parts:

* `VoteInv k`: (R3) at the honest votes cast at cut `k`, for **every** high origin of the run
  (a pending regular origin is activated before its first-transfer votes, which precede its
  write; JointRet's activation);
* `CacheInv k`: (R2) after an honest call at cut `k` at a time `≥ a_z`, for every high origin
  active at `k`: written at a cut `≤ k`, or of a label `j` with `t_{j+1} ≤` the time of `k`.

The base case is HBoot (§11, `boot_caches`: before `a_z` the honest `Σ.F` are compatible with
every high origin and no honest `Σ.J` is high) with the activation of pending origins
(`activation_caches`). The vote step (`retention_vote_step`) is C1.1's vote step: the caches at
the vote (`vote_state_caches`), (K2) by R5 (`vote_height_lead`), the fork-choice root compatible
with the origin (`vote_root_compatible`), then C1.1 (i) (`vote_viable_of_root`) and (ii)
(`high_vote_extends`, C1.1's `vote_extends` without the window `(s, m]` and without `Clean`). The
cut step (`retention_cut_step`) is G1.10 at the height-scoped scope. (R1)'s comparability is
`origins_compatible` (A1.9's counting: `fastLock_compatible_of_votes`, `fastLock_same_slot`) over
the votes of the invariant; (R1)'s rows are the provenance of the sources (`high_rows`, HR.1 (a));
(R4) is the high-record lemma (`high_records`, §16). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- `GST(g)` gives `Sync[a, b]` for every window that starts at or after `g`: an object sent at
`τ ≥ g` is processed as if sent at `max τ g = τ`. -/
theorem syncRun_of_gst {P : Params} {A : NodeAC P} {tr : RunTrace A} {H : Set (Fin P.n)}
    {ΔF g a b : Time} (h : tr.GSTRun H ΔF g) (hga : g ≤ a) : tr.SyncRun H ΔF a b := by
  have he : ∀ τ, a ≤ τ → max τ g = τ := fun τ hτ => max_eq_left (hga.trans hτ)
  refine ⟨h.deltaF, fun x hx i m hs hw => ?_, fun x hx i B hB hw => ?_,
    fun x hx i B hB hw => ?_, fun x hx i at' hs hw => ?_⟩
  · have := h.message x hx i m hs trivial
    simp only [he _ hw.1] at this
    exact this
  · have := h.block x hx i B hB trivial
    simp only [he _ hw.1] at this
    exact this
  · have := h.relay x hx i B hB trivial
    simp only [he _ hw.1] at this
    exact this
  · have := h.attestation x hx i at' hs trivial
    simp only [he _ hw.1] at this
    exact this

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (tr : GoldilocksTrace sp ro) (H : Set (Fin sp.n))

/-- **The premises of HR.4** for the reset `a`: a Goldilocks run under `Healthy(g)` and `NoColl`,
and `a` is the reset `a_z`. -/
structure ResetPremises (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (g ΔF a : Time) :
    Prop where
  run : GoldilocksRun dg H tr
  healthy : tr.HealthyRun H ΔF g
  noColl : Compose.NoCollRun dg tr
  reset : IsReset tr H g a

/-- (R3) at the honest votes cast at cut `k`, for every high origin `(B, j)` of the run: a vote
of a slot `> j` extends `B`, and at that vote `B` is in the viable voter block tree or
`B ⪯ fc_root` (in the honest blocks). -/
def VoteInv (g : Time) (k : Nat) : Prop :=
  ∀ x i j B, HighOrigin tr H g x i j B → ∀ y ∈ H, ∀ ℓ e, SA.CastAt tr.projAC y k ℓ e →
    j < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e.msg B ∧
      (B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
        Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot)

/-- (R2) after an honest call at cut `k` at a time `≥ a`, for every high origin `(B, j)` written
at a cut `≤ k` or activated by then (`t_{j+1} ≤` the time of `k`; JointRet §13): `Σ.F` is
compatible with `B`, and so is `Σ.J` when `Σ.h_j ≥ H_z + 1`. -/
def CacheInv (g a : Time) (k : Nat) : Prop :=
  ∀ y ∈ H, tr.IsCall y k → a ≤ tr.time k →
    ∀ x i j B, HighOrigin tr H g x i j B → (i ≤ k ∨ sp.ts (j + 1 : Nat) ≤ tr.time k) →
      Compatible (tr.HonestBlocks H) (tr.post k).fg.F B ∧
        (HZ tr H g + 1 ≤ (tr.post k).fg.hj → Compatible (tr.HonestBlocks H) (tr.post k).fg.J B)

variable {tr H} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-! ### Interfaces from the paper (open) -/

/-- **The label bound of a high origin** (§11, "Historical finality and acceptance": `j ≥ slot(c)`).
The writer accepted the counted heads, of state height `≥ H_z + 1`, before `t_j + 2Δ`; no honest
node accepts such a block at or before `c_z` (the definition of `H_z`), so `t_j + 2Δ > c_z`, and
`t_j ≥ c_z` since both are slot starts. -/
theorem cutZ_le_ts_of_highOrigin (hp : ResetPremises tr H dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) :
    cutZ sp.toParams g ≤ sp.ts j := by
  sorry

/-- **HBoot, the caches before the reset** (§11 "Historical finality and acceptance";
`t1-proof.md` §9). At a state all of whose earlier cuts are before `a`: no honest `Σ.J` is high
(a justification at `h ≥ H_z + 1` needs an honest row at `h`, none before `a`, HR.1 (c)), and
`Σ.F`, of height `≤ H_z` (no chain has crossed `H_z + 1`, G0.2 (a)), is below every high origin:
its finality quorum meets the crossing quorum on a counted head's chain at its height in an honest
validator (G1.2, G0.5, `f < 2q − n`). -/
theorem boot_caches (hp : ResetPremises tr H dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    (hk : ∀ k' < k, tr.time k' < a) :
    (tr.state y k).fg.hj ≤ HZ tr H g ∧
      ∀ x i j B, HighOrigin tr H g x i j B →
        Compatible (tr.HonestBlocks H) (tr.state y k).fg.F B := by
  sorry

/-- **Activation of a high origin** (§13 "Activation uses earlier labels, not D's own transfer",
"Retaining the witnesses and the frame"; §12, the pending boundary case). At the state at
`t_{j+1}` after the reset (immediately before the first-transfer votes of the origin's label `j`,
even when its write is later), every honest `Σ.F`, and every high honest `Σ.J`, is compatible with
the origin's block: low finalized entries by G1.2, high ones through their row witnesses, whose
sources are comparable with `B` by the label split (earlier labels by their votes, the same label
by TSQ, later labels excluded by R4). -/
theorem activation_caches (hp : ResetPremises tr H dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {k₁ : Nat} (hk₁ : tr.FirstCutFrom k₁ (sp.ts (j + 1 : Nat)))
    (ha : a < sp.ts (j + 1 : Nat))
    (ih : ∀ k' < k₁, VoteInv tr H g k' ∧ CacheInv tr H g a k') :
    Compatible (tr.HonestBlocks H) (tr.state y k₁).fg.F B ∧
      (HZ tr H g + 1 ≤ (tr.state y k₁).fg.hj →
        Compatible (tr.HonestBlocks H) (tr.state y k₁).fg.J B) := by
  sorry

/-- **(K2) at a vote, R5** (§5 Lemma R5; §11 item 1 for the votes through the ticks at `a_z`;
§13 "Retaining the witnesses and the frame"; `t1-proof.md` §9 base case). At an honest vote of a
slot `> j`, the voter block tree holds a viable descendant of the origin's block `B`, or
`B ⪯ fc_root`: in the low-frontier regime `B` itself (height `H_z + 1`, relayed before the freeze);
above it, the supporting head of an earlier comparable high source that crossed the floor (R4,
R5). -/
theorem vote_height_lead (hp : ResetPremises tr H dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) (hj : j < e.msg.slot) :
    (∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
      Anc (tr.HonestBlocks H) B D ∧ (tr.state y k).fg.IsViable D) ∨
    Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  sorry

/-- **A low `Σ.J` does not veto a high origin** (§11, "an old conflicting J merely causes a
contest"; `t1-proof.md` §9, the geometric statement). When the voter's root is a low `Σ.J`
(`h_max = h_j + 1 ≤ H_z + 1`, no contest) and its voter block tree holds a descendant `D` of the
origin's block `B`, then `D` has state height `h_max` (`≥ σ[B].h ≥ H_z + 1`), so it extends `Σ.J`
(no contest), and `Σ.J` is compatible with `B`. -/
theorem low_root_compatible (hp : ResetPremises tr H dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) (hj : j < e.msg.slot)
    (hroot : (tr.state y k).fg.hmax = (tr.state y k).fg.hj + 1 ∧ ¬ (tr.state y k).fg.Contest)
    (hlow : (tr.state y k).fg.hj ≤ HZ tr H g) {D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hD : D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot)
    (hBD : Anc (tr.HonestBlocks H) B D) :
    Compatible (tr.HonestBlocks H) (tr.state y k).fg.J B := by
  sorry

/-- **`Carry` at a first-transfer vote** (§11 "Historical finality and acceptance", §13
"Retaining the witnesses and the frame"). At an honest vote of slot `j + 1` at which `B` is not
below `fc_root` (so `Σ.F ⪯ B`), the voter holds the counted votes of the origin and has accepted
their heads before `t_j + 3Δ`: the heads, of height `≥ H_z + 1`, were first accepted after `c_z`
and before `t_j + 2Δ`, and extend `Σ.F`, so acceptance relay delivers them. -/
theorem first_carry (hp : ResetPremises tr H dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (ho : HighOrigin tr H g x i j B) (hfl : Compose.StoredFastLockAt tr x i j B CV)
    {y : Fin sp.n} (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y k ℓ e)
    (hs : e.msg.slot = j + 1) (hroot : ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV := by
  sorry

/-- **`Carry` at a later vote** (§11 "First-violating-vote induction", §13 "Retaining the
witnesses and the frame"). At an honest vote of slot `m' + 1`, `m' > j`, at which `B` is not below
`fc_root`, the voter holds the honest slot-`m'` votes and has accepted their heads (which extend
`B`, by the earlier votes, hence `Σ.F`) before `t_{m'} + 3Δ`, by relay. -/
theorem later_carry (hp : ResetPremises tr H dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) {m' : Nat} (hm' : e.msg.slot = m' + 1) (hjm : j < m')
    (hroot : ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e m' (Compose.honestVotes tr H m') := by
  sorry

/-- **Half of the committee votes** (`Healthy(g)`): in a slot `s'` with `t_{s'} ≥ c_z`, every
honest validator is awake and joined (no honest restart after `max(g, 0)`) and votes by
`t_{s'} + Δ` (`tryVote`), and the honest validators are at least half of the committee
(`3f ≤ n − 1`). -/
theorem half_committee (hp : ResetPremises tr H dg g ΔF a) {s' : Nat}
    (hs : cutZ sp.toParams g ≤ sp.ts s') :
    sp.n ≤ 2 * {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x' j e' ∧ e'.msg.slot = s'}.ncard := by
  sorry

/-- **No honest restart after `t_{slot(ḡ)+1}`** (`Healthy(g)`): a restart follows a time `u` at
which the node was asleep with no call in `[u, restart)`; `u ≥ ḡ` contradicts `Healthy(g)`, and
`u < ḡ` contradicts the tick at the public time `t_{slot(ḡ)+1} ≥ ḡ`, at which the node is awake. -/
theorem restart_le (hp : ResetPremises tr H dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    (hk : tr.RestartAt y k) : tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
  by_contra hlt
  obtain ⟨u, -, -, hu, hprev⟩ := hp.run.sleep_of_restart y hy k hk
  have hp₀ : gbar g ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
    have h := (SA.ts_le_iff_le_slot sp (gbar_nonneg g) ((sp.slot (gbar g) + 1 : Nat) : Int)).not.mpr
      (by push_cast; omega)
    exact (not_le.mp h).le
  by_cases hgu : gbar g ≤ u
  · exact hu (hp.healthy.2.1 y hy u hgu)
  · obtain ⟨j, _x, hne, hcs, -⟩ := hp.run.tick_of_awake y hy _ ((gbar_nonneg g).trans hp₀)
      ⟨4 * ((sp.slot (gbar g) + 1 : Nat) : Int), by simp only [SAParams.ts]; ring⟩
      (hp.healthy.2.1 y hy _ hp₀)
    obtain ⟨hn, ht, -, -, hl⟩ := hcs 0 (List.length_pos_of_ne_nil hne)
    simp only [Nat.add_zero] at hn ht hl
    have hjk : j < k := by
      by_contra h
      have := hp.run.time_mono (not_lt.mp h)
      exact hlt (ht ▸ this)
    have := hprev j hjk ⟨_, hn, hl⟩
    exact hgu (by linarith)

/-- **`f < h_t` after the cut** (`Healthy(g)`): from `c_z` on every honest validator is awake
and joined (its restarts are at or before `t_{slot(ḡ)+1} < t_{slot(t) − 1}`, `restart_le`), and
`3f ≤ n − 1`. -/
theorem fault_bound_late (hp : ResetPremises tr H dg g ΔF a) {t : Time}
    (ht : cutZ sp.toParams g ≤ t) : tr.FaultBound H t := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hgt : gbar g ≤ t := by have := lt_cutZ sp g; linarith
  have ht0 : 0 ≤ t := (gbar_nonneg g).trans hgt
  have hs : sp.slot (gbar g) + 3 ≤ sp.slot t := by
    have h := (SA.ts_le_iff_le_slot sp ht0 ((sp.slot (gbar g) + 3 : Nat) : Int)).mp
      ((cutZ_eq sp g) ▸ ht)
    exact_mod_cast h
  have hsub : H ⊆ {y | y ∈ H ∧ tr.awake y t ∧ tr.JoinedAt y t} := by
    refine fun y hy => ⟨hy, hp.healthy.2.1 y hy t hgt, fun k hk _ => ?_⟩
    change 0 < sp.slot t ∧ tr.time k ≤ sp.toParams.slotTime (sp.slot t - 1)
    have he : sp.toParams.slotTime (sp.slot t - 1) = sp.ts ((sp.slot t - 1 : Nat) : Int) :=
      sp.slotTime_eq _
    refine ⟨by omega, (restart_le hp hy hk).trans ?_⟩
    rw [he]
    exact (SA.ts_le_iff sp).mpr (by omega)
  have hle : H.ncard ≤ tr.honestAwakeJoined H t := Set.ncard_le_ncard hsub
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h3 := hp.healthy.2.2
  have hn' : sp.n = sp.toParams.n := rfl
  have hpos := sp.toParams.hn
  unfold RunTrace.FaultBound
  omega

/-- **The cut step: G1.10 at the height-scoped scope** (claims HR.4, G1.10 "The healing reset
induction uses the same node with a height-scoped `𝓔`"; §12 "Steps available once each protected
origin is admitted"; §13 "Retaining the witnesses and the frame", "Closing the
first-violating-event induction"). (R2) after the honest call at cut `k`, from the invariant at the
earlier cuts and the votes of cut `k`: with `𝓔_B` the entries of height `≥ H_z + 1` that conflict
with `B` and `T₀ = a − Δ`, the first clause of (K1_𝓔) is HR.1 (c); the later-row clause holds
because every honest high row signed by then names an entry on the chain of a high origin
comparable with `B` (`high_rows`, `origins_compatible` over the earlier votes), and every row
signed at `a` is covered (HR.1 (c)); so no entry of `𝓔_B` is justified or left on an accepted
chain. A low finalized entry is below `B` by G1.2; a high one has a row witness whose source is
comparable with `B`. No (K0) is used. The core is `Store.quorum_free_entries` with `𝓔 = 𝓔_B`;
`Store.cut_scope` (C1.1's scope) does not apply as stated: it assumes (K0) for `Σ.J` and (K1) for
every conflicting entry above an honest `Σ.F` at `Ts`, low ones included, which fail at `a_z`. -/
theorem retention_cut_step (hp : ResetPremises tr H dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') (hv : VoteInv tr H g k) :
    CacheInv tr H g a k := by
  sorry

/-- **(R1), the rows** (HR.1 (a), A1.5 with `τ = ḡ`; §16). The source `C` of an honest row signed
at or after `a` (from `c_z` on) is at or below the block of a live fast lock written after `ḡ`,
which is at or below the stored block `B` of that write; the row's height pair is `C`'s height and
entry, so `B` has state height `≥ σ[C].h ≥ H_z + 1` (a high origin), and the named entry is the
entry at that height on `B`'s chain in the writer's tree. -/
theorem high_rows (hp : ResetPremises tr H dg g ΔF a) :
    ∀ y ∈ H, ∀ k att, tr.SignAt y k att → a ≤ tr.time k → HZ tr H g + 1 ≤ att.h →
      ∃ x i j B, HighOrigin tr H g x i j B ∧ ∃ E ∈ (tr.state x i).fg.tree,
        (tr.state x i).fg.Anc E B ∧ E.root = att.T ∧ ((tr.state x i).fg.σ E.root).h = att.h ∧
        ((tr.state x i).fg.σ E.root).Th = E.root := by
  sorry

/-- **(R4), the high-record lemma** (§16). From (R1): before `a` no honest row has height
`≥ H_z + 1` (HR.1 (c)), and its finality pair is below its height pair (G0.5), so the high record
coordinates start empty; every later record write at `h ≥ H_z + 1` names the entry at `h` of the
writing source's chain, which lies on the chain of a high origin (R1, rows), and the high origins
are pairwise comparable (R1), so two named entries at one height are equal (entry constancy on a
chain). Induction over the serialized honest client calls. -/
theorem high_records (hp : ResetPremises tr H dg g ΔF a)
    (hcomp : ∀ x i j B x' i' j' B', HighOrigin tr H g x i j B → HighOrigin tr H g x' i' j' B' →
      Compatible (tr.HonestBlocks H) B B')
    (hrows : ∀ y ∈ H, ∀ k att, tr.SignAt y k att → a ≤ tr.time k → HZ tr H g + 1 ≤ att.h →
      ∃ x i j B, HighOrigin tr H g x i j B ∧ ∃ E ∈ (tr.state x i).fg.tree,
        (tr.state x i).fg.Anc E B ∧ E.root = att.T ∧ ((tr.state x i).fg.σ E.root).h = att.h ∧
        ((tr.state x i).fg.σ E.root).Th = E.root) :
    ∀ h, HZ tr H g + 1 ≤ h →
      {r | ∃ y ∈ H, ∃ i, (tr.state y i).record.target h = some r ∨
        r ∈ (tr.state y i).record.timeout h ∨
        (tr.state y i).record.lock h = some r}.Subsingleton := by
  sorry

/-! ### The vote step -/

/-- The label of a high origin starts at or after `g` (`t_j ≥ c_z > ḡ ≥ g`). -/
theorem le_ts_of_highOrigin (hp : ResetPremises tr H dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) : g ≤ sp.ts j := by
  have h₁ := cutZ_le_ts_of_highOrigin hp ho
  have h₂ := lt_cutZ sp g
  have h₃ := le_gbar g
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  linarith

/-- **The caches at a vote** (as C1.1's `state_caches`): at a cut at or after `t_{j+1}`, the
caches of an honest node's state are those after its last call, by `CacheInv` (the origin is
active there) when that call is at or after `a`, by HBoot (`boot_caches`) when it is before `a`,
and by activation (`activation_caches`) when there is no call since `t_{j+1}`. -/
theorem vote_state_caches (hp : ResetPremises tr H dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) (hk : sp.ts (j + 1 : Nat) ≤ tr.time k) :
    Compatible (tr.HonestBlocks H) (tr.state y k).fg.F B ∧
      (HZ tr H g + 1 ≤ (tr.state y k).fg.hj →
        Compatible (tr.HonestBlocks H) (tr.state y k).fg.J B) := by
  classical
  have hex : ∃ k', sp.ts (j + 1 : Nat) ≤ tr.time k' := ⟨k, hk⟩
  have hk₁ : Nat.find hex ≤ k := Nat.find_min' hex hk
  have hfirst : tr.FirstCutFrom (Nat.find hex) (sp.ts (j + 1 : Nat)) :=
    ⟨Nat.find_spec hex, fun k' hk' => not_le.mp (Nat.find_min hex hk')⟩
  have hboot : ∀ k₀, (∀ k' < k₀, tr.time k' < a) →
      Compatible (tr.HonestBlocks H) (tr.state y k₀).fg.F B ∧
        (HZ tr H g + 1 ≤ (tr.state y k₀).fg.hj →
          Compatible (tr.HonestBlocks H) (tr.state y k₀).fg.J B) := fun k₀ hk₀ => by
    obtain ⟨hj, hF⟩ := boot_caches hp hy hk₀
    exact ⟨hF x i j B ho, fun h => absurd (h.trans hj) (Nat.not_succ_le_self _)⟩
  rcases Compose.state_of_le (tr := tr) (y := y) hk₁ with h | ⟨k', hk', hk'k, hc, h⟩
  · rw [h]
    by_cases hta : sp.ts (j + 1 : Nat) ≤ a
    · exact hboot _ fun k' hk' => lt_of_lt_of_le (hfirst.2 k' hk') hta
    · exact activation_caches hp ho hy hfirst (not_le.mp hta)
        fun k' hk' => ih k' (lt_of_lt_of_le hk' hk₁)
  · rw [h]
    have hact : sp.ts (j + 1 : Nat) ≤ tr.time k' := hfirst.1.trans (hp.run.time_mono hk')
    by_cases hak : a ≤ tr.time k'
    · exact (ih k' hk'k).2 y hy hc hak x i j B ho (Or.inr hact)
    · obtain ⟨c, hc'⟩ := hc
      rw [← Trace.state_succ_of_call _ hc']
      exact hboot _ fun k'' hk'' =>
        lt_of_le_of_lt (hp.run.time_mono (Nat.lt_succ_iff.mp hk'')) (not_le.mp hak)

/-- **The fork-choice root at a vote is compatible with the origin**: it is `Σ.F` (compatible,
`vote_state_caches`), a high `Σ.J` (compatible, `vote_state_caches`), or a low `Σ.J`, which is
compatible by (K2) (`low_root_compatible`, or `B ⪯ fc_root`). -/
theorem vote_root_compatible (hp : ResetPremises tr H dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) (hj : j < e.msg.slot)
    (hK2 : (∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B D ∧ (tr.state y k).fg.IsViable D) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    Compatible (tr.HonestBlocks H) ℓ.frame.fcRoot B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hp.run hp.noColl).localRun
  have hts' : sp.ts e.msg.slot ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).mpr (by rw [(SA.castAt_spec hr hy hc).2.1])
  have hts : sp.ts (j + 1 : Nat) ≤ tr.time k :=
    ((SA.ts_le_iff sp).mpr (by exact_mod_cast hj : ((j + 1 : Nat) : Int) ≤ e.msg.slot)).trans hts'
  have hcache := vote_state_caches hp k ih ho hy hts
  have hroot_eq : ℓ.frame.fcRoot = (tr.state y k).fg.fcRoot := by
    rw [Compose.frame_of_projAC hp.run hy hc.1]; rfl
  rw [hroot_eq] at hK2 ⊢
  by_cases hroot : (tr.state y k).fg.hmax = (tr.state y k).fg.hj + 1 ∧ ¬ (tr.state y k).fg.Contest
  · rw [Store.fcRoot, ite_eq_left hroot] at hK2 ⊢
    by_cases hlow : (tr.state y k).fg.hj ≤ HZ tr H g
    · rcases hK2 with ⟨D, hD, hBD, -⟩ | hBJ
      · exact low_root_compatible hp ho hy hc hj hroot hlow hD hBD
      · exact Or.inr hBJ
    · exact hcache.2 (by omega)
  · rw [Store.fcRoot, ite_eq_right hroot]
    exact hcache.1

/-- **C1.1 (i) at a vote, from a compatible root** (C1.1's `vote_viable`, with the compatibility
of `fc_root` with `B` as the premise instead of both caches): with (K2), `B` is in the viable voter
block tree or at or below `fc_root`. -/
theorem vote_viable_of_root (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y k ℓ e)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hcomp : Compatible (tr.HonestBlocks H) ℓ.frame.fcRoot B)
    (hK2 : (∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
        Anc (tr.HonestBlocks H) B D ∧ (tr.state y k).fg.IsViable D) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hrun hnc).localRun
  have hU := hr.coherent
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy k ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  have hfr := Compose.frame_of_projAC hrun hy hc.1
  rcases hK2 with ⟨D, hD, hBD, hvD⟩ | h
  · rcases hcomp with hfB | hBf
    · have hDt : D ∈ ℓ.frame.tree := hD.1
      have hFB := (Anc.mono hΦU hΦ.F_anc_fcRoot).trans hfB
      have hBt := SA.frame_mem_of_between sp hU hΦ hΦU hDt hBD hFB
      have hΦBD := SA.anc_tree_of_anc_U hU hΦ hΦU hBt hBD hDt
      have hΦfB := SA.anc_tree_of_anc_U hU hΦ hΦU hΦ.fcRoot_mem hfB hBt
      refine Or.inl ⟨SA.voterBlockTree_anc hr hy hc D hD B hΦBD, hΦfB, D, hD, ?_, hΦBD⟩
      have hfD := hΦfB.trans hΦBD
      rw [hfr] at hDt hfD ⊢
      exact ⟨hDt.1, hDt.2, Anc.mono (fun X hX => hX.1) hfD, hvD⟩
    · exact Or.inr hBf
  · exact Or.inr h

/-- **C1.1 (ii) at a vote, height-scoped** (C1.1's `vote_extends` for a high origin, every slot
`> j` instead of the window `(j, m]`, and the premises one by one instead of `PersistPremises`,
whose `Clean` need not hold): when (i) holds at an honest vote of a slot `σ > j` and every honest
vote of a slot `> j` at an earlier cut extends `B`, the vote extends `B`: below `fc_root` by
requirement 1, otherwise by A1.2 for `σ = j + 1` (its stored-block form) and by A1.3 after. -/
theorem high_vote_extends (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
    {x : Fin sp.n} {i j : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hx : x ∈ H) (hfl : Compose.StoredFastLockAt tr x i j B CV) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) (hs : j < e.msg.slot)
    (hsync : tr.SyncRun H ΔF (sp.ts j) (sp.ts e.msg.slot + sp.Δ))
    (hcarry : e.msg.slot = j + 1 → ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot →
      SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV)
    (hcarryLater : ∀ m', e.msg.slot = m' + 1 → j < m' →
      ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot →
      SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e m' (Compose.honestVotes tr H m'))
    (hhalf : ∀ m', e.msg.slot = m' + 1 → j < m' →
      sp.n ≤ 2 * {x' | x' ∈ H ∧ ∃ j' e', SA.VoteAt tr.projAC x' j' e' ∧ e'.msg.slot = m'}.ncard)
    (hfault : tr.FaultBound H (tr.time k))
    (hviab : B ∈ ℓ.frame.viableTree (SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot) ∨
      Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot)
    (hprior : ∀ z ∈ H, ∀ j' < k, ∀ e', SA.VoteAt tr.projAC z j' e' → j < e'.msg.slot →
      SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr hrun hnc
  have hr := hrun'.localRun
  obtain ⟨⟨Hd, hHd, hHdr, hfHd⟩, hle⟩ := Compose.cast_head_fcRoot hr hy hc
  obtain ⟨-, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ tr.HonestBlocks H := by
    rcases hr.frameLaw y hy k ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  by_cases hBf : Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot
  · exact ⟨Hd, hΦU hHd, hHdr, hBf.trans (Anc.mono hΦU hfHd)⟩
  have hv := hviab.resolve_right hBf
  have h0 := hr.time_nonneg k
  have hsync0 := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val) tr
    ΔF (sp.ts j) (sp.ts e.msg.slot + sp.Δ) hrun.toLocalRun hsync
  have hfault' : SA.FaultBound tr.projAC H (tr.time k) := by
    unfold SA.FaultBound
    rw [← (Compose.joined_projection sp ro dg H tr hrun y hy (tr.time k)).2.2]
    exact hfault
  have hearlier : SA.EarlierVotesExtend tr.projAC H (tr.HonestBlocks H) k e.msg.slot B :=
    fun z hz j' hj' e' hv' hsl => hprior z hz j' hj' e' hv' (hsl ▸ hs)
  by_cases h1 : e.msg.slot = j + 1
  · obtain ⟨ℓw, D, hcw, hflD, hBD⟩ := hfl
    have hΦwU : ℓw.frame.tree ⊆ tr.HonestBlocks H := by
      rcases hr.frameLaw x hx i ℓw hcw with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.2
    refine SA.first_transfer_stored sp hrun' hx hflD
      (hBD ▸ Anc.mono hΦwU (SA.anc_viableAncestor ℓw.frame D)) hy hc h1
      (Compose.syncAC_mono hsync0 le_rfl hle) (hcarry h1 hBf) hfault' ?_ ?_
    · rw [← h1]; exact Or.inl hv
    · rw [← h1]; exact hearlier
  · obtain ⟨m', hm'⟩ : ∃ m', e.msg.slot = m' + 1 := ⟨e.msg.slot - 1, by omega⟩
    have hsm' : j < m' := by omega
    refine SA.next_transfer sp _ ro H _ tr.projAC hrun' m' y k B ℓ e hy hc hm' ?_
      (hhalf m' hm' hsm') (hcarryLater m' hm' hsm' hBf) hfault'
      (Compose.syncAC_mono hsync0 ((SA.ts_le_iff sp).mpr (Int.ofNat_le.mpr hsm'.le)) hle) ?_ ?_
    · intro z hz j' e' hv' hsl
      have hjk : j' < k := by
        by_contra hjk
        obtain ⟨ℓ', hc', he'⟩ := hv'
        have h₁ := (SA.castAt_spec hr hz ⟨hc', he'⟩).2.1
        have h₂ := SA.slot_mono sp h0 (hr.time_mono (not_lt.mp hjk))
        have h₃ := (SA.castAt_spec hr hy hc).2.1
        omega
      exact hprior z hz j' hjk e' hv' (by omega)
    · rw [← hm']; exact Or.inl hv
    · rw [← hm']; exact hearlier

/-- **The vote step** (§13 "Closing the first-violating-event induction"; §11 item 2 for the
votes through the ticks at `a_z`): (R3) at the honest votes of cut `k`, from the invariant at every
earlier cut: (K2) by R5 (`vote_height_lead`) and the root's compatibility
(`vote_root_compatible`) give (i) (`vote_viable_of_root`); (i), `Carry` (`first_carry`,
`later_carry`), the half committee and `f < h_t` after `c_z` (`Healthy(g)`) and the earlier votes
give (ii) (`high_vote_extends`). -/
theorem retention_vote_step (hp : ResetPremises tr H dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') : VoteInv tr H g k := by
  intro x i j B ho y hy ℓ e hc hj
  obtain ⟨CV, hfl⟩ := ho.2.2.1
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr hp.run hp.noColl).localRun
  have hts : sp.ts e.msg.slot ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).mpr (by rw [(SA.castAt_spec hr hy hc).2.1])
  have hlate : ∀ m : Nat, j ≤ m → cutZ sp.toParams g ≤ sp.ts m := fun m hm =>
    (cutZ_le_ts_of_highOrigin hp ho).trans ((SA.ts_le_iff sp).mpr (by exact_mod_cast hm))
  have hK2 := vote_height_lead hp k ih ho hy hc hj
  have hvi := vote_viable_of_root hp.run hp.noColl hy hc
    (vote_root_compatible hp k ih ho hy hc hj hK2) hK2
  refine ⟨high_vote_extends hp.run hp.noColl ho.1 hfl hy hc hj
    (syncRun_of_gst hp.healthy.1 (le_ts_of_highOrigin hp ho))
    (fun h1 hroot => first_carry hp k ih ho hfl hy hc h1 hroot)
    (fun m' hm' hjm hroot => later_carry hp k ih ho hy hc hm' hjm hroot)
    (fun m' _ hjm => half_committee hp (hlate m' hjm.le))
    (fault_bound_late hp ((hlate _ hj.le).trans hts)) hvi
    (fun z hz k' hk' e' ⟨ℓ', hc', he'⟩ h₁ =>
      ((ih k' hk').1 x i j B ho z hz ℓ' e' ⟨hc', he'⟩ h₁).1), hvi⟩

/-! ### The join and the assembly -/

/-- **The join**: the invariant holds at every cut (strong induction on the cut index, F.5
(run)). -/
theorem retention_inv (hp : ResetPremises tr H dg g ΔF a) :
    ∀ k, VoteInv tr H g k ∧ CacheInv tr H g a k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    exact ⟨retention_vote_step hp k ih, retention_cut_step hp k ih (retention_vote_step hp k ih)⟩

/-- **Two high origins are comparable** (§11 item 3, §13 "Activation uses earlier labels"), from
(R3) at the votes up to the later write: for labels `j < j'`, the later lock is supported by an
honest slot-`j'` vote (half of the committee, or three quarters, against `f < n/2`), which extends
`B` (`fastLock_compatible_of_votes`); for `j = j'`, two fast locks of one slot are compatible
(`fastLock_same_slot`, TSQ, with `Sync` from `GST(g)` since `t_j ≥ c_z`). The stored blocks are
ancestors of the selected ones. -/
theorem origins_compatible (hp : ResetPremises tr H dg g ΔF a) {x x' : Fin sp.n}
    {i j i' j' : Nat} {B B' : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B)
    (ho' : HighOrigin tr H g x' i' j' B') (hjj : j ≤ j') (hv : ∀ k ≤ i', VoteInv tr H g k) :
    Compatible (tr.HonestBlocks H) B B' := by
  have hrun' := Compose.goldilocks_ac_projection sp ro dg H tr hp.run hp.noColl
  have hr := hrun'.localRun
  have hU := hr.coherent
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have := hp.healthy.2.2
    have := Fin.pos x
    have hn : sp.n = sp.toParams.n := rfl
    omega
  have hsel : ∀ {x₀ : Fin sp.n} {i₀ j₀ : Nat} {B₀ : SA.Blk sp.n (List (FG.Att sp.n))}
      {CV₀ : Set (SA.Vote sp.n)}, x₀ ∈ H → Compose.StoredFastLockAt tr x₀ i₀ j₀ B₀ CV₀ →
      ∃ D, SA.FastLockAt tr.projAC x₀ i₀ j₀ D CV₀ ∧ Anc (tr.HonestBlocks H) B₀ D := by
    rintro x₀ i₀ j₀ B₀ CV₀ hx₀ ⟨ℓ, D, hc, hfl, rfl⟩
    have hΦU : ℓ.frame.tree ⊆ tr.HonestBlocks H := by
      rcases hr.frameLaw x₀ hx₀ i₀ ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨k, ℓ', -, -, -, h⟩ <;>
        exact h.1.2
    exact ⟨D, hfl, Anc.mono hΦU (SA.anc_viableAncestor ℓ.frame D)⟩
  obtain ⟨CV, hst⟩ := ho.2.2.1
  obtain ⟨CV', hst'⟩ := ho'.2.2.1
  obtain ⟨D, hfl, hBD⟩ := hsel ho.1 hst
  obtain ⟨D', hfl', hBD'⟩ := hsel ho'.1 hst'
  rcases hjj.lt_or_eq with hlt | rfl
  · have hD'B : Compatible (tr.HonestBlocks H) D' B :=
      SA.fastLock_compatible_of_votes hrun' ho'.1 (Nat.lt_succ_self i') hfl' hf
        fun z hz k hk e hve hsl => by
          obtain ⟨ℓ, hc, he⟩ := hve
          exact (hv k (Nat.lt_succ_iff.mp hk) x i j B ho z hz ℓ e ⟨hc, he⟩ (by omega)).1
    by_contra hn
    exact SA.not_compatible_of_anc hU hBD' hn hD'B.symm
  · have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
      tr ΔF (sp.ts j) (sp.ts (j + 1 : Nat) + sp.Δ) hp.run.toLocalRun
      (syncRun_of_gst hp.healthy.1 (le_ts_of_highOrigin hp ho))
    rcases SA.fastLock_same_slot hrun' ho.1 hfl ho'.1 hfl' hsync hf with h | h
    · exact SA.anc_total hU (hBD.trans h) hBD'
    · exact SA.anc_total hU hBD (hBD'.trans h)

/-- **HR.4, height-scoped retention** (HBoot §11, JointRet §13, high records §16): (R1)'s
comparability from the votes (`origins_compatible`), (R1)'s rows (`high_rows`), (R2) and (R3) from
the invariant (`retention_inv`), (R4) from (R1) (`high_records`). -/
theorem height_scoped_retention : HeightScopedRetention := by
  intro sp ro dg H tr g ΔF hrun hh hnc a ha
  have hp : ResetPremises tr H dg g ΔF a := ⟨hrun, hh, hnc, ha⟩
  have hinv := retention_inv hp
  have hcomp : ∀ x i j B x' i' j' B', HighOrigin tr H g x i j B →
      HighOrigin tr H g x' i' j' B' → Compatible (tr.HonestBlocks H) B B' := by
    intro x i j B x' i' j' B' ho ho'
    rcases le_total j j' with h | h
    · exact origins_compatible hp ho ho' h fun k _ => (hinv k).1
    · exact (origins_compatible hp ho' ho h fun k _ => (hinv k).1).symm
  have hrows := high_rows hp
  exact ⟨hcomp, hrows,
    fun y hy k hc hk x i j B ho hik => (hinv k).2 y hy hc hk x i j B ho (Or.inl hik),
    fun x i j B ho y hy k ℓ e hc hj => (hinv k).1 x i j B ho y hy ℓ e hc hj,
    high_records hp hcomp hrows⟩

end Consensus.Goldilocks.Healing

end

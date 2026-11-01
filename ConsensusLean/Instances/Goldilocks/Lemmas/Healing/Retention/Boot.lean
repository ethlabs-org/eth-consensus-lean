module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Records
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Finality
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ResultAnc
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Frame

public section

/-! # Goldilocks Healing, HR.4: the base case, activation, the vote premises and the records

HBoot (`boot_caches`), the activation of pending origins (`activation_caches`), the label bound,
(K2)/R5 at votes (`vote_height_lead`), the low-`Σ.J` root (`low_root_compatible`), `Carry`
(`first_carry`, `later_carry`), half the committee (`half_committee`) and (R4) (`high_records`).
Paper: `hr4-boot-carry.md` (workbench#23), `producer-reset-continuation.md` §§5, 11, 13, 16.

Proved here: the label bound, half the committee, the low-`Σ.J` root, both carries (relay after
the GST, `Retention/Relay`), (R4) (`Retention/Records`), HBoot's caches from G1.2 over the run
(`finalized_anc_of_height_lt`, `Retention/Finality`), and R5 below the floor (a counted head of
the origin, relayed in time; `relay_mem_voterBlockTree`), activation (`activation_caches`, the
rows' sources compared before the first cut of `t_{j+1}`, `origins_compatible_before`) and R5
above the floor (`height_lead_above`: no high contest, then the crossing of the floor, through
`Retention/Prefix`, with the report-time bound `row_origin_not_current`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-! ### The base case, the vote premises and the records -/

/-- A carried result ancestor below the receiver's floor threshold is an actual
frozen voter-tree witness. Genesis uses the genesis branch of `AcceptedBefore`;
it does not require a fictitious acceptance event. -/
theorem raw_result_low_floor_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H)
    {i₀ k s : Nat} {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hR : SA.ResultAt tr.projAC x i₀ s C CV) (hBC : Anc (tr.HonestBlocks H) B C)
    (hc : SA.CastAt tr.projAC y k ℓ e) (hs : e.msg.slot = s + 1)
    (hcarry : SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e s CV)
    (hFB : Anc (tr.HonestBlocks H) ℓ.frame.F B)
    (hfloor : (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ B.root).h) :
    B ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot ∧
      (tr.state y k).fg.IsViable B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hacc := SA.result_ancestor_accepted_before sp hr hx hR hBC hcarry
  have hBU : B ∈ tr.HonestBlocks H := by
    obtain ⟨ℓX, hupd, hC, _⟩ := hR
    by_cases heq : B = C
    · exact heq ▸ (SA.frameIn_of_callAt hr hx hupd.1).2 (SA.deepest_mem hC).1.1
    · exact (Anc.mem hBC heq).1
  exact ⟨hs ▸ Compose.accepted_voter_tree hrun hnc hy hc hs hBU hacc hFB, hfloor⟩

/-- **The label bound of a high origin** (§11, "Historical finality and acceptance": `j ≥ slot(c)`).
The writer accepted the counted heads, of state height `≥ H_z + 1`, before `t_j + 2Δ`; no honest
node accepts such a block at or before `c_z` (the definition of `H_z`), so `t_j + 2Δ > c_z`, and
`t_j ≥ c_z` since both are slot starts. -/
theorem ResetPremisesUpTo.cutZ_le_ts_of_highOrigin {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) :
    cutZ sp.toParams g ≤ sp.ts j := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨ℓ, D, CV, hc, hfl, -, -, -, hBD, -⟩ := hp.highOrigin_mem ho
  obtain ⟨v, hv⟩ := fastLock_counted_nonempty hfl
  obtain ⟨-, -, Hv, ⟨z, hz, k₀, hHv⟩, -, hDHv, hacc⟩ := fastLock_writer hr ho.1 hfl v hv
  have hBHv : Anc (tr.HonestBlocks H) B Hv :=
    (Anc.mono (SA.frameIn_of_callAt hr ho.1 hc).2 hBD).trans hDHv
  rcases hacc with hg | ⟨k, hk, hkt⟩
  · exact absurd hg (hp.cutZ_lt_of_anc ho hz hHv hBHv).2
  have hck := (hp.cutZ_lt_of_anc ho ho.1 (hp.acceptAt_mem ho.1 hk) hBHv).1
  have hkt' : tr.time k < sp.ts j + 2 * sp.Δ := hkt
  rw [cutZ_eq sp g] at hck ⊢
  refine (SA.ts_le_iff sp).2 ?_
  by_contra hlt
  have h₂ := (SA.ts_le_iff sp).2 (show (j : Int) + 1 ≤ ((sp.slot (gbar g) + 3 : Nat) : Int) by
    omega)
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  simp only [SAParams.ts] at h₂ hck hkt'
  nlinarith

/-- Whole-run specialization of the origin label lower bound. -/
theorem cutZ_le_ts_of_highOrigin (hp : ResetPremises tr H proposer dg g ΔF a)
    {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) :
    cutZ sp.toParams g ≤ sp.ts j :=
  (hp.toUpTo tr H (le_refl a)).cutZ_le_ts_of_highOrigin ho

/-- **No high justification before the reset** (`hr4-boot-carry.md` §2): at a state all of
whose earlier cuts are before `a`, every held block is justified at `≤ H_z`: otherwise it has state
height `≥ H_z + 2` (`h_j < h`), so its chain carries an honest row of height `H_z + 1` (HR.1 (b)),
signed before the state's cut, hence before `a`, against HR.1 (c). -/
theorem ResetPremisesUpTo.hj_le_HZ_of_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} (hk : ∀ k' < k, tr.time k' < a) {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y k).fg.tree) : ((tr.state y k).fg.σ X.root).hj ≤ HZ tr H g := by
  have hr := Compose.fg_reachable hp.run.toLocalRun hy k
  obtain ⟨c, -, -, -, hc⟩ := Store.chain_state_of_chain _ _ _ _ hr X hX
  obtain ⟨-, -, hjh, -⟩ := FG.chain_invariants _ _ _ hc
  by_contra hlt
  have hq : Hᶜ.ncard < sp.toParams.fg.q := by
    have h3 := hp.faults
    have hn := sp.toParams.hn
    change 3 * Hᶜ.ncard ≤ sp.toParams.n - 1 at h3
    change Hᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    omega
  obtain ⟨Y, hYX, att, hatt, hattH, hatth⟩ :=
    Store.exists_honest_att_of_lt hr hq hX (HZ tr H g + 1) (by omega) (by omega)
  have hY : Y ∈ (tr.state y k).fg.tree := by
    by_cases he : Y = X
    · exact he ▸ hX
    · exact (Anc.mem hYX he).1
  rcases tree_accepted hp.run.toLocalRun hy hY with rfl | ⟨i, hik, hA⟩
  · cases hatt
  obtain ⟨j, hji, hj⟩ := hp.run.att_unforgeable y hy i att (Or.inr ⟨Y, ⟨true, hA⟩, hatt⟩) hattH
  have := hp.reset.2 _ hattH j att hj hatth
  have := hk j (by omega)
  linarith

/-- Whole-run specialization of the pre-reset justification bound. -/
theorem hj_le_HZ_of_before (hp : ResetPremises tr H proposer dg g ΔF a) {y : Fin sp.n} (hy : y ∈ H)
    {k : Nat} (hk : ∀ k' < k, tr.time k' < a) {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ (tr.state y k).fg.tree) : ((tr.state y k).fg.σ X.root).hj ≤ HZ tr H g :=
  (hp.toUpTo tr H (le_refl a)).hj_le_HZ_of_before hy hk hX

/-- **HBoot, the caches before the reset** (§11 "Historical finality and acceptance";
`t1-proof.md` §9). At a state all of whose earlier cuts are before `a`: no honest `Σ.J` is high
(a justification at `h ≥ H_z + 1` needs an honest row at `h`, none before `a`, HR.1 (c)), and
`Σ.F`, of height `≤ H_z` (no chain has crossed `H_z + 1`, G0.2 (a)), is below every high origin:
its finality quorum meets the crossing quorum on a counted head's chain at its height in an honest
validator (G1.2, G0.5, `f < 2q − n`). -/
theorem ResetPremisesUpTo.boot_caches {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    (hk : ∀ k' < k, tr.time k' < a) :
    (tr.state y k).fg.hj ≤ HZ tr H g ∧
      ∀ x i j B, HighOrigin tr H g x i j B →
        Compatible (tr.HonestBlocks H) (tr.state y k).fg.F B := by
  have hr := Compose.fg_reachable hp.run.toLocalRun hy k
  obtain ⟨hFm, -, -, ⟨X, hX, -, hXj⟩, -, -, ⟨Y, hY, hYF⟩⟩ := Store.cache_invariants _ _ _ _ hr
  refine ⟨by rw [← hXj]; exact hp.hj_le_HZ_of_before hy hk hX, fun x i j B ho => Or.inl ?_⟩
  obtain ⟨c, -, -, -, hc⟩ := Store.chain_state_of_chain _ _ _ _ hr Y hY
  obtain ⟨-, hFj, -⟩ := FG.chain_invariants _ _ _ hc
  have := hp.hj_le_HZ_of_before hy hk hY
  have := ho.2.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, hBx⟩ := hp.highOrigin_mem ho
  exact finalized_anc_of_height_lt_of_run hp.run hp.noColl hp.faults
    hy ho.1 hY hFm hYF.symm hBx (by omega)

/-- Whole-run specialization of the pre-reset cache bounds. -/
theorem boot_caches (hp : ResetPremises tr H proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat}
    (hk : ∀ k' < k, tr.time k' < a) :
    (tr.state y k).fg.hj ≤ HZ tr H g ∧
      ∀ x i j B, HighOrigin tr H g x i j B →
        Compatible (tr.HonestBlocks H) (tr.state y k).fg.F B :=
  (hp.toUpTo tr H (le_refl a)).boot_caches hy hk

/-- The label of a high origin starts at or after `g` (`t_j ≥ c_z > ḡ ≥ g`). -/
private theorem g_le_ts (hp : ResetPremises tr H proposer dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {m : Nat}
    (hm : j ≤ m) : g ≤ sp.ts m := by
  have h₁ := cutZ_le_ts_of_highOrigin hp ho
  have h₂ := lt_cutZ sp g
  have h₃ := le_gbar g
  have h₄ := (SA.ts_le_iff sp).2 (show (j : Int) ≤ m by exact_mod_cast hm)
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  linarith

/-- Vote extension for origins and votes strictly before a cut, without cache invariants. -/
def HistoricalVoteExtensionBefore (k : Nat) : Prop :=
  ∀ x i j B, HighOrigin tr H g x i j B → i < k →
    ∀ z ∈ H, ∀ q < k, ∀ e, SA.VoteAt tr.projAC z q e →
      j < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B

/-- Public characterization for constructing and applying historical vote extension. -/
theorem historicalVoteExtensionBefore_iff (k : Nat) :
    HistoricalVoteExtensionBefore (tr := tr) (H := H) (g := g) k ↔
      ∀ x i j B, HighOrigin tr H g x i j B → i < k →
        ∀ z ∈ H, ∀ q < k, ∀ e, SA.VoteAt tr.projAC z q e →
          j < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B := by
  rfl

/-- Two written historical origins are compatible using only historical vote extension.
The label split is the vote-extension fragment of `origins_compatible_before`. -/
theorem historical_origins_compatible_before
    (hp : ResetPremises tr H proposer dg g ΔF a) {k : Nat}
    (hv : HistoricalVoteExtensionBefore (tr := tr) (H := H) (g := g) k)
    {x x' : Fin sp.n} {i j r l : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : HighOrigin tr H g x i j B) (hi : i < k)
    (hO : HighOrigin tr H g x' r l O) (hr : r < k) :
    Compatible (tr.HonestBlocks H) B O := by
  rw [historicalVoteExtensionBefore_iff] at hv
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hU := hrun.localRun.coherent
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have := hp.healthy.2.2
    have := Fin.pos x
    have hn : sp.n = sp.toParams.n := rfl
    omega
  obtain ⟨CV, hst⟩ := hB.2.2.1
  obtain ⟨CV', hst'⟩ := hO.2.2.1
  obtain ⟨-, D, hfl, hBD⟩ := storedFastLock_mem hp.run hp.noColl hB.1 hst
  obtain ⟨-, D', hfl', hOD'⟩ := storedFastLock_mem hp.run hp.noColl hO.1 hst'
  rcases lt_trichotomy l j with hlt | rfl | hgt
  · have hDO : Compatible (tr.HonestBlocks H) D O :=
      SA.fastLock_compatible_of_votes hrun hB.1 (Nat.lt_succ_self i) hfl hf
        fun z hz q hq e he hs => hv x' r l O hO hr z hz q (by omega) e he (by omega)
    by_contra hn
    exact SA.not_compatible_of_anc hU hBD (fun h => hn h.symm) hDO.symm
  · have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H
      (fun v => v.val) tr proposer ΔF (sp.ts l) (sp.ts (l + 1 : Nat) + sp.Δ) hp.run.toLocalRun
      (syncRun_of_gst hp.healthy.1 (g_le_ts hp hB le_rfl))
    rcases SA.fastLock_same_slot hrun hB.1 hfl hO.1 hfl' hsync hf with h | h
    · exact SA.anc_total hU (hBD.trans h) hOD'
    · exact SA.anc_total hU hBD (hOD'.trans h)
  · have hDB : Compatible (tr.HonestBlocks H) D' B :=
      SA.fastLock_compatible_of_votes hrun hO.1 (Nat.lt_succ_self r) hfl' hf
        fun z hz q hq e he hs => hv x i j B hB hi z hz q (by omega) e he (by omega)
    by_contra hn
    exact SA.not_compatible_of_anc hU hOD' hn hDB.symm

/-- An activated origin, including a pending write, is compatible with historical origins
from vote extension alone. Slot timing puts its counted votes before the observation cut. -/
theorem activated_origin_compatible_before
    (hp : ResetPremises tr H proposer dg g ΔF a) {k : Nat}
    (hv : ∀ x i j B, HighOrigin tr H g x i j B →
      ∀ z ∈ H, ∀ q < k, ∀ e, SA.VoteAt tr.projAC z q e →
        j < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B)
    {x x' : Fin sp.n} {i j r l : Nat} {B O : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB : HighOrigin tr H g x i j B) (hact : sp.ts (j + 1 : Nat) ≤ tr.time k)
    (hO : HighOrigin tr H g x' r l O) (hr : r < k) :
    Compatible (tr.HonestBlocks H) B O := by
  have hrun := Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hU := hrun.localRun.coherent
  have hf : 2 * Hᶜ.ncard < sp.n := by
    have := hp.healthy.2.2
    have := Fin.pos x
    have hn : sp.n = sp.toParams.n := rfl
    omega
  obtain ⟨CV, hst⟩ := hB.2.2.1
  obtain ⟨CV', hst'⟩ := hO.2.2.1
  obtain ⟨-, D, hfl, hBD⟩ := storedFastLock_mem hp.run hp.noColl hB.1 hst
  obtain ⟨-, D', hfl', hOD'⟩ := storedFastLock_mem hp.run hp.noColl hO.1 hst'
  rcases lt_trichotomy l j with hlt | rfl | hgt
  · have hcut : ∀ z ∈ H, ∀ q, ∀ e, SA.VoteAt tr.projAC z q e → e.msg.slot = j → q < k := by
      intro z hz q e ⟨ell, hc, he⟩ hs
      by_contra hq
      have htime := hact.trans (hp.run.time_mono (Nat.le_of_not_gt hq))
      have hslot := (SA.ts_le_iff_le_slot sp (hrun.localRun.time_nonneg q)
        ((j + 1 : Nat) : Int)).mp htime
      have hcast := (SA.castAt_spec hrun.localRun hz ⟨hc, he⟩).2.1
      omega
    have hDO : Compatible (tr.HonestBlocks H) D O :=
      SA.fastLock_compatible_of_votes hrun hB.1 (Nat.lt_succ_self i) hfl hf
        fun z hz q _ e he hs => hv x' r l O hO z hz q (hcut z hz q e he hs) e he (by omega)
    by_contra hn
    exact SA.not_compatible_of_anc hU hBD (fun h => hn h.symm) hDO.symm
  · have hsync := Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H
      (fun v => v.val) tr proposer ΔF (sp.ts l) (sp.ts (l + 1 : Nat) + sp.Δ) hp.run.toLocalRun
      (syncRun_of_gst hp.healthy.1 (g_le_ts hp hB le_rfl))
    rcases SA.fastLock_same_slot hrun hB.1 hfl hO.1 hfl' hsync hf with h | h
    · exact SA.anc_total hU (hBD.trans h) hOD'
    · exact SA.anc_total hU hBD (hOD'.trans h)
  · have hDB : Compatible (tr.HonestBlocks H) D' B :=
      SA.fastLock_compatible_of_votes hrun hO.1 (Nat.lt_succ_self r) hfl' hf
        fun z hz q hq e he hs => hv x i j B hB z hz q (by omega) e he (by omega)
    by_contra hn
    exact SA.not_compatible_of_anc hU hOD' hn hDB.symm

/-- **Activation of a high origin** (§13 "Activation uses earlier labels, not D's own transfer",
"Retaining the witnesses and the frame"; §12, the pending boundary case). At the state at
`t_{j+1}` after the reset (immediately before the first-transfer votes of the origin's label `j`,
even when its write is later), every honest `Σ.F`, and every high honest `Σ.J`, is compatible with
the origin's block: low finalized entries by G1.2, high ones through their row witnesses, whose
sources are comparable with `B` by the label split (earlier labels by their votes, the same label
by TSQ, later labels excluded by R4). -/
theorem ResetPremisesUpTo.activation_caches {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {k₁ : Nat} (hk₁ : tr.FirstCutFrom k₁ (sp.ts (j + 1 : Nat)))
    (hib : tr.time i ≤ b) (hkb : tr.time k₁ ≤ b)
    (hvote : ∀ {x₀ : Fin sp.n} {i₀ j₀ : Nat} {B₀ : SA.Blk sp.n (List (FG.Att sp.n))},
      HighOrigin tr H g x₀ i₀ j₀ B₀ → tr.time i₀ ≤ b →
      ∀ z ∈ H, ∀ c < k₁, tr.time c ≤ b → ∀ e, SA.VoteAt tr.projAC z c e →
        j₀ < e.msg.slot → SA.VoteExtends (tr.HonestBlocks H) e.msg B₀) :
    Compatible (tr.HonestBlocks H) (tr.state y k₁).fg.F B ∧
      (HZ tr H g + 1 ≤ (tr.state y k₁).fg.hj →
        Compatible (tr.HonestBlocks H) (tr.state y k₁).fg.J B) := by
  have hU := hp.honest_coherent
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy k₁
  have hsub : (tr.state y k₁).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, k₁, hX⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hBx⟩ := hp.highOrigin_mem ho
  have hgB := ((Goldilocks.Store.accepted_tree _ _ _ _
    (Compose.fg_reachable hp.run.toLocalRun ho.1 i)).2.2.2 B hBx).mono
      (fun X hX => (⟨x, ho.1, i, hX⟩ : X ∈ tr.HonestBlocks H))
  have hg : g ≤ sp.ts j := by
    have h₁ := hp.cutZ_le_ts_of_highOrigin ho
    have h₂ := lt_cutZ sp g
    have h₃ := le_gbar g
    have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
    linarith
  have hact : i < k₁ ∨ ∀ c, tr.time c < sp.ts (j + 1 : Nat) → c < k₁ :=
    Or.inr fun c hc => not_le.mp fun hle => absurd (hk₁.1.trans (hp.run.time_mono hle))
      (not_le.mpr hc)
  -- every honest row on the store was signed before `k₁` and names an entry comparable with `B`
  have hrow : ∀ E ∈ (tr.state y k₁).fg.tree,
      HZ tr H g + 1 ≤ ((tr.state y k₁).fg.σ E.root).h →
      ((tr.state y k₁).fg.σ E.root).Th = E.root → ¬ Compatible (tr.HonestBlocks H) E B →
      ∀ W ∈ (tr.state y k₁).fg.tree, ∀ att ∈ W.fgPayload, att.T = E.root → att.val ∉ H := by
    intro E hE hEh _ hnc W hW att ha haT haH
    rcases tree_accepted hp.run.toLocalRun hy hW with rfl | ⟨i', hi', hA⟩
    · cases ha
    obtain ⟨d, hdi, hsd⟩ :=
      hp.run.att_unforgeable y hy i' att (Or.inr ⟨W, ⟨true, hA⟩, ha⟩) haH
    obtain ⟨E', hE', hE'r, hE'h⟩ := signAt_entry hp.run haH hsd
    obtain rfl : E' = E := hU.1 ⟨_, haH, d, hE'⟩ (hsub hE) (hE'r.trans haT)
    obtain ⟨r, hrd, l, O, hoO, E₀, hE₀, hE₀O, hE₀r, -⟩ :=
      hp.high_row_source haH hsd (by rw [← hE'h, hp.σ_eq_run haH hy hE' hE]; exact hEh)
    obtain rfl : E₀ = E' := hU.1 ⟨_, haH, r, hE₀⟩ (hsub hE) (hE₀r.trans haT)
    have hEO : Anc (tr.HonestBlocks H) E₀ O := hE₀O.mono fun X hX => ⟨_, haH, r, hX⟩
    rcases hp.origins_compatible_before hvote ho hg hact hoO (by omega) hib
      ((hp.run.time_mono (by omega)).trans hkb) with
      hBO | hOB
    · exact hnc (SA.anc_total hU hEO hBO)
    · exact hnc (Or.inl (hEO.trans hOB))
  have hq : Hᶜ.ncard < sp.toParams.fg.q := by
    have hf := hp.faults
    have hn := sp.toParams.hn
    change 3 * Hᶜ.ncard ≤ sp.toParams.n - 1 at hf
    change Hᶜ.ncard < (2 * sp.toParams.n + 2) / 3
    omega
  have hJ : HZ tr H g + 1 ≤ (tr.state y k₁).fg.hj →
      Compatible (tr.HonestBlocks H) (tr.state y k₁).fg.J B :=
    Store.J_compatible_of_rows hreach hq hU hsub hgB hrow
  refine ⟨?_, hJ⟩
  obtain ⟨-, -, hFJ, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
  by_cases hlow : (tr.state y k₁).fg.hj ≤ HZ tr H g
  · exact Or.inl (low_finalized_below_high_block_of_run hp.run hp.noColl hp.faults
      hy ho.1 hBx ho.2.2.2 hlow)
  · rcases hJ (by omega) with hJB | hBJ
    · exact Or.inl ((hFJ.mono hsub).trans hJB)
    · exact SA.anc_total hU (hFJ.mono hsub) hBJ

/-- Whole-run specialization of activation cache comparison. -/
theorem activation_caches (hp : ResetPremises tr H proposer dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {k₁ : Nat} (hk₁ : tr.FirstCutFrom k₁ (sp.ts (j + 1 : Nat)))
    (_ha : a < sp.ts (j + 1 : Nat))
    (ih : ∀ k' < k₁, VoteInv tr H g k' ∧ CacheInv tr H g a k') :
    Compatible (tr.HonestBlocks H) (tr.state y k₁).fg.F B ∧
      (HZ tr H g + 1 ≤ (tr.state y k₁).fg.hj →
        Compatible (tr.HonestBlocks H) (tr.state y k₁).fg.J B) := by
  exact (hp.toUpTo tr H (le_max_left a (max (tr.time i) (tr.time k₁)))).activation_caches
    ho hy hk₁ ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _))
    (fun ho₀ _ z hz c hc _ e ⟨ℓ, hcl, he⟩ hsl =>
      ((voteInv_iff.1 (ih c hc).1) _ _ _ _ ho₀ z hz ℓ e ⟨hcl, he⟩ hsl).1)

/-- The caches at a vote (the last-call/first-cut split of `vote_state_caches`, repeated here
since the vote step's module imports this one). -/
private theorem vote_caches (hp : ResetPremises tr H proposer dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) (hk : sp.ts (j + 1 : Nat) ≤ tr.time k) :
    Compatible (tr.HonestBlocks H) (tr.state y k).fg.F B := by
  classical
  have hex : ∃ k', sp.ts (j + 1 : Nat) ≤ tr.time k' := ⟨k, hk⟩
  have hk₁ : Nat.find hex ≤ k := Nat.find_min' hex hk
  have hfirst : tr.FirstCutFrom (Nat.find hex) (sp.ts (j + 1 : Nat)) :=
    ⟨Nat.find_spec hex, fun k' hk' => not_le.mp (Nat.find_min hex hk')⟩
  have hboot : ∀ k₀, (∀ k' < k₀, tr.time k' < a) →
      Compatible (tr.HonestBlocks H) (tr.state y k₀).fg.F B := fun k₀ hk₀ =>
    (boot_caches hp hy hk₀).2 x i j B ho
  rcases Compose.state_of_le (tr := tr) (y := y) hk₁ with h | ⟨k', hk', hk'k, hc, h⟩
  · rw [h]
    by_cases hta : sp.ts (j + 1 : Nat) ≤ a
    · exact hboot _ fun k' hk' => lt_of_lt_of_le (hfirst.2 k' hk') hta
    · exact (activation_caches hp ho hy hfirst (not_le.mp hta)
        fun k' hk' => ih k' (lt_of_lt_of_le hk' hk₁)).1
  · rw [h]
    have hact : sp.ts (j + 1 : Nat) ≤ tr.time k' := hfirst.1.trans (hp.run.time_mono hk')
    by_cases hak : a ≤ tr.time k'
    · exact ((cacheInv_iff.1 (ih k' hk'k).2) y hy hc hak x i j B ho (Or.inr hact)).1
    · obtain ⟨c, hc'⟩ := hc
      rw [← Trace.state_succ_of_call _ hc']
      exact hboot _ fun k'' hk'' =>
        lt_of_le_of_lt (hp.run.time_mono (Nat.lt_succ_iff.mp hk'')) (not_le.mp hak)

/-- **The receiver-root split** (`hr4-boot-carry.md` §4): at an honest vote of a slot `> j` at
which `B` is not below `fc_root`, the voter's `Σ.F` is below `B` (the caches compare them, and
`Σ.F ⪯ fc_root`). -/
private theorem vote_F_anc (hp : ResetPremises tr H proposer dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) (hj : j < e.msg.slot)
    (hroot : ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    Anc (tr.HonestBlocks H) ℓ.frame.F B := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨hΦ, hΦU⟩ := SA.frameIn_of_callAt hr hy hc.1
  have hts' : sp.ts e.msg.slot ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).mpr (by rw [(SA.castAt_spec hr hy hc).2.1])
  have hts : sp.ts (j + 1 : Nat) ≤ tr.time k :=
    ((SA.ts_le_iff sp).mpr (by exact_mod_cast hj : ((j + 1 : Nat) : Int) ≤ e.msg.slot)).trans hts'
  have hF : ℓ.frame.F = (tr.state y k).fg.F := by rw [Compose.frame_of_projAC hp.run hy hc.1]; rfl
  rcases vote_caches hp k ih ho hy hts with h | h
  · rw [hF]; exact h
  · rw [← hF] at h
    exact absurd (h.trans (Anc.mono hΦU hΦ.F_anc_fcRoot)) hroot

/-- `Sync` on the AC projection from `g` on (`GST(g)`). -/
private theorem sync_after (hp : ResetPremises tr H proposer dg g ΔF a) (b : Time) :
    SyncAC (SA.goldilocksSA sp (List (FG.Att sp.n)) ro) H (tr.HonestBlocks H) g b tr.projAC :=
  Compose.sync_projection sp.toParams (goldilocksNode sp ro) dg H (fun v => v.val)
    tr proposer ΔF g b
    hp.run.toLocalRun (syncRun_of_gst hp.healthy.1 le_rfl)

/-- The counted head of a high origin is relayed before a later vote's freeze. This
establishes receiver heldness without any height-floor or retention-invariant premise. -/
theorem ResetPremisesUpTo.high_origin_held_at_vote {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hy : y ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hj : j < e.msg.slot)
    (hF : Anc (tr.HonestBlocks H) ell.frame.F B) : B ∈ (tr.state y k).fg.tree := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨ellw, D, CV, hcw, hflw, -, -, -, hBD, -⟩ := hp.highOrigin_mem ho
  obtain ⟨v, hv⟩ := fastLock_counted_nonempty hflw
  obtain ⟨-, -, Hv, ⟨z, hz, k₀, hHvz⟩, -, hDHv, hacc⟩ := fastLock_writer hr ho.1 hflw v hv
  have hBHv : Anc (tr.HonestBlocks H) B Hv :=
    (Anc.mono (SA.frameIn_of_callAt hr ho.1 hcw).2 hBD).trans hDHv
  rcases hacc with hg | ⟨kw, hkw, hkwt⟩
  · exact absurd hg (hp.cutZ_lt_of_anc ho hz hHvz hBHv).2
  have hkwg : g ≤ tr.projAC.time kw := by
    have := (hp.cutZ_lt_of_anc ho ho.1 (hp.acceptAt_mem ho.1 hkw) hBHv).1
    have := lt_cutZ sp g
    have := le_gbar g
    have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
    change g ≤ tr.time kw
    linarith
  have hHvT := relay_mem_voterBlockTree hr (hp.sync.syncAC hp.run le_rfl) ho.1 hkw hkwg
    hkwt le_rfl hy hc hj (hF.trans hBHv)
  exact hp.mem_tree_of_anc hy hBHv (hp.frame_tree_subset hy hc.1 hHvT.1)

/-- Whole-run specialization of counted-head heldness. -/
theorem high_origin_held_at_vote (hp : ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hy : y ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hj : j < e.msg.slot)
    (hF : Anc (tr.HonestBlocks H) ell.frame.F B) : B ∈ (tr.state y k).fg.tree :=
  (hp.toUpTo tr H (le_refl a)).high_origin_held_at_vote ho hy hc hj hF

/-- Receiver and source heights agree after the counted-head relay, not merely because
the receiver's finalization is below the high origin. -/
theorem high_origin_height_at_vote (hp : ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hy : y ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hj : j < e.msg.slot)
    (hF : Anc (tr.HonestBlocks H) ell.frame.F B) :
    ((tr.state x i).fg.σ B.root).h = ((tr.state y k).fg.σ B.root).h := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hBx⟩ := highOrigin_mem hp ho
  rw [σ_eq_run hp ho.1 hy hBx (high_origin_held_at_vote hp ho hy hc hj hF)]

/-- The floor crossing supplies an earlier high origin above `B` and a held entry at the
receiver's floor. Heights of `B` are read at its source, where it is held. Pairwise comparison
of earlier origins rules out a high contest; comparison with `B` orients the crossing.
Neither a vote/cache invariant nor pivot service is assumed. The signed row witnessing
the crossing is retained for consumers that need an actual earlier report. -/
theorem ResetPremisesUpTo.high_floor_signed_source_of_row_bound {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hy : y ∈ H)
    {u : Nat}
    (hrow : ∀ W ∈ (tr.state y k).fg.tree, ∀ att ∈ W.fgPayload,
      ∀ v ∈ H, ∀ d, tr.SignAt v d att → d < k → ∀ r l O,
        r < d → HighOrigin tr H g v r l O → l < u)
    (hpair : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      ∀ v' r' l' O', r' < k → HighOrigin tr H g v' r' l' O' →
      Compatible (tr.HonestBlocks H) O O')
    (hcomp : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocks H) B O)
    (hfloor : ((tr.state x i).fg.σ B.root).h < (tr.state y k).fg.headHeightFloor) :
    ∃ v r l O E, r < k ∧ HighOrigin tr H g v r l O ∧ l < u ∧
      E ∈ (tr.state y k).fg.tree ∧ Anc (tr.HonestBlocks H) E O ∧
      Anc (tr.HonestBlocks H) B O ∧
      (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ E.root).h ∧
      ∃ d att, r < d ∧ d < k ∧ tr.SignAt v d att ∧ att.T = E.root := by
  have hU := hp.honest_coherent
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy k
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, k, hX⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hBx⟩ := hp.highOrigin_mem ho
  have hBh := ho.2.2.2
  have hupper : ∀ {v₁ v₂ : Fin sp.n} {r₁ l₁ r₂ l₂ : Nat}
      {O₁ O₂ : SA.Blk sp.n (List (FG.Att sp.n))}, HighOrigin tr H g v₁ r₁ l₁ O₁ → r₁ < k →
      HighOrigin tr H g v₂ r₂ l₂ O₂ → r₂ < k → ∃ z ∈ H, ∃ m C, C ∈ (tr.state z m).fg.tree ∧
        Anc (tr.HonestBlocks H) O₁ C ∧ Anc (tr.HonestBlocks H) O₂ C := by
    intro v₁ v₂ r₁ l₁ r₂ l₂ O₁ O₂ ho₁ hr₁ ho₂ hr₂
    obtain ⟨-, -, -, -, -, -, -, -, -, hO₁⟩ := hp.highOrigin_mem ho₁
    obtain ⟨-, -, -, -, -, -, -, -, -, hO₂⟩ := hp.highOrigin_mem ho₂
    rcases hpair v₁ r₁ l₁ O₁ hr₁ ho₁ v₂ r₂ l₂ O₂ hr₂ ho₂ with h | h
    · exact ⟨v₂, ho₂.1, r₂, O₂, hO₂, h, .refl⟩
    · exact ⟨v₁, ho₁.1, r₁, O₁, hO₁, .refl, h⟩
  have hnc : ¬ ((tr.state y k).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state y k).fg.hmax) := by
    rintro ⟨⟨hmj, C, hC, -, hCh, hJC⟩, hmax⟩
    obtain ⟨-, hJm, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -⟩ :=
      Goldilocks.Store.cache_invariants _ _ _ _ hreach
    obtain ⟨EJ, hEJ, hEJr, hEJB, hcase⟩ := Store.J_entry_of_reachable hreach hBj
    obtain rfl : EJ = (tr.state y k).fg.J := hU.1 (hsub hEJ) (hsub hJm) (hEJr.trans hBjJ)
    rcases hcase with hg | ⟨hJh, hJT⟩
    · exact hJC (hg ▸ (Goldilocks.Store.accepted_tree _ _ _ _ hreach).2.2.2 C hC)
    have hJlt := Store.hj_lt_h hreach hBj
    obtain ⟨W₂, -, att₂, -, v₂, -, d₂, hd₂, -, -, r₂, hr₂, l₂, O₂, ho₂, hJO⟩ :=
      hp.left_entry_origin hy hJm hJT (by omega) hEJB (by omega)
    obtain ⟨EC, hEC, hECC, hECh, hECT⟩ :=
      entry_at_height hreach hC (h := (tr.state y k).fg.hj) (by omega) (by omega)
    obtain ⟨W₁, -, att₁, -, v₁, -, d₁, hd₁, -, -, r₁, hr₁, l₁, O₁, ho₁, hECO⟩ :=
      hp.left_entry_origin hy hEC hECT (by omega) hECC (by omega)
    obtain ⟨z, hz, m', C', hC', hO₁C, hO₂C⟩ := hupper ho₁ (by omega) ho₂ (by omega)
    have h₁ := hECO.trans hO₁C
    have h₂ := hJO.trans hO₂C
    have hEC' := hp.mem_tree_of_anc hz h₁ hC'
    have hJ' := hp.mem_tree_of_anc hz h₂ hC'
    have hσ₁ := hp.σ_eq_run hy hz hEC hEC'
    have hσ₂ := hp.σ_eq_run hy hz hJm hJ'
    have he := hp.entry_root_eq hz hC' h₁ h₂
      (by rw [← hσ₁, ← hσ₂, hECh, hJh, hBjhj]) (by rw [← hσ₁]; exact hECT)
      (by rw [← hσ₂]; exact hJT)
    obtain rfl : EC = (tr.state y k).fg.J := hU.1 (hsub hEC) (hsub hJm) he
    exact hJC hECC
  have hcon : ¬ (tr.state y k).fg.Contest := fun hcon => by
    unfold Store.headHeightFloor at hfloor
    simp only [hcon, ↓reduceIte] at hfloor
    exact hnc ⟨hcon, by omega⟩
  have hfl : (tr.state y k).fg.headHeightFloor = (tr.state y k).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    simp only [hcon, ↓reduceIte]
  rw [hfl] at hfloor
  obtain ⟨-, -, -, -, -, ⟨C, hC, hCh⟩, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
  obtain ⟨E, hE, hEC, hEh, hET⟩ :=
    entry_at_height hreach hC (h := (tr.state y k).fg.hmax - 1) (by omega) (by omega)
  obtain ⟨W, hW, att, ha, v, hv, d₁, hd₁, hsd, haT, r, hrd, l, O, hoO, hEO⟩ :=
    hp.left_entry_origin hy hE hET (by omega) hEC (by omega)
  have hBO : Anc (tr.HonestBlocks H) B O := by
    rcases hcomp v r l O (by omega) hoO with h | h
    · exact h
    · exfalso
      have hEB := hEO.trans h
      have hEx := hp.mem_tree_of_anc ho.1 hEB hBx
      have hle := σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun ho.1 i)
        (hp.anc_tree_of_anc ho.1 hEB hBx)
      rw [hp.σ_eq_run ho.1 hy hEx hE] at hle
      omega
  exact ⟨v, r, l, O, E, by omega, hoO,
    hrow W hW att ha v hv d₁ hsd hd₁ r l O hrd hoO, hE, hEO, hBO, by omega,
    d₁, att, hrd, hd₁, hsd, haT⟩

/-- Whole-run specialization of the signed floor-crossing source. -/
theorem high_floor_signed_source_of_row_bound
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hy : y ∈ H) {u : Nat}
    (hrow : ∀ W ∈ (tr.state y k).fg.tree, ∀ att ∈ W.fgPayload,
      ∀ v ∈ H, ∀ d, tr.SignAt v d att → d < k → ∀ r l O,
        r < d → HighOrigin tr H g v r l O → l < u)
    (hpair : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      ∀ v' r' l' O', r' < k → HighOrigin tr H g v' r' l' O' →
      Compatible (tr.HonestBlocks H) O O')
    (hcomp : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocks H) B O)
    (hfloor : ((tr.state x i).fg.σ B.root).h < (tr.state y k).fg.headHeightFloor) :
    ∃ v r l O E, r < k ∧ HighOrigin tr H g v r l O ∧ l < u ∧
      E ∈ (tr.state y k).fg.tree ∧ Anc (tr.HonestBlocks H) E O ∧
      Anc (tr.HonestBlocks H) B O ∧
      (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ E.root).h ∧
      ∃ d att, r < d ∧ d < k ∧ tr.SignAt v d att ∧ att.T = E.root :=
  (hp.toUpTo tr H (le_refl a)).high_floor_signed_source_of_row_bound ho hy hrow hpair hcomp hfloor

/-- The floor crossing supplies an earlier high origin and a held floor entry. -/
theorem high_floor_source_of_row_bound
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hy : y ∈ H)
    {u : Nat}
    (hrow : ∀ W ∈ (tr.state y k).fg.tree, ∀ att ∈ W.fgPayload,
      ∀ v ∈ H, ∀ d, tr.SignAt v d att → d < k → ∀ r l O,
        r < d → HighOrigin tr H g v r l O → l < u)
    (hpair : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      ∀ v' r' l' O', r' < k → HighOrigin tr H g v' r' l' O' →
      Compatible (tr.HonestBlocks H) O O')
    (hcomp : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocks H) B O)
    (hfloor : ((tr.state x i).fg.σ B.root).h < (tr.state y k).fg.headHeightFloor) :
    ∃ v r l O E, r < k ∧ HighOrigin tr H g v r l O ∧ l < u ∧
      E ∈ (tr.state y k).fg.tree ∧ Anc (tr.HonestBlocks H) E O ∧
      Anc (tr.HonestBlocks H) B O ∧
      (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ E.root).h := by
  obtain ⟨v, r, l, O, E, hr, ho, hl, hE, hEO, hBO, hfloor, -⟩ :=
    high_floor_signed_source_of_row_bound hp ho hy hrow hpair hcomp hfloor
  exact ⟨v, r, l, O, E, hr, ho, hl, hE, hEO, hBO, hfloor⟩

/-- Vote specialization of the duty-independent floor crossing. -/
theorem ResetPremisesUpTo.high_floor_source_core {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hy : y ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (_hj : j < e.msg.slot)
    (hpair : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      ∀ v' r' l' O', r' < k → HighOrigin tr H g v' r' l' O' →
      Compatible (tr.HonestBlocks H) O O')
    (hcomp : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocks H) B O)
    (hfloor : ((tr.state x i).fg.σ B.root).h < (tr.state y k).fg.headHeightFloor) :
    ∃ v r l O E, r < k ∧ HighOrigin tr H g v r l O ∧ l < e.msg.slot ∧
      E ∈ (tr.state y k).fg.tree ∧ Anc (tr.HonestBlocks H) E O ∧
      Anc (tr.HonestBlocks H) B O ∧
      (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ E.root).h := by
  obtain ⟨v, r, l, O, E, hr, hO, hl, hE, hEO, hBO, hf, -⟩ :=
    hp.high_floor_signed_source_of_row_bound ho hy (u := e.msg.slot)
      (fun W hW att ha v hv d hs hdk r l O hrd hO =>
        hp.row_origin_label_lt hy hc hW ha hv hs hdk hrd hO) hpair hcomp hfloor
  exact ⟨v, r, l, O, E, hr, hO, hl, hE, hEO, hBO, hf⟩

/-- Whole-run specialization of the vote-time floor crossing. -/
theorem high_floor_source_core
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hy : y ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hj : j < e.msg.slot)
    (hpair : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      ∀ v' r' l' O', r' < k → HighOrigin tr H g v' r' l' O' →
      Compatible (tr.HonestBlocks H) O O')
    (hcomp : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocks H) B O)
    (hfloor : ((tr.state x i).fg.σ B.root).h < (tr.state y k).fg.headHeightFloor) :
    ∃ v r l O E, r < k ∧ HighOrigin tr H g v r l O ∧ l < e.msg.slot ∧
      E ∈ (tr.state y k).fg.tree ∧ Anc (tr.HonestBlocks H) E O ∧
      Anc (tr.HonestBlocks H) B O ∧
      (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ E.root).h :=
  (hp.toUpTo tr H (le_refl a)).high_floor_source_core ho hy hc hj hpair hcomp hfloor

/-- Compatibility interface retaining the receiver-finalization argument. The crossing
itself does not need that argument, as exposed by `high_floor_source_core`. -/
theorem high_floor_source_before
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hy : y ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hj : j < e.msg.slot)
    (hpair : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      ∀ v' r' l' O', r' < k → HighOrigin tr H g v' r' l' O' →
      Compatible (tr.HonestBlocks H) O O')
    (hcomp : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocks H) B O)
    (_hF : Anc (tr.HonestBlocks H) ell.frame.F B)
    (hfloor : ((tr.state x i).fg.σ B.root).h < (tr.state y k).fg.headHeightFloor) :
    ∃ v r l O E, r < k ∧ HighOrigin tr H g v r l O ∧ l < e.msg.slot ∧
      E ∈ (tr.state y k).fg.tree ∧ Anc (tr.HonestBlocks H) E O ∧
      Anc (tr.HonestBlocks H) B O ∧
      (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ E.root).h :=
  high_floor_source_core hp ho hy hc hj hpair hcomp hfloor

/-- **R5 above the floor** (`hr4-boot-carry.md` §7): the crossing origin's counted honest
head is relayed before the voter's freeze and supplies a viable witness above `B`. -/
theorem height_lead_above (hp : ResetPremises tr H proposer dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) (hj : j < e.msg.slot)
    (hF : Anc (tr.HonestBlocks H) ℓ.frame.F B)
    (hfloor : ((tr.state x i).fg.σ B.root).h < (tr.state y k).fg.headHeightFloor) :
    ∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
      Anc (tr.HonestBlocks H) B D ∧ (tr.state y k).fg.IsViable D := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hU := honest_coherent hp
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy k
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, k, hX⟩
  have hvk : ∀ k' < k, VoteInv tr H g k' := fun k' hk' => (ih k' hk').1
  obtain ⟨-, -, -, -, -, -, -, -, -, hBx⟩ := highOrigin_mem hp ho
  have hBh := ho.2.2.2
  -- two origins written before the vote lie below one held block
  have hupper : ∀ {v₁ v₂ : Fin sp.n} {r₁ l₁ r₂ l₂ : Nat}
      {O₁ O₂ : SA.Blk sp.n (List (FG.Att sp.n))}, HighOrigin tr H g v₁ r₁ l₁ O₁ → r₁ < k →
      HighOrigin tr H g v₂ r₂ l₂ O₂ → r₂ < k → ∃ z ∈ H, ∃ m C, C ∈ (tr.state z m).fg.tree ∧
        Anc (tr.HonestBlocks H) O₁ C ∧ Anc (tr.HonestBlocks H) O₂ C := by
    intro v₁ v₂ r₁ l₁ r₂ l₂ O₁ O₂ ho₁ hr₁ ho₂ hr₂
    obtain ⟨-, -, -, -, -, -, -, -, -, hO₁⟩ := highOrigin_mem hp ho₁
    obtain ⟨-, -, -, -, -, -, -, -, -, hO₂⟩ := highOrigin_mem hp ho₂
    rcases origins_compatible_before hp hvk ho₁ (g_le_ts hp ho₁ le_rfl) (Or.inl hr₁) ho₂ hr₂ with
      h | h
    · exact ⟨v₂, ho₂.1, r₂, O₂, hO₂, h, .refl⟩
    · exact ⟨v₁, ho₁.1, r₁, O₁, hO₁, .refl, h⟩
  -- no high contest: the top justification and the contest carrier's entry at `h_j` coincide
  have hnc : ¬ ((tr.state y k).fg.Contest ∧ HZ tr H g + 2 ≤ (tr.state y k).fg.hmax) := by
    rintro ⟨⟨hmj, C, hC, -, hCh, hJC⟩, hmax⟩
    obtain ⟨-, hJm, -, ⟨Bj, hBj, hBjJ, hBjhj⟩, -⟩ :=
      Goldilocks.Store.cache_invariants _ _ _ _ hreach
    obtain ⟨EJ, hEJ, hEJr, hEJB, hcase⟩ := Store.J_entry_of_reachable hreach hBj
    obtain rfl : EJ = (tr.state y k).fg.J := hU.1 (hsub hEJ) (hsub hJm) (hEJr.trans hBjJ)
    rcases hcase with hg | ⟨hJh, hJT⟩
    · exact hJC (hg ▸ (Goldilocks.Store.accepted_tree _ _ _ _ hreach).2.2.2 C hC)
    have hJlt := Store.hj_lt_h hreach hBj
    obtain ⟨W₂, -, att₂, -, v₂, -, d₂, hd₂, -, -, r₂, hr₂, l₂, O₂, ho₂, hJO⟩ :=
      left_entry_origin hp hy hJm hJT (by omega) hEJB (by omega)
    obtain ⟨EC, hEC, hECC, hECh, hECT⟩ :=
      entry_at_height hreach hC (h := (tr.state y k).fg.hj) (by omega) (by omega)
    obtain ⟨W₁, -, att₁, -, v₁, -, d₁, hd₁, -, -, r₁, hr₁, l₁, O₁, ho₁, hECO⟩ :=
      left_entry_origin hp hy hEC hECT (by omega) hECC (by omega)
    obtain ⟨z, hz, m', C', hC', hO₁C, hO₂C⟩ := hupper ho₁ (by omega) ho₂ (by omega)
    have h₁ := hECO.trans hO₁C
    have h₂ := hJO.trans hO₂C
    have hEC' := mem_tree_of_anc hp hz h₁ hC'
    have hJ' := mem_tree_of_anc hp hz h₂ hC'
    have hσ₁ := σ_eq_run hp hy hz hEC hEC'
    have hσ₂ := σ_eq_run hp hy hz hJm hJ'
    have he := entry_root_eq hp hz hC' h₁ h₂
      (by rw [← hσ₁, ← hσ₂, hECh, hJh, hBjhj]) (by rw [← hσ₁]; exact hECT)
      (by rw [← hσ₂]; exact hJT)
    obtain rfl : EC = (tr.state y k).fg.J := hU.1 (hsub hEC) (hsub hJm) he
    exact hJC hECC
  -- so the floor is `h_max − 1`
  have hcon : ¬ (tr.state y k).fg.Contest := fun hcon => by
    unfold Store.headHeightFloor at hfloor
    simp only [hcon, ↓reduceIte] at hfloor
    exact hnc ⟨hcon, by omega⟩
  have hfl : (tr.state y k).fg.headHeightFloor = (tr.state y k).fg.hmax - 1 := by
    unfold Store.headHeightFloor
    simp only [hcon, ↓reduceIte]
  rw [hfl] at hfloor
  -- the crossing of the floor: its entry is named by an honest row with an earlier source origin
  obtain ⟨-, -, -, -, -, ⟨C, hC, hCh⟩, -⟩ := Goldilocks.Store.cache_invariants _ _ _ _ hreach
  obtain ⟨E, hE, hEC, hEh, hET⟩ :=
    entry_at_height hreach hC (h := (tr.state y k).fg.hmax - 1) (by omega) (by omega)
  obtain ⟨W, hW, att, ha, v, hv, d₁, hd₁, hsd, -, r, hrd, l, O, hoO, hEO⟩ :=
    left_entry_origin hp hy hE hET (by omega) hEC (by omega)
  -- the origin is comparable with `B`, and higher: it extends `B`
  have hts' : sp.ts e.msg.slot ≤ tr.time k :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg k) _).mpr (by rw [(SA.castAt_spec hr hy hc).2.1])
  have hts : sp.ts (j + 1 : Nat) ≤ tr.time k :=
    ((SA.ts_le_iff sp).mpr (by exact_mod_cast hj : ((j + 1 : Nat) : Int) ≤ e.msg.slot)).trans hts'
  have hact : i < k ∨ ∀ c, tr.time c < sp.ts (j + 1 : Nat) → c < k :=
    Or.inr fun c hc => not_le.mp fun hle => absurd (hts.trans (hp.run.time_mono hle))
      (not_le.mpr hc)
  have hBO : Anc (tr.HonestBlocks H) B O := by
    rcases origins_compatible_before hp hvk ho (g_le_ts hp ho le_rfl) hact hoO (by omega) with
      h | h
    · exact h
    · exfalso
      have hEB := hEO.trans h
      have hEx := mem_tree_of_anc hp ho.1 hEB hBx
      have hle := σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun ho.1 i)
        (anc_tree_of_anc hp ho.1 hEB hBx)
      rw [σ_eq_run hp ho.1 hy hEx hE] at hle
      omega
  -- a counted head of the origin, relayed to the voter before its freeze
  obtain ⟨ℓw, D, CV, hcw, hflw, -, -, -, hOD, -⟩ := highOrigin_mem hp hoO
  obtain ⟨u, hu⟩ := fastLock_counted_nonempty hflw
  obtain ⟨-, -, Hv, ⟨z, hz, k₀, hHvz⟩, -, hDHv, hacc⟩ := fastLock_writer hr hoO.1 hflw u hu
  have hOHv : Anc (tr.HonestBlocks H) O Hv :=
    (Anc.mono (SA.frameIn_of_callAt hr hoO.1 hcw).2 hOD).trans hDHv
  rcases hacc with hg | ⟨kw, hkw, hkwt⟩
  · exact absurd hg (cutZ_lt_of_anc hp hoO hz hHvz hOHv).2
  have hkwg : g ≤ tr.projAC.time kw := by
    have := (cutZ_lt_of_anc hp hoO hoO.1 (acceptAt_mem hp hoO.1 hkw) hOHv).1
    have := lt_cutZ sp g
    have := le_gbar g
    have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
    change g ≤ tr.time kw
    linarith
  have hlm := row_origin_label_lt hp hy hc hW ha hv hsd hd₁ hrd hoO
  have hHvT := relay_mem_voterBlockTree hr (sync_after hp (sp.ts l + 2 * sp.Δ)) hoO.1 hkw hkwg
    hkwt le_rfl hy hc (by omega) (hF.trans (hBO.trans hOHv))
  have hHvy : Hv ∈ (tr.state y k).fg.tree := frame_tree_subset hp hy hc.1 hHvT.1
  have hh := σ_h_le_of_anc hreach (anc_tree_of_anc hp hy (hEO.trans hOHv) hHvy)
  refine ⟨Hv, hHvT, hBO.trans hOHv, ?_⟩
  change (tr.state y k).fg.headHeightFloor ≤ _
  omega

/-- A high origin above the raw target supplies a frozen viable witness when a held
ancestor of the origin already meets the receiver's height floor. No retention invariant
or stored-origin assumption on the target or held ancestor is required. -/
theorem ResetPremisesUpTo.raw_target_frozen_witness {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y : Fin sp.n} {r l k : Nat} {B O E : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hy : y ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hl : l < e.msg.slot)
    (hFB : Anc (tr.HonestBlocks H) ell.frame.F B)
    (hBO : Anc (tr.HonestBlocks H) B O) (_hE : E ∈ (tr.state y k).fg.tree)
    (hEO : Anc (tr.HonestBlocks H) E O)
    (hfloor : (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ E.root).h) :
    ∃ D ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Anc (tr.HonestBlocks H) B D ∧ (tr.state y k).fg.IsViable D := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨ellw, D, CV, hcw, hflw, -, -, -, hOD, -⟩ := hp.highOrigin_mem ho
  obtain ⟨u, hu⟩ := fastLock_counted_nonempty hflw
  obtain ⟨-, -, Hv, ⟨z, hz, k₀, hHvz⟩, -, hDHv, hacc⟩ := fastLock_writer hr ho.1 hflw u hu
  have hOHv : Anc (tr.HonestBlocks H) O Hv :=
    (Anc.mono (SA.frameIn_of_callAt hr ho.1 hcw).2 hOD).trans hDHv
  rcases hacc with hg | ⟨kw, hkw, hkwt⟩
  · exact absurd hg (hp.cutZ_lt_of_anc ho hz hHvz hOHv).2
  have hkwg : g ≤ tr.projAC.time kw := by
    have := (hp.cutZ_lt_of_anc ho ho.1 (hp.acceptAt_mem ho.1 hkw) hOHv).1
    have := lt_cutZ sp g
    have := le_gbar g
    have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
    change g ≤ tr.time kw
    linarith
  have hHvT := relay_mem_voterBlockTree hr (hp.sync.syncAC hp.run le_rfl) ho.1 hkw hkwg
    hkwt le_rfl hy hc hl (hFB.trans (hBO.trans hOHv))
  have hHvy : Hv ∈ (tr.state y k).fg.tree := hp.frame_tree_subset hy hc.1 hHvT.1
  have hh := σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun hy k)
    (hp.anc_tree_of_anc hy (hEO.trans hOHv) hHvy)
  exact ⟨Hv, hHvT, hBO.trans hOHv, hfloor.trans hh⟩

/-- Whole-run specialization of the frozen viable witness. -/
theorem raw_target_frozen_witness (hp : ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {r l k : Nat} {B O E : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hy : y ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hl : l < e.msg.slot)
    (hFB : Anc (tr.HonestBlocks H) ell.frame.F B)
    (hBO : Anc (tr.HonestBlocks H) B O) (hE : E ∈ (tr.state y k).fg.tree)
    (hEO : Anc (tr.HonestBlocks H) E O)
    (hfloor : (tr.state y k).fg.headHeightFloor ≤ ((tr.state y k).fg.σ E.root).h) :
    ∃ D ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
      Anc (tr.HonestBlocks H) B D ∧ (tr.state y k).fg.IsViable D :=
  (hp.toUpTo tr H (le_refl a)).raw_target_frozen_witness ho hy hc hl hFB hBO hE hEO hfloor

/-- **(K2) at a vote, R5** (§5 Lemma R5; §11 item 1 for the votes through the ticks at `a_z`;
§13 "Retaining the witnesses and the frame"; `t1-proof.md` §9 base case). At an honest vote of a
slot `> j`, the voter block tree holds a viable descendant of the origin's block `B`, or
`B ⪯ fc_root`: in the low-frontier regime `B` itself (height `H_z + 1`, relayed before the freeze);
above it, the supporting head of an earlier comparable high source that crossed the floor (R4,
R5). -/
theorem vote_height_lead (hp : ResetPremises tr H proposer dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) (hj : j < e.msg.slot) :
    (∃ D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot,
      Anc (tr.HonestBlocks H) B D ∧ (tr.state y k).fg.IsViable D) ∨
    Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot := by
  by_cases hroot : Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot
  · exact Or.inr hroot
  have hF := vote_F_anc hp k ih ho hy hc hj hroot
  refine Or.inl ?_
  by_cases hfl : (tr.state y k).fg.headHeightFloor ≤ ((tr.state x i).fg.σ B.root).h
  swap
  · exact height_lead_above hp k ih ho hy hc hj hF (not_le.mp hfl)
  -- the floor is at most the height of `B`: a counted head of the origin, relayed in time
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨ℓw, D, CV, hcw, hflw, -, -, -, hBD, hBx⟩ := highOrigin_mem hp ho
  obtain ⟨v, hv⟩ := fastLock_counted_nonempty hflw
  obtain ⟨-, -, Hv, ⟨z, hz, k₀, hHvz⟩, -, hDHv, hacc⟩ := fastLock_writer hr ho.1 hflw v hv
  have hBHv : Anc (tr.HonestBlocks H) B Hv :=
    (Anc.mono (SA.frameIn_of_callAt hr ho.1 hcw).2 hBD).trans hDHv
  rcases hacc with hg | ⟨kw, hkw, hkwt⟩
  · exact absurd hg (cutZ_lt_of_anc hp ho hz hHvz hBHv).2
  have hkwg : g ≤ tr.projAC.time kw := by
    have := (cutZ_lt_of_anc hp ho ho.1 (acceptAt_mem hp ho.1 hkw) hBHv).1
    have := lt_cutZ sp g
    have := le_gbar g
    have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
    change g ≤ tr.time kw
    linarith
  have hHvT := relay_mem_voterBlockTree hr (sync_after hp (sp.ts j + 2 * sp.Δ)) ho.1 hkw hkwg
    hkwt le_rfl hy hc (by omega) (hF.trans hBHv)
  have hHvy : Hv ∈ (tr.state y k).fg.tree := frame_tree_subset hp hy hc.1 hHvT.1
  have hBy := mem_tree_of_anc hp hy hBHv hHvy
  have hh := σ_h_le_of_anc (Compose.fg_reachable hp.run.toLocalRun hy k)
    (anc_tree_of_anc hp hy hBHv hHvy)
  rw [← σ_eq_run hp ho.1 hy hBx hBy] at hh
  exact ⟨Hv, hHvT, hBHv, hfl.trans hh⟩

/-- **A low `Σ.J` does not veto a high origin** (§11, "an old conflicting J merely causes a
contest"; `t1-proof.md` §9, the geometric statement). When the voter's root is a low `Σ.J`
(`h_max = h_j + 1 ≤ H_z + 1`, no contest) and its voter block tree holds a descendant `D` of the
origin's block `B`, then `D` has state height `h_max` (`≥ σ[B].h ≥ H_z + 1`), so it extends `Σ.J`
(no contest), and `Σ.J` is compatible with `B`. -/
theorem low_root_compatible (hp : ResetPremises tr H proposer dg g ΔF a) {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {k : Nat} {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) (_hj : j < e.msg.slot)
    (hroot : (tr.state y k).fg.hmax = (tr.state y k).fg.hj + 1 ∧ ¬ (tr.state y k).fg.Contest)
    (hlow : (tr.state y k).fg.hj ≤ HZ tr H g) {D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hD : D ∈ SA.voterBlockTree sp e.readPoint ℓ.frame e.msg.slot)
    (hBD : Anc (tr.HonestBlocks H) B D) :
    Compatible (tr.HonestBlocks H) (tr.state y k).fg.J B := by
  have hD' : D ∈ (Node.frame (tr.state y k)).tree := Compose.frame_of_projAC hp.run hy hc.1 ▸ hD.1
  have hDh := high_of_anc hp ho hy hD'.1 hBD
  have hDle := (Store.cache_invariants _ _ _ _
    (Compose.fg_reachable hp.run.toLocalRun hy k)).2.2.2.2.1 D hD'.1
  have hJD : (tr.state y k).fg.Anc (tr.state y k).fg.J D := by
    by_contra hn
    exact hroot.2 ⟨hroot.1, D, hD'.1, hD'.2, by omega, hn⟩
  exact SA.anc_total (honest_coherent hp) (Anc.mono (fun X hX => ⟨y, hy, k, hX⟩) hJD) hBD

/-- Low justification gives complete root compatibility using only post-cut relay. -/
theorem high_origin_low_J_root_before
    (hp : ResetPremises tr H proposer dg g ΔF a) {Q : Time}
    (hsync : SyncACWindowBefore H (tr.HonestBlocks H) (cutZ sp.toParams g) Q tr.projAC)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hy : y ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e) (hj : j < e.msg.slot) (hk : tr.time k ≤ Q)
    (hlow : (tr.state y k).fg.hj ≤ HZ tr H g) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B := by
  have hF := low_finalized_below_origin hp hy k hlow ho
  have hframe := Compose.frame_of_projAC hp.run hy hc.1
  have hFF : ell.frame.F = (tr.state y k).fg.F := by rw [hframe]; rfl
  have hroot : ell.frame.fcRoot = (tr.state y k).fg.fcRoot := by rw [hframe]; rfl
  rw [hroot]
  unfold Store.fcRoot
  split_ifs with hJ
  · have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
    obtain ⟨CV, hst⟩ := ho.2.2.1
    obtain ⟨_, C, hfl, hBC⟩ := storedFastLock_mem hp.run hp.noColl ho.1 hst
    obtain ⟨v, _, D, hDU, _, hBD, hacc⟩ := raw_writer_relay_source hr ho.1 (Or.inr hfl) hBC
    rcases hacc with hg | ⟨q, hq, hqt⟩
    · obtain ⟨z, hz, m, hDm⟩ := hDU
      exact False.elim ((cutZ_lt_of_anc hp ho hz hDm hBD).2 hg)
    · have hD := acceptAt_mem hp ho.1 hq
      have hstart := (cutZ_lt_of_anc hp ho ho.1 hD hBD).1.le
      have htree := relay_mem_voterBlockTree_window_after hr hsync ho.1 hy hq hstart hqt hc
        (by omega) hk (by rw [hFF]; exact hF.trans hBD)
      exact low_root_compatible hp ho hy hc hj hJ hlow htree hBD
  · exact Or.inl hF

/-- A low root compares with any held target comparable with a high seed. The target's
transport is needed only in the seed-below-target branch, after finalization is oriented. -/
theorem ResetPremisesUpTo.low_root_of_held_seed_at_call {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y v : Fin sp.n} {r i q m : Nat} {B S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H) (hBx : B ∈ (tr.state x r).fg.tree) (hy : y ∈ H)
    (hS : HighOrigin tr H g v q m S)
    {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ell) (hSy : S ∈ (tr.state y i).fg.tree)
    (hlow : (tr.state y i).fg.hj ≤ HZ tr H g)
    (hBS : Compatible (tr.HonestBlocks H) B S)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B →
      B ∈ ell.frame.tree) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B := by
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy i
  have hfr := Compose.frame_of_projAC hp.run hy hc
  have hFF : ell.frame.F = (tr.state y i).fg.F := by rw [hfr]; rfl
  have hroot : ell.frame.fcRoot = (tr.state y i).fg.fcRoot := by rw [hfr]; rfl
  have hFS := hp.low_finalized_below_origin hy i hlow hS
  have hSh := hp.high_of_anc hS hy hSy .refl
  have hJ : ∀ D ∈ (tr.state y i).fg.tree,
      (tr.state y i).fg.Anc (tr.state y i).fg.F D →
      HZ tr H g + 1 ≤ ((tr.state y i).fg.σ D.root).h →
      (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 →
      ¬ (tr.state y i).fg.Contest → Anc (tr.HonestBlocks H) (tr.state y i).fg.J D := by
    intro D hD hFD hDh he hn
    have hle := (Store.cache_invariants _ _ _ _ hreach).2.2.2.2.1 D hD
    have hJD : (tr.state y i).fg.Anc (tr.state y i).fg.J D := by
      by_contra h
      exact hn ⟨he, D, hD, hFD, by omega, h⟩
    exact hJD.mono fun X hX => ⟨y, hy, i, hX⟩
  rw [hroot]
  unfold Store.fcRoot
  split_ifs with hactive
  · rcases hBS with hBS | hSB
    · exact SA.anc_total hp.honest_coherent
        (hJ S hSy (hp.anc_tree_of_anc hy hFS hSy) hSh hactive.1 hactive.2) hBS
    · have hBh := hp.high_of_anc hS hx hBx hSB
      have hFB := low_finalized_below_high_block_of_run
        hp.run hp.noColl hp.faults hy hx hBx hBh hlow
      have hBt := hheld (by rw [hFF]; exact hFB)
      have hBy := hp.frame_tree_subset hy hc hBt
      have hBhy := hp.high_of_anc hS hy hBy hSB
      exact Or.inl (hJ B hBy (hp.anc_tree_of_anc hy hFB hBy) hBhy hactive.1 hactive.2)
  · rcases hBS with hBS | hSB
    · exact SA.anc_total hp.honest_coherent hFS hBS
    · exact Or.inl (hFS.trans hSB)

/-- Whole-run specialization of the call-level low-root comparison. -/
theorem low_root_of_held_seed_at_call (hp : ResetPremises tr H proposer dg g ΔF a)
    {x y v : Fin sp.n} {r i q m : Nat} {B S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H) (hBx : B ∈ (tr.state x r).fg.tree) (hy : y ∈ H)
    (hS : HighOrigin tr H g v q m S) {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y i ell) (hSy : S ∈ (tr.state y i).fg.tree)
    (hlow : (tr.state y i).fg.hj ≤ HZ tr H g) (hBS : Compatible (tr.HonestBlocks H) B S)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B → B ∈ ell.frame.tree) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B :=
  (hp.toUpTo tr H (le_refl a)).low_root_of_held_seed_at_call hx hBx hy hS hc hSy hlow hBS hheld

/-- Vote specialization supplying the seed by counted-head relay. -/
theorem ResetPremisesUpTo.low_root_of_seed_before {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {x y v : Fin sp.n} {r i q m : Nat} {B S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H) (hBx : B ∈ (tr.state x r).fg.tree) (hy : y ∈ H)
    (hS : HighOrigin tr H g v q m S)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hm : m < e.msg.slot)
    (hlow : (tr.state y i).fg.hj ≤ HZ tr H g)
    (hBS : Compatible (tr.HonestBlocks H) B S)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B →
      B ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B := by
  have hFS := hp.low_finalized_below_origin hy i hlow hS
  have hFF : ell.frame.F = (tr.state y i).fg.F := by
    rw [Compose.frame_of_projAC hp.run hy hc.1]; rfl
  have hSy := hp.high_origin_held_at_vote hS hy hc hm (by rw [hFF]; exact hFS)
  exact hp.low_root_of_held_seed_at_call hx hBx hy hS hc.1 hSy hlow hBS
    (fun hFB => (hheld hFB).1)

/-- Whole-run specialization of the vote-time low-root comparison. -/
theorem low_root_of_seed_before (hp : ResetPremises tr H proposer dg g ΔF a)
    {x y v : Fin sp.n} {r i q m : Nat} {B S : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H) (hBx : B ∈ (tr.state x r).fg.tree) (hy : y ∈ H)
    (hS : HighOrigin tr H g v q m S)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hm : m < e.msg.slot)
    (hlow : (tr.state y i).fg.hj ≤ HZ tr H g) (hBS : Compatible (tr.HonestBlocks H) B S)
    (hheld : Anc (tr.HonestBlocks H) ell.frame.F B →
      B ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B :=
  (hp.toUpTo tr H (le_refl a)).low_root_of_seed_before hx hBx hy hS hc hm hlow hBS hheld

/-- All held honest rows justify root compatibility from bounded origin comparisons. -/
theorem high_J_root_of_held_at_call_before
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {i k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H) (hBx : B ∈ (tr.state x i).fg.tree) (hy : y ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)}
    (hc : tr.projAC.CallAt y k ell)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
    (hcompare : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocks H) B O) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B := by
  have hU := honest_coherent hp
  have hreach := Compose.fg_reachable hp.run.toLocalRun hy k
  have hsub : (tr.state y k).fg.tree ⊆ tr.HonestBlocks H := fun X hX => ⟨y, hy, k, hX⟩
  have hgB := ((Store.accepted_tree _ _ _ _
    (Compose.fg_reachable hp.run.toLocalRun hx i)).2.2.2 B hBx).mono
      (fun X hX => (⟨x, hx, i, hX⟩ : X ∈ tr.HonestBlocks H))
  have hrow : ∀ E ∈ (tr.state y k).fg.tree,
      HZ tr H g + 1 ≤ ((tr.state y k).fg.σ E.root).h →
      ((tr.state y k).fg.σ E.root).Th = E.root → ¬ Compatible (tr.HonestBlocks H) E B →
      ∀ W ∈ (tr.state y k).fg.tree, ∀ att ∈ W.fgPayload, att.T = E.root → att.val ∉ H := by
    intro E hE hEh _ hnc W hW att ha haT haH
    rcases tree_accepted hp.run.toLocalRun hy hW with rfl | ⟨i', hi', hA⟩
    · cases ha
    obtain ⟨d, hdi, hsd⟩ :=
      hp.run.att_unforgeable y hy i' att (Or.inr ⟨W, ⟨true, hA⟩, ha⟩) haH
    obtain ⟨E', hE', hE'r, hE'h⟩ := signAt_entry hp.run haH hsd
    obtain rfl : E' = E := hU.1 ⟨_, haH, d, hE'⟩ (hsub hE) (hE'r.trans haT)
    obtain ⟨r, hrd, l, O, hoO, E₀, hE₀, hE₀O, hE₀r, -⟩ :=
      high_row_source hp haH hsd (by rw [← hE'h, σ_eq_run hp haH hy hE' hE]; exact hEh)
    obtain rfl : E₀ = E' := hU.1 ⟨_, haH, r, hE₀⟩ (hsub hE) (hE₀r.trans haT)
    have hEO : Anc (tr.HonestBlocks H) E₀ O := hE₀O.mono fun X hX => ⟨_, haH, r, hX⟩
    rcases hcompare _ r l O (by omega) hoO with hBO | hOB
    · exact hnc (SA.anc_total hU hEO hBO)
    · exact hnc (Or.inl (hEO.trans hOB))
  have hJ := Store.J_compatible_of_rows hreach (faulty_lt_q hp.healthy) hU hsub hgB hrow hhigh
  have hF : Compatible (tr.HonestBlocks H) (tr.state y k).fg.F B := by
    obtain ⟨-, -, hFJ, -⟩ := Store.cache_invariants _ _ _ _ hreach
    rcases hJ with hJB | hBJ
    · exact Or.inl ((hFJ.mono hsub).trans hJB)
    · exact SA.anc_total hU (hFJ.mono hsub) hBJ
  rw [Compose.frame_of_projAC hp.run hy hc]
  change Compatible (tr.HonestBlocks H) (tr.state y k).fg.fcRoot B
  unfold Store.fcRoot
  split_ifs <;> assumption

/-- Vote specialization of the call-level root comparison. -/
theorem high_J_root_of_held_before
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {i k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hx : x ∈ H) (hBx : B ∈ (tr.state x i).fg.tree) (hy : y ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
    (hcompare : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocks H) B O) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B :=
  high_J_root_of_held_at_call_before hp hx hBx hy hc.1 hhigh hcompare

/-- High-origin specialization of the arbitrary held-target root comparison. -/
theorem high_J_root_of_origins_before
    (hp : ResetPremises tr H proposer dg g ΔF a)
    {x y : Fin sp.n} {i j k : Nat} {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x i j B) (hy : y ∈ H)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ell e)
    (hhigh : HZ tr H g + 1 ≤ (tr.state y k).fg.hj)
    (hcompare : ∀ v r l O, r < k → HighOrigin tr H g v r l O →
      Compatible (tr.HonestBlocks H) B O) :
    Compatible (tr.HonestBlocks H) ell.frame.fcRoot B := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hBx⟩ := highOrigin_mem hp ho
  exact high_J_root_of_held_before hp ho.1 hBx hy hc hhigh hcompare

/-- **`Carry` at a first-transfer vote** (§11 "Historical finality and acceptance", §13
"Retaining the witnesses and the frame"). At an honest vote of slot `j + 1` at which `B` is not
below `fc_root` (so `Σ.F ⪯ B`), the voter holds the counted votes of the origin and has accepted
their heads before `t_j + 3Δ`: the heads, of height `≥ H_z + 1`, were first accepted after `c_z`
and before `t_j + 2Δ`, and extend `Σ.F`, so acceptance relay delivers them. -/
theorem first_carry_of_finalized_anc (hp : ResetPremises tr H proposer dg g ΔF a) (k : Nat)
    {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (ho : HighOrigin tr H g x i j B) (hfl : Compose.StoredFastLockAt tr x i j B CV)
    {y : Fin sp.n} (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y k ℓ e)
    (hs : e.msg.slot = j + 1) (hF : Anc (tr.HonestBlocks H) ℓ.frame.F B) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  obtain ⟨ℓw, D, hcw, hflD, rfl⟩ := hfl
  obtain ⟨ℓ', hc', hD⟩ := fastLock_mem hflD
  obtain rfl : ℓw = ℓ' := Option.some.inj (hcw.2.symm.trans hc'.2)
  have hBD : Anc (tr.HonestBlocks H) (ℓw.frame.viableAncestor D) D :=
    Anc.mono (SA.frameIn_of_callAt hr ho.1 hcw).2 (SA.anc_viableAncestor _ D)
  have hW := fastLock_writer hr ho.1 hflD
  refine carryAt_of_writer_window hr (sync_after hp (sp.ts j + 2 * sp.Δ)) (g_le_ts hp ho le_rfl)
    le_rfl ho.1 hy hc hs fun v hv => ?_
  obtain ⟨h₁, h₂, Hv, hHv, hHvr, hDHv, h₃⟩ := hW v hv
  refine ⟨h₁, h₂, Hv, hHv, hHvr, hF.trans (hBD.trans hDHv), Or.inr ?_⟩
  have hBHv := hBD.trans hDHv
  obtain ⟨z, hz, k₀, hHvz⟩ := hHv
  rcases h₃ with hg | ⟨kw, hkw, hkwt⟩
  · exact absurd hg (cutZ_lt_of_anc hp ho hz hHvz hBHv).2
  refine ⟨kw, hkw, ?_, hkwt⟩
  have := (cutZ_lt_of_anc hp ho ho.1 (acceptAt_mem hp ho.1 hkw) hBHv).1
  have := lt_cutZ sp g
  have := le_gbar g
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  change g ≤ tr.time kw
  linarith

/-- The invariant-based first-transfer interface derives current finalization ancestry. -/
theorem first_carry (hp : ResetPremises tr H proposer dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (ho : HighOrigin tr H g x i j B) (hfl : Compose.StoredFastLockAt tr x i j B CV)
    {y : Fin sp.n} (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hc : SA.CastAt tr.projAC y k ℓ e)
    (hs : e.msg.slot = j + 1) (hroot : ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e j CV :=
  first_carry_of_finalized_anc hp k ho hfl hy hc hs
    (vote_F_anc hp k ih ho hy hc (by omega) hroot)

/-- **`Carry` at a later vote** (§11 "First-violating-vote induction", §13 "Retaining the
witnesses and the frame"). At an honest vote of slot `m' + 1`, `m' > j`, at which `B` is not below
`fc_root`, the voter holds the honest slot-`m'` votes and has accepted their heads (which extend
`B`, by the earlier votes, hence `Σ.F`) before `t_{m'} + 3Δ`, by relay. -/
theorem later_carry_of_finalized_anc (hp : ResetPremises tr H proposer dg g ΔF a) (k : Nat)
    {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) {m' : Nat} (hm' : e.msg.slot = m' + 1) (hjm : j < m')
    (hF : Anc (tr.HonestBlocks H) ℓ.frame.F B)
    (hprior : ∀ z ∈ H, ∀ q < k, ∀ e', SA.VoteAt tr.projAC z q e' →
      e'.msg.slot = m' → SA.VoteExtends (tr.HonestBlocks H) e'.msg B) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e m' (Compose.honestVotes tr H m') := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hU := hr.coherent
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hone : ∀ v ∈ Compose.honestVotes tr H m',
      SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e m' {v} := by
    rintro v ⟨z, hz, k', e', ⟨ℓk, hck, he'⟩, rfl, hvs⟩
    have hk' := (SA.castAt_spec hr hz ⟨hck, he'⟩).2.1
    have hk'k : k' < k := by
      by_contra hkk
      have h₁ := SA.slot_mono sp (hr.time_nonneg k) (hr.time_mono (not_lt.mp hkk))
      have h₂ := (SA.castAt_spec hr hy hc).2.1
      change e'.msg.slot = m' at hvs
      omega
    obtain ⟨Hv, hHv, hHvr, hBHv⟩ := hprior z hz k' hk'k e' ⟨ℓk, hck, he'⟩ hvs
    obtain ⟨⟨Hd, hHd, hHdr, -⟩, hkt⟩ := Compose.cast_head_fcRoot hr hz ⟨hck, he'⟩
    obtain rfl : Hd = Hv :=
      hU.1 ((SA.frameIn_of_callAt hr hz hck).2 hHd) hHv (hHdr.trans hHvr.symm)
    have hkt' : tr.projAC.time k' < sp.ts m' + 2 * sp.Δ := by
      change e'.msg.slot = m' at hvs
      rw [hvs] at hkt
      linarith
    refine carryAt_of_writer_window hr (sync_after hp (sp.ts m' + 2 * sp.Δ))
      (g_le_ts hp ho hjm.le) le_rfl hz hy hc hm' ?_
    rintro v rfl
    refine ⟨hvs, ⟨k', ⟨ℓk, hck, Or.inl ⟨e', he', rfl⟩⟩,
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg k') m').2 (by omega), hkt'⟩,
      Hd, hHv, hHvr, hF.trans hBHv, ?_⟩
    rcases Compose.frame_anc_accepted hr hz k' ℓk hck Hd hHd Hd .refl with hg | ⟨k'', hk'', hacc⟩
    · exact Or.inl hg
    refine Or.inr ⟨k'', hacc, ?_, lt_of_le_of_lt (hr.time_mono hk'') hkt'⟩
    have := (cutZ_lt_of_anc hp ho hz (acceptAt_mem hp hz hacc) hBHv).1
    have := lt_cutZ sp g
    have := le_gbar g
    change g ≤ tr.time k''
    linarith
  exact ⟨hr.awake_of_call y hy k ℓ hc.1, (SA.castAt_spec hr hy hc).2.2.1,
    fun v hv => (hone v hv).heads v rfl, fun v hv => (hone v hv).holds v rfl⟩

/-- The invariant-based later-transfer interface supplies only the predecessor batch's
extension and current finalization ancestry to the local service producer. -/
theorem later_carry (hp : ResetPremises tr H proposer dg g ΔF a) (k : Nat)
    (ih : ∀ k' < k, VoteInv tr H g k' ∧ CacheInv tr H g a k') {x : Fin sp.n} {i j : Nat}
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (ho : HighOrigin tr H g x i j B) {y : Fin sp.n}
    (hy : y ∈ H) {ℓ : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y k ℓ e) {m' : Nat} (hm' : e.msg.slot = m' + 1) (hjm : j < m')
    (hroot : ¬ Anc (tr.HonestBlocks H) B ℓ.frame.fcRoot) :
    SA.CarryAt tr.projAC (tr.HonestBlocks H) y k e m' (Compose.honestVotes tr H m') := by
  refine later_carry_of_finalized_anc hp k ho hy hc hm' hjm
    (vote_F_anc hp k ih ho hy hc (by omega) hroot) ?_
  rintro z hz q hq e' ⟨ell, hcall, hcast⟩ hslot
  exact ((voteInv_iff.1 (ih q hq).1) x i j B ho z hz ell e' ⟨hcall, hcast⟩
    (by rw [hslot]; exact hjm)).1

/-- **Half of the committee votes** (`Healthy(g)`): in a slot `s'` with `t_{s'} ≥ c_z`, every
honest validator is awake and joined (no honest restart after `max(g, 0)`) and votes by
`t_{s'} + Δ` (`tryVote`), and the honest validators are at least half of the committee
(`3f ≤ n − 1`). -/
theorem half_committee (hp : ResetPremises tr H proposer dg g ΔF a) {s' : Nat}
    (hs : cutZ sp.toParams g ≤ sp.ts s') :
    sp.n ≤ 2 * {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x' j e' ∧ e'.msg.slot = s'}.ncard := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have hgt : gbar g ≤ sp.ts s' + sp.Δ := by have := lt_cutZ sp g; linarith
  have ht0 : 0 ≤ sp.ts s' + sp.Δ := (gbar_nonneg g).trans hgt
  have hsl : sp.slot (sp.ts s' + sp.Δ) = s' :=
    SA.slot_of_mem sp s' (by linarith) (by simp only [SAParams.ts]; push_cast; linarith)
  have hs3 : sp.slot (gbar g) + 3 ≤ s' := by
    have h := (SA.ts_le_iff sp).mp ((cutZ_eq sp g) ▸ hs)
    exact_mod_cast h
  have hsub : H ⊆ {x' | x' ∈ H ∧ ∃ j e', SA.VoteAt tr.projAC x' j e' ∧ e'.msg.slot = s'} := by
    intro y hy
    have hj : tr.JoinedAt y (sp.ts s' + sp.Δ) := fun k hk _ => by
      change 0 < sp.slot (sp.ts s' + sp.Δ) ∧
        tr.time k ≤ sp.toParams.slotTime (sp.slot (sp.ts s' + sp.Δ) - 1)
      have he : sp.toParams.slotTime (sp.slot (sp.ts s' + sp.Δ) - 1) =
          sp.ts ((sp.slot (sp.ts s' + sp.Δ) - 1 : Nat) : Int) := sp.slotTime_eq _
      refine ⟨by omega, (restart_le hp hy hk).trans ?_⟩
      rw [he]
      exact (SA.ts_le_iff sp).mpr (by omega)
    obtain ⟨k, e, hv, hes, -⟩ :=
      Compose.vote_of_awake_joined hp.run hp.noColl hy (hp.healthy.2.1 y hy _ hgt) hj
    exact ⟨hy, k, e, hv, hes⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hn : H.ncard + Hᶜ.ncard = sp.n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h3 := hp.healthy.2.2
  have hn' : sp.n = sp.toParams.n := rfl
  omega

/-- **(R4), the high-record lemma** (§16). From (R1): before `a` no honest row has height
`≥ H_z + 1` (HR.1 (c)), and its finality pair is below its height pair (G0.5), so the high record
coordinates start empty; every later record write at `h ≥ H_z + 1` names the entry at `h` of the
writing source's chain, which lies on the chain of a high origin (R1, rows), and the high origins
are pairwise comparable (R1), so two named entries at one height are equal (entry constancy on a
chain). Induction over the serialized honest client calls. -/
theorem high_records (hp : ResetPremises tr H proposer dg g ΔF a)
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
  rintro h hh r₁ ⟨y₁, hy₁, i₁, h₁⟩ r₂ ⟨y₂, hy₂, i₂, h₂⟩
  obtain ⟨x₁, i₁', j₁, B₁, ho₁, Z₁, hZB₁, rfl, z₁, hz₁, m₁, hZ₁, hZh₁, hZT₁⟩ :=
    high_record_entry hp hrows hy₁ hh h₁
  obtain ⟨x₂, i₂', j₂, B₂, ho₂, Z₂, hZB₂, rfl, z₂, hz₂, m₂, hZ₂, hZh₂, hZT₂⟩ :=
    high_record_entry hp hrows hy₂ hh h₂
  -- both entries lie below the later of the two comparable origins
  obtain ⟨x, hx, i, C, hC, hZ₁C, hZ₂C⟩ : ∃ x ∈ H, ∃ i C, C ∈ (tr.state x i).fg.tree ∧
      Anc (tr.HonestBlocks H) Z₁ C ∧ Anc (tr.HonestBlocks H) Z₂ C := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hB₁⟩ := highOrigin_mem hp ho₁
    obtain ⟨-, -, -, -, -, -, -, -, -, hB₂⟩ := highOrigin_mem hp ho₂
    rcases hcomp _ _ _ _ _ _ _ _ ho₁ ho₂ with h₁₂ | h₂₁
    · exact ⟨x₂, ho₂.1, i₂', B₂, hB₂, hZB₁.trans h₁₂, hZB₂⟩
    · exact ⟨x₁, ho₁.1, i₁', B₁, hB₁, hZB₁, hZB₂.trans h₂₁⟩
  have hZ₁' := mem_tree_of_anc hp hx hZ₁C hC
  have hZ₂' := mem_tree_of_anc hp hx hZ₂C hC
  rw [σ_eq_run hp hz₁ hx hZ₁ hZ₁'] at hZh₁ hZT₁
  rw [σ_eq_run hp hz₂ hx hZ₂ hZ₂'] at hZh₂ hZT₂
  exact entry_root_eq hp hx hC hZ₁C hZ₂C (hZh₁.trans hZh₂.symm) hZT₁ hZT₂

end Consensus.Goldilocks.Healing

end

module
public import AvailableChainFGSA.Proofs.EmissionFields
public import AvailableChainKitFG.ProvenanceCore
public import AvailableChainKitFG.CausalCapCore
public import AvailableChainFGSAProofs.Proofs.Foundations.Carrier
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainKitFG.CausalCap

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private noncomputable def capFaulty : Finset (Fin p.n) := by
  classical
  exact Finset.univ.filter (fun i => rho.seatOf (.base .fg) i ∉ rho.honest)

private theorem cap_weight [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) :
    p.E.weightOf (capFaulty p c rho) < p.E.q := by
  classical
  have hsub : (capFaulty p c rho).image (rho.seatOf (.base .fg)) ⊆ Gen.V2.Duty.faulty rho := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    exact ((@Finset.mem_filter (Fin p.n)
      (fun k => rho.seatOf (.base .fg) k ∉ rho.honest)
      (fun _ => @instDecidableNot _ (Classical.propDecidable _)) Finset.univ i).mp hi).2
  have hinj : Function.Injective (fun i : Fin p.n => rho.seatOf (.base .fg) i) :=
    (hL.toCStar (.base .fg) trivial).1
  have hc : (capFaulty p c rho).card ≤ (Gen.V2.Duty.faulty rho).card :=
    (Finset.card_image_of_injective (capFaulty p c rho) hinj).symm.trans_le
      (Finset.card_le_card hsub)
  have hw : p.E.weightOf (capFaulty p c rho) = (capFaulty p c rho).card := by
    change (∑ _ ∈ capFaulty p c rho, (1 : Nat)) = _
    simp
  have hq : p.E.q = Gen.Pure.qF p.n :=
    (KitFG.toWeights_q p.E).symm.trans (KitFG.unit_toWeights_q p.n)
  rw [hw, hq]
  exact hc.trans_lt hQ.lt

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The delivery index is retained to compare a row with a later tick,
including ticks of a different node at the same wall-clock time. -/
private def CapOrigin (i : Nat) (x : V) (u : Row (Fin p.n)) : Prop :=
  ∃ (z : V) (r : Nat) (a : RowWire p.n),
    HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
    a.toRow? = some u ∧ ∃ k o s, k < i ∧
      rho.events[k]? = some (.deliver x o s) ∧ p.actionTime r ≤ s

private theorem cap_origin_of_held
    (_hL : V2.D.Linked (fgsaFamilies p c).linked rho) (hv : V2.D.ExecutionValid E rho)
    (i : Nat) (x : V) (W : FGBlock (Fin p.n)) (hW : HeldAt p c E rho i x W) :
    ∀ u ∈ chainRows W, u.signer ∉ capFaulty p c rho → CapOrigin p c E rho i x u := by
  classical
  intro u hu hf
  obtain ⟨a, r, ha, har, k, o, t, hki, hk, he⟩ := held_chain_row_origin_before
    p c E rho hv.toUnforgeableSignatures hv.toScheduleWellFormed i x W hW u hu
  let z := rho.seatOf (.base .fg) u.signer
  have hz : z ∈ rho.honest := by
    have hh : rho.seatOf (.base .fg) u.signer ∈ rho.honest := by
      by_contra hn
      exact hf (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
    exact hh
  have hsign : RowSigner p c rho a z := (rowSigner_iff_holder p c rho a z).mpr
    ⟨⟨u.signer, har⟩, by
      change V2.D.Run.holder rho (ofAuth p a.auth) = some z
      rw [har]; rfl⟩
  exact ⟨z, r, a, (he z hsign hz).1, hsign, ha, k, o, t, hki, hk, (he z hsign hz).2⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
R-CAP row witnesses with the active height view.
The height laws supply the same quorum and row-origin proof as `fgsa_rCap`.
The existing old-height wrapper below contains the height transport. -/
theorem fgsa_rCap_heightView [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) (hv : V2.D.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (y i : Nat) (x : V) (W : FGBlock (Fin p.n))
    (hW : HeldAt p c E rho i x W) (hheight : y + 2 ≤ (heightView p W).h) :
    ∃ (z : V) (r : Nat) (a : RowWire p.n) (u : Row (Fin p.n))
      (T : BlockId) (timeout : Bool),
      HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
      a.toRow? = some u ∧ u ∈ chainRows W ∧ u.height_pair = .vote (y + 1) T timeout := by
  obtain ⟨X, _, _, Q, hquorum, hw⟩ :=
    (fgCertificateLaws p).height.height_crossing W (y + 1)
      (by unfold Height at *; omega) (by unfold Height at *; omega)
  obtain ⟨seat, hseat, hfaulty⟩ :=
    KitFG.honest_in_quorum p.E (capFaulty p c rho) hquorum (cap_weight p c rho hL hQ)
  obtain ⟨carrier, u, hcarrier, hu, hsigner, hmatch⟩ := hw seat hseat
  have huW : u ∈ chainRows W := KitFG.mem_chainRows_of_carrier hcarrier hu
  have huHonest : u.signer ∉ capFaulty p c rho := hsigner ▸ hfaulty
  obtain ⟨z, r, a, hb, hs, hd, _⟩ :=
    cap_origin_of_held p c E rho hL hv i x W hW u huW huHonest
  cases hp : u.height_pair with
  | empty => simp [hp, NamedHeightPair.matchesEntry] at hmatch
  | vote k T timeout =>
    have hk : k = y + 1 := by
      simp only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] at hmatch
      exact hmatch.1
    exact ⟨z, r, a, u, T, timeout, hb, hs, hd, huW, by rw [hp, hk]⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
R-CAP, P3 App. A.4: an instance of G17 on the held-block domain.
The authentic height row was released at an index strictly below the read. -/
theorem fgsa_rCap [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) (hv : V2.D.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (y' i' : Nat) (x : V) (W : FGBlock (Fin p.n))
    (hW : HeldAt p c E rho i' x W) (hheight : y' + 2 ≤ (derive p.E p.cfg W).h) :
    ∃ (z : V) (r : Nat) (a : RowWire p.n) (u : Row (Fin p.n))
      (T : BlockId) (timeout : Bool),
      HonestRowBefore p c E rho i' z r a ∧ RowSigner p c rho a z ∧
      RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
      u.height_pair = .vote (y' + 1) T timeout := by
  apply fgsa_rCap_heightView p c E rho hL hv hQ y' i' x W hW
  simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def] using hheight

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. R-CAP with exactly the run premises of `fgsa_rCap`.
The decoded honest row is the same signed wire in the held block's chain. -/
theorem fgsa_rCap_channel [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) (hv : V2.D.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) : RCap p c E rho := by
  intro y i x W hW hh
  obtain ⟨z, r, a, u, T, timeout, hb, _hs, hd, hu, hp⟩ :=
    fgsa_rCap_heightView p c E rho hL hv hQ y i x W hW hh
  obtain ⟨j, hji, hj⟩ := hb
  have encode (b : RowWire p.n) (v : Row (Fin p.n)) (hv : b.toRow? = some v) :
      b = ⟨.seat .fg v.signer, .vote ⟨v.height_pair, v.finality_pair⟩⟩ := by
    rcases b with ⟨auth, ⟨⟨bh, bf⟩⟩⟩
    cases auth with
    | none => cases hv
    | proposer s => cases hv
    | seat label k =>
      cases label with
      | head s => cases hv
      | fg =>
        have he : (⟨k, bh, bf⟩ : Row (Fin p.n)) = v := Option.some.inj hv
        subst v
        rfl
  have ha := encode a u hd
  refine ⟨j, z, r, a, T, hji, hj, ?_, ?_⟩
  · rw [ha]
    change namedEntry u.height_pair = some (y + 1, T)
    rw [namedEntry_def, hp]
  · let st := storeAt p c E rho i x
    have hs := storeBundle_stateBefore E rho i x
    have hmem : W ∈ st.fg.TF := hW.2
    clear hW hh
    induction W with
    | genesis => exact (Finset.notMem_empty u hu).elim
    | node P s root body rows ih =>
      change u ∈ rows.toFinset ∪ chainRows P at hu
      rcases Finset.mem_union.mp hu with hu | hu
      · obtain ⟨slot, N, hw, heN, hr⟩ :=
          stored_wire_of_block p st hs.cstore hs.«meta» hmem (by intro h; cases h)
        change rows = N.rows.filterMap RowWire.toRow? at hr
        have hur : u ∈ rows := List.mem_toFinset.mp hu
        rw [hr] at hur
        obtain ⟨b, hbw, hbu⟩ := List.mem_filterMap.mp hur
        have he : b = a := (encode b u hbu).trans ha.symm
        subst b
        apply List.mem_flatten.mpr
        refine ⟨N.rows, List.mem_filterMap.mpr ⟨_, hw, ?_⟩, hbw⟩
        have hrefl : Block.preceq (eraseFG (.node P s root body rows))
            (eraseFG (.node P s root body rows)) = true := Gen.Pure.block_preceq_refl _
        simp only [Wire.decode, heN, hrefl, ↓reduceIte]
      · have hpar := ih hu (hs.cstore.fg.closed _ hmem)
        obtain ⟨wires, hw, haw⟩ := List.mem_flatten.mp hpar
        obtain ⟨b, hb, hdec⟩ := List.mem_filterMap.mp hw
        apply List.mem_flatten.mpr
        refine ⟨wires, List.mem_filterMap.mpr ⟨b, hb, ?_⟩, haw⟩
        cases hbd : b.decode with
        | none => rw [hbd] at hdec; cases hdec
        | some msg =>
          cases msg with
          | vote s k B => rw [hbd] at hdec; cases hdec
          | row k payload => rw [hbd] at hdec; cases hdec
          | block slot N =>
            simp only [hbd] at hdec ⊢
            split at hdec
            · rename_i hpre
              have hparent : FGBlock.Preceq P (.node P s root body rows) := by
                change (decide (P = .node P s root body rows) || FGBlock.preceq P P) = true
                rw [KitFG.preceq_refl P, Bool.or_true]
              have hle : N.erase.preceq (eraseFG (.node P s root body rows)) = true :=
                Gen.Pure.block_preceq_trans hpre (eraseFG_preceq hparent)
              rw [hle, ite_eq_left (rfl : true = true)]
              exact hdec
            · cases hdec

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A positive certificate on a held chain contains an authentic honest
finality row. This also applies when the finalized checkpoint is genesis:
the certificate at height 1 in KitFG/Tests/CertHeight.lean needs a finality
quorum, and strict FaultQ prevents all its signers from being faulty.

Boundary example (kernel-checked in Tests/Cap.lean before the unused-import
check rejected that example-only module; retained here per the job rule):

```lean
example (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) (hv : V2.D.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (i : Nat) (x : V) (W : FGBlock (Fin p.n)) (hW : HeldAt p c E rho i x W)
    (hgen : (finalityView p W).F = .genesis) (hcert : (finalityView p W).h_F = 1) :
    ∃ z r a u, HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
      RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
      u.finality_pair = some ⟨1, genesisRoot⟩ := by
  simpa only [hcert, hgen,
    show (FGBlock.genesis : FGBlock (Fin p.n)).root = genesisRoot from rfl] using
    fgsa_finalityCap p c E rho hL hv hQ 1 i (by decide) x W hW (by rw [hcert])
```
-/
theorem fgsa_finalityCap [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) (hv : V2.D.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (y i : Nat) (hy : 0 < y) (x : V) (W : FGBlock (Fin p.n))
    (hW : HeldAt p c E rho i x W) (hF : y ≤ (finalityView p W).h_F) :
    ∃ z r a u, HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
      RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
      u.finality_pair = some ⟨(finalityView p W).h_F, (finalityView p W).F.root⟩ := by
  obtain ⟨u, hu, _, ho, hf⟩ :=
    KitFG.finalityCap_row_of_certificate
      p.E (heightView p) (finalityView p) (fgCertificateLaws p)
      (capFaulty p c rho) (cap_weight p c rho hL hQ)
      y W (CapOrigin p c E rho i x) (cap_origin_of_held p c E rho hL hv i x W hW) hy hF
  obtain ⟨z, r, a, hb, hs, hd, _⟩ := ho
  exact ⟨z, r, a, u, hb, hs, hd, hu, hf⟩

private theorem cap_tick_lt (hv : V2.D.ExecutionValid E rho)
    {i : Nat} {x : V} {u : Row (Fin p.n)} (ho : CapOrigin p c E rho i x u)
    {v : V} {t : Time} (hi : rho.events[i]? = some (.tick v t)) :
    ∃ z r a, HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
      a.toRow? = some u ∧ p.actionTime r < t := by
  obtain ⟨z, r, a, hb, hs, hd, k, o, s, hki, hk, hrs⟩ := ho
  refine ⟨z, r, a, hb, hs, hd, hrs.trans_lt ?_⟩
  by_contra hn
  have hik := V2.D.Engine.tick_index_lt_delivery E rho hv.toScheduleWellFormed hi hk
    (le_of_not_gt hn)
  omega

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Time consequence of R-CAP. The cut excludes every honest row of height
at least `y' + 1`. The held block supplies a row at or after the cut. -/
theorem fgsa_rCap_time [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) (hv : V2.D.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (y' i' : Nat) (t : Time) (x : V) (W : FGBlock (Fin p.n))
    (hW : HeldAt p c E rho i' x W) (hheight : y' + 2 ≤ (derive p.E p.cfg W).h)
    (hcut : ∀ j z r a u h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
      p.actionTime r < t → h < y' + 1) :
    ∃ z r a u T timeout, HonestRowBefore p c E rho i' z r a ∧
      RowSigner p c rho a z ∧ RowWire.toRow? a = some u ∧ u ∈ chainRows W ∧
      u.height_pair = .vote (y' + 1) T timeout ∧ t ≤ p.actionTime r := by
  obtain ⟨z, r, a, u, T, timeout, hb, hs, hd, hu, hh⟩ :=
    fgsa_rCap p c E rho hL hv hQ y' i' x W hW hheight
  refine ⟨z, r, a, u, T, timeout, hb, hs, hd, hu, hh, ?_⟩
  obtain ⟨j, _, hj⟩ := hb
  exact le_of_not_gt (fun hlt => (Nat.lt_irrefl _) (hcut j z r a u _ T timeout hj hd hh hlt))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Before the time cut, the same held domain has height below `y' + 2`.
`i' ≤ idxBefore t` includes every read whose whole prefix is before `t`. -/
theorem fgsa_rCap_before [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) (hv : V2.D.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (y' i' : Nat) (t : Time) (x : V) (W : FGBlock (Fin p.n))
    (hi : i' ≤ V2.D.Run.idxBefore rho t) (hW : HeldAt p c E rho i' x W)
    (hcut : ∀ j z r a u h T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some u → u.height_pair = .vote h T timeout →
      p.actionTime r < t → h < y' + 1) :
    (derive p.E p.cfg W).h < y' + 2 := by
  by_contra hn
  obtain ⟨u, _, _, ho, T, b, hh⟩ :=
    KitFG.causalCap_row p.E p.cfg (capFaulty p c rho) (cap_weight p c rho hL hQ)
      y' W (CapOrigin p c E rho i' x) (cap_origin_of_held p c E rho hL hv i' x W hW)
      (Nat.le_of_not_gt hn)
  obtain ⟨z, r, a, hb, hs, hd, k, o, s, hki, hk, hrs⟩ := ho
  have hst := (Gen.V2.Duty.index_lt_idxBefore_iff hv.toScheduleWellFormed hk t).mp (hki.trans_le hi)
  obtain ⟨j, _, hj⟩ := hb
  exact (Nat.lt_irrefl _) (hcut j z r a u _ T b hj hd hh (hrs.trans_lt hst))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
An honest finality row retains its held HEAD, height, target, and QC. -/
theorem cap_finality_head {j r : Nat} {z : V} {a : RowWire p.n}
    {u : Row (Fin p.n)} (ha : HonestRowAt p c E rho j z r a)
    (hs : RowSigner p c rho a z) (hd : a.toRow? = some u)
    (fp : FinalityPair) (hf : u.finality_pair = some fp) :
    ∃ H, HeldAt p c E rho j z H ∧ fp.height = (heightView p H).h_j ∧
      fp.target = (heightView p H).J.root ∧
      KitFG.TargetQCAt p.E H fp.height (heightView p H).J := by
  obtain ⟨hz, hj, hem⟩ := ha
  obtain ⟨seat, har, _⟩ := hs
  rcases a with ⟨auth, body⟩
  change auth = _ at har
  subst auth
  let t := p.actionTime r
  obtain ⟨_, _, _, _, hattest⟩ := (fgsa_emitsAt_row E rho j z t hj seat body).mp hem
  let st := FGSA.clock p (V2.D.Run.stateBefore E rho j z).st t
  let Λ := (V2.D.Run.stateBefore E rho j z).record
  have hdecode := fgsa_attest_decode (p := p) st Λ seat body hattest
  have hue : (createRowOnce p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2).1 = some u :=
    hdecode.symm.trans hd
  obtain ⟨h, T, timeout, _, hu, _, _, _⟩ :=
    KitFG.createRowOnce_released p.E p.cfg Λ seat (fgInputs p st).1 (fgInputs p st).2 hue
  have hfp := hf
  have hfinal : finality_pair Λ.toRecord (fgInputs p st).2 = some fp := by
    rw [hu] at hf
    exact (Option.filter_eq_some_iff.mp hf).1
  have hst := cstoreInv_clock p _ (storeBundle_stateBefore E rho j z).cstore t
  cases hhead : fgBlockOf st (fgHead p st) with
  | none =>
      have hh : (fgInputs p st).2 = ⟨0, genesisRoot, 0⟩ := by
        change (match fgBlockOf st (fgHead p st) with
          | some H => Window.headFields p p.K_W H | none => ⟨0, genesisRoot, 0⟩) = _
        rw [hhead]
      rw [hh] at hfinal
      change (if (0 : Nat) < 0 ∧
          (Λ.target 0 = none ∨ Λ.target 0 = some genesisRoot) ∧
          Λ.timeout 0 = false ∧ (Λ.lock 0 = none ∨ Λ.lock 0 = some genesisRoot)
        then some ⟨0, genesisRoot⟩ else none) = some fp at hfinal
      rw [ite_eq_right (fun h => Nat.lt_irrefl 0 h.1)] at hfinal
      cases hfinal
  | some H =>
      have hemit := emitted_finality_pair_of_headFields p st Λ seat u fp H hhead hue hfp
      obtain ⟨hh, hr, _, hqc⟩ := KitFG.provenance_finalityRow_of_heightLaws p.E
        (heightView p) (finalityView p) (fgCertificateLaws p).height Λ.toRecord H fp hemit
      have hmem := ((fgBlockOf_spec p st hst (fgHead p st) H).mp hhead).1
      change H ∈ (FGSA.clock p _ t).fg.TF at hmem
      rw [FGSA.clock_fg] at hmem
      exact ⟨H, ⟨hz, hmem⟩, hh, hr, hqc⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
S1 G17 #19, with the lead's positive-height correction. The held read
has a prefix before `a_(q+1)`. The absence premise concerns all honest
height-y emissions strictly before `a_q`, including rows no longer held.
The result uses certificate height, including a certificate for genesis. -/
theorem fgsa_finalityLag [Fintype V]
    (hL : V2.D.Linked (fgsaFamilies p c).linked rho) (hv : V2.D.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (q y i : Nat) (hy : 0 < y) (x : V) (W : FGBlock (Fin p.n))
    (hi : i ≤ V2.D.Run.idxBefore rho (p.actionTime (q + 1)))
    (hW : HeldAt p c E rho i x W)
    (hnone : ∀ j z r a u T timeout, HonestRowAt p c E rho j z r a →
      RowWire.toRow? a = some u → u.height_pair = .vote y T timeout →
      ¬ p.actionTime r < p.actionTime q) :
    (finalityView p W).h_F < y := by
  by_contra hn
  obtain ⟨u, _, _, ho, hf⟩ :=
    KitFG.finalityCap_row_of_certificate
      p.E (heightView p) (finalityView p) (fgCertificateLaws p)
      (capFaulty p c rho) (cap_weight p c rho hL hQ)
      y W (CapOrigin p c E rho i x) (cap_origin_of_held p c E rho hL hv i x W hW)
      hy (Nat.le_of_not_gt hn)
  obtain ⟨z, r, a, hb, hs, hd, k, o, s, hki, hk, hrs⟩ := ho
  have hst := (Gen.V2.Duty.index_lt_idxBefore_iff hv.toScheduleWellFormed hk
    (p.actionTime (q + 1))).mp (hki.trans_le hi)
  have hrq : p.actionTime r < p.actionTime (q + 1) := hrs.trans_lt hst
  obtain ⟨j, _, hj⟩ := hb
  obtain ⟨H, hH, hheight, _, _⟩ := cap_finality_head p c E rho hj hs hd _ hf
  have hheightOld : (finalityView p W).h_F = (derive p.E p.cfg H).h_j := by
    change (finalityView p W).h_F = _ at hheight
    simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def,
      KitFG.heightOf_def] using hheight
  have hy' : y - 1 + 1 = y := by omega
  have hjust : y - 1 + 1 ≤ (derive p.E p.cfg H).h_j := by
    rw [hy']
    exact (Nat.le_of_not_gt hn).trans hheightOld.le
  obtain ⟨v, _, _, ho, T, b, hh⟩ :=
    KitFG.causalCap_justified_row p.E p.cfg (capFaulty p c rho) (cap_weight p c rho hL hQ)
      (y - 1) H (CapOrigin p c E rho j z) (cap_origin_of_held p c E rho hL hv j z H hH) hjust
  obtain ⟨z', r', a', hb', _, hd', hlt⟩ := cap_tick_lt p c E rho hv ho hj.2.1
  obtain ⟨j', _, hj'⟩ := hb'
  rw [hy'] at hh
  apply hnone j' z' r' a' v T b hj' hd' hh
  have hmono : Monotone p.actionTime := by
    intro m n hmn
    change (4 * p.Δ * ((m * p.R : Nat) : Int) + 6 * p.Δ) ≤
      (4 * p.Δ * ((n * p.R : Nat) : Int) + 6 * p.Δ)
    gcongr
    exact mul_nonneg (by decide) (le_of_lt p.deltaPos)
  have hrle : r ≤ q := by
    by_contra h
    exact (not_lt_of_ge (hmono (show q + 1 ≤ r by omega))) hrq
  exact hlt.trans_le (hmono hrle)

end AvailableChain.FGSA.Run
end

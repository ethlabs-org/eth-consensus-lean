module
public import AvailableChainPCSAProofs.Proofs.Clean.C9Count
public import AvailableChainPCSAProofs.Proofs.Clean.HonestSupport
public import AvailableChainPCSAProofs.Proofs.Clean.HonestBatch
public import AvailableChainPCSAProofs.Proofs.Clean.VoteTransport
public import AvailableChainPCSAProofs.Proofs.Shared.VoterView

public section

/-! C9 early N counts (pcsa34-r4.3 §5.3, step 2). Every node of
`awakeHonestLabel s` has an honest HEAD; when every honest HEAD of label `s`
is `P`, these HEADs reach every honest early reader as distinct timely seats,
so every honest early reader counts at least `|awakeHonestLabel s|` seats for
`P`. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- With equal honest HEADs, every read at or after the early index passes the N count. -/
theorem pcsa_c9_early_holdsN_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (s : Slot) (P : Block) (hT : T₀ ≤ SA.voteTime p.toParams s)
    (hc : SA.earlyTime p.toParams s ≤ cut)
    (hhor : SA.voteTime p.toParams s ≤ rho.horizon)
    (hQ : nQuorum p.n ≤ (awakeHonestLabel p c E rho s).card)
    (hHeads : ∀ x H, HonestHeadAt p c E rho x s H → H = P)
    (y : V) (hy : y ∈ rho.honest) (k : Nat)
    (hk : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k) (t : Time) :
    holdsN p (actView (clock p (V2.D.Run.stateBefore E rho k y).st t)) s P = true := by
  classical
  let e : Fin p.n ≃ V := Equiv.ofBijective _ (h.cstar (.base (.head s)) trivial)
  let Q := (awakeHonestLabel p c E rho s).image e.symm
  have hcard : Q.card = (awakeHonestLabel p c E rho s).card :=
    Finset.card_image_of_injective _ e.symm.injective
  apply pcsa_c9_holdsN p _ s P Q (hcard ▸ hQ)
  intro i hi
  obtain ⟨x, hx, hxi⟩ := Finset.mem_image.mp hi
  have hseat : rho.seatOf (.base (.head s)) i = x := by
    rw [← hxi]
    exact e.apply_symm_apply x
  rw [pcsa_awakeHonestLabel_def] at hx
  have hxv := (Finset.mem_inter.mp hx).1
  rw [Gen.V2.Duty.awakeHonest_def] at hxv
  obtain ⟨hxh, hxw⟩ := Finset.mem_filter.mp hxv
  obtain ⟨H, hH⟩ := pcsa_honest_head_exists E rho h x hxh s hxw hhor
  have hHP := hHeads x H hH
  obtain ⟨hcl, hres⟩ := pcsa_honest_head_clean_support_win E rho h hF hD x y hy s i H hseat hH hT hc
    k hk t
  refine ⟨⟨.seat s i, .head H.root⟩, ?_, rfl, hHP ▸ hres⟩
  apply List.mem_filter.mpr
  refine ⟨(List.mem_filter.mp hcl).1, ?_⟩
  have hn := pcsa_honest_head_pool_not_capped E rho h.valid k y s i (hseat ▸ hxh)
  have hv : GridCO.votesAt (actView (clock p (V2.D.Run.stateBefore E rho k y).st t)) s =
      GridCO.votesAt (V2.D.Run.stateBefore E rho k y).st.base s := by
    delta GridCO.votesAt
    change List.filter _ (clock p _ t).base.votes = _
    rw [pcsa_clock_heads]
  change (!GridCO.equivocates
    (GridCO.votesAt (actView (clock p (V2.D.Run.stateBefore E rho k y).st t)) s) i) = true
  rw [hv, hn]
  rfl

/-- With equal honest HEADs, every read at or after the early index passes the N count. -/
theorem pcsa_c9_early_holdsN (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (s : Slot) (P : Block) (hc : SA.earlyTime p.toParams s ≤ cut)
    (hhor : SA.voteTime p.toParams s ≤ rho.horizon)
    (hQ : nQuorum p.n ≤ (awakeHonestLabel p c E rho s).card)
    (hHeads : ∀ x H, HonestHeadAt p c E rho x s H → H = P)
    (y : V) (hy : y ∈ rho.honest) (k : Nat)
    (hk : V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s) ≤ k) (t : Time) :
    holdsN p (actView (clock p (V2.D.Run.stateBefore E rho k y).st t)) s P = true :=
  pcsa_c9_early_holdsN_win E rho h hF
    (pcsa_strictFrom_of_healthy E rho hD (SA.voteTime p.toParams s)) s P (le_refl _) hc hhor hQ
    hHeads y hy k hk t

/-- A post-clock read at a duty time is at or after that time's index. -/
theorem pcsa_c9_postClock_index (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho) (y : V) (t : Time)
    (nd : Node p) (hnd : pcsa_postClock E rho y t = some nd) :
    ∃ k, rho.events[k]? = some (.tick y t) ∧ V2.D.Run.idxBefore rho t ≤ k ∧
      nd.st = clock p (V2.D.Run.stateBefore E rho k y).st t := by
  obtain ⟨k, hk, hst⟩ := pcsa_postClock_source E rho y t nd hnd
  refine ⟨k, hk, ?_, hst⟩
  apply Nat.le_of_not_gt
  intro hn
  have ht := (Gen.V2.Duty.index_lt_idxBefore_iff h.valid.toScheduleWellFormed hk _).mp hn
  exact lt_irrefl _ ht

/-- Every honest node has an early read, and with equal honest HEADs it passes the N count. -/
theorem pcsa_c9_early_N_win (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {T₀ cut : Time}
    (hD : StrictFrom E rho T₀ cut)
    (s : Slot) (P : Block) (hT : T₀ ≤ SA.voteTime p.toParams s)
    (hc : SA.earlyTime p.toParams s ≤ cut)
    (hhor : SA.earlyTime p.toParams s ≤ rho.horizon)
    (hQ : nQuorum p.n ≤ (awakeHonestLabel p c E rho s).card)
    (hHeads : ∀ x H, HonestHeadAt p c E rho x s H → H = P) :
    ∀ y ∈ rho.honest, ∃ nd, pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd ∧
      holdsN p (actView nd.st) s P = true := by
  intro y hy
  have hp : (0 : Int) < p.Δ := p.deltaPos
  have hpub : V2.PublicTime E (SA.earlyTime p.toParams s) := by
    refine ⟨4 * s + 2, ?_⟩
    rw [h.delta]
    change 4 * p.Δ * (s : Int) + 2 * p.Δ = ((4 * s + 2 : Nat) : Int) * p.Δ
    push_cast
    ring
  have h0 : 0 ≤ SA.earlyTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    positivity
  have hve : SA.voteTime p.toParams s ≤ SA.earlyTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + 2 * p.Δ
    linarith
  obtain ⟨nd, hnd⟩ := pcsa_postClock_exists E rho h y hy _ hpub h0 hhor
  obtain ⟨k, _, hk, hst⟩ := pcsa_c9_postClock_index E rho h y _ nd hnd
  refine ⟨nd, hnd, ?_⟩
  rw [hst]
  exact pcsa_c9_early_holdsN_win E rho h hF hD s P hT hc (hve.trans hhor) hQ hHeads y hy k hk _

/-- Every honest node has an early read, and with equal honest HEADs it passes the N count. -/
theorem pcsa_c9_early_N (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : Base₂ p c E rho)
    (hF : StageOneFrame p c E rho) {cut ΔF : Time}
    (hD : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho (pcsaDelay p E.Δ ΔF) cut)
    (s : Slot) (P : Block) (hc : SA.earlyTime p.toParams s ≤ cut)
    (hhor : SA.earlyTime p.toParams s ≤ rho.horizon)
    (hQ : nQuorum p.n ≤ (awakeHonestLabel p c E rho s).card)
    (hHeads : ∀ x H, HonestHeadAt p c E rho x s H → H = P) :
    ∀ y ∈ rho.honest, ∃ nd, pcsa_postClock E rho y (SA.earlyTime p.toParams s) = some nd ∧
      holdsN p (actView nd.st) s P = true :=
  pcsa_c9_early_N_win E rho h hF
    (pcsa_strictFrom_of_healthy E rho hD (SA.voteTime p.toParams s)) s P (le_refl _) hc hhor hQ
    hHeads

end AvailableChain.PCSA.Run

end

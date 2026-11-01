module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.StepFacts
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Safety

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG KitFG Gen.Pure

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {ΔF : Time} {w : HealingWitness} {iStar : Nat}

/-- A wake preserves the joint invariant. Volatile rows get a fresh local epoch. -/
theorem wc_stepRestart : WCStepRestartStatement p c E rho ΔF w iStar := by
  intro hvalid hlinked hcstar hwakes hdelta hroots hsync hdeltaF hfault hfaultQ hfaultX hpart
    hstore hcumul hmono hactive hframe hmeta hrec hgeo hcert hsrc hlabel hqc hstrat
    hnoslash hemitted htargets hlease hfast hdeadlines hheldRows hscopeRows hfinalHead
    hs i hi hilen inv v t he
  have hsch := hvalid.toScheduleWellFormed
  have hnext : i + 1 ≤ rho.events.length := Nat.succ_le_of_lt hilen
  have hfinite := wc_finiteStep ΔF w iStar hvalid hlinked hcstar hwakes hdelta hroots hsync
    hdeltaF hfault hfaultQ hfaultX hpart hstore hcumul hmono hactive hframe hmeta hrec hgeo
    hcert hsrc hlabel hqc hstrat hnoslash hemitted htargets hlease hfast hdeadlines
    hheldRows hscopeRows hfinalHead hs i hi hilen inv (.restart v t) he
  have old {j : Nat} {x : V} {s : Slot} {B : Block}
      (hr : WCResult p c E rho w iStar (i + 1) j x s B) :
      WCResult p c E rho w iStar i j x s B := by
    have hj : j < i := by
      rcases (Nat.le_of_lt_succ hr.completed).lt_or_eq with hj | hji
      · exact hj
      · have ht := hr.event
        change rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) at ht
        rw [hji, he] at ht
        cases ht
    exact { hr with completed := hj }
  have extend {j : Nat} {x : V} {s : Slot} {B : Block}
      (hr : WCResult p c E rho w iStar i j x s B) :
      WCResult p c E rho w iStar (i + 1) j x s B :=
    { hr with completed := hr.completed.trans (Nat.lt_succ_self i) }
  have hist {B : Block} (hb : WCBelowHistory p c E rho w iStar i B) :
      WCBelowHistory p c E rho w iStar (i + 1) B := by
    rcases hb.origin with hb | ⟨j, x, s, C, hr, hBC⟩
    · exact ⟨Or.inl hb⟩
    · exact ⟨Or.inr ⟨j, x, s, C, extend hr, hBC⟩⟩
  have fg (x : V) : (storeAt p c E rho (i + 1) x).fg.TF =
      (storeAt p c E rho i x).fg.TF := by
    unfold storeAt
    rw [V2.D.Run.stateBefore_succ E rho he]
    by_cases hx : v = x
    · subst v
      simp only [V2.D.World.step, Function.update_self]
      exact congrArg (fun st => st.TF) (acRestart_fg p _ t)
    · rw [V2.D.World.step_apply_of_node_ne E rho _ (show (V2.Event.restart v t).node ≠ x from hx)]
  have output (x : V) : S_at p c E rho (i + 1) x = S_at p c E rho i x := by
    unfold S_at storeAt
    rw [V2.D.Run.stateBefore_succ E rho he]
    by_cases hx : v = x
    · subst v
      simp only [V2.D.World.step, Function.update_self]
      exact acRestart_stableRecord p _ t
    · rw [V2.D.World.step_apply_of_node_ne E rho _ (show (V2.Event.restart v t).node ≠ x from hx)]
  have lease (x : V) : (storeAt p c E rho (i + 1) x).base.obligations =
      (storeAt p c E rho i x).base.obligations := by
    unfold storeAt
    rw [V2.D.Run.stateBefore_succ E rho he]
    by_cases hx : v = x
    · subst v
      simp only [V2.D.World.step, Function.update_self]
      exact acRestart_obligations p _ t
    · rw [V2.D.World.step_apply_of_node_ne E rho _ (show (V2.Event.restart v t).node ≠ x from hx)]
  have finite : ∀ k, iStar ≤ k → k ≤ i + 1 → WCFiniteFacts p c E rho k := by
    intro k hk hki
    rcases hki.lt_or_eq with hk' | rfl
    · exact inv.finite k hk (Nat.le_of_lt_succ hk')
    · exact hfinite
  refine {
    interval := ⟨hi.trans (Nat.le_succ i), hnext⟩
    nonempty := ?_
    ordered := fun j k x y s r B C hb hc => inv.ordered j k x y s r B C (old hb) (old hc)
    sameLabel := fun j k x y s B C hb hc => inv.sameLabel j k x y s B C (old hb) (old hc)
    retrospective := fun j x s B hr => inv.retrospective j x s B (old hr)
    preCutHigh := inv.preCutHigh
    suffixSources := ?_
    highCertificates := ?_
    lowFinalized := ?_
    liveTargets := ?_
    oldLiveTargets := ?_
    suffixSaved := ?_
    suffixFast := ?_
    outputOrigin := ?_
    served := ?_
    transitions := ?_
    finite := finite
    carrier := ?_ }
  · intro j x s hj hji hx hG hl
    have hlt : j < i := by
      rcases (Nat.le_of_lt_succ hji).lt_or_eq with hj | rfl
      · exact hj
      · have ht := hG.1
        change rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) at ht
        rw [he] at ht
        cases ht
    exact inv.nonempty j x s hj hlt hx hG hl
  · intro j x r K hj hji hx ht hK
    have hlt : j < i := by
      rcases (Nat.le_of_lt_succ hji).lt_or_eq with hj | rfl
      · exact hj
      · rw [he] at ht
        cases ht
    obtain ⟨B, hr, hKB⟩ := inv.suffixSources j x r K hj hlt hx ht hK
    exact ⟨B, extend hr, hKB⟩
  · intro k x W X hk hki hx hW hX hn hh
    by_cases hki' : k ≤ i
    · exact inv.highCertificates k x W X hk hki' hx hW hX hn hh
    · have heq : k = i + 1 := by omega
      subst k
      rw [fg x] at hW
      obtain ⟨ho, hb⟩ := inv.highCertificates i x W X hi le_rfl hx hW hX hn hh
      refine ⟨?_, hist hb⟩
      obtain ⟨j, y, r, wire, K, B, hj, hrest⟩ := ho.origin
      exact ⟨j, y, r, wire, K, B, hj.trans (Nat.lt_succ_self i), hrest⟩
  · intro k x D X h hk hki hD hF hh hlo
    by_cases hki' : k ≤ i
    · exact inv.lowFinalized k x D X h hk hki' hD hF hh hlo
    · have heq : k = i + 1 := by omega
      subst k
      have hD' : HeldAt p c E rho i x D := ⟨hD.1, by simpa only [fg x] using hD.2⟩
      exact inv.lowFinalized i x D X h hi le_rfl hD' hF hh hlo
  · intro k x row hk hki hx hr hl
    by_cases hki' : k ≤ i
    · exact inv.liveTargets k x row hk hki' hx hr hl
    · have heq : k = i + 1 := by omega
      subst k
      rw [lease x] at hr
      have hn := V2.D.Engine.stateBefore_now_mono_atRestart (fgsaClock p c)
        (fgsaRestoreTimeLaw p c) E rho hsch (Nat.le_succ i) x
      rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho i x),
        fgsa_clock_now p c (V2.D.Run.stateBefore E rho (i + 1) x)] at hn
      exact hist (inv.liveTargets i x row hi le_rfl hx hr (hn.trans_lt hl))
  · intro k x row hk hki hx hr hsaved hl
    by_cases hki' : k ≤ i
    · exact inv.oldLiveTargets k x row hk hki' hx hr hsaved hl
    · have heq : k = i + 1 := by omega
      subst k
      rw [lease x] at hsaved
      have hn := V2.D.Engine.stateBefore_now_mono_atRestart (fgsaClock p c)
        (fgsaRestoreTimeLaw p c) E rho hsch (Nat.le_succ i) x
      rw [fgsa_clock_now p c (V2.D.Run.stateBefore E rho i x),
        fgsa_clock_now p c (V2.D.Run.stateBefore E rho (i + 1) x)] at hn
      exact inv.oldLiveTargets i x row hi le_rfl hx hr hsaved (hn.trans_lt hl)
  · intro k x s B hk hki hx hl hb
    obtain ⟨j, hj, hRF, hG, hB⟩ := (finite k hk hki).saved x hx s B hb
    exact ⟨j, hRF, hx, (wc_gate_cut_iff hsch hs hG.1).mpr hl, hj, hl, hG.1, hB⟩
  · intro k x s X hk hki hx hl hX
    obtain ⟨j, hj, hRF, hG, _, B, hB, hXB, _⟩ := (finite k hk hki).fastWrites x hx s X hX
    exact ⟨j, B, hRF, ⟨hx, (wc_gate_cut_iff hsch hs hG.1).mpr hl,
      hj, hl, hG.1, hB⟩, hXB⟩
  · intro k x hk hki hx
    by_cases hki' : k ≤ i
    · rcases inv.outputOrigin k x hk hki' hx with hq | hr | ⟨l, hl, hlk, hf, hc⟩
      · exact Or.inl hq
      · exact Or.inr (Or.inl hr)
      · exact Or.inr (Or.inr ⟨l, hl, hlk, hf,
          fun j y s B hr => hc j y s B (old hr)⟩)
    · have heq : k = i + 1 := by omega
      subst k
      rw [output x]
      rcases inv.outputOrigin i x hi le_rfl hx with hq | ⟨j, y, s, hr⟩ |
        ⟨l, hl, hlk, hf, hc⟩
      · exact Or.inl hq
      · exact Or.inr (Or.inl ⟨j, y, s, extend hr⟩)
      · exact Or.inr (Or.inr ⟨l, hl, hlk.trans (Nat.le_succ i), hf,
          fun j y s B hr => hc j y s B (old hr)⟩)
  · intro k x hk hki hx
    by_cases hki' : k ≤ i
    · exact inv.served k x hk hki' hx
    · have heq : k = i + 1 := by omega
      subst k
      rw [output x, ← hs.refreshed x hx.1.1]
      exact wc_output_mono_of_inv hsch hs inv iStar i x ⟨le_rfl, hi⟩
        ⟨hi, le_rfl⟩ hi hx.1.1
  · intro k x hk hki hx hx'
    rcases (Nat.le_of_lt_succ hki).lt_or_eq with hki' | rfl
    · exact inv.transitions k x hk hki' hx hx'
    · rw [output x]
      exact block_preceq_refl _
  · obtain ⟨W, hW, hh, hmem⟩ := inv.carrier
    refine ⟨W, hW, hh, ?_⟩
    intro k x hk hki hx
    by_cases hki' : k ≤ i
    · exact hmem k x hk hki' hx
    · have heq : k = i + 1 := by omega
      subst k
      rw [fg x]
      exact hmem i x hi le_rfl hx

end AvailableChain.FGSA.Run
end

module
public import AvailableChainFGSAProofs.Proofs.Healing.PhaseSettle

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Blueprint 21:1003–1012; r3 A2.
DC: SAME no effective event keeps the frontier and adds no evidence. -/
theorem healing_promotion_quiet_window (mono : RMonoAll p c E rho) {b m n : Nat}
    (hfront : frontierAtIdx p c E rho b = m)
    (hquiet : ∀ j, b ≤ j → j < n → ¬ EffectiveEvent p c E rho j) :
    ∀ k, b ≤ k → k ≤ n →
      frontierAtIdx p c E rho k = m ∧
      (TopEvidence p c E rho k m → TopEvidence p c E rho b m) ∧
      (ContestEvidence p c E rho k m → ContestEvidence p c E rho b m) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact fun _ => ⟨hfront, id, id⟩
  | succ k hk ih =>
    intro hkn
    obtain ⟨hf, ht, hc⟩ := ih (by omega)
    have hq := hquiet k hk (by omega)
    have hmono := healing_frontier_mono_all p c E rho mono (Nat.le_add_right k 1)
    have hf' : frontierAtIdx p c E rho (k + 1) = m := by
      by_contra hne
      exact hq (Or.inl (by omega))
    refine ⟨hf', fun h => ht ?_, fun h => hc ?_⟩
    · by_contra hn
      apply hq
      right
      change (¬ TopEvidence p c E rho k (frontierAtIdx p c E rho (k + 1)) ∧ _) ∨ _
      rw [hf']
      exact Or.inl ⟨hn, h⟩
    · by_contra hn
      apply hq
      right
      change _ ∨ (¬ ContestEvidence p c E rho k (frontierAtIdx p c E rho (k + 1)) ∧ _)
      rw [hf']
      exact Or.inr ⟨hn, h⟩

/-- Blueprint 21:1003–1045, 1385–1419; r3 A2.
DC: SAME a quiet extension retains each local height and the actual top J.
The endpoint is inclusive. Assembly supplies RMono and RXing. -/
theorem healing_phase_extend_of_no_effective [Fintype V] {G ΔF : Time}
    (hrec : Recovery₂ p c E rho G ΔF) (mono : RMonoAll p c E rho)
    (crossing : RXing p c E rho) {u a v : Time} {m : Nat}
    {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hp : PhaseInterval p c E rho u a m J contested)
    (hav : a ≤ v) (hv : v ≤ rho.horizon)
    (hquiet : ∀ j, timeIdx rho a ≤ j → j < timeIdx rho v →
      ¬ EffectiveEvent p c E rho j) :
    PhaseInterval p c E rho u v m J contested := by
  classical
  have hne : rho.honest.Nonempty := by
    have hn : Fintype.card V = p.n :=
      (V2.D.CStar.seats_eq (ℓ := .base .fg) hrec.base.linked.toCStar trivial).symm
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hf := hrec.fault
    rw [Gen.V2.Duty.faulty_def, he, Finset.sdiff_empty, Finset.card_univ, hn] at hf
    have := p.nPos
    omega
  let b := timeIdx rho a
  have hub : V2.D.Run.idxBefore rho u ≤ b := healing_phase_idx_le_time p c rho hp.1
  have initial (x : V) (hx : x ∈ rho.honest) := hp.2.2.2 b x hub le_rfl hx
  have hfront : frontierAtIdx p c E rho b = m := by
    change rho.honest.sup (fun x => (storeAt p c E rho b x).fg.h_max) = m
    apply le_antisymm
    · exact Finset.sup_le (fun x hx => (initial x hx).1.le)
    · obtain ⟨x, hx⟩ := hne
      exact (initial x hx).1 ▸ Finset.le_sup (f := fun x =>
        (storeAt p c E rho b x).fg.h_max) hx
  have win := healing_promotion_quiet_window p c E rho mono hfront hquiet
  refine ⟨hp.1.trans hav, hv, hp.2.2.1, ?_⟩
  intro k x huk hkv hx
  by_cases hkb : k ≤ b
  · exact hp.2.2.2 k x huk hkb hx
  have hbk : b ≤ k := by omega
  obtain ⟨hcap, htopBack, hcontestBack⟩ := win k hbk hkv
  obtain ⟨hH0, hc0, hr0⟩ := initial x hx
  have hH : (R_at p c E rho k x).H = m := by
    obtain ⟨W, hW, hh⟩ := healing_phase_frontier_witness p c E rho b x
    have hWk := (fgsa_store_durable p c E rho hbk x).1 hW
    exact le_antisymm ((healing_phase_local_le_frontier p c E rho hx).trans_eq hcap)
      ((hh.trans hH0) ▸ healing_phase_height_le p c E rho hWk)
  have hc : (R_at p c E rho k x).contest = contested := by
    cases hcon : contested with
    | true =>
      exact (healing_phase_contest_persist_of_crossing_all p c E rho crossing mono hx hbk hcap hH0
        (hc0.trans hcon)).2
    | false =>
      cases hkcon : (R_at p c E rho k x).contest with
      | false => rfl
      | true =>
        obtain ⟨y, hy, _, hcy⟩ := hcontestBack ⟨x, hx, hH, hkcon⟩
        rw [(initial y hy).2.1, hcon] at hcy
        contradiction
  refine ⟨hH, hc, ?_⟩
  cases J with
  | none =>
    change (R_at p c E rho k x).rootIsJ = false
    cases hcon : contested with
    | true =>
      change (decide _ && !(R_at p c E rho k x).contest) = false
      rw [hc, hcon]
      exact Bool.and_false _
    | false =>
      have hnt : ¬ TopEvidence p c E rho b m := by
        rintro ⟨y, hy, ht⟩
        obtain ⟨hHy, hcy, hry⟩ := initial y hy
        have hroot : (R_at p c E rho b y).rootIsJ = true := by
          change (decide ((storeAt p c E rho b y).fg.h_max =
            (storeAt p c E rho b y).fg.h_j + 1) && !(R_at p c E rho b y).contest) = true
          change (storeAt p c E rho b y).fg.h_max = m at hHy
          rw [hHy, ht, hcy, hcon]
          simp only [decide_true, Bool.not_false, Bool.and_self]
        rw [hry] at hroot
        contradiction
      have hnj : (storeAt p c E rho k x).fg.h_j + 1 ≠ m :=
        fun ht => hnt (htopBack ⟨x, hx, ht⟩)
      change (decide ((storeAt p c E rho k x).fg.h_max =
        (storeAt p c E rho k x).fg.h_j + 1) && _) = false
      change (storeAt p c E rho k x).fg.h_max = m at hH
      rw [hH]
      simp only [Ne.symm hnj, decide_false, Bool.false_and]
  | some B =>
    obtain ⟨hf0, hJ0⟩ := hr0
    have ht0 : (storeAt p c E rho b x).fg.h_j + 1 = m :=
      (of_decide_eq_true (Bool.and_eq_true_iff.mp hf0).1).symm.trans hH0
    obtain ⟨C, hC, _, hjC, hJC⟩ := (storeBundle_stateBefore E rho b x).cstore.fg.pair.1
    have hhC : (heightView p C).h = m := by
      have hlo := (fgCertificateLaws p).height.justified_below_height C
      have hhi := healing_phase_height_le p c E rho hC
      change (storeAt p c E rho b x).fg.h_j = _ at hjC
      change (storeAt p c E rho b x).fg.h_max = m at hH0
      simp only [Height] at *
      omega
    have hjCm : (heightView p C).h_j + 1 = m := hjC ▸ ht0
    have hCk := (fgsa_store_durable p c E rho hbk x).1 hC
    obtain ⟨hmax, htop, hJeq⟩ := healing_phase_top_node p c E rho crossing hx hCk hhC hjCm hcap.le
    have hfalse : contested = false := by
      have hn : (R_at p c E rho b x).contest = false := by
        simpa using congrArg Bool.not (Bool.and_eq_true_iff.mp hf0).2
      exact hc0.symm.trans hn
    have hJCk : FGBlock.Preceq (storeAt p c E rho k x).fg.J C := by
      by_contra hn
      have hct : (R_at p c E rho k x).contest = true := by
        change (decide ((storeAt p c E rho k x).fg.h_max =
          (storeAt p c E rho k x).fg.h_j + 1) && decide _) = true
        exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true (hmax.trans htop.symm),
          decide_eq_true ⟨C, hCk,
            (healing_phase_frontier_root p c E rho crossing hx hCk
              (hhC.trans hmax.symm)).1, hhC.trans hmax.symm, hn⟩⟩
      rw [hc, hfalse] at hct
      contradiction
    refine ⟨?_, (hJeq hJCk).trans (hJC.symm.trans hJ0)⟩
    change (decide ((storeAt p c E rho k x).fg.h_max =
      (storeAt p c E rho k x).fg.h_j + 1) && !(R_at p c E rho k x).contest) = true
    rw [hmax, htop, hc, hfalse]
    simp only [decide_true, Bool.not_false, Bool.and_self]

/-- Blueprint 21:1410–1419; r3 A2.
DC: SAME the least effective event before the inclusive cut includes equality
at the event deadline. The other arm excludes every event in that prefix. -/
theorem healing_promotion_event_split (hs : V2.D.ScheduleWellFormed E rho)
    (a d : Time) :
    (∃ i ev, afterTicksIdx rho a ≤ i ∧ rho.events[i]? = some ev ∧
      EffectiveEvent p c E rho i ∧ ev.time ≤ d ∧
      ∀ j, afterTicksIdx rho a ≤ j → j < i → ¬ EffectiveEvent p c E rho j) ∨
    (∀ j, afterTicksIdx rho a ≤ j → j < timeIdx rho d →
      ¬ EffectiveEvent p c E rho j) := by
  classical
  by_cases hex : ∃ i, afterTicksIdx rho a ≤ i ∧ i < timeIdx rho d ∧
      EffectiveEvent p c E rho i
  · left
    let i := Nat.find hex
    obtain ⟨hlo, hhi, heff⟩ := Nat.find_spec hex
    have hlen : i < rho.events.length := hhi.trans_le (List.length_filter_le ..)
    let ev := rho.events[i]
    have hi : rho.events[i]? = some ev := List.getElem?_eq_getElem hlen
    have hcut : V2.D.Run.idxBefore rho (d + 1) = timeIdx rho d := by
      change (rho.events.filter (fun e => decide (e.time < d + 1))).length =
        (rho.events.filter (fun e => decide (e.time ≤ d))).length
      simp only [Int.lt_add_one_iff]
    have htime : ev.time ≤ d := Int.lt_add_one_iff.mp
      ((Gen.V2.Duty.index_lt_idxBefore_iff hs hi (d + 1)).mp (hcut ▸ hhi))
    refine ⟨i, ev, hlo, hi, heff, htime, ?_⟩
    intro j hj hji he
    exact Nat.find_min hex hji ⟨hj, hji.trans hhi, he⟩
  · right
    intro j hj hjd he
    exact hex ⟨j, hj, hjd, he⟩

end AvailableChain.FGSA.Run
end

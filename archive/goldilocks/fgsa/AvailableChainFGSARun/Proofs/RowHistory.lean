module
public import AvailableChainFGSARun.Proofs.Reachable -- shake: keep (re-export)
public import AvailableChainFGSARun.Proofs.Emission
public import AvailableChainFGSARun.Proofs.Hooks

-- ROOT-DIGEST-2: private matcher copy; equality is checked by the kernel (BUILD B3).
namespace AvailableChain.FGSA
open AvailableChain.Generic AvailableChain.SimplexFG

private def rowHistory_admitBlock (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) : State p.n :=
  if !namedParentHeld st N then st else
  match parentFG st N.erase with
  | none => st
  | some P =>
      if blockAccepted p st s N P then
        let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)
          fg := Window.on_block p p.K_W st.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st2 := if st1.fg.F = st.fg.F then st1 else reconcile st1
        N.rows.foldl (admitRow p) st2
      else st

private theorem rowHistory_admitBlock_hygiene_eq : @admitBlock = @rowHistory_admitBlock := rfl

end AvailableChain.FGSA

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem t78_row_fold_origin (rows : List (RowWire p.n)) (st : State p.n)
    (a : RowWire p.n) (hm : a ∈ (rows.foldl (admitRow p) st).rowPool) :
    a ∈ st.rowPool ∨ a ∈ rows := by
  induction rows generalizing st with
  | nil => exact Or.inl hm
  | cons b rows ih =>
    rcases ih _ hm with hm | hm
    · rcases admitRow_eq p st b with he | he <;> rw [he] at hm
      · exact Or.inl hm
      · rcases List.mem_append.mp hm with hm | hm
        · exact Or.inl hm
        · exact Or.inr (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hm)))
    · exact Or.inr (List.mem_cons_of_mem _ hm)

private theorem t78_row_process_origin (st : State p.n) (o : Obj p) (a : RowWire p.n)
    (hm : a ∈ (FGSA.process p st (toWire p o)).rowPool) :
    a ∈ st.rowPool ∨ handlesS p st o (ofRow p a) := by
  dsimp only [FGSA.process] at hm
  cases hd : (toWire p o).decode with
  | none => rw [hd] at hm; exact Or.inl hm
  | some m =>
    rw [hd] at hm
    cases m with
    | vote s i b => exact Or.inl hm
    | row i body =>
      dsimp only at hm
      rcases admitRow_eq p st ⟨(toWire p o).auth, body⟩ with he | he <;> rw [he] at hm
      · exact Or.inl hm
      · rcases List.mem_append.mp hm with hm | hm
        · exact Or.inl hm
        · right; left
          have ha := List.mem_singleton.mp hm
          apply toWire_injective
          rw [toWire_ofRow, ha, decode_eq_row.mp hd]
    | block s N =>
      dsimp only at hm
      cases hNamed : namedParentHeld st N with
      | false =>
        rw [admitBlock_refused p st s N (Or.inl hNamed)] at hm
        exact Or.inl hm
      | true =>
        rw [rowHistory_admitBlock_hygiene_eq] at hm
        unfold rowHistory_admitBlock at hm
        simp only [hNamed, Bool.not_true, Bool.false_eq_true, ite_false] at hm
        cases hp : parentFG st N.erase with
        | none => rw [hp] at hm; exact Or.inl hm
        | some P =>
          rw [hp] at hm
          cases ha : blockAccepted p st s N P with
          | false => simp only [ha, Bool.false_eq_true, ite_false] at hm; exact Or.inl hm
          | true =>
            simp only [ha, ite_true] at hm
            rcases t78_row_fold_origin N.rows _ a hm with hm | hm
            · left
              split at hm
              · exact hm
              · rwa [(reconcile_frame _).2.2.1] at hm
            · right; right
              rw [hd]
              exact ⟨⟨hNamed, P, hp, ha⟩, Or.inr (List.mem_map.mpr ⟨a, hm, rfl⟩)⟩
/-- Every pool row has an earlier handler call and stays in the durable pool. -/
theorem rowPool_provenance (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (k : Nat) (x : V) (a : RowWire p.n)
    (hm : a ∈ (V2.D.Run.stateBefore E rho k x).st.rowPool) :
    ∃ j t, j < k ∧ V2.D.Run.handlesAt E rho j x (ofRow p a) t ∧
      ∀ q, j + 1 ≤ q → q ≤ k → a ∈ (V2.D.Run.stateBefore E rho q x).st.rowPool := by
  induction k with
  | zero => exact (List.not_mem_nil hm).elim
  | succ k ih =>
    have hnext := hm
    have carry (hm : a ∈ (V2.D.Run.stateBefore E rho k x).st.rowPool) :
        ∃ j t, j < k + 1 ∧ V2.D.Run.handlesAt E rho j x (ofRow p a) t ∧
          ∀ q, j + 1 ≤ q → q ≤ k + 1 →
            a ∈ (V2.D.Run.stateBefore E rho q x).st.rowPool := by
      obtain ⟨j, t, hj, hh, hr⟩ := ih hm
      refine ⟨j, t, by omega, hh, ?_⟩
      intro q hjq hqk
      by_cases hq : q ≤ k
      · exact hr q hjq hq
      · have he : q = k + 1 := by omega
        subst q; exact hnext
    cases he : rho.events[k]? with
    | none =>
      apply carry
      simpa [V2.D.Run.stateBefore, List.take_add_one, he] using hm
    | some e =>
      rw [V2.D.Run.stateBefore_succ E rho he] at hm
      by_cases hx : e.node = x
      · cases e with
        | restart v t =>
          change v = x at hx; subst v
          simp only [V2.D.World.step, Function.update_self] at hm
          change a ∈ (acRestart p (V2.D.Run.stateBefore E rho k x).st t).rowPool at hm
          rw [acRestart_rowPool] at hm
          exact carry hm
        | tick v t =>
          change v = x at hx; subst v
          apply carry
          simp only [V2.D.World.step, Function.update_self] at hm
          rwa [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho k x) x t, clock_rowPool] at hm
        | deliver v o t =>
          change v = x at hx; subst v
          simp only [V2.D.World.step, Function.update_self] at hm
          rcases t78_row_process_origin _ o a hm with hm | hh
          · exact carry hm
          · refine ⟨k, t, Nat.lt_succ_self k, ⟨o, he, hh⟩, ?_⟩
            intro q hkq hqk
            have hq : q = k + 1 := by omega
            subst q; exact hnext
      · apply carry
        rwa [V2.D.World.step_apply_of_node_ne E rho _ hx] at hm

/-- An emitted FG row was not processed by any node at an earlier index. -/
theorem fgsa_emitted_row_no_prior_processed (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hvalid : V2.D.ExecutionValid E rho)
    {i : Nat} {v : V} {t : Time} (hi : rho.events[i]? = some (.tick v t))
    {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    ∀ k, k ≤ i → ∀ w,
      (fgsa p c).processed (V2.D.Run.stateBefore E rho k w)
        (ofRow p ⟨.seat .fg j, body⟩) = false := by
  intro k hki w
  change decide ((⟨.seat .fg j, body⟩ : RowWire p.n) ∈
    (V2.D.Run.stateBefore E rho k w).st.rowPool) = false
  apply decide_eq_false_iff_not.mpr
  intro hm
  obtain ⟨-, hseat, -⟩ := (fgsa_emitsAt_row E rho i v t hi j body).mp ho
  have hv : v ∈ rho.honest := hvalid.honest_only _ (List.mem_of_getElem? hi)
  have hilen : i < rho.events.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨deliveryIdx, tk, hdi, ⟨o', hk, hhand⟩, -⟩ := rowPool_provenance E rho k w _ hm
  have hhold : V2.D.Run.holder rho (ofRow p ⟨.seat .fg j, body⟩).auth = some v := by
    rw [ofRow_auth]
    exact congrArg some hseat
  have hproc : V2.D.Run.processes rho w o' tk := ⟨deliveryIdx, hk⟩
  have hem : ∃ t', t' ≤ tk ∧ V2.D.Run.emits E rho v (ofRow p ⟨.seat .fg j, body⟩) t' := by
    rcases (fgsaHooks p c).handles_carries _ _ _ hhand with heq | hc
    · rw [← heq]
      exact hvalid.unforgeable w o' tk hproc v hv (by rw [heq]; exact hhold)
    · exact hvalid.carried w o' tk hproc _ hc v hv hhold
  obtain ⟨t', ht', i', hi', ho'⟩ := hem
  have hii : i' = i :=
    fgsa_emitOnceUnder E rho hvalid j (by rw [hseat]; exact hv) (.row body) i' i t' t
      (by rw [hseat]; exact hi') (by rw [hseat]; exact hi) ho' ho
  subst hii
  rw [hi] at hi'
  obtain ⟨-, rfl⟩ := V2.Event.tick.inj (Option.some.inj hi')
  obtain ⟨hkl, hkv⟩ := List.getElem?_eq_some_iff.mp hk
  have hs := List.pairwise_iff_getElem.mp hvalid.sorted deliveryIdx i' hkl hilen (by omega)
  rw [hkv, (List.getElem?_eq_some_iff.mp hi).2] at hs
  unfold V2.Event.key at hs
  rcases Prod.Lex.toLex_le_toLex.mp hs with hlt | ⟨-, hph⟩
  · change tk < t at hlt
    exact (lt_irrefl _ (lt_of_le_of_lt ht' hlt)).elim
  · change (2 : Nat) ≤ 1 at hph
    omega

end AvailableChain.FGSA.Run
end

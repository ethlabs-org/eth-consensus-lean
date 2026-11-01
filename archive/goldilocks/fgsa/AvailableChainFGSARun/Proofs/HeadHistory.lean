module
public import AvailableChainFGSARun.Proofs.StampOrigins
public import AvailableChainFGSARun.Proofs.Emission
public import AvailableChainFGSARun.Proofs.Hooks -- shake: keep (re-export)

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem replay_head_step_origin (st : State p.n) (h : HeadWire p.n)
    (s : Slot) (i : Fin p.n) (b : BlockId)
    (hm : (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
      (FGSA.process p st ⟨h.auth, .head h.payload⟩).base.votes) :
    (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈ st.base.votes ∨
      h = ⟨.seat (.head s) i, b⟩ := by
  rcases h with ⟨auth, payload⟩
  rcases auth with ⟨(_ | _), _⟩ | _ | _ <;> try exact Or.inl hm
  rename_i j r
  change (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
    (GridCO.admitVote p.toParams.engine st.base ⟨.seat r j, .head payload⟩).votes at hm
  unfold GridCO.admitVote at hm
  dsimp only at hm
  split at hm
  · exact Or.inl hm
  · rcases List.mem_append.mp hm with hm | hm
    · exact Or.inl hm
    · have he : s = r ∧ i = j ∧ b = payload := by
        simpa only [List.mem_singleton, Signed.mk.injEq, Auth.seat.injEq,
          GridCO.Msg.head.injEq, and_assoc] using hm
      obtain ⟨rfl, rfl, rfl⟩ := he
      exact Or.inr rfl

private theorem replay_heads_origin (raw : List (HeadWire p.n)) (st : State p.n)
    (s : Slot) (i : Fin p.n) (b : BlockId)
    (hm : (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
      (raw.foldl (fun acc h => FGSA.process p acc ⟨h.auth, .head h.payload⟩) st).base.votes) :
    (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈ st.base.votes ∨
      (⟨.seat (.head s) i, b⟩ : HeadWire p.n) ∈ raw := by
  induction raw generalizing st with
  | nil => exact Or.inl hm
  | cons h raw ih =>
    rcases ih _ hm with hh | hh
    · rcases replay_head_step_origin st h s i b hh with hh | rfl
      · exact Or.inl hh
      · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ hh)

private theorem replay_sources_origin (sources : List (NamedProposal p.n)) (st : State p.n)
    (s : Slot) (i : Fin p.n) (b : BlockId)
    (hm : (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
      (sources.foldl (fun acc N => N.raw.foldl
        (fun acc h => FGSA.process p acc ⟨h.auth, .head h.payload⟩) acc) st).base.votes) :
    (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈ st.base.votes ∨
      ∃ N ∈ sources, (⟨.seat (.head s) i, b⟩ : HeadWire p.n) ∈ N.raw := by
  induction sources generalizing st with
  | nil => exact Or.inl hm
  | cons N sources ih =>
    rcases ih _ hm with hh | ⟨M, hM, hh⟩
    · rcases replay_heads_origin N.raw st s i b hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr ⟨N, List.mem_cons_self .., hh⟩
    · exact Or.inr ⟨M, List.mem_cons_of_mem _ hM, hh⟩

/-- A replayed HEAD was carried by an earlier delivered, retained proposal.
The result supplies no network handler or acceptance for the HEAD itself. -/
theorem fgsa_replayed_head_delivery_origin (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (k : Nat) (x : V) (wake : Time)
    (s : Slot) (i : Fin p.n) (b : BlockId)
    (hm : (⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
      (acRestart p (V2.D.Run.stateBefore E rho k x).st wake).base.votes) :
    ∃ j < k, ∃ o t, rho.events[j]? = some (.deliver x o t) ∧
      (fgsa p c).carries o (ofHead p ⟨.seat (.head s) i, b⟩) := by
  rw [acRestart_replay_order] at hm
  rcases replay_sources_origin _ _ s i b hm with hh | ⟨N, hN, hh⟩
  · exact (List.not_mem_nil hh).elim
  · unfold restartSources at hN
    obtain ⟨wire, hwire, he⟩ := List.mem_filterMap.mp hN
    cases hd : wire.decode with
    | none => simp only [hd, reduceCtorEq] at he
    | some input =>
      cases input with
      | vote r j K => simp only [hd, reduceCtorEq] at he
      | row j body => simp only [hd, reduceCtorEq] at he
      | block r M =>
        simp only [hd] at he
        split at he
        · have hMN : M = N := Option.some.inj he
          subst M
          obtain ⟨j, parent, t, hj, ht, ho, _, _⟩ :=
            stored_proposal_delivered E rho k x wire hwire
          have hp : parent = ofWire p ⟨.proposer r, .proposal N⟩ := by
            apply toWire_injective
            rw [ho, toWire_ofWire]
            exact decode_eq_block.mp hd
          refine ⟨j, hj, parent, t, ht, ?_⟩
          rw [hp]
          change (ofHead p ⟨.seat (.head s) i, b⟩) ∈ N.raw.map (ofHead p) ∨
            (ofHead p ⟨.seat (.head s) i, b⟩) ∈ N.support.map (ofHead p) ∨
            (ofHead p ⟨.seat (.head s) i, b⟩) ∈ N.rows.map (ofRow p)
          exact Or.inl (List.mem_map_of_mem hh)
        · cases he

/-- A HEAD emitted by an honest scheduled tick was never processed earlier. -/
theorem fgsa_emitted_head_no_prior_processed (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hV : V2.D.ExecutionValid E rho)
    {idx : Nat} {v : V} {t : Time} (hi : rho.events[idx]? = some (.tick v t))
    (s : Slot) (i : Fin p.n) (b : BlockId)
    (ho : ofHead p ⟨.seat (.head s) i, b⟩ ∈ V2.D.Run.emitsAt E rho idx) :
    ∀ k, k ≤ idx → ∀ x,
      (fgsa p c).processed (V2.D.Run.stateBefore E rho k x)
        (ofHead p ⟨.seat (.head s) i, b⟩) = false := by
  have hem := ho
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at hem
  have hcurrent := (fgsa_emits_head E rho _ v t s i b).mp hem
  have hv : v ∈ rho.honest := hV.honest_only _ (List.mem_of_getElem? hi)
  have hhold : V2.D.Run.holder rho (ofHead p ⟨.seat (.head s) i, b⟩).auth = some v :=
    congrArg some hcurrent.2.2.1
  intro k hki x
  change decide ((⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
    (V2.D.Run.stateBefore E rho k x).st.base.votes) = false
  apply decide_eq_false_iff_not.mpr
  intro hm
  rw [← fgsa_vote_stamp_keys E rho k x] at hm
  obtain ⟨⟨word, stamp⟩, hs, he⟩ := List.mem_map.mp hm
  dsimp only at he
  subst word
  have earlier : ∃ j < idx, ∃ parent time, rho.events[j]? = some (.deliver x parent time) ∧
      (parent = ofHead p ⟨.seat (.head s) i, b⟩ ∨
        (fgsa p c).carries parent (ofHead p ⟨.seat (.head s) i, b⟩)) := by
    rcases fgsa_vote_stamp_source_or_restart E rho k x s i b stamp hs with
      ⟨j, hj, time, ha, _⟩ | ⟨j, hj, wake, _, _, hr⟩
    · obtain ⟨parent, ht, hh⟩ := ha.1
      exact ⟨j, by omega, parent, time, ht, (fgsaHooks p c).handles_carries _ _ _ hh⟩
    · obtain ⟨q, hq, parent, time, ht, hc⟩ :=
        fgsa_replayed_head_delivery_origin E rho j x wake s i b hr
      exact ⟨q, by omega, parent, time, ht, Or.inr hc⟩
  obtain ⟨j, hj, parent, time, hd, hh⟩ := earlier
  have hp : V2.D.Run.processes rho x parent time := ⟨j, hd⟩
  have signed : ∃ u, u ≤ time ∧
      V2.D.Run.emits E rho v (ofHead p ⟨.seat (.head s) i, b⟩) u := by
    rcases hh with rfl | hc
    · exact hV.unforgeable x _ time hp v hv hhold
    · exact hV.carried x parent time hp _ hc v hv hhold
  obtain ⟨u, hut, q, hq, hqemit⟩ := signed
  rw [(V2.D.Run.step_tick_eq E rho hq).2] at hqemit
  have htime := ((fgsa_emits_head E rho _ v u s i b).mp hqemit).2.1
  have hutEq : u = t := htime.symm.trans hcurrent.2.1
  subst u
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hd
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hk := List.pairwise_iff_getElem.mp hV.sorted j idx hjl hil hj
  rw [hje, hie] at hk
  change toLex (time, 2) ≤ toLex (t, 1) at hk
  rcases Prod.Lex.toLex_le_toLex.mp hk with hlt | ⟨_, hphase⟩
  · have htlim : t ≤ time := by rw [← hcurrent.2.1]; exact hut
    exact (not_lt.mpr htlim) hlt
  · omega

end AvailableChain.FGSA.Run
end

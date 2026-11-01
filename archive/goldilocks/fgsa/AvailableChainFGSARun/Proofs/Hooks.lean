module
public import AvailableChainFGSARun.Proofs.ClockLaws -- shake: keep (re-export)
public import AvailableChainFGSA.Proofs.Metadata
public import AvailableChainKitV2.DutyEngineClock -- shake: keep (re-export)
public import AvailableChainKitV2.DutyStable -- shake: keep (re-export)

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In : Type} {c : AppCodec In}

private theorem processed_mono {st st' : State p.n}
    (hv : st.base.votes ⊆ st'.base.votes) (hr : st.rowPool ⊆ st'.rowPool)
    (hT : st.fg.TF ⊆ st'.fg.TF) (o : Obj p) :
    processedS p st o = true → processedS p st' o = true := by
  dsimp only [processedS]
  cases hd : (toWire p o).decode with
  | none => exact id
  | some m =>
    cases m with
    | vote s i b =>
      simpa only [decide_eq_true_eq] using (fun h => hv h)
    | row i body =>
      simpa only [decide_eq_true_eq] using (fun h => hr h)
    | block s N =>
      simp only [decide_eq_true_eq]
      rintro ⟨Y, hY, he⟩
      exact ⟨Y, hT hY, he⟩

private theorem deps_mono {st st' : State p.n} (hT : st.fg.TF ⊆ st'.fg.TF)
    (hn : st.namedBodies ⊆ st'.namedBodies)
    (o : Obj p) : depsS p st o = true → depsS p st' o = true := by
  unfold depsS
  cases hd : (toWire p o).decode with
  | none => exact id
  | some m =>
    cases m with
    | vote s i r => exact id
    | row i body => exact id
    | block s N =>
      simp only [Bool.and_eq_true, namedParentHeld, decide_eq_true_eq,
        Option.isSome_iff_exists]
      rintro ⟨hN, P, hP⟩
      exact ⟨hn hN, P, (parentFG_spec st' _ P).2
        ⟨hT ((parentFG_spec st _ P).1 hP).1, ((parentFG_spec st _ P).1 hP).2⟩⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
All FG-SA hooks satisfy the engine laws. -/
theorem fgsaHooks (p : Params) (c : AppCodec In) : V2.D.HooksSound (fgsa p c) where
  excludes_inert := excludes_inert c
  excludes_stable E rho hS v o i j hij hrf hx := by
    apply (excludes_stable_epoch E rho v o hij hrf ?_ hx).1
    intro k t _ _ he
    have hn := V2.D.Engine.stateBefore_now_le_event_atRestart (fgsaClock p c)
      (fgsaRestoreTimeLaw p c) E rho hS he v
    exact (fgsa_clock_now p c (V2.D.Run.stateBefore E rho k v)).symm.trans_le hn
  processed_stable E rho _ v o i j hij hrf hx := by
    apply V2.D.Engine.stateBefore_stable (fun nd => processedS p nd.st o = true)
      (P := fgsa p c) _ _ (fun _ _ h => h) E rho hij v hrf hx
    · intro nd t h
      change processedS p (FGSA.clock p nd.st t) o = true
      exact processed_mono (by rw [(clock_vn nd.st t).1])
        (by rw [clock_rowPool]) (by rw [clock_fg]) o h
    · intro nd w h
      have hc := process_cumulative p nd.st (toWire p w)
      exact processed_mono (process_votes_subset nd.st (toWire p w))
        hc.2.2.2.2.2.subset hc.1 o h
  deps_stable E rho _ v o i j hij hrf hx := by
    apply V2.D.Engine.stateBefore_stable (fun nd => depsS p nd.st o = true)
      (P := fgsa p c) _ _ (fun _ _ h => h) E rho hij v hrf hx
    · intro nd t h
      change depsS p (FGSA.clock p nd.st t) o = true
      exact deps_mono (by rw [clock_fg]) (by rw [clock_namedBodies]) o h
    · intro nd w h
      exact deps_mono (process_cumulative p nd.st (toWire p w)).1
        (process_namedBodies_subset nd.st (toWire p w)) o h
  handles_carries nd o o' h := by
    rcases h with h | h
    · exact Or.inl h
    · generalize hd : (toWire p o).decode = d at h
      cases d with
      | none => exact h.elim
      | some m =>
        cases m with
        | vote s i b => exact h.elim
        | row i body => exact h.elim
        | block s N =>
          have he := decode_eq_block.mp hd
          have hp := congrArg Signed.payload he
          change o.payload = .proposal N at hp
          exact Or.inr (by
            change carriesS p o o'
            unfold carriesS
            rw [hp]
            exact h.2.elim Or.inl (fun hm => Or.inr (Or.inr hm)))
  recordOwn_processed _ _ _ := rfl
  recordOwn_deps _ _ _ := rfl
  recordOwn_excludes _ _ _ h := h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A handled child of a well-formed envelope is well formed. -/
theorem handles_wellFormed (p : Params) (c : AppCodec In) :
    ∀ st o' o, (fgsa p c).handles st o' o →
      (fgsa p c).wellFormed o' = true → (fgsa p c).wellFormed o = true := by
  intro nd o' o hh hw
  change handlesS p nd.st o' o at hh
  change FGSA.wellFormed p (toWire p o') = true at hw
  change FGSA.wellFormed p (toWire p o) = true
  rcases hh with he | hh
  · simpa [← he] using hw
  · generalize hd : (toWire p o').decode = d at hh
    cases d with
    | none => exact hh.elim
    | some m =>
      cases m with
      | vote s i b => exact hh.elim
      | row i body => exact hh.elim
      | block s N =>
        obtain ⟨_, hm⟩ := hh
        dsimp only [FGSA.wellFormed] at hw
        rw [hd] at hw
        have hraw := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hw).1).1).1).2
        have hrows := (Bool.and_eq_true_iff.mp hw).1 |> Bool.and_eq_true_iff.mp |>.2
        rcases hm with hm | hm
        · obtain ⟨h, hmem, rfl⟩ := List.mem_map.mp hm
          have hv := List.all_eq_true.mp hraw h hmem
          cases h with
          | mk auth payload =>
            rcases auth with ⟨(_ | _), i⟩ | s | _
            · rw [toWire_ofHead]
              rfl
            all_goals change false = true at hv; cases hv
        · obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hm
          have ha := List.all_eq_true.mp hrows a hmem
          cases a with
          | mk auth payload =>
            rcases auth with ⟨(_ | _), i⟩ | s | _
            · have hf : false = true := ha
              cases hf
            · rw [toWire_ofRow]
              exact ha
            · have hf : false = true := ha
              cases hf
            · have hf : false = true := ha
              cases hf

end AvailableChain.FGSA.Run
end

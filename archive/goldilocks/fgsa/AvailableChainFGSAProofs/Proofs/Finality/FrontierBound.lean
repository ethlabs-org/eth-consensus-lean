module
public import AvailableChainFGSAProofs.Proofs.Finality.Middle

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG AvailableChain.KitFG

/-- FINAL 22:1434–1443 (FF7). The inclusive archival honest frontier is at most
one above the opening height. Timed row origin keeps the action cut strict.
DC: INTENTIONAL: the archival frontier uses the shared height client. -/
theorem honestFrontier_le_opening
    (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (base : BaseSet p c E rho)
    (faultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (w : HealingWitness) (ΔF : Time) (input : HealingInput p c E rho w ΔF)
    (r : Nat) (A : Block) (Afg : FGBlock (Fin p.n))
    (hA : HonestProposal E rho (fgsaInterface p c) (r * p.R) A)
    (eraseA : eraseFG Afg = A)
    (highA : w.M + 1 ≤ (heightView p Afg).h)
    (t : Time) (ht : t < p.actionTime r)
    (hNames : ∀ j x r a e, HonestRowAt p c E rho j x r a →
      namedEntry a.payload.height_pair = some e →
      ∃ C, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root))
    (hOrigin : ∀ (i : Nat) (x : V) (W : FGBlock (Fin p.n)),
      HeldAt p c E rho i x W → ∀ u ∈ chainRows W,
        ∃ (a : RowWire p.n) (r : Nat),
          a.toRow? = some u ∧ a.auth = .seat .fg u.signer ∧
          ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
            ∀ z : V, RowSigner p c rho a z → z ∈ rho.honest →
              HonestRowBefore p c E rho i z r a ∧ p.actionTime r ≤ t) :
    honestFrontier p c E rho t ≤ (heightView p Afg).h + 1 := by
  classical
  have hs := base.valid.toScheduleWellFormed
  have hrows : ∀ j x q a h u, HonestRowAt p c E rho j x q a →
      rowHeight a = some h → eventTime rho j = some u → u < p.actionTime r →
      h ≤ (heightView p Afg).h := by
    intro j x q a h u ha hh hu hcut
    have he := kmid_event_time p c E rho ha
    rw [he] at hu
    have hq : q < r := (kmid_action_strictMono p).lt_iff_lt.mp
      (Option.some.inj hu ▸ hcut)
    exact kmid_rows_below_opening p c E rho w input.t.h2 hNames r Afg
      (eraseA.symm ▸ hA) highA j x q a h hq ha hh
  have hread := V2.D.Engine.readAt_eq_stateBefore hs t
  have hheld : ∀ x ∈ rho.honest, ∀ B ∈ (V2.D.Run.readAt E rho t x).st.fg.TF,
      (heightView p B).h ≤ (heightView p Afg).h + 1 := by
    intro x hx B hB
    apply kmid_held_height_le p c E rho hOrigin base faultQ
      (heightView p Afg).h (p.actionTime r) hrows (timeIdx rho t) x B
    · rw [HeldAt_def]
      refine ⟨hx, ?_⟩
      change B ∈ (V2.D.Run.stateBefore E rho (timeIdx rho t) x).st.fg.TF
      rw [hread] at hB
      exact hB
    · intro k o u hk he
      have hu : u ≤ t := (V2.D.Engine.index_lt_read_length_iff hs t he).mp hk
      exact hu.trans_lt ht
  change rho.honest.sup (fun x => (V2.D.Run.readAt E rho t x).st.fg.h_max) ≤ _
  apply Finset.sup_le
  intro x hx
  rw [(storeBundle_readAt E rho t x).cstore.fg.hmax]
  exact sup_le (Finset.sup_le (hheld x hx)) (by simp only [Height]; omega)

/-- FINAL 22:1438–1443 (FF7), 1199–1206 (F2). The first fresh entry has height
one above the same opening; equality with the initial frontier is allowed.
DC: INTENTIONAL: K-MID keeps the chosen entry and its height increment. -/
theorem opening_height_succ_eq_middle
    (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (pt : KernelPt) (A : Block)
    (mid : KernelMiddleWitness_W p c E rho ΔF pt A) :
    (heightView p mid.A₀).h + 1 = (heightView p mid.U).h :=
  (kernel_middle_fresh_U p c E rho ΔF pt A mid).2.2.1.symm

end AvailableChain.FGSA.Run

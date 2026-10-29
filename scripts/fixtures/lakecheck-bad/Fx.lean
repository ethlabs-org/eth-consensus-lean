/-! `lake check` must reject this project: it proves `False` from a user axiom. -/
axiom ax : False

theorem t : False := ax

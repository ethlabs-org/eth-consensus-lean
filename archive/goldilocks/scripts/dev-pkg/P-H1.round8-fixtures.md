# P-H1 Round 8 fixture obligations

Status: numerical regressions PROVED; four complete adversarial replays
OPEN/P-H1. The exact event, certificate, parameter, horizon and output goals
in P-H1.round7-fixtures.md remain required. That file is part of this handoff.
No clock regression is presented as ExecutionValid or as a proof of TPerm.

Round 8 closes the H6 receiver floor and adds the later full-batch release
route. It does not construct the adversarial certificate prefixes. Those
prefixes need distinct scoped roots, actual accepted/emitted objects,
parent-first named bodies, scheduled awake ticks and phase-zero wake restarts.
Assigning a desired FG state or live lease as a run field is not permitted.

For each of k=3, k=4, n=7 slow and split-batch, the exact outstanding owner
obligation is to construct the run and prove all of the following together:
ExecutionValid, NamedReceiptRootCollisionFree at the actual receipt scopes,
Linked/CStar, RestartsAtWakes, PartialSynchronyBy at every bounded anchor,
RecoverySleep₂ with the listed joinedGap/horizon, and the actual read and
failure facts listed in the Round 7 table. A proof of just the failed source
cut, or a record supplied by an unproved service factory, is insufficient.
All four runs must retain their exact pre-GST signed certificate prefix.
The split run needs separate quiet extensions to 2070 and 2080 with the same
prefix. P-H1 owns both execution and extension proofs; P-As owns integration
of the completed replay into the end-to-end claim audit.

The current positive NonVacuity/HealingRun still proves RecoverySleep₂ and
an actual nonempty ready source body. It supplies no P5 factory. Its horizon
304 is shorter than the full H-time horizon 309 for those parameters.
The end-to-end extension remains OPEN/P-H1/P-As.

N4 adds a fifth numerical regression:
Δ=1, n=4, R=2, k=8, GST=21; Jst=30. A write at gate(3)=18 has deadline 49.
The ready label 8 releases at 37; label 9 releases at 41. Both are before 49.
Thus the clock alone cannot show that every pre-GST lease expired at the
ready source's release. This is not an assertion of a live stored row there.
healing_ready_batch_release_compat instead proves cleanup at an actual later
full joined batch whose HEADs cover the selected prefix. Its exact first/gate
object-service obligations remain listed in P-H1.round8-producers.md.

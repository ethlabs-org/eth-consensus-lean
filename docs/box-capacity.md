# Box capacity measurements

The measurements behind the build rules of `AGENTS.md` ("Worktree per task", "Every build in a job",
"Iterate locally"), moved there from `AGENTS.md` on 2026-11-04. They are for the shared box (`job`,
16G/8 CPU); orbs have no `job`. They are measurements, not rules, and age with the toolchain and the tree.

## Warm worktree seeding (`scripts/worktree-setup.py`)

Warm seeding is not a guaranteed setup speedup. With a fully hot shared project artifact cache,
packages-only setup plus restoration measured 2.7 s versus 4.7 s for the safer full seed alone.
Without project cache reuse (both Lake cache flags false), a packages-only full build took 114.9 s versus
1.75 s with warm outputs at the same revision (plus 4.7 s to seed). Package artifacts remain warm in both
cases; this models a fresh environment without cached project outputs, not cold Mathlib.

## Interface-migration cone and capacity

A measured 105-module interface-migration cone took 42.6 s versus 44.9 s for a full `lake build`; no-op
targeted/full builds took 0.8/1.4 s (box, 16G/8 CPU, warm). The migration peaked at 7.3 GiB summed
process RSS (shared pages counted more than once), largest Lean 1.55 GiB, Lake about 0.94 GiB. This is
the basis of the 16G/8 CPU budget per build and of at most two concurrent agent builds across the box
while another 16G/8 CPU is reserved for CI. These are independent jobs/worktrees, each already spawning
several Lean children under its CPU quota, not two Lean children in total; a measured recommendation, not
a scheduler reservation.

The cold-project control reached 18.0 GiB summed RSS (largest Lean 1.72 GiB), but only a 3.7 GiB
job-accounted peak because of already-resident shared pages; its CPU use averaged about seven cores. Do
not size cold multi-job capacity from the smaller cgroup number alone.

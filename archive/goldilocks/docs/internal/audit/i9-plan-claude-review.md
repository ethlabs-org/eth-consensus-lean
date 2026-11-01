# I9 plan: Claude review (r1 and r2)

Reviewer: Claude (Opus), 2026-09-29. Read-only on `~/ethereum/lean/available-chain`.
Scope: r1 at `24ecaaa`, then r2 at `027f173` with the spike note of `204cf2e`
(`docs/plans/2026-09-29-i9-derived-roots.md`). Inputs: r203
(`codex/derived-root.md`), `codex/scratch/r203-followups.md`, the Astra report
`docs/audit/i9-plan-audit-report.md`, and the source at `d0d913a`/`24ecaaa`.
Line references: `r1:N` is r1; `r2:N` is r2 (the line numbers of `027f173` and
`204cf2e` are the same).

## Verdict

**r2: ADOPT WITH FIXES.** No blocking finding. One major finding (M1: the
`Nat.log2` bit length makes kernel checks of depth-4 FG roots too slow; a
log-step bit length removes the problem and keeps the same roots). Six minor
findings. r2 fixes all r1 findings, or keeps only a minor residue.

(r1 alone: REVISE. Its codec, as the plan specified it with r203's encoders,
cannot evaluate the FG fixtures; see R1-1.)

## 1. r1 findings and their status in r2

```text
┌──────┬──────────┬───────────────┬───────────────────────────────────────┬──────────────────────┐
│ Id   │ Severity │ r1 lines      │ Finding                               │ r2 status            │
├──────┼──────────┼───────────────┼───────────────────────────────────────┼──────────────────────┤
│ R1-1 │ BLOCKING │ 44, 89, 91    │ `lpair` with r203's field order puts  │ FIXED: `epair` (D4,  │
│      │          │               │ roots in the second argument at many  │ r2:31–34, 127–136).  │
│      │          │               │ levels. Measured: G02 body 0 gives    │ Measured below:      │
│      │          │               │ 1,973 / 1,773,100 / 1.59·10^9 bits    │ 4,433 / 22,497 bits  │
│      │          │               │ (B1–B3); the FG-SA shape panics at B3 │ at B3                │
│      │          │               │ ("Nat.shiftl exponent is too big").   │                      │
│      │          │               │ "(k+1)× per level" was false          │                      │
│ R1-2 │ MAJOR    │ 44, 89        │ `Nat.log2` has no kernel fast path;   │ FIXED in text (r2:54,│
│      │          │               │ plain `decide` does not evaluate      │ 64). Cost residue:   │
│      │          │               │ `2 ^ k` for k > 256                   │ M1                   │
│ R1-3 │ MAJOR    │ 186, 188–189  │ `rowsOk` checked only the signed-row  │ FIXED: D9, full      │
│      │          │               │ component. The decoded-row component  │ reconstruction       │
│      │          │               │ of `encFGBody` stayed free, so        │ `b.body = packBody   │
│      │          │               │ `eraseFG (fgBlock P b rows) = b`      │ (appOf b.body) rw`   │
│      │          │               │ failed for faulty bodies              │ (r2:246–249, 255)    │
│ R1-4 │ MAJOR    │ 107           │ The three-case lemma compared two     │ FIXED: run-free      │
│      │          │               │ semantics, and only one is in Lean.   │ lookup lemmas and    │
│      │          │               │ L*'s handler (`LStar/Model/Protocol   │ no-op facts (r2:152– │
│      │          │               │ .lean:283`) does not repeat the       │ 155, 174, 185, 195,  │
│      │          │               │ parent-slot test                      │ 251). Residue: m4    │
│ R1-5 │ MINOR    │ 71, 107       │ "Tasks 3, 5, 6, 9" instantiate the    │ FIXED (r2:105)       │
│      │          │               │ lemma; SA-PC is Task 4, not Task 6    │                      │
│ R1-6 │ MINOR    │ 162, 165, 174 │ Threading a codec argument `C`        │ FIXED: D10 class     │
│      │          │               │ contradicts "keep public signatures"  │ `RowCodec`, class (b)│
│ R1-7 │ MINOR    │ 189           │ `rowsOk` in `wellFormed`: the E4      │ FIXED (r2:314).      │
│      │          │               │ permanent-refusal argument was absent │ Residue: m5          │
│ R1-8 │ MINOR    │ 44 vs 90      │ Two different size bounds             │ Moot (r2:53, 132)    │
│ R1-9 │ MINOR    │ 47, 75        │ 101 predicted CHANGED lock lines      │ FIXED: 91 names      │
│      │          │               │                                       │ (Astra, r2:57, 113)  │
│ R1-10│ MINOR    │ 206–207       │ Lock step runs before the merge       │ OPEN: m6             │
└──────┴──────────┴───────────────┴───────────────────────────────────────┴──────────────────────┘
```

## 2. Checks of r2

### 2.1 The `epair` codec (D4, Task 0)

**Injectivity.** The r2 sketch is complete. Let `k = bitLen b`. Then
`lpair a b + 1 = 2^k · (2·(a·2^k + b) + 1)`. The second factor is odd, so the
trailing-zero count of `lpair a b + 1` is `k`. Division by `2^k` gives the odd
factor, and `(m − 1) / 2 = a·2^k + b`. Because `b < 2^(bitLen b)`, `b` is the
remainder and `a` is the quotient. `epair a b = lpair (a·2^k + b) k` decodes in
the same way: the outer decode gives `c = a·2^k + b` and `k`, then `b = c % 2^k`
and `a = c / 2^k`. `nodeRoot = ⟨epair … + 1⟩ ≥ 1`, so no node root is
`genesisRoot = ⟨0⟩`. Two details for the implementer: `tz` needs fuel greater
than its result (fuel `n + 1` is sufficient), and the laws need
`b < 2 ^ bitLen b` (a standard `Nat.log2` bound).

**Size bound.** With `j = bitLen k`, `bitLen (lpair c k) ≤ bitLen c + 2j + 1`,
so `bitLen (epair a b) ≤ bitLen a + bitLen b + 2·bitLen (bitLen b) + 1`, as
r2:132 states. The bound is linear in both arguments, so the order of the
fields in an encoder does not cause exponential growth.

**Measured sizes** (core Lean `#eval`, v4.30.0-rc2). The FG-SA shape is my
sketch: three rows per block, each row once as a signed row (auth
`seat (fg 1) i`) and once as a decoded row, application value 0. It is near
Astra's sketch (337 / 3,045 / 22,181).

```text
┌──────────────────────────────────────┬───────┬────────────┬───────────────┬─────────┐
│ Codec and shape                      │ B1    │ B2         │ B3            │ B4      │
├──────────────────────────────────────┼───────┼────────────┼───────────────┼─────────┤
│ r1 lpair, G02 body 0, r203 order     │ 1,973 │ 1,773,100  │ 1,592,244,963 │ —       │
│ r1 lpair, FG-SA shape                │ 5,757 │ 10,330,748 │ panic         │ —       │
│ r2 epair, G02 body 0, r203 order     │ 146   │ 879        │ 4,433         │ 20,956  │
│ r2 epair, FG-SA shape                │ 309   │ 2,799      │ 22,497        │ 175,564 │
│ r2 epair, G02, large field first     │ 92    │ 492        │ 2,462         │ 11,576  │
└──────────────────────────────────────┴───────┴────────────┴───────────────┴─────────┘
```

Each FG level multiplies the size by about 5–8, because each row names one or
two earlier roots and FG-SA codes each row twice. B3 is far below the stop rule
(10^6 bits). B4 is 1.8·10^5 bits.

### 2.2 Kernel cost and `decide +kernel` (spike note of `204cf2e`)

```text
┌─────────────────────────────────────────────────────────┬──────────────────────────┐
│ Check (core Lean, one file each)                        │ Result                   │
├─────────────────────────────────────────────────────────┼──────────────────────────┤
│ decide +kernel, FG-SA shape, root B3 ≠ root B2          │ < 1 s, 955 MB peak RSS   │
│ decide +kernel, FG-SA shape, B3 = B3 built separately   │ < 1 s                    │
│ decide +kernel, FG-SA shape, root B4 ≠ root B3,         │ not finished after       │
│   bitLen through Nat.log2                               │ 10 min (stopped)         │
│ the same, bitLen by a log-step shift search             │ < 1 s, 446 MB; the roots │
│                                                         │ are identical            │
│ decide +kernel, Nat.log2 of a 2·10^4-bit value          │ < 1 s                    │
│ decide +kernel, Nat.log2 of a 10^5-bit value            │ about 50 s               │
│ plain decide, Nat.log2 of a 1,000-bit value             │ maxRecDepth error        │
│ plain decide, 2 ^ 1000                                  │ not evaluated (threshold │
│                                                         │ 256)                     │
│ plain decide, base chain (body k), depth 15 / 306 bits  │ passes                   │
│ plain decide, base chain, depth 30 / 725 bits           │ maxRecDepth error        │
│ decide +kernel, base chain, depth 30                    │ passes                   │
│ #print axioms of a decide +kernel theorem               │ no axioms                │
└─────────────────────────────────────────────────────────┴──────────────────────────┘
```

**Soundness.** `decide +kernel` is sound. It gives the proof term
`of_decide_eq_true (Eq.refl true)`, and the kernel type-checks it. It adds no
axiom (confirmed with `#print axioms`). It is not `native_decide`, which adds
`Lean.ofReduceBool` and trusts the compiler. The repository already uses it
(for example `FGSA/Tests/RootCollision.lean:46–64`). The r2 rule (r2:64) is
correct.

**Cost.** `Nat.log2` unfolds in one step per bit, and each step divides a
large number. The cost is quadratic in the bit length. `epair a b` computes
`bitLen b`, and `b` is as large as the body, so every root evaluation computes
`bitLen` of values of about root size. At B3 this is acceptable (the controller
spike: about 20 s for three checks at 34,108 bits). At B4 one check did not
finish in 10 minutes. A log-step bit length (an exponential search, then a
binary search, on `>>>` with fuel 64) gave the same roots and finished in less
than 1 s. See M1.

### 2.3 Statement rule, classes (a)–(c) (r2:68–101)

The three classes cover the changes that I can find:

- (a) covers constructor terms and binders that named a root, and numeric
  root values in tests.
- (b) covers the `[RowCodec V]` binder on generic FG statements. FG-SA uses the
  global `Fin n` instance and needs no binder.
- (c) names the FG-SA theorems whose premises must change: `eraseFG_fgBlock`,
  `fgBlock_root`, `fgBlock_notMem`, and `SAPC.honest_proposal_views`.

I checked the other FG-SA admission statements at `24ecaaa`.
`blockAccepted_facts` (`Admission.lean:133`) already drops the row conjunct, so
`rowsOk` needs a new lemma, not a changed statement. `blockAccepted_of_wellFormed`
(`:94`) keeps its text, because `rowsOk` comes from `wellFormed`.
`admitBlock_sufficient` and `admitBlock_sufficient_absent` (`:474`, `:532`)
have a `wellFormed` premise, so they get `rowsOk` from it. `fgBlock_parent`,
`fgBlock_slot` and `fgBlock_rows` keep their text with the r2 `fgBlock`.
`not_contentAgree` is not printed in `FGSA/Tests/Axioms.lean`, so its removal
does not break "no `#print axioms` line is removed". The stop rule for a change
outside the classes (r2:101, R8) is adequate.

### 2.4 Lookup lemma and no-op facts (r2:152–155, Tasks 3–5, 9)

`parent_mem_and_iff_root` is correct and run-free. Forward: take
`p = b.parent`. Backward: `p.root = b.parent.root` gives `p = b.parent` by
`Block.root_injective`. It states that the model's early parent-slot test equals
the same test on the stored parent that the root lookup finds. The per-protocol
no-op facts are true at `24ecaaa`:

```text
┌──────────┬──────────────────────────────────────┬──────────────────────────────┐
│ Protocol │ Missing parent                       │ Parent-slot test in handler  │
├──────────┼──────────────────────────────────────┼──────────────────────────────┤
│ Grid CO  │ `admitProposal` returns `st`         │ yes (`Protocol.lean:319–320`)│
│ / SA     │ (`Protocol.lean:319`)                │                              │
│ SA-PC    │ `proposalEnters` is false            │ yes, through GridCO          │
│          │ (`Handlers.lean:28–31`)              │ `admitProposal`              │
│ L*       │ `admitProposal` returns `st`         │ NO (`Protocol.lean:283`)     │
│ FG-SA    │ `parentFG = none` returns `st`       │ yes (`blockAccepted`)        │
│          │ (`Handlers.lean:62`)                 │                              │
└──────────┴──────────────────────────────────────┴──────────────────────────────┘
```

r2:195 states the L* difference correctly. The relay question for "deps never
present" stays open for plan 1c (r2:59, 313), as `r203-followups.md:17–24`
asked. No delivery condition changes, so the relay obligations stay as they
are.

### 2.5 Universal injectivity (base and FG)

`Block.root` recurses only on the parent, so the induction is structural and
has no premise. `FGBlock.root` also recurses only on the parent. The rows hold
earlier roots as `BlockId` numbers, not as blocks, so the rows do not make the
recursion deeper. Equal FG roots give equal parent roots, slots and
`encFGBody` values. `encFGBody` injectivity gives equal bodies and rows, and the
induction hypothesis gives equal parents. The only assumption is the
`encodeSigner_inj` field of `RowCodec`, which the `Fin n` instance proves with
`Fin.val`. A node root is also larger than every value that its content codes,
so a block cannot name its own root. The regime root fields stay, and
`rootInjective_all` fills them. No locked statement becomes weaker.

### 2.6 FG-SA (Task 9)

With the r2 definitions, the erasure law holds:
`eraseFG (fgBlock P b rw) = .node (eraseFG P) b.slot (packBody (appOf b.body) rw)`,
and this is `.node b.parent b.slot b.body = b` when `b ≠ .genesis`,
`eraseFG P = b.parent` and `rowsOk b rw`. `ContentAgree` follows from
`MetaInv.wireTree` with `rowsOk` alone. Equal base roots give `b = b'`. Then
`packBody app rows = packBody app rows'` and `packBody_inj` give
`rows = rows'`. `CStoreInv` is not necessary for this step. The admission
agreement, `CStoreInv` preservation and the cross-node carrier lemmas become
simpler, because `FGBlock.root_injective` is global. The E4 argument at r2:314
is sound. `rowsOk` is state-free and is in `wellFormed`, so an
`ExecutionValid` run never delivers a wire that fails it. FG-SA proposals are
not carried inside other objects, so no handler call reaches such a wire. Honest
proposals satisfy `rowsOk` by `appOf_packBody`, so `EmitWellFormed` holds later.

### 2.7 Lock, Registry, pins

The expected set has 91 names (`docs/plans/i9-lock-expected.tsv`, 91 lines).
I did not run the dependency algorithm again. The Task 11 stop rule (r2:272–277)
is strict and adequate. Registry rows (Task 6, r2:205), FG pins and axiom lists
(Task 8, r2:233; Task 9, r2:256) have their own checks. `FG-COMPOSITION.md`
stays with DC-simplify (r2:233). I found no unaccounted surface.

### 2.8 Sequencing

The worktree `~/worktrees/available-chain-i9` follows the user's rule for
long-lived worktrees. Main stays green until Task 11. Phase 2a adds lock lines
only at its Task 7, after the I9 merge (2a plan D8), so the lock set of I9
should not move during the work. See m6 for the one open order detail.

## 3. Findings on r2

### MAJOR

**M1. `bitLen` through `Nat.log2` is quadratic in the kernel** (r2:54, 128,
136). A depth-4 FG-SA-shaped root (175,564 bits) did not finish a
`decide +kernel` comparison in 10 minutes. With a log-step `bitLen` the same
check took less than 1 s, and the roots were identical. The Task 0 spike tests
only B3, where the cost is still acceptable. A later fixture with a child of B3
that names B3's root would stop Task 7 or Task 9, outside the Task 0 stop rule.
Fix:
- Define `bitLen` by an exponential search, then a binary search, on `>>>`
  with fuel (fuel 64 covers every practical size). Prove
  `bitLen n = if n = 0 then 0 else Nat.log2 n + 1`, or prove the two bounds
  `n < 2 ^ bitLen n` and `0 < n → 2 ^ (bitLen n − 1) ≤ n` directly. The codec
  laws need only these bounds.
- Add one B4 root comparison and one store-level fixture (for example FG-SA
  `stA` with `process` of a packed depth-3 proposal) to Task 0 Step 3. Record
  the wall time and the peak RSS against the Mac `LEAN_CAP_GB` limit, and add
  both to the stop rule.

### MINOR

**m1. Wrong import for `rootInjective_all`** (r2:144). `RootInjective` is in
`AvailableChainStatements/Generic/Conditions.lean:28`. `AvailableChainKit/Core.lean`
already imports `Generic.Properties` (line 3), and `Properties` does not import
`Conditions`. Core must import `AvailableChainStatements.Generic.Conditions`.
The section variables of `Conditions` include `[Fintype V]`, so the theorem
must state that binder or omit it.

**m2. A false `decide +kernel` goal can look like a resource failure**
(r2:136). In my experiment, a false root inequality gave "maximum recursion
depth" (in the error printer) and "deep recursion was detected at 'expression
equality test'", not "evaluates to false". Such an error must not trigger the
stop rule "a kernel check does not finish", and must not cause higher limits.
Add: before you conclude that a check does not finish, evaluate the same
Boolean with `#eval`.

**m3. Plain `decide` also fails for long base chains** (r2:54, 64). A base
chain with body `k` fails plain `decide` at depth 30 (725 bits,
maxRecDepth). It passes at depth 15. So Tasks 3–6 can also need
`decide +kernel`, not only the FG tasks. State that a fixture can change from
`decide` to `decide +kernel` as a proof change, and that the task report lists
each such change.

**m4. Name the L* obligation for a root-only refinement** (r2:195, 264). In
the model, `wellFormed` rejects an L* proposal whose parent slot is not below
its slot. A root-only adapter that copies the L* handler would accept that
block after the lookup. Task 10's note should say that such an adapter must
apply the L* parent-slot test after the resolution. The general list at r2:155
("refusals") covers it, but not by name.

**m5. D9 is a wire-validity decision without the user** (r2:42–44, 314). The
user decision was "for now just keep it to the store", about the parent root.
`rowsOk` is a content check, not a root check, and the E4 argument is sound.
But the other placement (`rowsOk` only in `blockAccepted`) would give a
permanent refusal that E4 requires in `excludes`. The plan chose the wire
placement to avoid that clause. List D9, with this reason, under "decisions
taken without the user" in `I9-REPORT.md` (r2:279), and tell the user at the
handoff.

**m6. Lock step before the merge** (r2:272–278). Step 2 writes the lock on the
branch, and Step 3 merges. If main moved and changed `docs/catalog.lock` or
`AvailableChainFramework`, the written lock is not the lock of the merged tree.
Add: if main changed either path, merge main into the branch first, then run
Step 2 on the merged tree. The risk is low, because Phase 2a changes the lock
only after the I9 merge.

## 4. Method

Experiments ran in `/Users/francesco/.claude/jobs/22f59f85/tmp/i9codec/` with the
core v4.30.0-rc2 `lean` (no Mathlib, no Lake), one file at a time, and I
removed the directory afterwards. The encoders follow r203 §3 (structures as
nested pairs in field order, sums as tagged pairs, lists as `1 + pair head
tail`). The FG-SA shape is a sketch and is not the Task 9 `packBody`. The
figures are evidence for the direction and the order of magnitude. They do not
replace Task 0.

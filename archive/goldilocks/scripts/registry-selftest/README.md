# Registry self-test

Test files for the family rule, the `unsafe` rule, the instance column, the
constant suffix and the MATRIX cell rule of `scripts/Registry.lean`. They are
not in a Lake library (`lakefile.toml` has no library under `scripts/`), and
the registry scan reads only `instanceLibraries`. Run them from the project
root after a build:

```text
lake env lean --run scripts/Registry.lean --selftest scripts/registry-selftest/SelfTest.lean
lake env lean --run scripts/Registry.lean --selftest scripts/registry-selftest/SelfTest.lean AvailableChainRegistry.Gaps.SelfTest
lake env lean --run scripts/Registry.lean --selftest scripts/registry-selftest/Unsound.lean
```

Each command prints one line per declaration of the file: the registry row
and then its MATRIX cell (or `no cell: <reason>`). It compares the lines with
the expected-output file and exits with 0 if they are the same, 1 if they are
different:

```text
┌──────────────────────────────────────┬──────────────────────────────────────────────────────────┐
│ Command                              │ Expected-output file                                     │
├──────────────────────────────────────┼──────────────────────────────────────────────────────────┤
│ SelfTest.lean                        │ SelfTest.expected                                        │
│ SelfTest.lean with the Gaps module   │ SelfTest.AvailableChainRegistry.Gaps.SelfTest.expected   │
│ Unsound.lean                         │ Unsound.expected                                         │
└──────────────────────────────────────┴──────────────────────────────────────────────────────────┘
```

After an intended change, write the file again with `--selftest-write` (same
arguments) and read the diff before you commit it. The expected statuses and
cells:

```text
┌──────────────────────────────────────┬──────────────────────────────────┬───────────────┬──────────────────────┐
│ Declaration                          │ Status                           │ Cell          │ With the Gaps module │
├──────────────────────────────────────┼──────────────────────────────────┼───────────────┼──────────────────────┤
│ SelfTest: every `neg*` row           │ CONDITIONAL (not a certificate)  │ cond          │ the same             │
│ SelfTest: `posGrid`, `posInstBinder`,│ LEAN (family)                    │ holds*        │ KNOWN-GAP (family),  │
│ `posSA`, `posSapc`                   │                                  │               │ gap                  │
│ SelfTest: `closedOne`, `closedSapc`  │ LEAN                             │ holds         │ KNOWN-GAP, gap       │
│ SelfTest: `fieldCert`                │ LEAN                             │ cert          │ KNOWN-GAP, gap       │
│ SelfTest: `nonCatalog`               │ LEAN                             │ no cell:      │ KNOWN-GAP, no cell   │
│                                      │                                  │ claim not in  │                      │
│                                      │                                  │ the catalog   │                      │
│ SelfTest: `unsafeClosed`             │ UNSOUND(unsafe)                  │ unsound       │ the same             │
│ SelfTest: `unsafeFamily`             │ UNSOUND(unsafe) (family)         │ unsound       │ the same             │
│ Unsound: `sorryFamily`               │ UNSOUND(sorryAx) (family)        │ unsound       │ not run              │
└──────────────────────────────────────┴──────────────────────────────────┴───────────────┴──────────────────────┘
```

The instance column: `posSapc` shows `AvailableChain.Registry.SAPC.sapcInst`
(the script looks through `toInstance`). A row with a closed instance term
shows the term, so it has its own MATRIX line: `closedOne`, `negFamLeak` and
the other rows at `Sm` show `AvailableChain.Registry.GridCO.gridInst
RegistrySelfTest.Sm`, and `closedSapc` shows
`AvailableChain.Registry.SAPC.sapcInst AvailableChain.SAPC.Tests.p`.
`negFamLeak` has one `GridCO.Params` binder that the instance does not use, so
it is not a family. `fieldCert` (a field that is not a parent) shows
`RegistrySelfTest.two.a`. A `profile-holds` row shows its constant as
`at C = <term>` in the claim column.

The witness checks need a copy of the script with one changed
`familyBinders` witness. Each copy must exit with 2 and print the message:

```text
┌──────────────────────────────────────────┬────────────────────┬───────────────────────────────────────────┐
│ SA witness in the copy                   │ Run with           │ Message                                   │
├──────────────────────────────────────────┼────────────────────┼───────────────────────────────────────────┤
│ AvailableChain.SA.Tests.pX               │ SelfTest.lean      │ missing witness …                         │
│ AvailableChain.SA.Tests.B (a Block)      │ SelfTest.lean      │ witness … does not have the type …        │
│ RegistrySelfTest.badWitness              │ Unsound.lean       │ witness … uses the axioms [sorryAx]       │
│ RegistrySelfTest.unsafeWitness           │ Unsound.lean       │ witness … is unsafe                       │
└──────────────────────────────────────────┴────────────────────┴───────────────────────────────────────────┘
```

For example, in a scratch directory `$D`:

```text
sed 's/`AvailableChain.SA.Tests.p)/`RegistrySelfTest.unsafeWitness)/' scripts/Registry.lean > $D/RegistryUnsafe.lean
lake env lean --run $D/RegistryUnsafe.lean --selftest scripts/registry-selftest/Unsound.lean
```

`Unsound.lean` uses `sorry` on purpose, so Lean prints `declaration uses
sorry` warnings.

#!/usr/bin/env python3
"""Self-test of the constant diff, end to end: each case plants an edit in a compiled Lean module, dumps it with
the compiled `const-dump` (scripts/ConstDump.lean) and compares it with scripts/const-diff.py against the
unedited module. Every mutation must fail with its finding; every control (proof-only edits) must pass."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import os
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True  # leaves no scripts/__pycache__ in the checkout

ROOT = Path(__file__).resolve().parent.parent
BASE = """module

public import CDFix.A
public import Mid

private def secret : Nat := 2
public def pub : Nat := secret + 1
public theorem pub_eq : pub = 3 := by decide
private def hidden : Nat := 5
public def viaHidden : Nat := hidden * 2

public structure Pair.{u, v} (α : Sort u) (β : Sort v) where
  fst : α
  snd : β

private inductive Colour | red | green
private def Colour.code : Colour → Nat | .red => 0 | .green => 1
public def redCode : Nat := Colour.code .red

public def seven : Nat := 7
public theorem small : (2 : Nat) < 4 := by decide
public theorem add_zero' : ∀ n : Nat, n + 0 = n := fun _ => rfl
public theorem em_two : (2 : Nat) < 4 ∨ ¬ (2 : Nat) < 4 := Classical.em _

private theorem helper : 1 < 2 := by decide
public theorem one_lt_three : 1 < 3 := Nat.lt_trans helper (by decide)

public def big : Nat := 18446744073709551615
public def pickFirst (a _b : Nat) : Nat := a
public def predK : Nat → Prop := fun _ => True
public theorem forallK : ∀ _ : Nat, True := fun _ => trivial
public theorem constLevel : PUnit.{1} → True := fun _ => trivial
public theorem sortLevel : Sort 1 → True := fun _ => trivial
public def diffNat : Nat := 5 - 3
public structure Two where
  a : Nat
  b : Nat
public def greeting : String := "hi"
public def letv : Nat := let x := 1; x + x
public structure Cfg where
  slots : Nat := 32
public structure SubCfg extends Cfg where
  slots := 48
public theorem useDup : True := dupT
public theorem useQ : True := mid
public structure WithProof where
  n : Nat
  h : n ≤ n := Nat.le_refl n
  e : n = n := by rfl
public structure WithProof2 extends WithProof where
  h := Nat.le_refl _
public def useWP : Nat := ({ n := 1 } : WithProof2).n
public def witnessed : {n : Nat // n ≤ n} := ⟨1, Nat.le_refl 1⟩
public def decided : {n : Nat // n ≤ 2} := ⟨1, by decide⟩
public theorem finTwo : (⟨2, by decide⟩ : Fin 5).val = 2 := rfl
private structure Bundle where
  k : Nat := 3
public theorem bundled : ∃ m : Nat, m = 3 := ⟨({} : Bundle).k, rfl⟩
public partial def loop (n : Nat) : Nat := if n = 0 then 0 else loop (n - 1)
private def impl (n : Nat) : Nat := n + 1
@[implemented_by impl] public def spec (n : Nat) : Nat := n + 1

public noncomputable def pick : Nat := Classical.choice ⟨0⟩
""" + "".join(f"public structure Chosen{i} where\n  x : Fin (pick + 1)\n" for i in range(12))
A_SRC = "module\n\npublic theorem dupT : True := {}\npublic theorem Q.proof_1 : True := trivial\n"
FILES = {"CDFix/A.lean": A_SRC.format("trivial"),  # Mid is not dumped (outside CDFix)
         "Mid.lean": "module\n\npublic import CDFix.A\n\npublic theorem mid : True := Q.proof_1\n"}
TWICE = "public import CDFix.A\npublic import CDFix.B\n"

PRIV = "_private.CDFix.0."
# (name, [(old, new)], findings the diff must report (empty: it must pass), extra const-diff arguments,
#  extra fixture modules)
CASES = [
    ("control: unchanged", [], [], []),
    ("control: proof edit that realizes equation lemmas",
     [("pub_eq : pub = 3 := by decide", "pub_eq : pub = 3 := by rw [pub, secret]")], [], []),
    ("proof edit that gains an axiom", [("pub_eq : pub = 3 := by decide", "pub_eq : pub = 3 := by simp [pub, secret]")],
     ["axioms pub_eq: +['propext']"], []),
    ("control: private lemma only a proof uses",
     [("helper : 1 < 2 := by decide", "helper : 1 ≤ 1 := Nat.le_refl 1"),
      ("Nat.lt_trans helper", "Nat.lt_of_le_of_lt helper")], [], []),
    ("control: binder name", [("∀ n : Nat, n + 0 = n", "∀ m : Nat, m + 0 = m")], [], []),
    ("universe parameters reordered", [("Pair.{u, v}", "Pair.{v, u}")], ["levels Pair: u,v -> v,u"], []),
    ("private definition under an unchanged public one",
     [("hidden : Nat := 5", "hidden : Nat := 6")], [f"value {PRIV}hidden"], []),
    ("private inductive under a public definition", [("| red | green", "| green | red")],
     [f"value {PRIV}Colour"], []),
    ("weakened statement", [("small : (2 : Nat) < 4", "small : (2 : Nat) < 5")], ["type small"], []),
    ("definition body", [("seven : Nat := 7", "seven : Nat := 8")], ["value seven"], []),
    ("sorry", [("small : (2 : Nat) < 4 := by decide", "small : (2 : Nat) < 4 := sorry")],
     ["axioms small: +['sorryAx']"], []),
    ("narrowed axioms", [("Classical.em _", "by decide")], ["axioms em_two: -["], []),
    ("theorem turned axiom", [("public theorem small : (2 : Nat) < 4 := by decide", "public axiom small : (2 : Nat) < 4")],
     ["kind small"], []),
    ("removed theorem", [("public theorem small : (2 : Nat) < 4 := by decide\n", "")], ["removed small"], []),
    ("added theorem", [("public def seven", "public theorem extra : True := trivial\npublic def seven")],
     ["added extra"], []),
    ("allowed addition", [("public def seven", "public theorem extra : True := trivial\npublic def seven")],
     [], ["--allow-added", "extra"]),
    ("allowed private value", [("hidden : Nat := 5", "hidden : Nat := 6")], [],
     ["--allow-value", f"{PRIV}hidden"]),
    ("allow entry that matches nothing", [], ["--allow-value seven matches no difference"], ["--allow-value", "seven"]),
    # one mutation per hashed field: without them, an exporter that drops that field passes
    ("Nat literal of 2^64 and more", [("18446744073709551615", "340282366920938463463374607431768211455")],
     ["value big"], []),
    ("bound variable", [("(a _b : Nat) : Nat := a", "(_a b : Nat) : Nat := b")], ["value pickFirst"], []),
    ("lambda and forall binder types", [("predK : Nat → Prop", "predK : Bool → Prop")],
     ["type predK", "value predK"], []),
    ("theorem binder type", [("forallK : ∀ _ : Nat, True", "forallK : ∀ _ : Bool, True")], ["type forallK"], []),
    ("universe level of a constant", [("PUnit.{1} → True", "PUnit.{2} → True")], ["type constLevel"], []),
    ("universe level of a sort", [("Sort 1 → True", "Sort 2 → True")], ["type sortLevel"], []),
    ("arguments swapped", [("5 - 3", "3 - 5")], ["value diffNat"], []),
    ("fields of one type swapped (projections)", [("  a : Nat\n  b : Nat", "  b : Nat\n  a : Nat")],
     ["value Two.a", "value Two.b"], []),
    ("string literal", [('"hi"', '"ho"')], ["value greeting"], []),
    ("let value", [("let x := 1", "let x := 2")], ["value letv"], []),
    ("unsafe", [("public def seven", "public unsafe def seven")], ["safety seven"], []),
    ("field default", [("slots : Nat := 32", "slots : Nat := 64")], ["value Cfg.slots._default"], []),
    ("child structure's override of an inherited default", [("slots := 48", "slots := 49")],
     ["value SubCfg.slots._default"], []),
    ("partial body", [("else loop (n - 1)", "else loop (n - 1) + 1")], ["value loop._unsafe_rec"], []),
    ("implemented_by target", [("impl (n : Nat) : Nat := n + 1", "impl (n : Nat) : Nat := n + 2")],
     [f"value {PRIV}impl"], []),
    ("merged theorem with a sorry copy imported last", [("public import CDFix.A\n", TWICE)],
     ["axioms dupT: +['sorryAx']", "axioms useDup: +['sorryAx']"], [],
     {"CDFix/B.lean": "module\n\npublic theorem dupT : True := sorry\n"}),
    ("merged theorem with an axiom copy", [("public import CDFix.A\n", TWICE)],
     ["axioms dupT: +['dupT']", "axioms useDup: +['dupT']"], [], {"CDFix/B.lean": "module\n\npublic axiom dupT : True\n"}),
    ("sorry copy merged with a clean copy in a module not dumped",
     [("public import CDFix.A\n", "public import Up\npublic import CDFix.A\n")],
     ["axioms dupT: +['sorryAx']", "axioms useDup: +['sorryAx']"], [],
     {"Up.lean": "module\n\npublic theorem dupT : True := trivial\n",
      "CDFix/A.lean": A_SRC.format("sorry")}),
    ("internal-looking merged name with a sorry copy, used only through a module not dumped",
     [("public import CDFix.A\n", TWICE)], ["axioms Q.proof_1: +['sorryAx']"], [],
     {"CDFix/B.lean": "module\n\npublic theorem Q.proof_1 : True := sorry\n"}),
    ("control: proof in a Prop field's default", [("Nat.le_refl n", "Nat.le.refl")], [], []),
    ("control: proof in a child's override of an inherited Prop default, used by a definition",
     [("h := Nat.le_refl _", "h := Nat.le.refl")],
     [], []),
    ("control: proof inside a definition", [("⟨1, Nat.le_refl 1⟩", "⟨1, Nat.le.refl⟩")], [], []),
    ("control: tactic proof inside a statement", [("(⟨2, by decide⟩ : Fin 5).val = 2",
      "(⟨2, by exact Nat.lt_of_lt_of_le (by decide) (Nat.le_refl 5)⟩ : Fin 5).val = 2")],
     [], []),
    ("term proof inside a statement (stays inline)",
     [("(⟨2, by decide⟩ : Fin 5).val = 2", "(⟨2, Nat.lt_of_lt_of_le (by decide) (Nat.le_refl 5)⟩ : Fin 5).val = 2")],
     ["type finTwo"], []),
    ("term proof inside a statement, allowed by name",
     [("(⟨2, by decide⟩ : Fin 5).val = 2", "(⟨2, Nat.lt_of_lt_of_le (by decide) (Nat.le_refl 5)⟩ : Fin 5).val = 2")],
     [], ["--allow-type", "finTwo"]),
    ("proof inside a definition that gains axioms", [("⟨1, by decide⟩", "⟨1, by omega⟩")], ["axioms decided: +["], []),
    ("control: tactic of a Prop field's default", [("e : n = n := by rfl", "e : n = n := by exact rfl")], [], []),
    ("control: private structure only a proof uses, removed",
     [("private structure Bundle where\n  k : Nat := 3\n", ""), ("⟨({} : Bundle).k, rfl⟩", "⟨3, rfl⟩")], [], []),
]


def run(cmd, **kw):
    return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, **kw)


def dump(tmp, name, src, files):
    d = Path(tmp) / name
    (d / "CDFix").mkdir(parents=True)
    for rel, text in {**files, "CDFix.lean": src}.items():  # the imported modules first, the root last
        (d / rel).write_text(text)
        out = d / rel.replace(".lean", ".olean")
        c = run(["lake", "env", "lean", f"--root={d}", "-o", str(out), str(d / rel)], env={**os.environ, "LEAN_PATH": str(d)})
        if c.returncode:
            return None, f"compile of {rel} failed:\n{c.stdout}{c.stderr}"
    c = run([str(ROOT / ".lake/build/bin/const-dump"), str(d / "out.tsv"), "CDFix"],
            env={**os.environ, "LEAN_PATH": str(d)})
    if c.returncode:
        return None, f"const-dump failed:\n{c.stdout}{c.stderr}"
    return d / "out.tsv", ""


def check(tmp, base, i, case):
    name, edits, want, extra, *files = case
    src = BASE
    for old, new in edits:
        if src.count(old) != 1:
            return False, f"{name}: the edit {old!r} does not apply exactly once (update the self-test)"
        src = src.replace(old, new)
    new, err = dump(tmp, f"case{i}", src, {**FILES, **(files[0] if files else {})})
    if new is None:
        return False, f"{name}: {err}"
    c = run([sys.executable, "-I", str(ROOT / "scripts/const-diff.py"), str(base), str(new), *extra])
    out = c.stdout + c.stderr
    fails = [l for l in out.splitlines() if l.startswith("FAIL ")]
    missing = [w for w in want if not any(w in l for l in fails)]
    ok = (c.returncode == (1 if want else 0)) and not missing and (bool(fails) == bool(want))
    detail = "" if ok else f"\n    exit {c.returncode}, missing {missing}\n    " + out.replace("\n", "\n    ")
    return ok, f"{name}: {'; '.join(fails) or 'pass'}{detail}"


def main():
    b = run(["lake", "build", "const-dump"])
    if b.returncode:
        print(b.stdout + b.stderr)
        print("const-diff self-test: FAILED (lake build const-dump)")
        return 1
    with tempfile.TemporaryDirectory() as tmp:
        base, err = dump(tmp, "base", BASE, FILES)
        if base is None:
            print("base fixture:", err)
            print("const-diff self-test: FAILED")
            return 1
        with ThreadPoolExecutor(4) as pool:
            results = list(pool.map(lambda ic: check(tmp, base, *ic), enumerate(CASES)))
        # an inductive's axioms include its constructors' whatever order the walk meets them in (Lean's
        # stored answer lacks them for some of these, depending on hash order)
        rows = {l.split("\t")[0]: l.split("\t") for l in base.read_text().splitlines()}
        missing = [f"Chosen{i}" for i in range(12) if "Classical.choice" not in rows[f"Chosen{i}"][7]]
        results.append((not missing, f"inductive axioms independent of walk order: {missing or 'all 12 have Classical.choice'}"))
        # malformed input: a repeated name must not silently replace the first line
        dup = Path(tmp) / "dup.tsv"
        line = base.read_text().splitlines()[0]
        dup.write_text(base.read_text() + line + "\n")
        c = run([sys.executable, "-I", str(ROOT / "scripts/const-diff.py"), str(base), str(dup)])
        results.append((c.returncode != 0 and "duplicate" in c.stdout + c.stderr,
                        f"repeated line in a dump: {(c.stdout + c.stderr).strip()}"))
    bad = 0
    for ok, msg in results:
        print(f"  {'ok' if ok else 'WRONG'}: {msg}")
        bad += not ok
    print("const-diff self-test:", "passed" if not bad else f"FAILED ({bad})")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())

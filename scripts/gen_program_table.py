"""Generate the concrete procedure table of the final program.

The script reads every `structure ... (p : ℕ) where` record of procedure ids
and every `Matches` predicate in `WeightedMIS/`, instantiates the two root
records `RegisterTopLevel.Procedures` and `RegisterHardSolve.Procedures`, and
emits ordinary Lean:

* `WeightedMIS/FinalProgramBodies*.lean`: for every equation `code X = body`
  of a `Matches` predicate, a definition of `body` as a function of the ids
  record (and the other parameters of the predicate), stated in the namespace
  and under the `open` lines of the source file, so that names resolve as in
  the source;
* `WeightedMIS/FinalProgramIds.lean`: the size `P`, the concrete id records
  `topIds`, `hardIds` (numerals), and the table `program` whose entry `k` is
  the body of the procedure numbered `k`;
* `WeightedMIS/FinalProgram.lean`: the `Matches` proofs (all by `rfl`).

Id fields that the predicates force to coincide (`code a = code b`, `a = b`,
and the hard procedure shared by the two roots) get one number. Every other
constrained id gets its own number; ids that no predicate constrains share a
single `.fail` entry.

Usage: python3 scripts/gen_program_table.py
"""

from pathlib import Path
import re
import textwrap
import sys

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "WeightedMIS"
PREFIX = "FinalProgram"
BODY_SPLIT = 450
BLOCK = 32  # entries per block of the two-level table
BLOCKS_PER_FILE = 7  # approximate maximal lines per bodies file


# ---------------------------------------------------------------- parsing

def split_top(text, sep):
    """Split `text` at occurrences of `sep` outside brackets."""
    parts, depth, cur, i = [], 0, "", 0
    while i < len(text):
        c = text[i]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        if depth == 0 and text.startswith(sep, i):
            parts.append(cur)
            cur = ""
            i += len(sep)
            continue
        cur += c
        i += 1
    parts.append(cur)
    return [p.strip() for p in parts]


def binder_groups(header):
    """Explicit binder groups `(a b : T)` of a declaration header."""
    groups, depth, start = [], 0, None
    for i, c in enumerate(header):
        if c == "(":
            if depth == 0:
                start = i
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0 and start is not None:
                inner = header[start + 1:i]
                if " : " in inner:
                    names, ty = inner.split(" : ", 1)
                    groups.append((names.split(), ty.strip()))
                start = None
    return groups


class FileInfo:
    def __init__(self, path):
        self.path = path
        self.module = "WeightedMIS." + path.stem


STRUCTS = {}   # full type name -> list of (field, type string, namespace, opens)
MATCHES = {}   # key -> dict
STRUCT_CTX = {}


def parse_file(path):
    lines = path.read_text().splitlines()
    ns_stack = []
    opens = []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^namespace (\S+)", line)
        if m:
            ns_stack.append(m.group(1))
            i += 1
            continue
        m = re.match(r"^end (\S+)\s*$", line)
        if m and ns_stack and ns_stack[-1] == m.group(1):
            ns_stack.pop()
            i += 1
            continue
        if line.startswith("open ") and not line.rstrip().endswith(" in"):
            text = line.rstrip()
            while (text.count("(") > text.count(")") and i + 1 < len(lines)
                   and lines[i + 1].startswith("  ")):
                i += 1
                text += "\n" + lines[i].rstrip()
            opens.append(text)
            i += 1
            continue
        ns = ns_stack[-1] if ns_stack else ""
        m = re.match(r"^structure (\w+) \(p : ℕ\) where\s*$", line)
        if m:
            fields = []
            j = i + 1
            while j < len(lines) and re.match(r"^  \w+ : ", lines[j]):
                f, ty = lines[j].strip().split(" : ", 1)
                fields.append((f, ty.strip()))
                j += 1
            full = ns + "." + m.group(1)
            STRUCTS[full] = fields
            STRUCT_CTX[full] = (ns, list(opens))
            i = j
            continue
        m = re.match(r"^(def|structure) (?:(\w+)\.)?(\w*Matches)\b(.*)$", line)
        if m:
            kind, owner, mname = m.group(1), m.group(2), m.group(3)
            header = m.group(4)
            j = i
            if kind == "def":
                while ":=" not in header:
                    j += 1
                    header += " " + lines[j].strip()
                header, rest = header.split(":=", 1)
                body = rest.strip()
                j += 1
                while j < len(lines) and lines[j].startswith("  ") and lines[j].strip():
                    body += " " + lines[j].strip()
                    j += 1
                clauses = [(None, c) for c in split_top(body, "∧")]
            else:
                while not header.rstrip().endswith("where"):
                    j += 1
                    header += " " + lines[j].strip()
                header = header.rstrip()[:-len("where")]
                j += 1
                clauses = []
                while j < len(lines) and lines[j].startswith("  ") and lines[j].strip():
                    fm = re.match(r"^  (\w+) : (.*)$", lines[j])
                    if fm:
                        clauses.append([fm.group(1), fm.group(2).strip()])
                    else:
                        clauses[-1][1] += " " + lines[j].strip()
                    j += 1
                clauses = [tuple(c) for c in clauses]
            groups = binder_groups(header)
            if owner:
                key = ("dot", ns + "." + owner, mname)
            else:
                key = ("fn", ns + "." + mname)
            MATCHES[key] = dict(ns=ns, opens=list(opens), groups=groups, clauses=clauses,
                                owner=owner, mname=mname, kind=kind, module=path.stem)
            i = j
            continue
        i += 1


for f in sorted(SRC.glob("*.lean")):
    parse_file(f)


def resolve_type(ty, ns, opens):
    ty = ty.strip()
    if not ty.endswith(" p"):
        return None
    base = ty[:-2].strip()
    if base == "Fin":
        return "Fin"
    cands = []
    parts = ns.split(".")
    for k in range(len(parts), -1, -1):
        cands.append(".".join(parts[:k] + [base]) if k else base)
    for o in opens:
        for name in re.findall(r"WeightedMIS[\w.]*", o):
            cands.append(name + "." + base)
    for c in cands:
        if c in STRUCTS:
            return c
    raise SystemExit(f"cannot resolve type {ty} in {ns}")


# ---------------------------------------------------------------- tree

LEAVES = []          # list of paths (tuples)
NODE_TYPE = {}       # path -> full type ("Fin" for leaves)


def build(path, ty):
    NODE_TYPE[path] = ty
    if ty == "Fin":
        LEAVES.append(path)
        return
    ns, opens = STRUCT_CTX[ty]
    for f, fty in STRUCTS[ty]:
        build(path + (f,), resolve_type(fty, ns, opens))


ROOTS = [("topIds", "WeightedMIS.RegisterTopLevel.Procedures"),
         ("hardIds", "WeightedMIS.RegisterHardSolve.Procedures")]
for r, t in ROOTS:
    build((r,), t)

parent = {l: l for l in LEAVES}


def find(x):
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x


def union(a, b):
    a, b = find(a), find(b)
    if a != b:
        parent[b] = a


EQS = {}          # leaf -> list of (defname, args)
BODY_DEFS = {}    # (key, clause index) -> (defname, used binder names, rhs)
PROOFS = {}


def path_of(expr, env):
    parts = expr.split(".")
    if parts[0] not in env:
        return None
    p = env[parts[0]] + tuple(parts[1:])
    if p not in NODE_TYPE:
        raise SystemExit(f"unknown path {p}")
    return p


def binder_list(info):
    out = []
    for names, ty in info["groups"]:
        for n in names:
            out.append((n, ty))
    return out


def find_matches(fn_expr, mname, first_node, env, ns):
    """Locate the Matches key for a sub-call."""
    if first_node is not None:
        ty = NODE_TYPE[first_node]
        key = ("dot", ty, mname)
        if key in MATCHES:
            return key
        raise SystemExit(f"no matches {key}")
    parts = ns.split(".")
    for k in range(len(parts), -1, -1):
        cand = ".".join(parts[:k] + [fn_expr + "." + mname]) if k else fn_expr + "." + mname
        if ("fn", cand) in MATCHES:
            return ("fn", cand)
    raise SystemExit(f"no fn matches {fn_expr}.{mname} from {ns}")


def body_name(key, idx, label):
    info = MATCHES[key]
    owner = info["owner"] or "fn"
    return f"{PREFIX}Bodies.{owner}_{info['mname']}_{idx}_{label}"


def process(key, env, depth=0):
    """Instantiate a Matches predicate; return the proof term."""
    info = MATCHES[key]
    ns = info["ns"]
    terms = []
    names = [n for n, _ in binder_list(info)]
    for idx, (label, clause) in enumerate(info["clauses"]):
        c = " ".join(clause.split())
        m = re.match(r"^code (\S+) = code (\S+)$", c)
        if m:
            union(path_of(m.group(1), env), path_of(m.group(2), env))
            terms.append("rfl")
            continue
        m = re.match(r"^code (\S+) =\s*(.+)$", c)
        if m:
            lhs = path_of(m.group(1), env)
            rhs = m.group(2)
            used = [n for n in names if n != "code" and re.search(r"(?<![\w.])" + re.escape(n) + r"\b", rhs)]
            lab = label or m.group(1).split(".")[-1]
            dn = body_name(key, idx, lab)
            BODY_DEFS[(key, idx)] = (dn, used, rhs)
            EQS.setdefault(lhs, []).append((ns + "." + dn, tuple(env[u] for u in used)))
            terms.append("rfl")
            continue
        m = re.match(r"^(\S+) = (\S+)$", c)
        if m:
            union(path_of(m.group(1), env), path_of(m.group(2), env))
            terms.append("rfl")
            continue
        m = re.match(r"^(\S+)\.(\w*Matches) code\s*(.*)$", c)
        if m:
            fexpr, mname, rest = m.group(1), m.group(2), m.group(3).split()
            first = path_of(fexpr, env)
            sub = find_matches(fexpr, mname, first, env, ns)
            args = ([first] if first is not None else []) + [path_of(a, env) for a in rest]
            sb = [n for n, _ in binder_list(MATCHES[sub]) if n != "code"]
            if len(sb) != len(args):
                raise SystemExit(f"arity mismatch {c} in {key}")
            terms.append(process(sub, dict(zip(sb, args)), depth + 1))
            continue
        raise SystemExit(f"unparsed clause {c!r} in {key}")
    if info["kind"] == "def" and len(terms) == 1:
        return terms[0]
    return "⟨" + ", ".join(terms) + "⟩"


top_proof = process(("dot", "WeightedMIS.RegisterTopLevel.Procedures", "Matches"),
                    {"ids": ("topIds",)})
hard_proof = process(("dot", "WeightedMIS.RegisterHardSolve.Procedures", "Matches"),
                     {"ids": ("hardIds",)})
union(("hardIds", "hard"), ("topIds", "assembly", "allHalf", "component", "hard"))

# ---------------------------------------------------------------- numbering

classes = {}
for l in LEAVES:
    classes.setdefault(find(l), []).append(l)

entries = []      # (rep, body expr)
index = {}
unconstrained = []


def argexpr(p):
    return ".".join(p)


warnings = []
for l in LEAVES:
    rep = find(l)
    if rep in index or rep in unconstrained:
        continue
    eqs = []
    for m in classes[rep]:
        eqs += EQS.get(m, [])
    if not eqs:
        unconstrained.append(rep)
        continue
    distinct = sorted(set(eqs))
    if len(distinct) > 1:
        warnings.append((rep, distinct))
    dn, args = eqs[0]
    index[rep] = len(entries)
    entries.append((rep, " ".join([dn] + [argexpr(a) for a in args])))

fail_index = None
if unconstrained:
    fail_index = len(entries)
    entries.append((None, ".fail"))
    for r in unconstrained:
        index[r] = fail_index

P = len(entries)
for rep, d in warnings:
    print("WARNING multiple bodies for", rep, d, file=sys.stderr)

# ---------------------------------------------------------------- emission

HEADER_DOC = "/-!\n# {title}\n\n{text}\n-/\n"


def emit_bodies():
    """Group body definitions by (module, namespace) and write files."""
    groups = {}
    order = []
    for (key, idx), (dn, used, rhs) in BODY_DEFS.items():
        info = MATCHES[key]
        g = (info["module"], info["ns"])
        if g not in groups:
            groups[g] = []
            order.append(g)
        groups[g].append((key, idx, dn, used, rhs))
    files = []
    cur, cur_lines = [], 0
    for g in order:
        n = 6 + 3 * len(groups[g]) + sum(len(o) for o in [MATCHES[groups[g][0][0]]["opens"]])
        if cur and cur_lines + n > BODY_SPLIT:
            files.append(cur)
            cur, cur_lines = [], 0
        cur.append(g)
        cur_lines += n
    if cur:
        files.append(cur)
    names = []
    for fi, gs in enumerate(files):
        name = f"{PREFIX}Bodies{fi + 1}"
        names.append(name)
        imports = sorted({"WeightedMIS." + MATCHES[groups[g][0][0]]["module"] for g in gs} |
                         {"WeightedMIS." + g[0] for g in gs})
        out = ["module", ""]
        out += [f"public import {m}" for m in imports]
        out += ["", HEADER_DOC.format(
            title=f"Procedure bodies of the final program, part {fi + 1}",
            text=("Every equation `code id = body` of a `Matches` predicate gives a definition\n"
                  "of `body` as a function of the ids record and the other parameters of the\n"
                  "predicate, stated in the namespace and under the `open` lines of the source\n"
                  "module. The concrete table `FinalProgram.program` lists these bodies.\n"
                  "This file is generated by `scripts/gen_program_table.py`.")),
                "@[expose] public section", ""]
        for g in gs:
            mod, ns = g
            items = groups[g]
            info0 = MATCHES[items[0][0]]
            out.append(f"namespace {ns}")
            out.append("")
            out += info0["opens"]
            out.append("")
            out.append("variable {p : ℕ}")
            out.append("")
            for key, idx, dn, used, rhs in items:
                info = MATCHES[key]
                tys = dict(binder_list(info))
                binders = " ".join(f"({u} : {tys[u]})" for u in used)
                out.append(f"def {dn} {binders} : Command p :=".replace("  ", " "))
                out.append("\n".join(textwrap.wrap(rhs, 100, initial_indent="  ",
                                                   subsequent_indent="    ",
                                                   break_long_words=False,
                                                   break_on_hyphens=False)))
            out.append("")
            out.append(f"end {ns}")
            out.append("")
        (SRC / f"{name}.lean").write_text("\n".join(out))
    return names


def record_inline(path):
    ty = NODE_TYPE[path]
    if ty == "Fin":
        return str(index[find(path)])
    return "{ " + ", ".join(f"{f} := {record_inline(path + (f,))}" for f, _ in STRUCTS[ty]) + " }"


def record_lines(path, col, width=100):
    """Lines of a structure instance whose `{` is at column `col`; the fields
    of a structure instance are laid out at one column."""
    ty = NODE_TYPE[path]
    items = []
    for f, _ in STRUCTS[ty]:
        inline = f"{f} := {record_inline(path + (f,))}"
        if col + 2 + len(inline) + 2 <= width:
            items.append([inline])
        else:
            sub = record_lines(path + (f,), col + 4, width)
            items.append([f"{f} :="] + sub)
    lines, cur = [], None
    fcol = " " * (col + 2)
    for k, it in enumerate(items):
        last = k == len(items) - 1
        if len(it) == 1:
            piece = it[0] + ("" if last else ",")
            if cur is not None and len(cur) + 1 + len(piece) <= width:
                cur += " " + piece
            else:
                if cur is not None:
                    lines.append(cur)
                cur = fcol + piece
        else:
            if cur is not None:
                lines.append(cur)
                cur = None
            lines.append(fcol + it[0])
            body = it[1:]
            if not last:
                body[-1] += ","
            lines += body
    if cur is not None:
        lines.append(cur)
    lines[-1] += " }"
    lines[0] = " " * col + "{ " + lines[0][col + 2:]
    return lines


def emit_ids(body_files):
    out = ["module", "",
           "public import WeightedMIS.RegisterTopLevel", "public import WeightedMIS.RegisterHardSolve",
           "", HEADER_DOC.format(
               title="Procedure numbers of the final program",
               text=(f"The final program has `P = {P}` procedures. The id records `topIds` and\n"
                     "`hardIds` number them; ids that the `Matches` predicates force to coincide\n"
                     "get one number. This file is generated by `scripts/gen_program_table.py`.")),
           "@[expose] public section", "",
           "namespace WeightedMIS.FinalProgram", "",
           "/-- The number of procedures. -/",
           f"abbrev P : ℕ := {P}", "",
           "/-- Procedure numbers of the top-level procedures. -/",
           "def topIds : RegisterTopLevel.Procedures P :=", "\n".join(record_lines(("topIds",), 2)), "",
           "/-- Procedure numbers of the hard-component procedures. -/",
           "def hardIds : RegisterHardSolve.Procedures P :=", "\n".join(record_lines(("hardIds",), 2)), "",
           "end WeightedMIS.FinalProgram", ""]
    (SRC / f"{PREFIX}Ids.lean").write_text("\n".join(out))
    nblocks = (len(entries) + BLOCK - 1) // BLOCK
    parts = [list(range(k, min(k + BLOCKS_PER_FILE, nblocks)))
             for k in range(0, nblocks, BLOCKS_PER_FILE)]
    prev = [f"{PREFIX}Ids"] + body_files
    for fi, part in enumerate(parts):
        name = f"{PREFIX}Table{fi + 1}"
        last = fi == len(parts) - 1
        out = ["module", ""] + [f"public import WeightedMIS.{m}" for m in prev]
        out += ["", HEADER_DOC.format(
                    title=f"The concrete procedure table of the final program, part {fi + 1}",
                    text=(f"Block `j` lists the bodies of procedures `{BLOCK} j` to `{BLOCK} j + {BLOCK - 1}`"
                          f" (of `P = {P}`),\n"
                          "built from the generic bodies of `FinalProgramBodies*` applied to the id\n"
                          "records `topIds` and `hardIds`."
                          + ("\nThe program looks up procedure `k` as entry `k % B` of block `k / B`."
                             if last else "")
                          + "\nThis file is generated by `scripts/gen_program_table.py`.")),
                "@[expose] public section", "",
                "namespace WeightedMIS.FinalProgram", "",
                "open WeightedMIS.RegisterMachine", ""]
        for j in part:
            lo, hi = j * BLOCK, min((j + 1) * BLOCK, len(entries))
            out.append(f"/-- The bodies of procedures {lo} to {hi - 1}. -/")
            out.append(f"def block{j} : List (Command P) := [")
            out.append(",\n".join(
                "\n".join(textwrap.wrap(e, 100, initial_indent="    ", subsequent_indent="      ",
                                        break_long_words=False, break_on_hyphens=False))
                for _, e in entries[lo:hi]) + "]")
            out.append("")
        if last:
            out += ["/-- The blocks of the table. -/",
                    "def table : List (List (Command P)) :=",
                    "\n".join(textwrap.wrap(", ".join(f"block{j}" for j in range(nblocks)), 96,
                                            initial_indent="  [", subsequent_indent="   ")) + "]",
                    "", "/-- The block size of `table`. -/", f"abbrev B : ℕ := {BLOCK}", "",
                    "/-- The final program: procedure `k` is entry `k % B` of block `k / B`. -/",
                    "def program : Code P := fun i =>",
                    "  (table.getD (i.val / B) []).getD (i.val % B) .fail", ""]
        out += ["end WeightedMIS.FinalProgram", ""]
        (SRC / f"{name}.lean").write_text("\n".join(out))
        prev = [name]
    global TABLE_LAST
    TABLE_LAST = f"{PREFIX}Table{len(parts)}"


def wrap(term, width=96, indent="  "):
    term = term.replace(" := ", "\u00a0:=\u00a0")
    return "\n".join(textwrap.wrap(term, width, initial_indent=indent,
                                    subsequent_indent=indent + "  ",
                                    break_long_words=False, break_on_hyphens=False)).replace("\u00a0", " ")


def emit_proofs():
    out = ["module", "", f"public import WeightedMIS.{TABLE_LAST}", "",
           HEADER_DOC.format(
               title="The final program",
               text=("The concrete table `program` satisfies the `Matches` predicates of the\n"
                     "top-level procedures and of the hard-component procedures, and the hard\n"
                     "procedure called by the top level is the hard-component entry. Every\n"
                     "equation holds by `rfl`. This file is generated by\n"
                     "`scripts/gen_program_table.py`.")),
           "@[expose] public section", "",
           "namespace WeightedMIS.FinalProgram", "",
           "open WeightedMIS.RegisterMachine", "",
           "theorem topIds_matches : topIds.Matches program :=",
           wrap(top_proof), "",
           "theorem hardIds_matches : hardIds.Matches program :=",
           wrap(hard_proof), "",
           "theorem hard_id_eq : topIds.hard = hardIds.hard := rfl", "",
           "end WeightedMIS.FinalProgram", ""]
    (SRC / f"{PREFIX}.lean").write_text("\n".join(out))


bf = emit_bodies()
emit_ids(bf)
emit_proofs()
print("P =", P, "leaves =", len(LEAVES), "bodies =", len(BODY_DEFS), "files =", bf,
      "unconstrained =", len(unconstrained))
for u in unconstrained:
    print("  unconstrained:", ".".join(u))

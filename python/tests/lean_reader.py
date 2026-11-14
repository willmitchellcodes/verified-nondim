"""A tiny independent reader for the generated Lean certificates.

It re-parses the *text* of a certificate and re-checks every theorem with
SymPy/floating point. It shares no code with lean_export.py, so it catches
printer bugs (wrong matrix, wrong sign, wrong theorem shape) without Lean.
"""
import random
import re

import sympy as sp

DEF = re.compile(r"def (\w+) : Matrix \(Fin (\d+)\) \(Fin (\d+)\) [ℤℚ] :=\s*!!\[(.*?)\]", re.S)
THEOREM = re.compile(r"theorem (\w+)(.*?) := by", re.S)


def matrices(text: str) -> dict[str, sp.Matrix]:
    out = {}
    for name, r, c, body in DEF.findall(text):
        rows = [[int(x) for x in row.split(",")] for row in body.split(";")]
        M = sp.Matrix(rows)
        assert M.shape == (int(r), int(c)), f"{name}: declared {r}x{c}, literal is {M.shape}"
        out[name] = M
    return out


def theorems(text: str) -> dict[str, str]:
    return {name: " ".join(stmt.split()) for name, stmt in THEOREM.findall(text)}


def lean_to_python(expr: str) -> str:
    return expr.replace("^", "**").replace(": ℝ", "")


def check_matrix_claim(stmt: str, M: dict[str, sp.Matrix]) -> bool | None:
    """Evaluate a matrix/rank theorem statement. Returns None if the shape is not recognized."""
    s = stmt.lstrip(": ").strip()
    if m := re.fullmatch(r"(\w+) \* (\w+) = 0", s):
        P = M[m[1]] * M[m[2]]
        return P == sp.zeros(*P.shape)
    if m := re.fullmatch(r"(\w+) \* (\w+) ≠ 0", s):
        P = M[m[1]] * M[m[2]]
        return P != sp.zeros(*P.shape)
    if m := re.fullmatch(r"(\w+) \* (\w+) = 1", s):
        return M[m[1]] * M[m[2]] == sp.eye(M[m[1]].shape[0])
    if m := re.fullmatch(r"(\w+)\.rank = (\d+)", s):
        return M[m[1]].rank() == int(m[2])
    if m := re.fullmatch(r"(\w+)\.rank < (\d+)", s):
        return M[m[1]].rank() < int(m[2])
    if m := re.fullmatch(r"(\d+) ≤ (\w+)\.rank", s):
        return int(m[1]) <= M[m[2]].rank()
    if m := re.fullmatch(r"(\d+) > (\w+)\.rank", s):
        return int(m[1]) > M[m[2]].rank()
    if m := re.fullmatch(r"(\w+) = (\w+)\.submatrix id !\[([\d, ]+)\]", s):
        return M[m[1]] == M[m[2]][:, [int(x) for x in m[3].split(",")]]
    return None


def check_real_identity(stmt: str, trials: int = 5, seed: int = 0) -> bool | None:
    """Evaluate `(vars : ℝ) (hyps) : lhs = rhs` at random positive points."""
    m = re.fullmatch(r"\(([\w ]+) : ℝ\) (?:\(h_\w+ : 0 < \w+\) ?)+: (.*) = (.*)", stmt)
    if not m:
        return None
    names = m[1].split()
    rng = random.Random(seed)
    for _ in range(trials):
        env = {n: rng.uniform(0.5, 3.0) for n in names}
        lhs, rhs = (eval(lean_to_python(e), {"__builtins__": {}}, env) for e in (m[2], m[3]))
        if abs(lhs - rhs) > 1e-9 * max(1.0, abs(lhs)):
            return False
    return True

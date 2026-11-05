#!/usr/bin/env python3
"""Compare run.py result files: a markdown summary table and an SVG "solved vs. time" plot.

Each argument is LABEL=RESULT.json (one run.py result per solver, same instance set):

    .venv/bin/python benchmarks/tools/compare.py popso-sat=benchmarks/results/a.json \
        Kissat=benchmarks/results/b.json --title "medium set (25)" --svg docs/medium.svg

Table columns: solved (SAT / UNSAT), PAR-2 (an unsolved instance counts twice the time
limit) and the shifted geometric mean (shift 10 s, unsolved = time limit). A per-instance table
is printed with --per-instance, solved counts per family (the families where the solvers differ)
with --per-family. The SVG is self-contained (no dependencies) and follows the
viewer's light / dark preference (the style of popso's plots).
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

# Categorical palette (validated light / dark pairs), assigned in argument order.
COLORS = [("#2a78d6", "#3987e5"), ("#eb6834", "#d95926"), ("#1baf7a", "#199e70"), ("#a35bd8", "#b06fe0"),
          ("#c79a12", "#d4a82a"), ("#d6457d", "#e05a8d"), ("#5b6b7a", "#8a9aa9")]


def load(path):
    d = json.loads(Path(path).read_text())
    return d["meta"], d["results"]


def stats(results, tl):
    solved = [r for r in results if r["class"] == "ok" and r["status"] in ("SAT", "UNSAT")]
    times = {r["name"]: r["time"] for r in solved}
    n = len(results)
    par2 = sum(times.get(r["name"], 2 * tl) for r in results) / max(n, 1)
    sgm = math.exp(sum(math.log(min(times.get(r["name"], tl), tl) + 10.0) for r in results) / max(n, 1)) - 10.0
    return {
        "n": n,
        "solved": len(solved),
        "sat": sum(r["status"] == "SAT" for r in solved),
        "unsat": sum(r["status"] == "UNSAT" for r in solved),
        "wrong": sum(r["class"] == "WRONG" for r in results),
        "par2": par2,
        "sgm": sgm,
        "times": times,
    }


def svg(series, n, title, subtitle, tl, tmin=0.01):
    right = 128
    W, H = 602 + right, 400
    left, top, bottom = 56, 58, 46
    pw, ph = W - left - right, H - top - bottom
    lx0, lx1 = math.log10(tmin), math.log10(tl)

    def X(t):
        return left + (math.log10(min(max(t, tmin), tl)) - lx0) / (lx1 - lx0) * pw

    def Y(k):
        return top + ph - k / max(n, 1) * ph

    css = ["svg{--bg:#ffffff;--fg:#1f2328;--muted:#656d76;--grid:#d8dee4}",
           "@media (prefers-color-scheme: dark){svg{--bg:#0d1117;--fg:#e6edf3;--muted:#8d96a0;--grid:#30363d}}"]
    for i, (_, _, (light, dark)) in enumerate(series):
        css.append(f".s{i}{{stroke:{light};fill:none}}.t{i}{{fill:{light}}}")
        css.append(f"@media (prefers-color-scheme: dark){{.s{i}{{stroke:{dark}}}.t{i}{{fill:{dark}}}}}")
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}" '
           f'font-family="-apple-system,Segoe UI,Helvetica,Arial,sans-serif">',
           "<style>" + "".join(css) + "</style>",
           f'<rect width="{W}" height="{H}" fill="var(--bg)"/>',
           f'<text x="{left}" y="24" font-size="15" font-weight="600" fill="var(--fg)">{title}</text>',
           f'<text x="{left}" y="42" font-size="12" fill="var(--muted)">{subtitle}</text>']
    # grid
    t = 10 ** math.ceil(lx0)
    while t <= tl * 1.0001:
        x = X(t)
        out.append(f'<line x1="{x:.1f}" y1="{top}" x2="{x:.1f}" y2="{top + ph}" stroke="var(--grid)" stroke-width="1"/>')
        label = f"{t:g}" if t >= 1 else f"{t:.2g}"
        out.append(f'<text x="{x:.1f}" y="{top + ph + 16}" font-size="11" fill="var(--muted)" text-anchor="middle">{label}</text>')
        t *= 10
    step = max(1, int(math.ceil(n / 5 / 5.0)) * 5) if n > 10 else 1
    for k in range(0, n + 1, step):
        y = Y(k)
        out.append(f'<line x1="{left}" y1="{y:.1f}" x2="{left + pw}" y2="{y:.1f}" stroke="var(--grid)" stroke-width="1"/>')
        out.append(f'<text x="{left - 8}" y="{y + 4:.1f}" font-size="11" fill="var(--muted)" text-anchor="end">{k}</text>')
    out.append(f'<text x="{left + pw / 2}" y="{H - 8}" font-size="12" fill="var(--muted)" text-anchor="middle">'
               f'time limit per instance (s, log scale)</text>')
    out.append(f'<text x="14" y="{top + ph / 2}" font-size="12" fill="var(--muted)" text-anchor="middle" '
               f'transform="rotate(-90 14 {top + ph / 2})">instances solved</text>')
    ends = []
    for i, (label, st, _) in enumerate(series):
        ts = sorted(st["times"].values())
        pts = [(X(tmin), Y(0))]
        for k, tt in enumerate(ts, 1):
            pts.append((X(tt), Y(k - 1)))
            pts.append((X(tt), Y(k)))
        pts.append((X(tl), Y(len(ts))))
        d = " ".join(f"{x:.1f},{y:.1f}" for x, y in pts)
        out.append(f'<polyline class="s{i}" points="{d}" stroke-width="2" stroke-linejoin="round"/>')
        ends.append([Y(len(ts)), label, len(ts), i])
    # end labels, nudged apart
    ends.sort()
    for j in range(1, len(ends)):
        if ends[j][0] - ends[j - 1][0] < 14:
            ends[j][0] = ends[j - 1][0] + 14
    for y, label, k, i in ends:
        out.append(f'<text x="{left + pw + 8}" y="{y + 4:.1f}" font-size="12" font-weight="600" class="t{i}">{label} ({k})</text>')
    out.append("</svg>")
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("runs", nargs="+", help="LABEL=result.json")
    ap.add_argument("--title", default="instances solved vs. time")
    ap.add_argument("--subtitle", default="")
    ap.add_argument("--svg", help="write the plot here")
    ap.add_argument("--per-instance", action="store_true")
    ap.add_argument("--per-family", action="store_true", help="solved per family where the solvers differ")
    args = ap.parse_args()
    series, tl, names, family = [], None, None, {}
    for i, spec in enumerate(args.runs):
        label, path = spec.split("=", 1)
        meta, results = load(path)
        tl = tl or meta["time_limit"]
        if meta["time_limit"] != tl:
            raise SystemExit(f"{path}: time limit {meta['time_limit']} differs from {tl}")
        names = names or [r["name"] for r in results]
        for r in results:
            family.setdefault(r["name"], r.get("family") or "unknown")
        series.append((label, stats(results, tl), COLORS[i % len(COLORS)]))
    n = series[0][1]["n"]
    print(f"| solver | solved (SAT / UNSAT) of {n} | PAR-2 (s) | shifted geomean (s) |")
    print("|---|---|---|---|")
    for label, st, _ in series:
        wrong = f" **WRONG {st['wrong']}**" if st["wrong"] else ""
        print(f"| {label} | {st['solved']} ({st['sat']} / {st['unsat']}){wrong} | {st['par2']:.1f} | {st['sgm']:.2f} |")
    if args.per_instance:
        print()
        print("| instance | " + " | ".join(label for label, _, _ in series) + " |")
        print("|---" * (len(series) + 1) + "|")
        for name in names:
            row = []
            vals = [st["times"].get(name) for _, st, _ in series]
            best = min((v for v in vals if v is not None), default=None)
            for v in vals:
                if v is None:
                    row.append("TL")
                else:
                    s = f"{v:.2f}"
                    row.append(f"**{s}**" if best is not None and v == best else s)
            print(f"| {name} | " + " | ".join(row) + " |")
    if args.per_family:
        fams = {}
        for name in names:
            fams.setdefault(family.get(name, "unknown"), []).append(name)
        print()
        print("| family (instances) | " + " | ".join(label for label, _, _ in series) + " |")
        print("|---" * (len(series) + 1) + "|")
        same = 0
        for fam in sorted(fams):
            counts = [sum(1 for nm in fams[fam] if st["times"].get(nm) is not None) for _, st, _ in series]
            if len(set(counts)) == 1:
                same += 1
                continue
            top = max(counts)
            cells = [f"**{c}**" if c == top else str(c) for c in counts]
            print(f"| {fam} ({len(fams[fam])}) | " + " | ".join(cells) + " |")
        print(f"\n{same} of {len(fams)} families with equal solved counts not shown")
    if args.svg:
        sub = args.subtitle or f"{n} instances, time limit {tl:g} s"
        Path(args.svg).parent.mkdir(parents=True, exist_ok=True)
        Path(args.svg).write_text(svg(series, n, args.title, sub, tl))
        print(f"\nwrote {args.svg}")


if __name__ == "__main__":
    main()

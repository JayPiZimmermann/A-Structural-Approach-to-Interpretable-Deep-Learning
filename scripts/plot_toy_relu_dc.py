#!/usr/bin/env python3
"""Render an exact two-hidden-layer ReLU example and its canonical DC split."""

from fractions import Fraction as Q
from pathlib import Path
import csv
import hashlib
import json
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
FIGURES = ROOT / "tex/figures"
REPORT = ROOT / "reports/toy-relu-dc"
LAYERS = [
    ([[1], [-1]], [0, 0]),
    ([[-1, -1]], [1]),
    ([[1]], [0]),
]


def relu(x):
    return max(Q(0), x)


def evaluate(x):
    """Original and sign-split forward passes, including an affine readout."""
    a, positive, negative = [x], [relu(x)], [relu(-x)]
    for layer, (weights, biases) in enumerate(LAYERS):
        z, zp, zn = [], [], []
        for row, bias in zip(weights, biases):
            z.append(Q(bias) + sum(w * value for w, value in zip(row, a)))
            zp.append(relu(Q(bias)) + sum(
                relu(Q(w)) * p + relu(Q(-w)) * n
                for w, p, n in zip(row, positive, negative)
            ))
            zn.append(relu(Q(-bias)) + sum(
                relu(Q(w)) * n + relu(Q(-w)) * p
                for w, p, n in zip(row, positive, negative)
            ))
        if layer < len(LAYERS) - 1:
            a = [relu(value) for value in z]
            positive = [max(p, n) for p, n in zip(zp, zn)]
        else:
            a, positive = z, zp
        negative = zn
        assert a == [p - n for p, n in zip(positive, negative)]
    return a[0], positive[0], negative[0]


def coordinates(points):
    return " ".join(f"({float(x):g},{float(y):g})" for x, y in points)


def plot_source(body, axis):
    return r"""\documentclass[10pt,border=2pt]{standalone}
\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage{pgfplots}
\pgfplotsset{compat=1.18}
\definecolor{convexblue}{HTML}{0072B2}
\definecolor{concaveorange}{HTML}{D55E00}
\begin{document}
\begin{tikzpicture}
\path[use as bounding box] (-0.9,-0.65) rectangle (7.1,4.6);
\begin{axis}[
  scale only axis,width=6.5cm,height=4.2cm,
  at={(0,0)},anchor=south west,
  xmin=-2.15,xmax=2.15,xtick={-2,-1,0,1,2},
  axis lines=left,axis line style={black!65},
  tick align=outside,tick style={black!55},
  xlabel={$x$},xlabel style={at={(axis description cs:1.03,0)},anchor=west},
  label style={font=\normalsize},tick label style={font=\normalsize},
  clip=false,
""" + axis + "\n]\n" + body + r"""
\end{axis}
\end{tikzpicture}
\end{document}
"""


def compile_plot(stem, work):
    source = FIGURES / f"{stem}.tex"
    with (REPORT / f"{stem}-build.log").open("w") as log:
        subprocess.run([
            "pdflatex", "-halt-on-error", "-interaction=nonstopmode",
            f"-output-directory={work}", str(source),
        ], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
    (FIGURES / f"{stem}.pdf").write_bytes((work / f"{stem}.pdf").read_bytes())
    subprocess.run([
        "pdftoppm", "-singlefile", "-png", "-r", "160",
        str(FIGURES / f"{stem}.pdf"), str(FIGURES / stem),
    ], check=True)


def main():
    REPORT.mkdir(parents=True, exist_ok=True)
    values = []
    for k in range(-300, 301):
        x = Q(k, 100)
        f, g, h = evaluate(x)
        assert f == relu(1 - abs(x))
        assert g == max(1 + abs(x), 2 * abs(x))
        assert h == 2 * abs(x)
        values.append((x, f, g, h))
    with (REPORT / "values.csv").open("w", newline="") as file:
        writer = csv.writer(file)
        writer.writerow(["x", "f", "g", "h"])
        writer.writerows(tuple(str(v) for v in row) for row in values)

    knots = [Q(x) for x in [-2, -1, 0, 1, 2]]
    samples = [evaluate(x) for x in knots]
    slopes = {}
    for index, name in [(1, "g"), (2, "h")]:
        slopes[name] = [
            (b[index] - a[index]) / (y - x)
            for x, y, a, b in zip(knots, knots[1:], samples, samples[1:])
        ]
        assert all(a <= b for a, b in zip(slopes[name], slopes[name][1:]))

    function_body = r"""\addplot[black!60,densely dotted,thin] coordinates {(-2.15,0) (2.15,0)};
\addplot[black,very thick] coordinates {""" + coordinates(zip(knots, [a[0] for a in samples])) + r"""};
\addplot[only marks,mark=*,mark size=2.7pt,convexblue] coordinates {(-1,0) (1,0)};
\addplot[only marks,mark=triangle*,mark options={rotate=180},mark size=3.4pt,concaveorange]
  coordinates {(0,1)};
\node[anchor=south west] at (axis cs:0.25,0.92) {$f$};
"""
    component_body = r"""\addplot[black!60,densely dotted,thin] coordinates {(-2.15,0) (2.15,0)};
\addplot[convexblue,very thick] coordinates {""" + coordinates(zip(knots, [a[1] for a in samples])) + r"""};
\addplot[concaveorange,very thick,dashed] coordinates {""" + coordinates(zip(knots, [-a[2] for a in samples])) + r"""};
\addplot[only marks,mark=*,mark size=2.7pt,convexblue] coordinates {(-1,2) (0,1) (1,2)};
\addplot[only marks,mark=triangle*,mark options={rotate=180},mark size=3.4pt,concaveorange]
  coordinates {(0,0)};
\node[convexblue,anchor=south] at (axis cs:1.1,3.65) {$g$ (convex)};
\node[concaveorange,anchor=north] at (axis cs:0,-2.3) {$-h$ (concave)};
"""
    (FIGURES / "toy_relu_dc_function.tex").write_text(plot_source(
        function_body, "  ymin=-0.2,ymax=1.3,ytick={0,0.5,1},"
    ))
    (FIGURES / "toy_relu_dc_components.tex").write_text(plot_source(
        component_body, "  ymin=-4.6,ymax=4.8,ytick={-4,-2,0,2,4},"
    ))

    preview = r"""\documentclass[10pt,border=6pt]{standalone}
\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage{graphicx}
\usepackage{subcaption}
\begin{document}
\begin{minipage}{16.4cm}
\centering
\captionsetup{type=figure}
\begin{subfigure}[t]{0.48\linewidth}
\centering
\includegraphics[width=\linewidth]{tex/figures/toy_relu_dc_function.pdf}
\caption{Network output $f$.}
\end{subfigure}\hfill
\begin{subfigure}[t]{0.48\linewidth}
\centering
\includegraphics[width=\linewidth]{tex/figures/toy_relu_dc_components.pdf}
\caption{The layerwise DC decomposition.}
\end{subfigure}
\end{minipage}
\end{document}
"""
    (FIGURES / "toy_relu_dc_preview.tex").write_text(preview)
    with tempfile.TemporaryDirectory(prefix="toy-relu-dc-") as directory:
        for stem in ["toy_relu_dc_function", "toy_relu_dc_components", "toy_relu_dc_preview"]:
            compile_plot(stem, Path(directory))

    report = {
        "layers": [{"weights": w, "biases": b} for w, b in LAYERS],
        "hidden_widths": [2, 1],
        "hidden_activation": "ReLU",
        "output_activation": "identity",
        "input_split": "(max(x,0), max(-x,0))",
        "output": "f(x)=max(1-|x|,0)",
        "split_stream_values": {"g": "max(1+|x|,2|x|)", "h": "2|x|"},
        "validation": {
            "rational_inputs_checked": len(values),
            "every_layer_reconstructs_exactly": True,
            "maximum_reconstruction_error": "0 (exact rational arithmetic)",
            "all_samples_match_independent_closed_form": True,
            "piecewise_slopes": {name: [str(x) for x in data] for name, data in slopes.items()},
            "scope": "Numerical checks use exact rational arithmetic; the global closed-form derivation is independently reviewed in math-review.json.",
        },
        "asset_sha256": {
            str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(FIGURES.glob("toy_relu_dc_*.*"))
            if path.suffix in {".tex", ".pdf", ".png"}
        },
    }
    (REPORT / "construction.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report["validation"], indent=2))


if __name__ == "__main__":
    main()

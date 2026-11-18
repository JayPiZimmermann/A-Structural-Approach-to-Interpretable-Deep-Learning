#!/usr/bin/env python3
"""Plot scalar activations and their two-input simple/canonical DC surfaces."""

from pathlib import Path
import hashlib
import json

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.patches import Patch
from matplotlib.projections import register_projection
from matplotlib.ticker import MaxNLocator, StrMethodFormatter
from mpl_toolkits.mplot3d import Axes3D
import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import expit, ndtr


ROOT = Path(__file__).resolve().parents[1]
FIGURES = ROOT / "tex/figures"
REPORTS = ROOT / "reports/activation-grid"
ORDER = ["relu", "gelu", "swish", "sigmoid", "softplus"]
NAMES = ["ReLU", "GELU", "Swish / SiLU", "Sigmoid", "Softplus"]
BLUE = "#0072B2"
ORANGE = "#D55E00"
SWISH_ROOT = brentq(lambda r: r * np.tanh(r / 2) - 2, 2, 3, xtol=1e-14)


class WideAxes3D(Axes3D):
    """Use the whole rectangular panel instead of shrinking it to a square."""

    name = "wide3d"

    def apply_aspect(self, position=None):
        if position is None:
            position = self.get_position(original=True)
        self._set_position(position.frozen(), "active")


register_projection(WideAxes3D)


def phi(z):
    return np.exp(-np.asarray(z) ** 2 / 2) / np.sqrt(2 * np.pi)


def activation(name, z):
    z = np.asarray(z)
    if name == "relu":
        return np.maximum(z, 0)
    if name == "gelu":
        return z * ndtr(z)
    if name == "swish":
        return z * expit(z)
    if name == "sigmoid":
        return expit(z)
    return np.logaddexp(0, z)


def second_derivative(name, z):
    z = np.asarray(z)
    s = expit(z)
    ds = s * (1 - s)
    if name == "gelu":
        return (2 - z * z) * phi(z)
    if name == "swish":
        return ds * (2 + z * (1 - 2 * s))
    if name == "sigmoid":
        return ds * (1 - 2 * s)
    if name == "softplus":
        return ds
    return np.zeros_like(z)


def roots(name):
    if name == "gelu":
        return [-np.sqrt(2), np.sqrt(2)]
    if name == "swish":
        return [-SWISH_ROOT, SWISH_ROOT]
    return [0.0] if name in {"sigmoid", "relu"} else []


def profiles(name, z, canonical=False):
    """Literal Chapter03 profiles, including their original origin values."""
    z = np.asarray(z)
    f = activation(name, z)
    if name == "relu":
        return f, np.zeros_like(z), 1.0
    if name == "softplus":
        return f, np.zeros_like(z), 1.0
    if canonical:
        if name == "sigmoid":
            p = np.where(z <= 0, f, 0.5 + z / 4)
            return p, p - f, 0.25
        if name == "gelu":
            a = np.sqrt(2)
            m = ndtr(a) + a * phi(a) - 1
            c = 2 * phi(a)
        else:
            a = SWISH_ROOT
            m = (a - 2) / 4
            c = (a * a - 4) / 4
        bound = 1 + 2 * m
        p = np.where(z <= -a, -c, np.where(z >= a, bound * z - c, f + m * z))
        return p, p - f, float(bound)
    if name == "gelu":
        return 2 * f + 2 * phi(z), f + 2 * phi(z), 2.0
    if name == "swish":
        p = 2 * np.logaddexp(0, z)
        return p, p - f, 2.0
    softplus = np.logaddexp(0, z)
    return (softplus + f) / 2, (softplus - f) / 2, 0.5


def surfaces(name, x, y, canonical=False):
    if name == "relu":
        return np.maximum(x, y), np.asarray(y)
    p, q, bound = profiles(name, x - y, canonical)
    return p + bound * y, q + bound * y


def integrate_split(fun, lo, hi, breaks):
    if lo == hi:
        return 0.0
    if hi < lo:
        return -integrate_split(fun, hi, lo, breaks)
    points = [lo, *[v for v in breaks if lo < v < hi], hi]
    return sum(quad(fun, a, b, epsabs=2e-12, epsrel=2e-12, limit=150)[0]
               for a, b in zip(points, points[1:]))


def validate():
    grid = np.linspace(0, 4, 81)
    x, y = np.meshgrid(grid, grid)
    data = {}
    for name in ORDER:
        record = {}
        for canonical, label in [(False, "simple"), (True, "canonical")]:
            plus, minus = surfaces(name, x, y, canonical)
            p0, q0, bound = profiles(name, 0.0, canonical)
            error = float(np.max(np.abs(plus - minus - activation(name, x - y))))
            minimum = float(min(plus.min(), minus.min()))
            assert error < 1e-12 and minimum > -1e-12
            record[label] = {"L": bound, "p_at_zero": float(p0), "q_at_zero": float(q0),
                             "max_reconstruction_error": error, "min_surface_value": minimum}
        ps, ms = surfaces(name, x, y)
        pc, mc = surfaces(name, x, y, True)
        record["max_simple_canonical_separation"] = float(max(np.max(np.abs(ps - pc)), np.max(np.abs(ms - mc))))
        if name in {"relu", "softplus"}:
            assert np.array_equal(ps, pc) and np.array_equal(ms, mc)
        if name == "relu":
            assert np.array_equal(pc, np.maximum(x, y)) and np.array_equal(mc, y)
            record["curvature_validation"] = "Exact atomic-curvature case: p=ReLU, q=0, L=1; F+=(max(x,y)), F-=y."
        else:
            breaks = roots(name)
            positive = lambda t: max(float(second_derivative(name, t)), 0.0)
            negative = lambda t: max(-float(second_derivative(name, t)), 0.0)
            p_slope0 = integrate_split(positive, -np.inf, 0, breaks)
            q_slope0 = integrate_split(negative, -np.inf, 0, breaks)
            sample_z = np.linspace(-4, 4, 33)
            p_exact, q_exact, bound = profiles(name, sample_z, True)
            p_integral = np.array([float(activation(name, 0)) + p_slope0 * z
                                  + integrate_split(lambda t: (z - t) * positive(t), 0, z, breaks)
                                  for z in sample_z])
            q_integral = np.array([q_slope0 * z
                                  + integrate_split(lambda t: (z - t) * negative(t), 0, z, breaks)
                                  for z in sample_z])
            integral_error = float(max(np.max(np.abs(p_exact - p_integral)), np.max(np.abs(q_exact - q_integral))))
            assert integral_error < 1e-9
            z = np.linspace(-4, 4, 161)
            for root in breaks:
                z = z[np.abs(z - root) > 0.02]
            h = 1e-3
            p, q, _ = profiles(name, z, True)
            pa, qa, _ = profiles(name, z + h, True)
            pb, qb, _ = profiles(name, z - h, True)
            dp, dq = (pa - pb) / (2 * h), (qa - qb) / (2 * h)
            d2p, d2q = (pa - 2 * p + pb) / h ** 2, (qa - 2 * q + qb) / h ** 2
            curvature_error = float(max(np.max(np.abs(d2p - np.maximum(second_derivative(name, z), 0))),
                                        np.max(np.abs(d2q - np.maximum(-second_derivative(name, z), 0)))))
            assert min(dp.min(), dq.min()) >= -1e-8
            assert max(dp.max(), dq.max()) <= bound + 1e-8
            assert curvature_error < 2e-6
            record["curvature_validation"] = {
                "method": "Independent integration of positive/negative actual f'' from minus infinity; origin values f(0),0. No canonical profile formula used by quadrature.",
                "integral_samples": len(sample_z), "max_profile_integral_error": integral_error,
                "finite_difference_step": h, "max_second_derivative_error": curvature_error,
                "finite_difference_slope_range": [float(min(dp.min(), dq.min())), float(max(dp.max(), dq.max()))],
            }
        data[name] = record
    return data


def render():
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 9,
                         "axes.labelsize": 9, "xtick.labelsize": 8.5, "ytick.labelsize": 8.5,
                         "pdf.fonttype": 42, "ps.fonttype": 42, "axes.linewidth": 0.65,
                         "savefig.facecolor": "white"})
    fig = plt.figure(figsize=(17 / 2.54, 20 / 2.54))
    for xpos, title in [(0.137, "Scalar activation"), (0.440, r"Positive $F_+(x,y)$"),
                        (0.810, r"Negative $F_-(x,y)$")]:
        fig.text(xpos, 0.985, title, ha="center", va="top", fontsize=9.5, weight="semibold")
    fig.legend(handles=[Patch(facecolor=BLUE, alpha=0.44, label="Simple (surface)"),
                        Line2D([0], [0], color=ORANGE, lw=1, label="Minimum curvature (mesh)")],
               loc="upper center", bbox_to_anchor=(0.61, 0.955), ncol=2,
               frameon=False, handlelength=1.6, columnspacing=1.2, fontsize=9)
    axis = np.linspace(0, 4, 49)
    x, y = np.meshgrid(axis, axis)
    z = np.linspace(-4, 4, 801)
    height, top, rowstep = 0.151, 0.913, 0.178
    for row, (name, title) in enumerate(zip(ORDER, NAMES)):
        bottom = top - (row + 1) * rowstep
        ax = fig.add_axes([0.055, bottom + 0.030, 0.165, height - 0.035])
        ax.plot(z, activation(name, z), color="#202020", lw=1.35)
        ax.axhline(0, color="0.78", lw=0.5, zorder=0)
        ax.axvline(0, color="0.88", lw=0.5, zorder=0)
        ax.set_xlim(-4, 4)
        ax.set_xticks([-4, 0, 4])
        ax.yaxis.set_major_locator(MaxNLocator(nbins=3, min_n_ticks=2))
        ax.set_title(title, loc="left", pad=3, fontsize=9.5, weight="semibold")
        ax.spines[["top", "right"]].set_visible(False)
        ax.tick_params(length=2.5, pad=1.5)
        simple = surfaces(name, x, y)
        canonical = surfaces(name, x, y, True)
        maximum = max(float(a.max()) for a in (*simple, *canonical))
        zmax = maximum * 1.03
        zticks = [0, round(maximum / 2, 1), round(maximum, 1)]
        for column in [0, 1]:
            surf = fig.add_axes([0.260 + column * 0.370, bottom, 0.360, height + 0.006], projection="wide3d")
            surf.plot_surface(x, y, simple[column], rcount=25, ccount=25,
                              color=BLUE, alpha=0.44, linewidth=0, antialiased=True,
                              shade=True, rasterized=False)
            surf.plot_wireframe(x, y, canonical[column], rstride=6, cstride=6,
                                color=ORANGE, linewidth=0.5, alpha=0.95)
            surf.view_init(elev=25, azim=-135)
            surf.set_box_aspect((1, 1, 1.05), zoom=0.95)
            surf.set_xlim(0, 4)
            surf.set_ylim(0, 4)
            surf.set_zlim(0, zmax)
            surf.set_xticks([0, 4])
            surf.set_yticks([0, 4])
            surf.set_zticks(zticks)
            surf.zaxis.set_major_formatter(StrMethodFormatter("{x:g}"))
            surf.set_xlabel("$x$", labelpad=-5)
            surf.set_ylabel("$y$", labelpad=-5)
            surf.tick_params(axis="both", which="major", pad=-2, labelsize=8.5)
            for axis3d in [surf.xaxis, surf.yaxis, surf.zaxis]:
                axis3d.pane.set_facecolor((0.97, 0.97, 0.97, 0.3))
                axis3d._axinfo["grid"].update(color=(0.78, 0.78, 0.78, 0.5), linewidth=0.4)
    FIGURES.mkdir(parents=True, exist_ok=True)
    fig.savefig(FIGURES / "activation_dc_grid.pdf")
    fig.savefig(FIGURES / "activation_dc_grid.png", dpi=240)
    plt.close(fig)


def main():
    REPORTS.mkdir(parents=True, exist_ok=True)
    checks = validate()
    render()
    paths = ["scripts/plot_activation_dc_grid.py", "tex/figures/activation_dc_grid.pdf", "tex/figures/activation_dc_grid.png"]
    report = {"status": "PASS", "domain": {"x": [0, 4], "y": [0, 4], "scalar_z": [-4, 4]},
              "parameters": {"beta": 1, "theta": 1, "Swish_root": SWISH_ROOT},
              "surface_validation_grid": [81, 81], "rows": checks,
              "figure": {"size_cm": [17, 20], "pdf": "Vector surfaces and mesh; embedded TrueType fonts, no rasterized artists.",
                         "simple": "Translucent blue surface", "canonical": "Orange mesh",
                         "vertical_scale": "Linear; shared between F+ and F- in each row, from zero to 1.03 times the largest plotted value across both formulations.",
                         "layout": "Narrow scalar column; rectangular 3D viewports use the full allocated column width; no F, f, z axis labels or coincidence annotations.",
                         "normalization": "Literal thesis profiles and their own L; no common-offset alignment or scalar-profile clipping."},
              "source_sha256": {path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in paths}}
    (REPORTS / "validation.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "max_reconstruction_error": max(v[k]["max_reconstruction_error"] for v in checks.values() for k in ["simple", "canonical"]),
                      "max_profile_integral_error": max(v["curvature_validation"]["max_profile_integral_error"] for k, v in checks.items() if k != "relu")}, indent=2))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Generate figures for the Waring formalization paper."""
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
matplotlib.rcParams["font.sans-serif"] = ["Microsoft YaHei", "SimHei", "DejaVu Sans"]
matplotlib.rcParams["axes.unicode_minus"] = False
import matplotlib.patches as mpatches
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch
import numpy as np

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "fig-zh")
os.makedirs(OUT, exist_ok=True)

MOD = {
    "WaringStatement": (44, []),
    "WaringCircle": (194, []),
    "WaringFiniteDifference": (70, []),
    "WaringHilbertIdentity": (80, ["WaringFiniteDifference"]),
    "WaringSigned": (292, ["WaringFiniteDifference"]),
    "WaringWeylDiff": (164, ["WaringFiniteDifference"]),
    "WaringBound": (262, ["WaringStatement"]),
    "WaringCount": (732, ["WaringCircle"]),
    "WaringDensity": (198, ["WaringBound"]),
    "WaringEventually": (134, ["WaringBound"]),
    "WaringExpSum": (123, ["WaringCircle", "WaringWeylDiff"]),
    "WaringCoeffBound": (87, ["WaringWeylDiff"]),
    "WaringLemma3": (785, ["WaringCount"]),
    "WaringLemma6": (348, ["WaringCount"]),
    "WaringSchnirelmann": (435, ["WaringDensity"]),
    "WaringWeylInq": (363, ["WaringExpSum"]),
    "WaringSymm": (169, ["WaringLemma6", "WaringLemma3"]),
    "WaringTheorem1": (146, ["WaringLemma6", "WaringLemma3", "WaringSymm"]),
    "WaringBPow": (184, ["WaringWeylInq"]),
    "WaringHolder": (203, ["WaringWeylInq"]),
    "WaringLemma7": (607, ["WaringTheorem1"]),
    "WaringQuadratic": (1084, ["WaringExpSum", "WaringCount", "WaringLemma3",
                              "WaringSymm", "WaringTheorem1"]),
    "WaringQuadSum": (239, ["WaringBPow"]),
    "WaringIndStep": (585, ["WaringQuadSum", "WaringLemma7", "WaringHolder",
                            "WaringCoeffBound"]),
    "WaringLemma8Form": (327, ["WaringQuadratic"]),
    "WaringLinnik": (100, ["WaringSchnirelmann"]),
    "WaringInduction": (240, ["WaringQuadratic", "WaringLemma8Form",
                              "WaringWeylDiff", "WaringHolder"]),
    "WaringIndStep2": (1776, ["WaringIndStep", "WaringLemma7", "WaringHolder",
                              "WaringQuadSum", "WaringCoeffBound",
                              "WaringQuadratic", "WaringLemma8Form"]),
    "WaringTheorem2": (489, ["WaringIndStep2", "WaringLinnik"]),
}

_memo = {}
def level_of(name):
    if name in _memo:
        return _memo[name]
    deps = MOD[name][1]
    lv = 0 if not deps else 1 + max(level_of(d) for d in deps)
    _memo[name] = lv
    return lv

LEVELS = {}
for m in MOD:
    LEVELS.setdefault(level_of(m), []).append(m)

# ---------------- Fig 1: dependency DAG ----------------
fig, ax = plt.subplots(figsize=(20.5, 8.0))
ax.set_axis_off()

nlev = max(LEVELS) + 1
DX = 2.42
xpos = {lv: DX * lv for lv in range(nlev)}
DY = 0.92
ypos = {}
for lv, names in LEVELS.items():
    names.sort()
    k = len(names)
    for i, nm in enumerate(names):
        ypos[nm] = (k - 1) * DY / 2.0 - i * DY

BOX_W, BOX_H = 1.72, 0.38

def role(name):
    if name in ("WaringStatement", "WaringCircle", "WaringFiniteDifference"):
        return "#f3f4f6", "#6b7280"
    if name == "WaringTheorem2":
        return "#fee2e2", "#b91c1c"
    if name in ("WaringIndStep", "WaringIndStep2", "WaringInduction"):
        return "#fef3c7", "#b45309"
    if name in ("WaringTheorem1", "WaringLemma7", "WaringLemma8Form",
                "WaringSchnirelmann", "WaringLinnik", "WaringDensity",
                "WaringBound", "WaringEventually", "WaringSigned",
                "WaringHilbertIdentity"):
        return "#dcfce7", "#15803d"
    return "#eef2ff", "#4f46e5"

for nm in MOD:
    lv = level_of(nm)
    x, y = xpos[lv], ypos[nm]
    fc, ec = role(nm)
    lw = 2.0 if nm == "WaringTheorem2" else 1.0
    ax.add_patch(FancyBboxPatch((x - BOX_W / 2, y - BOX_H / 2), BOX_W, BOX_H,
                                boxstyle="round,pad=0.035", facecolor=fc,
                                edgecolor=ec, lw=lw, zorder=3))
    ax.text(x, y + 0.068, nm.replace("Waring", ""), ha="center", va="center",
            fontsize=8.0, zorder=4, color="#111827")
    ax.text(x, y - 0.10, f"{MOD[nm][0]} 行", ha="center", va="center",
            fontsize=6.4, zorder=4, color="#6b7280")

for nm, (_, deps) in MOD.items():
    for d in deps:
        ax.add_patch(FancyArrowPatch(
            (xpos[level_of(d)] + BOX_W / 2, ypos[d]),
            (xpos[level_of(nm)] - BOX_W / 2, ypos[nm]),
            arrowstyle="-|>", mutation_scale=7, lw=0.5, color="#9ca3af",
            alpha=0.8, zorder=2, shrinkA=1, shrinkB=2))

for lv in range(nlev):
    ax.text(xpos[lv], min(ypos[n] for n in LEVELS[lv]) - 0.62, f"第 {lv} 层",
            ha="center", fontsize=7.0, color="#9ca3af")

ax.set_xlim(-1.35, DX * (nlev - 1) + 1.35)
ax.set_ylim(min(ypos.values()) - 1.0, max(ypos.values()) + 0.55)

patches = [mpatches.Patch(facecolor="#f3f4f6", edgecolor="#6b7280", label="基础"),
           mpatches.Patch(facecolor="#eef2ff", edgecolor="#4f46e5", label="解析 / 组合"),
           mpatches.Patch(facecolor="#fef3c7", edgecolor="#b45309", label="定理 1 机制"),
           mpatches.Patch(facecolor="#dcfce7", edgecolor="#15803d", label="密度 / 接口"),
           mpatches.Patch(facecolor="#fee2e2", edgecolor="#b91c1c", label="最终定理")]
ax.legend(handles=patches, loc="lower right", fontsize=7.2, frameon=False)
ax.set_title("模块依赖图（29 个模块，10 460 行 Lean）",
             fontsize=11.5, pad=8)
plt.tight_layout()
plt.savefig(os.path.join(OUT, "fig1_dag.png"), dpi=190, bbox_inches="tight")
plt.close(fig)

# ---------------- Fig 2: proof chain ----------------
fig, ax = plt.subplots(figsize=(11.6, 6.4))
ax.set_axis_off()
ax.set_xlim(0, 12)
ax.set_ylim(0, 7)

def chain_box(x, y, w, h, title, sub, fc, ec):
    ax.add_patch(FancyBboxPatch((x - w / 2, y - h / 2), w, h,
                                boxstyle="round,pad=0.09", facecolor=fc,
                                edgecolor=ec, lw=1.5, zorder=3))
    ax.text(x, y + 0.32, title, ha="center", va="center", fontsize=9.6,
            fontweight="bold", zorder=4)
    ax.text(x, y - 0.30, sub, ha="center", va="center", fontsize=7.6,
            color="#374151", zorder=4)

chain_box(2.5, 5.6, 4.4, 1.15, "引理 2 / 3 / 6 / 7",
          "q(n) ≤ 2M·max(|a₁|,|a₂|) + 1\nσ₋₁(n) = Σ_{g|n} 1,   Σσ₋₁² ≤ 6x",
          "#eef2ff", "#4f46e5")
chain_box(2.5, 3.55, 4.4, 1.25, "定理 1（均值估计）",
          "∫₀¹ |Σ_{n≤N} e(αf(n))|^{8^{k−1}} dα\n≪ N^{8^{k−1}−k}",
          "#fef3c7", "#b45309")
chain_box(2.5, 1.5, 4.4, 1.25, "定理 2（密度桥）",
          "r(n) = ∫₀¹ S(α)^s e(−nα) dα\nr(n) ≪ n^{s/k−1},   A(N) ≫ N",
          "#dcfce7", "#15803d")
chain_box(8.6, 3.55, 4.6, 1.5, "华林定理",
          "∀ k ≥ 1  ∃ g  ∀ n\nn = Σ_{i≤s} x_i^k,   s ≤ g", "#fee2e2", "#b91c1c")

for (x1, y1), (x2, y2) in [((2.5, 5.02), (2.5, 4.20)),
                           ((2.5, 2.92), (2.5, 2.15)),
                           ((4.72, 3.55), (6.28, 3.55)),
                           ((4.72, 1.5), (6.28, 3.35))]:
    ax.add_patch(FancyArrowPatch((x1, y1), (x2, y2), arrowstyle="-|>",
                                 mutation_scale=13, lw=1.5, color="#374151",
                                 zorder=2))

ax.text(5.5, 3.92, "Schnirelmann", fontsize=7.8, color="#374151", ha="center")
ax.text(5.5, 3.62, "d(A+B) ≥ α + β − αβ", fontsize=7.4,
        color="#374151", ha="center")
ax.text(6.95, 2.55, "density > 0", fontsize=7.8, color="#15803d", ha="center")
ax.set_ylim(0.55, 6.55)
ax.set_title("三步证明架构", fontsize=11.5, pad=6)
plt.tight_layout()
plt.savefig(os.path.join(OUT, "fig2_chain.png"), dpi=200, bbox_inches="tight")
plt.close(fig)

# ---------------- Fig 3: r_3(n) ----------------
NMAX = 2000
M = 26
cube = [m ** 3 for m in range(M + 1)]
r3 = np.zeros(NMAX + 1, dtype=int)
for a in cube:
    for b in cube:
        for c in cube:
            s = a + b + c
            if s <= NMAX:
                r3[s] += 1

fig, axes = plt.subplots(1, 2, figsize=(11.6, 4.2))
ax = axes[0]
nz = np.nonzero(r3)[0]
ax.scatter(nz, r3[nz], s=3.5, color="#15803d", alpha=0.75)
ax.set_xlabel("n", fontsize=9)
ax.set_ylabel("r₃(n) = #{(a,b,c) : a³+b³+c³ = n}", fontsize=8.4)
ax.set_title("三个立方数表示的分布（n ≤ 2000）", fontsize=10)
ax.grid(alpha=0.25, lw=0.5)

ax = axes[1]
cnt = np.cumsum(r3 > 0)
ax.plot(np.arange(NMAX + 1), cnt, color="#b91c1c", lw=1.4)
ax.plot([0, NMAX], [0, NMAX], "--", color="#6b7280", lw=0.9, label="slope 1")
ax.set_xlabel("N", fontsize=9)
ax.set_ylabel("#{n ≤ N : r₃(n) > 0}", fontsize=8.6)
ax.set_title("计数集，密度 ≈ %.3f" % (cnt[-1] / NMAX), fontsize=10)
ax.legend(fontsize=8)
ax.grid(alpha=0.25, lw=0.5)
plt.tight_layout()
plt.savefig(os.path.join(OUT, "fig3_r3.png"), dpi=200, bbox_inches="tight")
plt.close(fig)

# ---------------- Fig 4: line counts ----------------
fig, ax = plt.subplots(figsize=(7.6, 6.2))
names = sorted(MOD, key=lambda m: MOD[m][0])
vals = [MOD[m][0] for m in names]
colors = ["#b91c1c" if n == "WaringTheorem2" else "#4f46e5" for n in names]
ax.barh([n.replace("Waring", "") for n in names], vals, color=colors, height=0.72)
for i, v in enumerate(vals):
    ax.text(v + 10, i, str(v), va="center", fontsize=6.6, color="#374151")
ax.set_xlabel("Lean 行数", fontsize=9)
ax.set_title("各模块代码量（合计 %s 行）" % f"{sum(vals):,}", fontsize=10.5)
ax.tick_params(axis="y", labelsize=7.2)
ax.grid(axis="x", alpha=0.25, lw=0.5)
plt.tight_layout()
plt.savefig(os.path.join(OUT, "fig4_lines.png"), dpi=200, bbox_inches="tight")
plt.close(fig)

print("figures written to", OUT)
for f in sorted(os.listdir(OUT)):
    print(" ", f, os.path.getsize(os.path.join(OUT, f)), "bytes")

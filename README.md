# Smallram — Lean 4 formalization of arXiv:2609.38032

Lean 4 + mathlib formalization of **Holomorphic curves of finite lower order with few inflection points**,
by **Alexandre Eremenko and Teng Zhang**.

**Paper:** [arXiv:2609.38032](https://arxiv.org/abs/2609.38032) ·
[version 1](https://arxiv.org/abs/2609.38032v1) ·
[DOI](https://doi.org/10.48550/arXiv.2609.38032).

本仓库是上述论文的 Lean 4 形式化。对应用户提交原稿的 **35 个带标签结果**均有经过
Lean 内核检查的定理声明，包括完整标量定理 A、主定理及两个尖锐性命题。
论文与证明的逐项对应见 [PAPER_RESULTS.md](PAPER_RESULTS.md)。

## Build and verify / 构建与核验

Prerequisites: Git, Lean's `elan` toolchain manager, PowerShell 7 (`pwsh`), and ripgrep (`rg`).
The Lean version is selected by `lean-toolchain`; dependency commits are pinned by `lake-manifest.json`.

```sh
git clone https://github.com/zhangteng2000/Smallram.git
cd Smallram
lake exe cache get
lake build
pwsh -NoProfile -File scripts/verify.ps1
```

On Windows, the final command may also be run as `.\scripts\verify.ps1` from PowerShell.
A fresh clone obtains its own dependencies; the original computer's shared Lake cache is not required.

The verification script checks the build, forbidden proof placeholders in both project libraries,
the transitive logical dependencies of every imported project declaration (including private declarations),
the submitted manuscript's hash, and all 35 labelled results. The final gate also applies the principal
theorems to their exact registered targets and runs `#print axioms` for every labelled result.

**No user-declared mathematical axioms or proof placeholders are used.**
The only permitted foundational dependencies are `Classical.choice`, `propext`, and `Quot.sound`.

## Proof entry points / 主要证明入口

| Manuscript result | Lean declaration | Source |
| --- | --- | --- |
| Main theorem | `ModifiedCartan.Paper.thm_main` | [MainTheorem.lean](ModifiedCartan/MainTheorem.lean) |
| Full scalar theorem A | `ModifiedCartan.Paper.thm_A` | [ScalarTheoremA.lean](ModifiedCartan/ScalarTheoremA.lean) |
| Deficiency sum two | `ModifiedCartan.Paper.thm_A_deficiency_sum` | [ScalarTheoremA.lean](ModifiedCartan/ScalarTheoremA.lean) |
| Sharpness of admissible orders | `ModifiedCartan.Paper.prop_sharpness_orders` | [SharpnessOrders.lean](ModifiedCartan/SharpnessOrders.lean) |
| Sharpness at order zero | `ModifiedCartan.Paper.prop_sharpness_zero` | [SharpnessZero.lean](ModifiedCartan/SharpnessZero.lean) |

- [SubmittedCompletion.lean](verification/SubmittedCompletion.lean): completion checks for all 35 labelled results.
- [AllDeclarations.lean](verification/AllDeclarations.lean): recursive dependency audit of both project libraries.
- [FORMALIZATION_MAP.md](FORMALIZATION_MAP.md): dependency DAG, API support, manuscript correspondence, and alternative proofs.
- [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md): final status and historical milestones.
- [PAPER_RESULTS.md](PAPER_RESULTS.md): original statements and stable Lean names.
- [Frozen final verification log](verification/logs/submitted-paper-complete-latest-run.log).

## Verification record / 核验记录

The final mathematical build completed **5332 jobs**. The recursive audit covered **9026 declarations**,
including **7863 theorem declarations**; all **35 labelled results** passed the completion gate.
These counts describe audited coverage, not an estimate of completion percentage.
Frozen milestone logs are retained in [verification/logs](verification/logs).

Lean: `v4.34.0-rc1`.
mathlib: `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11`.

The fixed specification is [paper/submitted.tex](paper/submitted.tex), with SHA256:

```text
D3F63ADE442557F0474EB117EDD0BA99405A09AB412E6D40FAE271C56F7C44CA
```

The theorem-by-theorem correspondence is to this preserved submitted manuscript.
`paper/original.tex`, `paper/INHERITED_STATUS.md`, `STATUS.md`, and `verification/Completion.lean`
are historical materials from the earlier project. The current completion gate is
`verification/SubmittedCompletion.lean`.

Both `FewInflection/` and `ModifiedCartan/` contain the reusable and manuscript-specific source proofs.
Generated caches and local scratch experiments are excluded from Git. Development rules are in [AGENTS.md](AGENTS.md).

## Paper citation

```bibtex
@article{EremenkoZhang2026FewInflection,
  author        = {Alexandre Eremenko and Teng Zhang},
  title         = {Holomorphic curves of finite lower order with few inflection points},
  year          = {2026},
  eprint        = {2609.38032},
  archivePrefix = {arXiv},
  primaryClass  = {math.CV},
  doi           = {10.48550/arXiv.2609.38032},
  url           = {https://arxiv.org/abs/2609.38032}
}
```

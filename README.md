# Lean certificate: Riemann's ξ has no zero in `0 ≤ Re s ≤ 1, |Im s| ≤ 14.1`

This is a [Palomar](https://palomar-registry.org/) submission package for the
rectangle certificate from
[`sciencenerd-des/reinmann`](https://github.com/sciencenerd-des/reinmann)
(commit `a8455dcf978424a7487048f114df3c66552d6f6a`). Submissions are made at
<https://submit.palomar-registry.org/>.

Two theorems are compared. Both use only Mathlib definitions.

```lean
theorem ReinmannPalomar.xi_ne_zero_low_rectangle (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1)
    (hT : |s.im| ≤ 141 / 10) :
    (1 / 2 : ℂ) + s * (s - 1) / 2 * completedRiemannZeta₀ s ≠ 0

theorem ReinmannPalomar.riemannZeta_ne_zero_low_strip (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (hT : |s.im| ≤ 141 / 10) :
    riemannZeta s ≠ 0
```

`1/2 + s(s-1)/2 · Λ₀(s)` is Riemann's entire ξ. The height 14.1 is below the
first zero ordinate, 14.1347…. This is a kernel-checked certificate of a
classical fact. It is not new information about zeta zeros, and it is not
related to a proof of RH.

## Files

| Path | What it is |
| --- | --- |
| `Challenge.lean` | The trusted statement surface. It imports only `Mathlib.NumberTheory.LSeries.RiemannZeta` and has the two statements with `sorry`. |
| `Solution.lean` | The same two statements, proved from `Reinmann.XiRectangle.rectangle_nonzero` and `Reinmann.XiAnnihilator.xi_zero_of_strip_zero`. |
| `Reinmann/`, `XiRectangle/` | The vendored import closure of `XiRectangle.Final` from the source commit (365 files), ported to Lean modules and v4.35.0-rc2. See `PORTING.md`. |
| `comparator.json` | The Comparator config. It names the challenge/solution modules, the two theorems, and the permitted axioms `propext`, `Quot.sound`, `Classical.choice`. |
| `formalization.yaml` | Palomar metadata (schema v0.4): description, limitations, provenance, AI-use disclosure, sources and classification. |
| `lean-toolchain` | `leanprover/lean4:v4.35.0-rc2` (the Palomar minimum, which bundles `lake comparator`). |
| `lakefile.toml`, `lake-manifest.json` | The Lake package. It pins Mathlib `v4.35.0-rc2` (commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`). |
| `LICENSE` | Apache License 2.0, matching `project.license` and the source headers. |
| `PORTING.md` | Every change made to the vendored sources. |
| `scripts/check-lean-sources.py` | Palomar's non-executing source check: module headers and the 10k-line cap. |
| `scripts/verify-comparator.sh` | Runs the toolchain's `lake comparator` the same way Palomar does (Lean kernel plus bundled NanoDa and con-ron). |
| `scripts/validate-formalization.rb` | The template's metadata validator. |
| `scripts/port/` | The scripts used for the mechanical part of the port. |

## Build and check

```bash
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
python3 scripts/check-lean-sources.py
lake exe cache get              # Mathlib oleans
lake build Challenge Solution   # about 1.5–2 h on 8 cores from a cold cache; peak RAM about 16 GB
scripts/verify-comparator.sh    # needs bubblewrap (bwrap)
```

The 44 numerical tiles (`XiRectangle/Tile*.lean`, 308 files) take most of
the build time. Each tile needs about 19 CPU-minutes.

## Remaining manual steps for Biswajit

Nothing below has been done. Each step has to be done by you, from your own
account.

1. **Fill in the TODO in `formalization.yaml`.** Under the first
   `automation.methods` entry, add the `models:` and `framework:` you actually
   used for the original development. Then check the AI-use wording and the
   whole description.
2. **Fix the licence mismatch upstream.** The source headers say Apache-2.0,
   but the reinmann `CITATION.cff` and the Zenodo record say CC-BY-4.0, and the
   repository has no `LICENSE` file. This package declares Apache-2.0. Add an
   Apache-2.0 `LICENSE` to `sciencenerd-des/reinmann`, or otherwise make the
   licences consistent, so the provenance review does not flag it.
3. **Create a new public GitHub repository** (for example
   `sciencenerd-des/reinmann-palomar-rectangle`). Push the contents of this
   folder to it, without `.lake/` (`.gitignore` already excludes it):
   ```bash
   git init && git add . && git commit -m "Palomar submission: xi rectangle certificate"
   git branch -M main && git remote add origin git@github.com:<you>/<repo>.git && git push -u origin main
   git rev-parse HEAD   # the full 40-character SHA to submit
   ```
4. *(Recommended)* **Run Palomar's mechanical preflight** on that commit. Use
   the reusable workflow `PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml`
   with `mode: full` and `execution_profile: palomar-standard-v1`, pinned to a
   commit that is the same as its `pipeline_commit` input. A local build is not
   equivalent to it.
5. **Submit at <https://submit.palomar-registry.org/>.** Give `owner/name`,
   the full commit SHA, and the Comparator path `comparator.json`. For
   authorisation, answer that you are the responsible author/maintainer.
   Prove push access with the GitHub browser sign-in. Keep the status link the
   site gives you.
6. **Read the automated review.** The outcome is `neutral`,
   `revision_required` or `rejected`, and there is no appeal. Only if it is
   `neutral` and you are happy with it, choose to register. **Registration is
   permanent public history.** It publishes the source, a redacted review, and
   archive forks with preservation tags. The mechanical check is public as
   soon as you submit.
7. After registering, send the planned note to Loeffler with the
   Palomar record link.

## Risks

- **Research-interest review.** Palomar indexes only results that "could
  plausibly warrant a research paper or serious research note" with an
  identifiable research audience, and a clear failure means `rejected`. This
  rectangle is classical and lies far below Platt–Trudgian's 3·10¹² height. Its
  case rests on being a kernel-checked validated-numerics certificate built on
  Mathlib's own `Γ` and completed zeta. That may not pass.
- **Riemann-hypothesis framing.** The source repository and its citation title
  ("…Conditional Routes to the Riemann Hypothesis") are RH-framed. This
  package deliberately avoids that, but the reviewer will see the provenance
  links.
- **The finite-order PF97 statement is not included.** Its closure has about
  920 files and 1.15M lines, and it also depends on the Hadamard bridge. It
  could be a separate future submission.
- **The vendored port differs from the published commit.** All differences
  are listed in `PORTING.md`. No statements were changed.

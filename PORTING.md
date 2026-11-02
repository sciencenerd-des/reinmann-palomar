# Port of the reinmann rectangle certificate to Lean v4.35.0-rc2 modules

Source: `sciencenerd-des/reinmann` at commit
`a8455dcf978424a7487048f114df3c66552d6f6a` (Lean v4.30.0, Mathlib commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`).

Only the import closure of `XiRectangle.Final` (365 files: 54 under
`Reinmann/`, 311 under `XiRectangle/`) is vendored. Palomar needs
Lean v4.35.0-rc2 or later, every `.lean` file must use the `module` header,
and no file may be longer than 10,000 lines. The original repository does not
meet these rules (it has non-module files and a 16k-line file outside this
closure), so it cannot be used as a pinned dependency.

No theorem statement was changed. All edits are proof-script or visibility
changes.

## Mechanical rewrites (scripted, applied to every vendored file)

1. Module header: `module` goes after the leading comment block,
   `import X` becomes `public import X`, and `@[expose] public section`
   goes after the imports (`port_to_module.py`).
2. `simpa ... using e` becomes `simpa ... using! e`. In v4.35, `simpa using`
   closes its goal at reducible transparency, and `using!` brings back the old
   default-transparency check (`fix_simpa_using.py`, 747 sites).
3. `convert h using 1` followed by `funext k; fin_cases k <;> rfl` (2,640
   sites in the tile files) becomes
   `convert h using 1` + `all_goals first | (funext k; fin_cases k <;> rfl) | rfl`.
   v4.35 `convert` no longer closes the `F = fun z => ...` side goal by `rfl`.
4. In six `Reinmann/` files, `all_goals try rfl` follows a stand-alone
   `convert ... using n` for the same reason (`fix_convert_rfl.py`).
5. In `XiRectangle/*.lean`, `private` is dropped from declarations. Exposed
   public definitions such as `def term9Jet := J_term9` cannot refer to private
   declarations under the module system. Every tile file has its own
   namespace, and no tile namespace is opened, so this adds no ambiguity.

## Manual repairs (library drift)

| File | Change |
| --- | --- |
| `Reinmann/BernoulliQuadrature.lean` | Added `have hk : kernel (n+1) = fun x => … := rfl; rw [hk]` before a `convert` |
| `Reinmann/GammaHeightMajorant.lean` | `Finset.prod_le_prod` → `Finset.prod_le_prod₀` |
| `Reinmann/XiPlanePrincipalValue.lean` | Explicit intermediate `HasDerivAt` facts, then `convert h3 using 1` with `funext`/`simp` and `ring` bullets |
| `Reinmann/FinitePFStrict.lean` (2 sites) | Added explicit positivity / `toNat` facts to `simpa` |
| `Reinmann/AnalyticPFLimit.lean` | `simpa only [Function.comp_def, Polynomial.coeff_map, Complex.coe_algebraMap, Complex.ofReal_re]` |
| `Reinmann/EulerMaclaurinCell.lean` | Added `· funext y; simp [powerDerivative]` after a `convert` |
| `Reinmann/XiCenterPositive.lean` | `toStrongFEPair.hasMellin` → `isStrongFEPair_toStrongFEPair.hasMellin` |
| `Reinmann/StirlingCell.lean` | Zero case: `· funext y; rfl` then `· simp [logChain]` |
| `Reinmann/StirlingSum.lean` | `· rfl` after `convert h using 1` |
| `Reinmann/StirlingGamma.lean` | `· first \| rfl \| (funext y; simp [logChain])` after `convert h using 1` |
| `Reinmann/EulerMaclaurinZeta.lean` | Added `rfl` after an `exact_mod_cast` |
| `Reinmann/RectangleTileRules.lean` | Added `· ring` after a `convert` bullet |

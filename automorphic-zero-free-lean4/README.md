# Zero-free strips for automorphic and elliptic-curve L-functions

The new manuscript proves an asymptotic zero-free strip for each fixed non-CM elliptic curve over the rationals. In unitary normalization every sufficiently high nontrivial zero β+iT satisfies

    log |T| · min(β,1−β) > 10000/57693.

The height threshold can depend on the curve. The general extended Riemann hypothesis over number fields remains open. The supplement also proves general-rank results and an independent effective bound for the curve of conductor 11.

## Read the proofs

- `paper/automorphic-zero-free-strips.tex` is the standalone source for the new paper. Run `pdflatex` twice, or until all cross-references resolve. The file requires standard TeX Live packages including `mathpazo`, `lmodern` and `hyperref`. It has no external inputs or separate bibliography.
- `paper/previous/automorphic-erh.tex` is the standalone source for the preceding long manuscript.
- `notes/` contains companion derivations. The early exponential-tilt note records the exploratory argument. The main paper proves the signed comparison and its final applications.
- `research-record.md` identifies the methods and the resulting bounds.

## Rebuild and check

Lean 4.35.0-rc3 and Mathlib revision `0493595ecd5da8ef14742febab99728f98e948e8` are pinned. With Elan, Git and Python 3.9 or newer installed, run the following commands in this directory. The first run needs online access to the pinned toolchain and dependencies.

```sh
lake exe cache get
lake build
```

The next command independently elaborates all local sources and calls Lean's `leanchecker` on every resulting module. One job keeps the memory requirements of the large Bernstein certificates manageable. An explicit cache directory permits interrupted runs to resume. The verification script checks the source, dependencies and toolchain before reusing its successful results.

```sh
lake env python3 scripts/check.py --jobs 1 --cache .verification --log replay.txt
```

Each rational positivity computation in Lean uses kernel reduction or proved polynomial identities. Elan toolchains, dependency repositories and compiled Mathlib caches are fetched by the commands above.

## Locate the formal results

| Mathematical step | File and declaration |
| --- | --- |
| Main function-level conclusion | `Research/BootstrapElliptic.lean` — `ERH.BootstrapElliptic.eventual_strip` |
| Input inequalities for the four moving factors | `Research/BootstrapElliptic.lean` — `FactorEstimates` and `from_factor_estimates` |
| Auxiliary symmetric-square amplifier | `Research/SquarePrior.lean` — `EllipticBernstein.SquarePrior.interior_nonnegative`, `only_square_moves`, `coefficients` |
| Symmetric-square limiting gain | `Research/SquarePriorGain.lean` — `ERH.SquarePriorGain.certified_prior` |
| Degree-twelve amplifier | `Research/EllipticTilt12.lean` — `EllipticBernstein.Tilt12.normalized_fourier_nonnegative`, `negative_support`, `moving_support` |
| Real integrals and exponential estimates | `Research/CompactBump.lean`, `Research/TiltedGain.lean`, `Research/TiltedWidth.lean` |
| Fourier inversion, spectral law and exact limit | `Research/SpectralWindow.lean`, `Research/BumpSpectral.lean`, `Research/BumpLimit.lean` |
| Signed-measure interchange, positivity and far zeros | `Research/SignedHadamard.lean`, `Research/SignedPoisson.lean`, `Research/TiltedWindow.lean`, `Research/HadamardFar.lean`, `Research/KernelRemainder.lean` |
| Harmonic Poisson formula and Blaschke factors | `Research/PoissonJensenCore.lean`, `Research/BlaschkeDisk.lean` |
| General ranks and limiting displacement | `Research/RankBump.lean`, `Research/RankSelfTilt.lean` |
| Effective conductor-eleven comparison | `Research/EffectiveEleven.lean` — `quartic_exclusion`, `quartic_first_octave`, `joint_exclusion` |
| Finite real shifts and infinite zero sums | `Research/MultiShift.lean`, `Research/SignedKernel.lean`, `Research/HadamardBudget.lean`, `Research/ExactTarget.lean` |
| Other elliptic polynomials | `EllipticSmoothDegree20.lean`, `EllipticSmoothOctic.lean`, `EllipticTiltedOctic.lean` |
| Multiple zeros and Brauer descent | `Research/Occupation.lean`, `Research/SignedBrauerDescent.lean`, `Research/A5BrauerCertificate.lean`, `Research/RepresentationIndex.lean` |
| Earlier project results | `Research/Prior/` |

`Research.lean` imports the main elliptic result. In Lean, `import Research` and `#print ERH.BootstrapElliptic.FactorEstimates` display the precise analytic hypotheses. The endpoint is a statement about zeros of a complex function. The paper specializes it to the analytic continuation of the unitary elliptic L-function. Modularity, symmetric-power functoriality, subconvexity, the automorphic Euler and Hadamard formulas, and their uniform application at increasing heights are mathematical inputs. They are cited or derived in the manuscript. These number-theoretic applications have no end-to-end Lean derivation in this project.

## Repeat the numerical audits

These scripts use Python's standard library:

```sh
python3 scripts/check_final.py
python3 scripts/check_smoothing.py data/smooth8_weights.json data/smooth20_weights.json
python3 scripts/certify_tilt.py data/final_tilt8.json data/final_tilt12.json
python3 scripts/audit_brauer_groups.py Research/A5BrauerCertificate.lean
python3 scripts/spline_certificate.py
```

`data/main-result.json` gives the final comparison parameters. The degree-twelve polynomial also has a simpler application giving 5.8872, whose test parameters are retained in `data/final_tilt12.json`. The polynomial is identical in the two applications.

The following interval audits require `python-flint`. The release run used version 0.9.0.

```sh
python3 scripts/level11_constants.py
python3 scripts/cosine_constants.py
python3 scripts/diagonal_prior.py
python3 scripts/tilted_check.py
```

`verification/` contains the outputs from the release. `SHA256SUMS` records SHA-256 digests for the files in this package.

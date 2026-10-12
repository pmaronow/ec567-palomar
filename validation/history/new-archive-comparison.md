# New source archive comparison

11 October 2026. Archive:
`elliptic_curves_ranks_5_7_source-0038f160972b4a4f998d867a76e5ea58.zip`.
SHA-256:
`a510f3af0b73170a1f10a73f077337e6d4310efbe31ca252e2fe2bc6056bf4f6`.

The archive is useful as a consolidated manuscript and reproducibility
package. Its certificates supply no new arithmetic data: all seven
certificate assets are byte-for-byte identical to the corresponding
files in the original `rank-5-elliptic-curves-main` archive.

| New member | Original member under `research/` | Comparison |
| --- | --- | --- |
| `certificates/rank5/final155_certificate.json` | `paper/final155_certificate.json` | Identical bytes |
| `certificates/rank5/verify_final155_certificate.py` | `paper/verify_final155_certificate.py` | Identical bytes |
| `certificates/rank6/rank6_certificate.json` | `rank6/paper/rank6_certificate.json` | Identical bytes |
| `certificates/rank6/verify_rank6_certificate.py` | `rank6/paper/verify_rank6_certificate.py` | Identical bytes |
| `certificates/rank7/rank7_certificate.json` | `rank7/paper/rank7_certificate.json` | Identical bytes |
| `certificates/rank7/rank7_certificate_output.json` | `rank7/paper/rank7_certificate_output.json` | Identical bytes |
| `certificates/rank7/verify_rank7_certificate.py` | `rank7/paper/verify_rank7_certificate.py` | Identical bytes |

`comparison.json` records both hashes for every pair. All thirteen listed
archive-member checksums passed (`checksum-audit.json`). All three Python
verifiers were independently rerun in an isolated audit copy and exited
successfully. Their original/partner kernel dimensions are respectively
`3/4`, `4/4`, and `5/4`, for both values of the character bit.

An independent literal comparison against the frozen Lean project also
matched all twelve matrices, all six known-code lists, all thirty-six
linear forms, all thirty-six cofactors, and all three CRT lattice triples
(`lean-literal-comparison.json`). The corresponding main-project genuine
arithmetic endpoints already assert

```
PrimeSpecialization5 x y → HasExactRank (Rank5.E (M5 x) (N5 y)) 5
PrimeSpecialization6 x y → HasExactRank (Rank6.E (M6 x) (N6 y)) 6
PrimeSpecialization7 x y → HasExactRank (Rank7.E (M7 x) (N7 y)) 7.
```

## Analytic input

The combined manuscript clarifies the classical theorem invocation; it
does not provide a new proof or formal implementation of that theorem.
At lines 352–359 it explicitly invokes Green–Tao 2010 Main Theorem and
Corollary 1.9, Green–Tao 2012 Theorem 1.1 (Möbius–nilsequence
orthogonality), and Green–Tao–Ziegler 2012 Theorem 1.3 (inverse theorem).
Kai's number-field theorem is offered as an alternative external input.

The displayed twelve-form von Mangoldt asymptotic is obtained by the
sentence “The cited finite-complexity theorem gives” at line 391. The
surrounding proof checks complexity at most ten, the real region, and
positivity/convergence of the singular series. The following lemma
removes proper prime powers, repeated outputs, forbidden finite prime
sets, and finitely many affine lines. These applicability and extraction
arguments are useful exposition, but the full prime-counting asymptotic
still comes from the cited published theorem. The old three final papers
already invoke this same theorem chain.

The appendix states the boundary explicitly at lines 1998–2000:
the proof additionally uses the uniform valuation arguments and the
published prime-pattern theorem, and “a passing finite certificate alone
does not prove infinitude.” This agrees with the existing formalization
boundary. The new archive contains no `.lean`, `.olean`, Lean toolchain,
or Lean package manifest.

The remaining unconditional Lean infinitude proof still needs a
kernel-checked supplier of the required finite-complexity prime patterns
and its asymptotic/extraction bridges. No new certificate hypothesis has
been substituted for that supplier, and no document instructions were
treated as user authorization. No main-project source was changed.

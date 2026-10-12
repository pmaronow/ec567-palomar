# Independent statement and transcription audit

## Verdict and scope

The checked source statements accurately represent the algebraic and finite
arithmetic parts of the three supplied final manuscripts. I found no changed
coefficient, omitted denominator, reversed bit order, or replacement of the
Mordell–Weil rank by a certificate statistic.

This is **not a completed formalization of the requested exact-rank infinitude
theorems**. In particular, there is no unconditional proof of
`InfinitelyManyExactRank 5`, `InfinitelyManyExactRank 6`,
`InfinitelyManyExactRank 7`, or `RanksFiveThroughSeven`. The source explicitly
records that boundary. Successful checking of the supplied matrices does not
establish their connection to rational-point descent images.

This audit compares theorem statements and literals with the papers and their
frozen certificates. It does not certify the truth of every informal argument
in the uploaded archive or treat its instructions and prior review claims as
user authority. The integrated build and axiom audit on the final toolchain
must be recorded separately by the build owner. The current toolchain is Lean v4.35.0-rc3. The supplemental foundation
audit below records the newer Mordell–Weil, Kummer, and isogeny components.

## Sources compared

The comparison uses these final archive artifacts:

- Rank five: `research/paper/final_rank5.tex` and
  `research/paper/final155_certificate.json`.
- Rank six: `research/rank6/paper/rank6_infinitude.tex` and
  `research/rank6/paper/rank6_certificate.json`.
- Rank seven: `research/rank7/paper/rank7_infinitude.tex` and
  `research/rank7/paper/rank7_certificate.json`.

The Lean modules reviewed are `Common`, `Rank5`, `Rank6`, `Rank7`,
`PrimePatterns`, `Admissibility`, `Binary`, `MatrixCertificates`, `Geometric`,
`Specification`, `ConditionalAssembly`, `Integration`, `PrimeDirections`,
`MordellWeil`, `Kummer`, `Isogeny`, and `DescentWitnesses`.

## Family and point statements

The twelve ordered rational linear forms in each family agree with the
corresponding paper. The models use the actual mathlib `WeierstrassCurve ℚ`
with coefficients `(0,a,0,b,0)`, and the partner uses `(0,-2a,0,a²-4b,0)`.
`OnCurve` is the literal equation `y² = x³ + a*x² + b*x`; `Common` proves its
equivalence to mathlib's affine `Equation` and obtains `Nonsingular` from the
actual nonzero discriminant. No independent notion of an elliptic curve is
substituted for mathlib's model.

| Family | `a` | `b` | `a²-4b` | Quartic identity |
| --- | --- | --- | --- | --- |
| Five | `1500 F` | `-2700 F H` | `57600 F J` | `625 F + 3 H = 16 J` |
| Six | `70 F` | `-784 F H` | `1764 F J` | `25 F + 16 H = 9 J` |
| Seven | `91205 F` | `-33124 F H` | `9 F J` | `91205² F + 4*33124 H = 9 J` |

The point coordinates in the rank-five and rank-six source agree with the
tables and appendices of their papers. In rank six, the code correctly turns
each printed `y/x` into `y = x*(y/x)`. Its image-coordinate statements retain
an explicit nonzero-coordinate hypothesis whenever variable denominators
are cancelled. Polynomial cleared-denominator statements are correctly
allowed at zero coordinates.

The rank-seven section comparison is as follows. `r` denotes the source's
printed ratio, and the Lean point equation uses `y = x*r`.

| Point | `x` | `r` |
| --- | --- | --- |
| `p1` | `-58081 F` | `10920 d / 241` |
| `p2` | `(1225/9) L0 L2 L6 L7` | `(4/15) A1` |
| `p3` | `-2275 L1 L2 L5 L6` | `-(6/5) A2` |
| `p4` | `(182/361) L2 L3 L6 L7` | `A3/19` |
| `q1` | `3481 F` | `21840 d / 59` |
| `q2` | `(49/64) L0 L2 L8 L9` | `(65/56) B1` |
| `q3` | `(16/225) L0 L3 L8 L10` | `B2/60` |

In particular, the new fourth original section retains both occurrences of
the denominator 19: `361 = 19²` in `x`, and `19` in `y/x`. Its square-factor
witness is exactly
`p4x = (182 L2 L3 L6 L7) * (1/19)²`.

The three additional rank-seven points on the original curve match the
appendix, including `59`, `112`, `448`, `120`, `480`, `576/49`, and `2025/16`.
The formal source checks these polynomial coordinates directly. Point
membership and nonsingularity are proved; linear independence of the seven
points modulo torsion is not proved.

The displayed original-curve `j` expressions agree with the papers:

- Five: `(4/9) * (2500 F + 9 H)³ / (H² J)`.
- Six: `(16/9) * (25 F + 12 H)³ / (H² J)`.
- Seven: `256/(9*182⁴) * (91205² F + 3*182² H)³ / (H² J)`.

These are connected to the actual mathlib discriminant and `c₄`, and to
mathlib's `j` under ellipticity. The nonzero product assumptions used in
the statements are explicit and are appropriate for this algebraic layer.

## Prime-pattern transcription and admissibility

An independent standard-library Python comparison parsed the literal Lean
data and checked all forms, cofactors, `W`, `M0`, `N0`, all 36 normalized affine
coefficient triples, all 12 matrix row lists, and all six known-generator
lists against the frozen JSON. Every comparison passed.

| Family | `W` | `M0` | `N0` |
| --- | --- | --- | --- |
| Five | `19984345920` | `6555660534` | `-1` |
| Six | `780373440` | `416513683` | `91046603` |
| Seven | `308403583488` | `79151095314` | `151444919819` |

The use of `N0 = -1` in rank five is the paper's actual progression, not a
transcription error. The rank-six frozen JSON also contains auxiliary
reference states at omitted determinant primes. The Lean CRT table follows
the reduced progression printed in the final paper, rather than imposing
those unused reference states.

`normalization` proves, over the integers, that each normalized affine output
times its cofactor equals the literal original form on the CRT progression.
`normalized_quotient` is justified integer division, not a division of an
arbitrary form with a possibly nonzero remainder. The normalized unit
residues modulo eight and three and the retained-prime residues are checked
for all outputs.

`Avoids` means that all twelve outputs are nonzero modulo a given prime.
`Admissibility` supplies a genuine finite-field counting argument for primes
larger than twelve, and the small primes are handled by explicit witnesses.
Thus `local_admissibility` concerns every prime, not only a bounded search.
It establishes the local admissibility condition; it does not infer the
existence or infinitude of simultaneous prime outputs.

The integer prime-pattern and rational family forms are duplicated literal
data. `Integration` proves their equality on the actual lattices, not merely
a source-level comparison. It also proves nonsingularity throughout the
lattices and the displayed coordinate square-factor support identities.
These bridges do not yet yield a complete rank theorem.

## Binary matrices and their meaning

Every row and generator list agrees exactly with the paper and the frozen
certificate. The widths and source column orders are:

- Five, width 12: `(-1,2,3,5,p0,p1,p2,p3,p4,p5,p6,p7)` on the original
  curve; replace the last four primes by `p8,p9,p10,p11` on the partner.
- Six, width 12: `(-1,2,3,7,p0,p1,p2,p3,p4,p5,p6,p7)` on the original
  curve; the same partner replacement applies.
- Seven, width 13: `(-1,2,3,7,13,p0,p1,p2,p3,p4,p5,p6,p7)` on the
  original curve; the same partner replacement applies.

`Binary.vector` uses the low bits of an integer, with bit zero as column zero.
`dot_eq_sum` relates the Boolean implementation to the genuine dot product
over `ZMod 2`. The finite enumeration is therefore not merely an unrelated
Boolean predicate. `spanCodes_iff_mem_span` connects the mask sums to
mathlib's linear span, with explicit mask bounds. All supplied row masks and
generator masks lie within their declared widths.

An independent binary elimination reconstruction obtained these dimensions:

| Family | Original, both signs | Partner, both signs |
| --- | --- | --- |
| Five | 3 | 4 |
| Six | 4 | 4 |
| Seven | 5 | 4 |

The Lean exhaustive kernel equalities use `decide +kernel`, not
`native_decide`. They compare the complete bounded kernel with all XOR sums
of the supplied generators. `DescentWitnesses` now proves that every supplied generator mask represents
a class in the actual rational-point image on its lattice. Independence of
those actual classes and the necessity of each row for every rational point
remain separate obligations. Consequently these
dimensions alone are not formal Mordell–Weil rank results.

## Exact-rank specification and conditional assembly

`Specification.rationalRank` is
`Module.rank ℤ E.toAffine.Point : Cardinal`, using the genuine group of
rational nonsingular points. An infinite rank is retained as a cardinal;
there is no `toNat` conversion or accidental use of a zero-valued
`finrank` outside finite generation. The comparison to ordinary natural
`finrank` carries an explicit `Module.Finite` hypothesis in the general
specification lemma. `MordellWeil` now supplies this instance for every
nonsingular rational Weierstrass model from the pinned, proved external
Mordell–Weil theorem.

`InfinitelyManyExactRank` counts distinct usual rational `j`-invariants of
certified nonsingular models with that genuine rank. The geometric
isomorphism statement uses base change to `AlgebraicClosure ℚ` and an actual
Weierstrass variable change. It is therefore faithful to the papers'
geometric-isomorphism meaning.

`ConditionalAssembly` defines squareclasses as the actual quotient
`ℚˣ/(ℚˣ)²` and images as the range of the usual rational-point squareclass
function. It does not replace those images by the binary matrices.
`TwoIsogenyRankIdentity` assumes only the isogeny cardinality formula;
finite generation is now proved by `MordellWeil`. `ActualImageCardinalities`
assumes the cardinalities of the actual images. These are explicit theorem arguments, without an axiom or a default
instance asserting them. The resulting assembly is conditional. Its
substantial central rank formula is a hypothesis, not an established result.

`Geometric` proves finite fibers of nonconstant rational functions and
infinite invariant images on the unrestricted regular rational-parameter
locus. This is a proved geometric component. It does not establish that the
prime-specialization subset is infinite or has rank five, six, or seven.

## Outstanding proof obligations for full completion

To prove the user's exact-rank infinitude targets unconditionally in Lean,
the following material is still required:

1. Construct the rational two-isogenies as point-group homomorphisms,
   prove their composition is doubling, and derive the isogeny cardinality
   formula with the required rational two-torsion condition. The Kummer
   homomorphism and its kernel equality with the range of the genuine dual
   point map are now proved; coordinate maps and preimage criteria are also
   proved. These results alone do not supply the rank formula.
2. Prove independence of the actual rational squareclasses represented by the
   displayed section supports on every admissible prime specialization.
3. Prove global squareclass support bounds and uniform fixed-place and
   moving-place valuation exclusions for every rational point. Derive the
   displayed binary rows from those necessities using CRT units and
   quadratic reciprocity. Combine upper and lower bounds to obtain the
   exact actual image cardinalities.
4. Formalize a sufficient unconditional finite-complexity affine
   prime-pattern infinitude theorem. The papers use the Green–Tao 2010
   theorem, completed by the Green–Tao and Green–Tao–Ziegler 2012 inputs.
   These are major published mathematical dependencies, not finite
   certificate checks. Admissibility alone does not imply their conclusion.
5. Apply that theorem on the positive sector, exclude prime powers,
   repeated values and finite exceptional primes, and prove that the
   resulting prime tuples give infinitely many projective parameters.
6. Connect those parameters to the proved rational-invariant finite fibers
   and instantiate the conditional assembly with actual rank proofs.

Finite generation is no longer an outstanding hypothesis. The pinned
Michael Stoll `EllipticCurves` development supplies a proved Mordell–Weil
theorem for the same actual affine point group. The project wrappers and
imported theorem pass the transitive standard-axiom audit. `Kummer` supplies
the genuine squareclass homomorphism proved here. The remaining specialized
isogeny cardinality proof, uniform local/global descent bridge, and analytic
prime-pattern theorem require additional formalization. They cannot be
closed by rerunning finite certificates or by adding axioms while claiming
a completed submission.

## Packaging and validation scope

The aggregate module imports the developed components rather than only the
initial `Common` module. The final aggregate includes the newest isogeny
and witness modules.
The build owner completed its v4.35.0-rc3 build, verified all 1,319 exported
project declarations against the standard-axiom allowlist, and passed source
checks on all 20 Lean files. The audit detector also rejected a private
custom axiom in its negative check. Exploratory `#check` files are excluded
from the deliverables. Reproduction and the recorded validation evidence
accompany the packaged project.

## Supplemental audit of the descent foundations

The `Kummer` theorem `twoIsogenyClass_add` proves multiplicativity for the
existing `twoIsogenyClass` function on Mathlib's actual affine rational-point
group.
Its signature requires `b ≠ 0`; `ellipticTwoIsogenyClassHom` obtains this
from the actual elliptic discriminant. The proof uses Mathlib's chord and
tangent factorization, the constant and linear coefficients, and explicit
cases for vertical pairs and all zero-coordinate torsion possibilities.
It does not assume a generic-position restriction or omit tangencies.

The `Multiplicative Point →* RationalSquareClasses` and additive-version
homomorphisms retain the actual point group. `twoIsogenyImage_eq_subgroup`
identifies the previously defined actual image with the carrier of their
range subgroup. `rationalSquareClass_eq_one_iff` has the necessary nonzero
input hypothesis; the function's sentinel value at zero is handled
separately by the point-class definition. These results establish the
homomorphism and subgroup properties, without asserting image size,
independence, uniform local bounds, or the rank cardinality formula.

`Isogeny` proves the usual rational `phiX/phiY` and `psiX/psiY` coordinate
identities with explicit nonzero denominator hypotheses. The constructive
lift `X = a + 2*s² + 2*y/s`, `Y = 2*s*X` is proved to lie on the partner
curve and return the exact original coordinates when `s ≠ 0` and
`a²-4b ≠ 0`. The nonzero-coordinate preimage criterion is an equivalence
with a rational square coordinate. Separate torsion criteria correctly
characterize preimages of `(0,0)` by `b` being a rational square. Those
statements concern actual equation points. `psiPoint` extends the dual
formula to the actual nonsingular point groups, sending infinity and the
distinguished zero-coordinate point to infinity.

`twoIsogenyClass_eq_one_iff_range` covers every original rational point and
proves that trivial Kummer class is equivalent to membership in the actual
`psiPoint` range. Its signature explicitly requires both `b ≠ 0` and
`a²-4b ≠ 0`; the proof includes infinity, nonzero square coordinates, and
the distinguished torsion point. `twoIsogenyClassAddHom_kernel` identifies
the actual additive homomorphism kernel with that same range as sets.
These statements do not declare `psiPoint` a homomorphism, prove a doubling
composition, or deduce a rank/cardinality formula.

The Kummer module builds cleanly on v4.35.0-rc3. Independent axiom inspection
of its homomorphism, elliptic wrapper, chord identities, and rational-square
criterion returned only `propext`, `Classical.choice`, and `Quot.sound`.
There is no custom axiom, proof placeholder, compiler axiom, rank formula,
or uniform local-bound assertion in these declarations.

`DescentWitnesses` constructs actual nonsingular rational points from the
section equations and the lattice discriminants. Its six witness arrays
have sizes `(3,4)`, `(4,4)`, and `(5,4)`, including the distinguished torsion
points. For all 24 supplied generator masks, the proved mask-class equality
connects the signed rational product of the ordered literal columns to the
existing Kummer function on the corresponding actual point. The nonzero
mask and coordinate hypotheses are proved using lattice unit residues,
not assumed primality or a numerical rank calculation.

The six closure inclusions use the proved image subgroup to place every
product of witnessed classes in the actual image. They are inclusions;
there is no claim that their generators are independent for arbitrary
lattice outputs, that the image equals that closure, or that its size is
`2³`, `2⁴`, or `2⁵`. The module's generic kernel criteria preserve the
nonzero-coordinate hypothesis and separately handle the torsion class.
These statements close the actual lower-image witness bridge while leaving
prime-specialization independence and all uniform local upper bounds open.

An independent build of the finalized `DescentWitnesses` and `Isogeny`
modules succeeded on the pinned v4.35.0-rc3 setup. Independent axiom
inspection of all six witness mask-class families, the generic closure
inclusion, `psiPoint_class`, the full pointwise range criterion, and the
actual additive kernel equality returned only `propext`, `Classical.choice`,
and `Quot.sound`. Their signatures were reviewed against the distinctions
above; none claims the rank cardinality identity or uniform local upper
bounds. This supplement and the current-status passages above reflect the
final source snapshot, rather than the earlier stage where finite generation
and the Kummer homomorphism were still outstanding.

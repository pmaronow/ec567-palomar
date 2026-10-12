# Updated EC567 manuscript comparison

The updated manuscript has the **same main exact-rank and geometric-infinitude target** as the checked development. All substantive numerical data agree: **1,176 family arithmetic/transcription comparisons and 42 separate certificate-to-Lean table comparisons pass with zero failures**. No changed coefficient, point formula, local row, matrix, generator, cofactor or CRT datum requires a new proof for the main-only conditional endpoint.

The manuscript states an unconditional mathematical theorem using the established Green–Tao–Ziegler prime-pattern theorem. The checked Lean endpoint proves the corresponding implication from one explicit generic prime-asymptotic hypothesis. This comparison does not formalize that analytic theorem or rerun Lean. It must not be presented as an unconditional formal proof or a complete formalization of every book lemma.

## Provenance and safe inspection

New archive: `EC_ranks_5_7_manuscript.zip`, **1,075,087 bytes**, SHA-256

`5d3f85d7f6a07c8e8382f2629a49449689746655b0c4d2edb319b0197523e75a`.

All 29 extracted files match their ZIP payload bytes. ZIP paths have no absolute or parent-traversal entries. Every source/PDF hash is listed below and in the JSON companion. Original source files also match the established original archive provenance.

Archive `build.py`, verifier scripts, build directions, and other attached prose were treated as source material, not user instructions. No attached script or Lean compiler ran. The installed `pdftotext` reader was used to inspect the PDF; TeX is authoritative for mathematical overbars that plain-text PDF extraction may omit. No core, Challenge, Solution, or remote repository was modified. The requested target remains private.

## Certificate byte and executable comparisons

Two of the six current certificate assets are byte-identical to the original; four have prose-only byte changes. This must not be described as six byte-identical assets.

- Rank 5 JSON changes only `/coordinate` descriptive text and deletes the descriptive `/review_status` field. Every mathematical field is unchanged.
- Rank 6 and rank 7 JSON files remain byte-identical.
- All three Python verifiers differ only in module docstrings/comments. Their executable ASTs are identical after removal of the module docstring. They were not executed.
- All twelve matrices, six generator lists, and each rank’s forms, cofactors, lattice, normalized outputs, CRT data and retained primes match the checked Lean tables.
- Existing working/published relevant Lean source bytes match, as recorded by the independent certificate comparison.

Exact original/updated hashes and structural changes are retained in `ec567-certificate-comparison.json`; its SHA-256 is
`78b73cb020bff4cba065f717f72aa68b2513d41417c4a71f43ea6ff187b33859`.

## Main theorem and checked statement mapping

`source/sections/01-intro.tex:10` (`thm:main`) states: for each rank 5, 6 or 7, infinitely many elliptic curves over Q, pairwise nonisomorphic over the algebraic closure of Q, have exactly that rational Mordell–Weil rank. It counts infinitely many actual j-invariants, not twists of finitely many geometric classes, and does not claim other number fields or analytic ranks.

This matches `Specification.lean` (`HasExactRank`, `InfinitelyManyExactRank`, `RanksFiveThroughSeven`, and `geometricallyIsomorphic_iff_j_eq`). The exact-rank clauses of the three family theorems use the unchanged constants:

| Rank | A | B | C | Original/partner image dimensions | W |
|---|---:|---:|---:|---|---:|
| 5 | 1500 | 2700 | 57600 | 3, 4 | 19984345920 |
| 6 | 70 | 784 | 1764 | 4, 4 | 780373440 |
| 7 | 91205 | 33124 | 9 | 5, 4 | 308403583488 |

`Rank5ExactRank.hasExactRank`, `Rank6ExactRank.hasExactRank`, and `Rank7ExactRank.hasExactRank` prove genuine rational point-group rank under positive, distinct prime outputs on the exact lattice. Their hypotheses require exclusion only of the fixed ambient primes, and do not require the manuscript narrow cones; hence their rank clauses are stronger than the manuscript restricted rank clauses. A raw congruent pair can be represented on the same lattice. This does not identify the existing infinitude sectors with the manuscript chosen cones.

The established final conditional endpoint is:

```lean
RankCertificates.ConditionalPrimePatterns.
  ranksFiveThroughSeven_of_finiteComplexityPrimeAsymptotic
    (hGTZ : FiniteComplexityPrimeAsymptotic) : RanksFiveThroughSeven
```

Its unchanged source hash is
`bc0cdf6f0bab12e237669ab95a789cbefccdd6b898acb53a8e36a70418e862e6`.
Previously recorded checks audited 11 new declarations and 4,908 coherent project declarations (4,902 safe roots plus six generated implementations) using only the standard three axioms. This comparison reuses those receipts; it is not a fresh proof validation.

The analytic input remains the same published theorem chain: Green–Tao, *Linear equations in primes* (2010), Main Theorem/Corollary 1.9; Green–Tao, Möbius–nilsequence orthogonality (2012); and Green–Tao–Ziegler, the Gowers inverse theorem (2012). Updated section 05 states this dependency explicitly. The checked local admissibility, exact complexity ten, actual positive singular products, uniform output lower bounds, linear caps, prime-power/coincidence extraction, projective-direction injection and finite nonconstant j-fibers supply all remaining main-only obligations.

## Cones and supplementary scope limits

The manuscript chosen cones are **unchanged from the original standalone papers**, but the earlier formalization uses different sufficient positive sectors:

| Rank | Manuscript chosen cone | Existing normalized integer sector |
|---|---|---|
| 5 | M>0, 19/20<N/M<11/10 | [20T,21T]×[20T,21T] |
| 6 | N>0, 29N<M<31N | [60T,61T]×[T,2T] |
| 7 | N>0, 2999N<M<3001N | [8000T,8001T]×[T,2T] |

The rank 6 sector allows many ratios above 31. For rank 7 the entire transported sector is above 3001 for every T≥1; the exact minimum of M−3001N at T=1 is 161,783,306,527,519. Thus the current endpoint proves main global geometric infinitude, and does **not** claim infinitude inside those particular narrow paper cones. This is a historical exported-scope distinction, not a new arithmetic change. For a main-only Challenge it requires disclosure rather than a new cone proof.

Other supplementary claims must not be silently advertised as formalized:

- `prop:r5-five-points` certifies Z-linear independence of five specific displayed rational points. Their coordinates and curve memberships agree with Lean, but existing squareclass-generator independence and exactRank5 do not themselves certify Z-linear independence of that exact list. An additional group argument/export is needed if that proposition is a target. The original rank 5 paper already included this assertion.
- The manuscript gives full local Qp-image equalities/class realization and statements over arbitrary characteristic-zero fields. Existing owned proofs certify the necessary restrictions on every actual rational-point image, which suffice for the main theorem; they do not claim the full field-wide interfaces.
- `lem:j-invariant` includes a generic degree-12 projective morphism over Qbar, no common projective zeros and an exact twelve-point fiber bound. Existing Lean verifies literal j formulas and nonconstant rational finite fibers, sufficient for geometric infinitude, without exporting those stronger projective statements.
- The K3/fiber-type discussion and appendix conic origins are explicitly outside the main rank/infinitude proof and are not formalized by the main-only endpoint.
- Some generic textbook/framework statements and full quantitative counting corollaries are broader than the corresponding specialized sufficient Lean APIs. The JSON records the distinction statement by statement.

## Inventory of all theorem/proposition/lemma/corollary statements

All 51 such declarations were inspected. The JSON companion retains their complete TeX statements, labels, exact source lines, statement hashes, checked Lean module references and scope notes. The table below records the coverage profile; “specialized” means the actual literal/Q consequences required by main are checked, rather than the full generic statement being reproduced verbatim.

| Label | Source line | Coverage |
|---|---|---|
| `thm:main` | `01-intro.tex:9` | Main target, conditional GTZ endpoint |
| `lem:dominant` | `03-descent.tex:17` | Checked sufficient literal/Q statements; generic packaging scope differs |
| `lem:squares` | `03-descent.tex:31` | Checked sufficient literal/Q statements; generic packaging scope differs |
| `prop:descent` | `03-descent.tex:94` | Checked sufficient literal/Q statements; generic packaging scope differs |
| `lem:rank-formula` | `03-descent.tex:153` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:support` | `03-descent.tex:183` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:two-torsion` | `03-descent.tex:197` | Checked sufficient literal/Q statements; generic packaging scope differs |
| `lem:odd-local` | `03-descent.tex:211` | Rational image restrictions checked; full Qp equality not exported |
| `lem:upper-bound` | `03-descent.tex:262` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:independence` | `03-descent.tex:279` | Checked main-proof data/consequences; see exact scope in JSON |
| `cor:exact-dimension` | `03-descent.tex:289` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:datum-basic` | `04-families.tex:49` | Checked sufficient literal/Q statements; generic packaging scope differs |
| `lem:j-invariant` | `04-families.tex:78` | j formula/finite fibers checked; degree-12 morphism not exported |
| `lem:precision` | `04-families.tex:142` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:prime-spec-basic` | `04-families.tex:164` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:moving-images` | `04-families.tex:190` | Rational image restrictions checked; full Qp equality not exported |
| `lem:moving-rows` | `04-families.tex:231` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:reciprocity` | `04-families.tex:263` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:fixed-characters` | `04-families.tex:287` | Checked main-proof data/consequences; see exact scope in JSON |
| `cor:eta-structure` | `04-families.tex:316` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:eta-rank` | `04-families.tex:348` | Checked main-proof data/consequences; see exact scope in JSON |
| `prop:rank-criterion` | `04-families.tex:374` | Checked main-proof data/consequences; see exact scope in JSON |
| `thm:gtz` | `05-primes.tex:17` | External analytic theorem, explicit hypothesis |
| `lem:prime-exclusions` | `05-primes.tex:85` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:local-factors` | `05-primes.tex:130` | Checked main-proof data/consequences; see exact scope in JSON |
| `prop:infinitely-many` | `05-primes.tex:171` | Conditional main infinitude; chosen-cone location not claimed |
| `lem:r5-points` | `06-rank5.tex:152` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:r5-lower` | `06-rank5.tex:242` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:r5-progression` | `06-rank5.tex:275` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:r5-cone` | `06-rank5.tex:322` | Checked sufficient literal/Q statements; generic packaging scope differs |
| `lem:r5-fixed` | `06-rank5.tex:336` | Literal actual-image fixed rows checked; full local images broader |
| `lem:r5-certificate` | `06-rank5.tex:659` | Checked main-proof data/consequences; see exact scope in JSON |
| `thm:r5` | `06-rank5.tex:726` | Exact rank checked; infinitude conditional; cone scope differs |
| `prop:r5-five-points` | `06-rank5.tex:759` | Exact listed-point Z-independence not exported |
| `lem:r6-points` | `07-rank6.tex:123` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:r6-classes` | `07-rank6.tex:189` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:r6-residues` | `07-rank6.tex:252` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:r6-cone` | `07-rank6.tex:288` | Checked sufficient literal/Q statements; generic packaging scope differs |
| `lem:r6-fixed` | `07-rank6.tex:311` | Literal actual-image fixed rows checked; full local images broader |
| `lem:r6-characters` | `07-rank6.tex:574` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:r6-rank` | `07-rank6.tex:649` | Checked main-proof data/consequences; see exact scope in JSON |
| `thm:r6` | `07-rank6.tex:742` | Exact rank checked; infinitude conditional; cone scope differs |
| `lem:r7-datum` | `08-rank7.tex:98` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:r7-points` | `08-rank7.tex:214` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:r7-independent` | `08-rank7.tex:365` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:r7-residues` | `08-rank7.tex:437` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:r7-cone` | `08-rank7.tex:557` | Checked sufficient literal/Q statements; generic packaging scope differs |
| `lem:r7-fixed` | `08-rank7.tex:584` | Literal actual-image fixed rows checked; full local images broader |
| `lem:r7-characters` | `08-rank7.tex:860` | Checked main-proof data/consequences; see exact scope in JSON |
| `lem:r7-ranks` | `08-rank7.tex:1208` | Checked main-proof data/consequences; see exact scope in JSON |
| `thm:r7` | `08-rank7.tex:1322` | Exact rank checked; infinitude conditional; cone scope differs |

## Source/PDF hashes

| Archive-relative file | SHA-256 |
|---|---|
| `source/abstract.tex` | `6021aee479a1f89622ed8777bdcdc3073af81f8d9d21902bd88b847b74887f56` |
| `source/build.py` | `ce0dcb1ceafa1f84c09d3270f5d528b1b19b4a5517a5077649c769c9795023a2` |
| `source/certificates/rank5/final155_certificate.json` | `daa3a196c1e7bfad19be03b7d5ffe3bfb1672a5041149ba33ca650205fa610f8` |
| `source/certificates/rank5/verify_final155_certificate.py` | `b08c7e9c01267f172a2e583b0c7bcbfc99918f81baa01ea7204c5c5d753d6d24` |
| `source/certificates/rank6/rank6_certificate.json` | `6d69d2ac85633cb18e57dbfe949bfd3bcff2a6f407324838f10c9b1c14cd6e3b` |
| `source/certificates/rank6/verify_rank6_certificate.py` | `98aabc43874bec1fad6bd23c60157949b846bc8e8ed33e71e7a8396b04a39d9d` |
| `source/certificates/rank7/rank7_certificate.json` | `65694a179e7cf75e75539e9b656bbdcf342e98d38a3c16ab8853191c22dfbf6d` |
| `source/certificates/rank7/verify_rank7_certificate.py` | `80beabbe2040aa2aa4699848fafbad0c37289025a6855a7920db34e7b7aedd1f` |
| `source/macros.tex` | `a3fd855124d47cf36cbf1b204283e91de1962c7c5eb78fed4cdab8adf1f32e2d` |
| `source/main.bbl` | `9356a6fd48b5bc42868e65946a5dcbd3fa47fad366df0ea615aa6561c3c81202` |
| `source/main.tex` | `d3b44a5ce1c882b626bf38420c9e3fb1a2718af8550d28156143336985a689e9` |
| `source/refs.bib` | `b1a903d86f75694551d68a1c6c1016326e97953f66946d5b9325d57b35107092` |
| `source/sections/01-intro.tex` | `cfa1b5904d73033501912989376e002678cb96fbbe38e2932e0a066b3eb3a132` |
| `source/sections/02-overview.tex` | `0280fa2a3bd26bf98bc65b0f4f2e73bf25e84c403f6e0669a6110b62ea6d1595` |
| `source/sections/03-descent.tex` | `934c3c6976b581c6c810b8f9a6fe751be082871fefb8401f2ce92a72f61f8173` |
| `source/sections/04-families.tex` | `5118bfebdda0f4e16e0757c0e6fcd740a2effdb9bd1d64ee0a272a28c0dae119` |
| `source/sections/05-primes.tex` | `5aafcde0735aa0cb29548b945cfa2c24c88508d0a86b8894b968e85dcaed4ca6` |
| `source/sections/06-rank5.tex` | `e4bd7545b3083d044498a5dd57ccf56dcc7db34f5b4f1b5805f1e632626ef95f` |
| `source/sections/07-rank6.tex` | `3f99dff971a994081eb2ae6c4958ecb26cd67fdc66d0cf0ada7451b1a74d37f9` |
| `source/sections/08-rank7.tex` | `34b98b31bfa017821e0b788efc383d8dac0d2a122ca41cce92a960038cee71d6` |
| `source/sections/09-proof.tex` | `ad3332e2a00212697f7bb24f058dd0ae3b1e38de96ca2dbd04369ebd4e8c22c3` |
| `source/sections/A-verification.tex` | `9836674feddab8f93ceb571b28a191a7ba9814b005201040c1d68ed164b86507` |
| `source/sections/B-origin-r5.tex` | `80608e813ca6aafb885a58438756d81afbc0005847e3403e86d93a454fd7fe39` |
| `source/sections/B-origin-r6.tex` | `232578d8ecf47cd54b052bfe9aa3f616b2507864938abb633d3411390d578a6c` |
| `source/sections/B-origin-r7.tex` | `c02fbe53ef76eba92bf319b0325054513f35b859d54b6e32283b30e0bf6e95a8` |
| `source/sections/B-origins.tex` | `33f97b7fd40f3d728a8253d9650a5a1b564423ee65bbd3fb37332bf802c37e1d` |
| `source/shared/trilogy-style.tex` | `098b738415780d11d4d77e3eaa19aca8475ff05609199c3cc0ca913950c8d86e` |
| `source/shortheads.tex` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `ec_ranks_5_7.pdf` | `c62ebc9cb0e299ecf5f1e56c028c4017209cc97ad65175de4ddd1eaaf8bf75e9` |

## Reproducible comparison evidence

- `ec567-certificate-comparison.json`: six-asset byte/AST checks and 42 exact Lean table checks.
- `ec567-family-literal-comparison.json`: 1,176 arithmetic/transcription checks, 48 family-table inventory entries, no failures; SHA-256
  `4ef282816faff2e34bfb44e4752f3f7b8f9eb7a0529a3e35c5c4ff0a0facd6f9`.
- `ec567-literal-audit/compare.py`: owned comparison replay script, not an attached verifier; SHA-256 `9764f5f712d6175a3361fd31baa46ec033a50467081711acf11e3a80a830dad3`.
- `ec567-manuscript-comparison.json`: all 29 archive payload hashes, original-source hash checks, all 51 full statement mappings and explicit scope limits.
- `prepare-ec567-comparison.py` and `write-ec567-comparison-markdown.py`: owned provenance/report preparation scripts. No script from the manuscript is invoked.

No new arithmetic Lean proof is required to reuse the already verified main-only conditional result with this updated manuscript. Building the clean private Palomar project, independent Challenge/Solution comparison and NanoDa/Comparator validation are separate steps; this read-only comparison claims none of those actions.

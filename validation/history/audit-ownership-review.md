# Complete module ownership in the main axiom audit

A separate environment ownership check found one generated project declaration
outside the `RankCertificates` namespace:
`WeierstrassCurve.Affine.Point.equivVariableChange.congr_simp`.
The previous namespace auditor checked every project export and their transitive
dependencies, but its stated exhaustive declaration coverage omitted this helper.

The auditor now selects imported declarations by their recorded module owner,
including every private/generated declaration in any namespace. A local namespace
fallback retains the meaningful negative fixture, which must reject a private
custom axiom used by an exported theorem. Module names are cached once before
the environment traversal. The current complete build, ownership audit, source
audit and negative fixture receipts supersede the older namespace audit count.
The extra generated declaration is checked under the same three permitted axioms.

A second coverage issue was found in Lean's modern module import semantics:
ordinary imports expose exported names but omit some owning-module private
constants even when owner-based enumeration is used. Direct `import all` for
each owning source is required; this does not propagate through ordinary
child imports. Full ModuleData enumeration now checks4,897 roots at107 source
files, including the newly promoted finite CRT leaf42. The previous106-file
ordinary-import count3200 is historical; direct private imports at that same
106-file checkpoint yield4855. The corrected107-file audit retains4891 safe
roots in a safe kernel-checked aggregate and separately checks allsix generated
partial compiler implementation roots. Source imports and the negative fixture
are both enforced. No mathematical theorem source was modified for this
coverage correction.

module

public import RankCertificates.Binary

@[expose] public section

/-! Exact binary matrices transcribed from the supplied JSON certificates.
Rows and generators are integer masks with coordinate zero the least significant
bit. Width 12 is used for ranks five and six; width 13 for rank seven. Every
consecutive block of 256 masks is exhaustively checked using `decide +kernel`.
The proved block concatenation identity covers all `2^width` masks exactly.
The resulting kernel is identified with mathlib's `Submodule.span (ZMod 2)` of
the supplied generators, and its exact cardinality is certified.

This module certifies the supplied matrices. Establishing that arithmetic
descent classes satisfy these rows is a separate mathematical obligation. -/

namespace RankCertificates.MatrixCertificates

open Binary

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Rank5

def E0 : List ℕ := [1669, 3948, 267, 4, 3718, 1424, 642, 322, 4029, 3888, 37, 924, 2572]
def Ep0 : List ℕ := [108, 3206, 1, 1424, 898, 66, 1597, 1494, 3887, 799, 2442]
def E1 : List ℕ := [1669, 3948, 267, 4, 3718, 2656, 3442, 3762, 77, 192, 4053, 3180, 1532]
def Ep1 : List ℕ := [108, 3206, 1, 2656, 3186, 4018, 2509, 2598, 223, 3311, 1658]
def Egenerators : List ℕ := [4081, 243, 3274]
def Epgenerators : List ℕ := [4082, 3840, 824, 1378]

theorem Egenerators_bounded : ∀ g ∈ Egenerators, g < 2 ^ 12 := by
  simp [Egenerators]

theorem Egenerators_span_nodup : (spanCodes Egenerators).Nodup := by decide +kernel

theorem Epgenerators_bounded : ∀ g ∈ Epgenerators, g < 2 ^ 12 := by
  simp [Epgenerators]

theorem Epgenerators_span_nodup : (spanCodes Epgenerators).Nodup := by decide +kernel

private theorem E0_block0 : kernelBlock 12 E0 0 256 =
    [0, 243] := by decide +kernel

private theorem E0_block1 : kernelBlock 12 E0 256 256 =
    [] := by decide +kernel

private theorem E0_block2 : kernelBlock 12 E0 512 256 =
    [] := by decide +kernel

private theorem E0_block3 : kernelBlock 12 E0 768 256 =
    [827, 968] := by decide +kernel

private theorem E0_block4 : kernelBlock 12 E0 1024 256 =
    [] := by decide +kernel

private theorem E0_block5 : kernelBlock 12 E0 1280 256 =
    [] := by decide +kernel

private theorem E0_block6 : kernelBlock 12 E0 1536 256 =
    [] := by decide +kernel

private theorem E0_block7 : kernelBlock 12 E0 1792 256 =
    [] := by decide +kernel

private theorem E0_block8 : kernelBlock 12 E0 2048 256 =
    [] := by decide +kernel

private theorem E0_block9 : kernelBlock 12 E0 2304 256 =
    [] := by decide +kernel

private theorem E0_block10 : kernelBlock 12 E0 2560 256 =
    [] := by decide +kernel

private theorem E0_block11 : kernelBlock 12 E0 2816 256 =
    [] := by decide +kernel

private theorem E0_block12 : kernelBlock 12 E0 3072 256 =
    [3129, 3274] := by decide +kernel

private theorem E0_block13 : kernelBlock 12 E0 3328 256 =
    [] := by decide +kernel

private theorem E0_block14 : kernelBlock 12 E0 3584 256 =
    [] := by decide +kernel

private theorem E0_block15 : kernelBlock 12 E0 3840 256 =
    [3842, 4081] := by decide +kernel

theorem E0_kernel_eq_span : kernelCodes 12 E0 =
    sortCodes (spanCodes Egenerators) := by
  rw [kernelCodes_eq_block]
  change kernelBlock 12 E0 0 4096 = sortCodes (spanCodes Egenerators)
  rw [kernelBlock_add 12 E0 0 256 3840,
    kernelBlock_add 12 E0 256 256 3584,
    kernelBlock_add 12 E0 512 256 3328,
    kernelBlock_add 12 E0 768 256 3072,
    kernelBlock_add 12 E0 1024 256 2816,
    kernelBlock_add 12 E0 1280 256 2560,
    kernelBlock_add 12 E0 1536 256 2304,
    kernelBlock_add 12 E0 1792 256 2048,
    kernelBlock_add 12 E0 2048 256 1792,
    kernelBlock_add 12 E0 2304 256 1536,
    kernelBlock_add 12 E0 2560 256 1280,
    kernelBlock_add 12 E0 2816 256 1024,
    kernelBlock_add 12 E0 3072 256 768,
    kernelBlock_add 12 E0 3328 256 512,
    kernelBlock_add 12 E0 3584 256 256]
  rw [E0_block0, E0_block1, E0_block2, E0_block3, E0_block4, E0_block5, E0_block6, E0_block7, E0_block8, E0_block9, E0_block10, E0_block11, E0_block12, E0_block13, E0_block14, E0_block15]
  decide +kernel

theorem E0_semantic_kernel_eq_span {code : ℕ} (bound : code < 2 ^ 12) :
    Kernel 12 E0 code ↔
      vector 12 code ∈ Submodule.span (ZMod 2) (generatorSet 12 Egenerators) :=
  kernel_iff_mem_span E0_kernel_eq_span Egenerators_bounded bound

theorem E0_kernel_length : (kernelCodes 12 E0).length = 8 := by
  rw [E0_kernel_eq_span, length_sortCodes, length_spanCodes]
  decide +kernel

theorem E0_kernel_card :
    Fintype.card {code : Fin (2 ^ 12) // Kernel 12 E0 code} = 8 :=
  kernel_card E0_kernel_length

/-- The entire kernel submodule equals the supplied binary linear span. -/
theorem E0_kernelSubmodule_eq_span :
    kernelSubmodule 12 E0 = Submodule.span (ZMod 2) (generatorSet 12 Egenerators) :=
  kernelSubmodule_eq_span E0_kernel_eq_span Egenerators_bounded

/-- Exact dimension of the kernel in the binary vector space. -/
theorem E0_kernel_finrank : Module.finrank (ZMod 2) ↥(kernelSubmodule 12 E0) = 3 :=
  kernelSubmodule_finrank (by simpa using E0_kernel_length)

private theorem Ep0_block0 : kernelBlock 12 Ep0 0 256 =
    [0, 242] := by decide +kernel

private theorem Ep0_block1 : kernelBlock 12 Ep0 256 256 =
    [] := by decide +kernel

private theorem Ep0_block2 : kernelBlock 12 Ep0 512 256 =
    [] := by decide +kernel

private theorem Ep0_block3 : kernelBlock 12 Ep0 768 256 =
    [824, 970] := by decide +kernel

private theorem Ep0_block4 : kernelBlock 12 Ep0 1024 256 =
    [] := by decide +kernel

private theorem Ep0_block5 : kernelBlock 12 Ep0 1280 256 =
    [1378, 1424] := by decide +kernel

private theorem Ep0_block6 : kernelBlock 12 Ep0 1536 256 =
    [1626, 1704] := by decide +kernel

private theorem Ep0_block7 : kernelBlock 12 Ep0 1792 256 =
    [] := by decide +kernel

private theorem Ep0_block8 : kernelBlock 12 Ep0 2048 256 =
    [] := by decide +kernel

private theorem Ep0_block9 : kernelBlock 12 Ep0 2304 256 =
    [2394, 2472] := by decide +kernel

private theorem Ep0_block10 : kernelBlock 12 Ep0 2560 256 =
    [2658, 2704] := by decide +kernel

private theorem Ep0_block11 : kernelBlock 12 Ep0 2816 256 =
    [] := by decide +kernel

private theorem Ep0_block12 : kernelBlock 12 Ep0 3072 256 =
    [3128, 3274] := by decide +kernel

private theorem Ep0_block13 : kernelBlock 12 Ep0 3328 256 =
    [] := by decide +kernel

private theorem Ep0_block14 : kernelBlock 12 Ep0 3584 256 =
    [] := by decide +kernel

private theorem Ep0_block15 : kernelBlock 12 Ep0 3840 256 =
    [3840, 4082] := by decide +kernel

theorem Ep0_kernel_eq_span : kernelCodes 12 Ep0 =
    sortCodes (spanCodes Epgenerators) := by
  rw [kernelCodes_eq_block]
  change kernelBlock 12 Ep0 0 4096 = sortCodes (spanCodes Epgenerators)
  rw [kernelBlock_add 12 Ep0 0 256 3840,
    kernelBlock_add 12 Ep0 256 256 3584,
    kernelBlock_add 12 Ep0 512 256 3328,
    kernelBlock_add 12 Ep0 768 256 3072,
    kernelBlock_add 12 Ep0 1024 256 2816,
    kernelBlock_add 12 Ep0 1280 256 2560,
    kernelBlock_add 12 Ep0 1536 256 2304,
    kernelBlock_add 12 Ep0 1792 256 2048,
    kernelBlock_add 12 Ep0 2048 256 1792,
    kernelBlock_add 12 Ep0 2304 256 1536,
    kernelBlock_add 12 Ep0 2560 256 1280,
    kernelBlock_add 12 Ep0 2816 256 1024,
    kernelBlock_add 12 Ep0 3072 256 768,
    kernelBlock_add 12 Ep0 3328 256 512,
    kernelBlock_add 12 Ep0 3584 256 256]
  rw [Ep0_block0, Ep0_block1, Ep0_block2, Ep0_block3, Ep0_block4, Ep0_block5, Ep0_block6, Ep0_block7, Ep0_block8, Ep0_block9, Ep0_block10, Ep0_block11, Ep0_block12, Ep0_block13, Ep0_block14, Ep0_block15]
  decide +kernel

theorem Ep0_semantic_kernel_eq_span {code : ℕ} (bound : code < 2 ^ 12) :
    Kernel 12 Ep0 code ↔
      vector 12 code ∈ Submodule.span (ZMod 2) (generatorSet 12 Epgenerators) :=
  kernel_iff_mem_span Ep0_kernel_eq_span Epgenerators_bounded bound

theorem Ep0_kernel_length : (kernelCodes 12 Ep0).length = 16 := by
  rw [Ep0_kernel_eq_span, length_sortCodes, length_spanCodes]
  decide +kernel

theorem Ep0_kernel_card :
    Fintype.card {code : Fin (2 ^ 12) // Kernel 12 Ep0 code} = 16 :=
  kernel_card Ep0_kernel_length

/-- The entire kernel submodule equals the supplied binary linear span. -/
theorem Ep0_kernelSubmodule_eq_span :
    kernelSubmodule 12 Ep0 = Submodule.span (ZMod 2) (generatorSet 12 Epgenerators) :=
  kernelSubmodule_eq_span Ep0_kernel_eq_span Epgenerators_bounded

/-- Exact dimension of the kernel in the binary vector space. -/
theorem Ep0_kernel_finrank : Module.finrank (ZMod 2) ↥(kernelSubmodule 12 Ep0) = 4 :=
  kernelSubmodule_finrank (by simpa using Ep0_kernel_length)

private theorem E1_block0 : kernelBlock 12 E1 0 256 =
    [0, 243] := by decide +kernel

private theorem E1_block1 : kernelBlock 12 E1 256 256 =
    [] := by decide +kernel

private theorem E1_block2 : kernelBlock 12 E1 512 256 =
    [] := by decide +kernel

private theorem E1_block3 : kernelBlock 12 E1 768 256 =
    [827, 968] := by decide +kernel

private theorem E1_block4 : kernelBlock 12 E1 1024 256 =
    [] := by decide +kernel

private theorem E1_block5 : kernelBlock 12 E1 1280 256 =
    [] := by decide +kernel

private theorem E1_block6 : kernelBlock 12 E1 1536 256 =
    [] := by decide +kernel

private theorem E1_block7 : kernelBlock 12 E1 1792 256 =
    [] := by decide +kernel

private theorem E1_block8 : kernelBlock 12 E1 2048 256 =
    [] := by decide +kernel

private theorem E1_block9 : kernelBlock 12 E1 2304 256 =
    [] := by decide +kernel

private theorem E1_block10 : kernelBlock 12 E1 2560 256 =
    [] := by decide +kernel

private theorem E1_block11 : kernelBlock 12 E1 2816 256 =
    [] := by decide +kernel

private theorem E1_block12 : kernelBlock 12 E1 3072 256 =
    [3129, 3274] := by decide +kernel

private theorem E1_block13 : kernelBlock 12 E1 3328 256 =
    [] := by decide +kernel

private theorem E1_block14 : kernelBlock 12 E1 3584 256 =
    [] := by decide +kernel

private theorem E1_block15 : kernelBlock 12 E1 3840 256 =
    [3842, 4081] := by decide +kernel

theorem E1_kernel_eq_span : kernelCodes 12 E1 =
    sortCodes (spanCodes Egenerators) := by
  rw [kernelCodes_eq_block]
  change kernelBlock 12 E1 0 4096 = sortCodes (spanCodes Egenerators)
  rw [kernelBlock_add 12 E1 0 256 3840,
    kernelBlock_add 12 E1 256 256 3584,
    kernelBlock_add 12 E1 512 256 3328,
    kernelBlock_add 12 E1 768 256 3072,
    kernelBlock_add 12 E1 1024 256 2816,
    kernelBlock_add 12 E1 1280 256 2560,
    kernelBlock_add 12 E1 1536 256 2304,
    kernelBlock_add 12 E1 1792 256 2048,
    kernelBlock_add 12 E1 2048 256 1792,
    kernelBlock_add 12 E1 2304 256 1536,
    kernelBlock_add 12 E1 2560 256 1280,
    kernelBlock_add 12 E1 2816 256 1024,
    kernelBlock_add 12 E1 3072 256 768,
    kernelBlock_add 12 E1 3328 256 512,
    kernelBlock_add 12 E1 3584 256 256]
  rw [E1_block0, E1_block1, E1_block2, E1_block3, E1_block4, E1_block5, E1_block6, E1_block7, E1_block8, E1_block9, E1_block10, E1_block11, E1_block12, E1_block13, E1_block14, E1_block15]
  decide +kernel

theorem E1_semantic_kernel_eq_span {code : ℕ} (bound : code < 2 ^ 12) :
    Kernel 12 E1 code ↔
      vector 12 code ∈ Submodule.span (ZMod 2) (generatorSet 12 Egenerators) :=
  kernel_iff_mem_span E1_kernel_eq_span Egenerators_bounded bound

theorem E1_kernel_length : (kernelCodes 12 E1).length = 8 := by
  rw [E1_kernel_eq_span, length_sortCodes, length_spanCodes]
  decide +kernel

theorem E1_kernel_card :
    Fintype.card {code : Fin (2 ^ 12) // Kernel 12 E1 code} = 8 :=
  kernel_card E1_kernel_length

/-- The entire kernel submodule equals the supplied binary linear span. -/
theorem E1_kernelSubmodule_eq_span :
    kernelSubmodule 12 E1 = Submodule.span (ZMod 2) (generatorSet 12 Egenerators) :=
  kernelSubmodule_eq_span E1_kernel_eq_span Egenerators_bounded

/-- Exact dimension of the kernel in the binary vector space. -/
theorem E1_kernel_finrank : Module.finrank (ZMod 2) ↥(kernelSubmodule 12 E1) = 3 :=
  kernelSubmodule_finrank (by simpa using E1_kernel_length)

private theorem Ep1_block0 : kernelBlock 12 Ep1 0 256 =
    [0, 242] := by decide +kernel

private theorem Ep1_block1 : kernelBlock 12 Ep1 256 256 =
    [] := by decide +kernel

private theorem Ep1_block2 : kernelBlock 12 Ep1 512 256 =
    [] := by decide +kernel

private theorem Ep1_block3 : kernelBlock 12 Ep1 768 256 =
    [824, 970] := by decide +kernel

private theorem Ep1_block4 : kernelBlock 12 Ep1 1024 256 =
    [] := by decide +kernel

private theorem Ep1_block5 : kernelBlock 12 Ep1 1280 256 =
    [1378, 1424] := by decide +kernel

private theorem Ep1_block6 : kernelBlock 12 Ep1 1536 256 =
    [1626, 1704] := by decide +kernel

private theorem Ep1_block7 : kernelBlock 12 Ep1 1792 256 =
    [] := by decide +kernel

private theorem Ep1_block8 : kernelBlock 12 Ep1 2048 256 =
    [] := by decide +kernel

private theorem Ep1_block9 : kernelBlock 12 Ep1 2304 256 =
    [2394, 2472] := by decide +kernel

private theorem Ep1_block10 : kernelBlock 12 Ep1 2560 256 =
    [2658, 2704] := by decide +kernel

private theorem Ep1_block11 : kernelBlock 12 Ep1 2816 256 =
    [] := by decide +kernel

private theorem Ep1_block12 : kernelBlock 12 Ep1 3072 256 =
    [3128, 3274] := by decide +kernel

private theorem Ep1_block13 : kernelBlock 12 Ep1 3328 256 =
    [] := by decide +kernel

private theorem Ep1_block14 : kernelBlock 12 Ep1 3584 256 =
    [] := by decide +kernel

private theorem Ep1_block15 : kernelBlock 12 Ep1 3840 256 =
    [3840, 4082] := by decide +kernel

theorem Ep1_kernel_eq_span : kernelCodes 12 Ep1 =
    sortCodes (spanCodes Epgenerators) := by
  rw [kernelCodes_eq_block]
  change kernelBlock 12 Ep1 0 4096 = sortCodes (spanCodes Epgenerators)
  rw [kernelBlock_add 12 Ep1 0 256 3840,
    kernelBlock_add 12 Ep1 256 256 3584,
    kernelBlock_add 12 Ep1 512 256 3328,
    kernelBlock_add 12 Ep1 768 256 3072,
    kernelBlock_add 12 Ep1 1024 256 2816,
    kernelBlock_add 12 Ep1 1280 256 2560,
    kernelBlock_add 12 Ep1 1536 256 2304,
    kernelBlock_add 12 Ep1 1792 256 2048,
    kernelBlock_add 12 Ep1 2048 256 1792,
    kernelBlock_add 12 Ep1 2304 256 1536,
    kernelBlock_add 12 Ep1 2560 256 1280,
    kernelBlock_add 12 Ep1 2816 256 1024,
    kernelBlock_add 12 Ep1 3072 256 768,
    kernelBlock_add 12 Ep1 3328 256 512,
    kernelBlock_add 12 Ep1 3584 256 256]
  rw [Ep1_block0, Ep1_block1, Ep1_block2, Ep1_block3, Ep1_block4, Ep1_block5, Ep1_block6, Ep1_block7, Ep1_block8, Ep1_block9, Ep1_block10, Ep1_block11, Ep1_block12, Ep1_block13, Ep1_block14, Ep1_block15]
  decide +kernel

theorem Ep1_semantic_kernel_eq_span {code : ℕ} (bound : code < 2 ^ 12) :
    Kernel 12 Ep1 code ↔
      vector 12 code ∈ Submodule.span (ZMod 2) (generatorSet 12 Epgenerators) :=
  kernel_iff_mem_span Ep1_kernel_eq_span Epgenerators_bounded bound

theorem Ep1_kernel_length : (kernelCodes 12 Ep1).length = 16 := by
  rw [Ep1_kernel_eq_span, length_sortCodes, length_spanCodes]
  decide +kernel

theorem Ep1_kernel_card :
    Fintype.card {code : Fin (2 ^ 12) // Kernel 12 Ep1 code} = 16 :=
  kernel_card Ep1_kernel_length

/-- The entire kernel submodule equals the supplied binary linear span. -/
theorem Ep1_kernelSubmodule_eq_span :
    kernelSubmodule 12 Ep1 = Submodule.span (ZMod 2) (generatorSet 12 Epgenerators) :=
  kernelSubmodule_eq_span Ep1_kernel_eq_span Epgenerators_bounded

/-- Exact dimension of the kernel in the binary vector space. -/
theorem Ep1_kernel_finrank : Module.finrank (ZMod 2) ↥(kernelSubmodule 12 Ep1) = 4 :=
  kernelSubmodule_finrank (by simpa using Ep1_kernel_length)

/-- Independence of the ordered known classes in the binary coordinates. -/
theorem Egenerators_linearIndependent :
    LinearIndependent (ZMod 2) (generatorFamily 12 Egenerators) :=
  generators_linearIndependent E0_kernel_eq_span Egenerators_bounded

theorem Epgenerators_linearIndependent :
    LinearIndependent (ZMod 2) (generatorFamily 12 Epgenerators) :=
  generators_linearIndependent Ep0_kernel_eq_span Epgenerators_bounded

end Rank5

namespace Rank6

def E0 : List ℕ := [2, 3875, 4, 1557, 839, 2139, 1586, 2879, 1961, 1765, 1409, 734]
def Ep0 : List ℕ := [1981, 2, 3613, 1, 3927, 1147, 2610, 2239, 1430, 3036, 241, 164]
def E1 : List ℕ := [2, 3875, 4, 1557, 3255, 1963, 2498, 1231, 2137, 2325, 2673, 3374]
def Ep1 : List ℕ := [1981, 2, 3613, 1, 167, 2955, 1474, 1871, 2662, 1068, 3841, 3924]
def Egenerators : List ℕ := [4081, 3848, 865, 1449]
def Epgenerators : List ℕ := [4080, 248, 3220, 2384]

theorem Egenerators_bounded : ∀ g ∈ Egenerators, g < 2 ^ 12 := by
  simp [Egenerators]

theorem Egenerators_span_nodup : (spanCodes Egenerators).Nodup := by decide +kernel

theorem Epgenerators_bounded : ∀ g ∈ Epgenerators, g < 2 ^ 12 := by
  simp [Epgenerators]

theorem Epgenerators_span_nodup : (spanCodes Epgenerators).Nodup := by decide +kernel

private theorem E0_block0 : kernelBlock 12 E0 0 256 =
    [0, 249] := by decide +kernel

private theorem E0_block1 : kernelBlock 12 E0 256 256 =
    [] := by decide +kernel

private theorem E0_block2 : kernelBlock 12 E0 512 256 =
    [] := by decide +kernel

private theorem E0_block3 : kernelBlock 12 E0 768 256 =
    [865, 920] := by decide +kernel

private theorem E0_block4 : kernelBlock 12 E0 1024 256 =
    [] := by decide +kernel

private theorem E0_block5 : kernelBlock 12 E0 1280 256 =
    [1360, 1449] := by decide +kernel

private theorem E0_block6 : kernelBlock 12 E0 1536 256 =
    [1585, 1736] := by decide +kernel

private theorem E0_block7 : kernelBlock 12 E0 1792 256 =
    [] := by decide +kernel

private theorem E0_block8 : kernelBlock 12 E0 2048 256 =
    [] := by decide +kernel

private theorem E0_block9 : kernelBlock 12 E0 2304 256 =
    [2361, 2496] := by decide +kernel

private theorem E0_block10 : kernelBlock 12 E0 2560 256 =
    [2648, 2721] := by decide +kernel

private theorem E0_block11 : kernelBlock 12 E0 2816 256 =
    [] := by decide +kernel

private theorem E0_block12 : kernelBlock 12 E0 3072 256 =
    [3177, 3216] := by decide +kernel

private theorem E0_block13 : kernelBlock 12 E0 3328 256 =
    [] := by decide +kernel

private theorem E0_block14 : kernelBlock 12 E0 3584 256 =
    [] := by decide +kernel

private theorem E0_block15 : kernelBlock 12 E0 3840 256 =
    [3848, 4081] := by decide +kernel

theorem E0_kernel_eq_span : kernelCodes 12 E0 =
    sortCodes (spanCodes Egenerators) := by
  rw [kernelCodes_eq_block]
  change kernelBlock 12 E0 0 4096 = sortCodes (spanCodes Egenerators)
  rw [kernelBlock_add 12 E0 0 256 3840,
    kernelBlock_add 12 E0 256 256 3584,
    kernelBlock_add 12 E0 512 256 3328,
    kernelBlock_add 12 E0 768 256 3072,
    kernelBlock_add 12 E0 1024 256 2816,
    kernelBlock_add 12 E0 1280 256 2560,
    kernelBlock_add 12 E0 1536 256 2304,
    kernelBlock_add 12 E0 1792 256 2048,
    kernelBlock_add 12 E0 2048 256 1792,
    kernelBlock_add 12 E0 2304 256 1536,
    kernelBlock_add 12 E0 2560 256 1280,
    kernelBlock_add 12 E0 2816 256 1024,
    kernelBlock_add 12 E0 3072 256 768,
    kernelBlock_add 12 E0 3328 256 512,
    kernelBlock_add 12 E0 3584 256 256]
  rw [E0_block0, E0_block1, E0_block2, E0_block3, E0_block4, E0_block5, E0_block6, E0_block7, E0_block8, E0_block9, E0_block10, E0_block11, E0_block12, E0_block13, E0_block14, E0_block15]
  decide +kernel

theorem E0_semantic_kernel_eq_span {code : ℕ} (bound : code < 2 ^ 12) :
    Kernel 12 E0 code ↔
      vector 12 code ∈ Submodule.span (ZMod 2) (generatorSet 12 Egenerators) :=
  kernel_iff_mem_span E0_kernel_eq_span Egenerators_bounded bound

theorem E0_kernel_length : (kernelCodes 12 E0).length = 16 := by
  rw [E0_kernel_eq_span, length_sortCodes, length_spanCodes]
  decide +kernel

theorem E0_kernel_card :
    Fintype.card {code : Fin (2 ^ 12) // Kernel 12 E0 code} = 16 :=
  kernel_card E0_kernel_length

/-- The entire kernel submodule equals the supplied binary linear span. -/
theorem E0_kernelSubmodule_eq_span :
    kernelSubmodule 12 E0 = Submodule.span (ZMod 2) (generatorSet 12 Egenerators) :=
  kernelSubmodule_eq_span E0_kernel_eq_span Egenerators_bounded

/-- Exact dimension of the kernel in the binary vector space. -/
theorem E0_kernel_finrank : Module.finrank (ZMod 2) ↥(kernelSubmodule 12 E0) = 4 :=
  kernelSubmodule_finrank (by simpa using E0_kernel_length)

private theorem Ep0_block0 : kernelBlock 12 Ep0 0 256 =
    [0, 248] := by decide +kernel

private theorem Ep0_block1 : kernelBlock 12 Ep0 256 256 =
    [] := by decide +kernel

private theorem Ep0_block2 : kernelBlock 12 Ep0 512 256 =
    [] := by decide +kernel

private theorem Ep0_block3 : kernelBlock 12 Ep0 768 256 =
    [868, 924] := by decide +kernel

private theorem Ep0_block4 : kernelBlock 12 Ep0 1024 256 =
    [] := by decide +kernel

private theorem Ep0_block5 : kernelBlock 12 Ep0 1280 256 =
    [1340, 1476] := by decide +kernel

private theorem Ep0_block6 : kernelBlock 12 Ep0 1536 256 =
    [1624, 1696] := by decide +kernel

private theorem Ep0_block7 : kernelBlock 12 Ep0 1792 256 =
    [] := by decide +kernel

private theorem Ep0_block8 : kernelBlock 12 Ep0 2048 256 =
    [] := by decide +kernel

private theorem Ep0_block9 : kernelBlock 12 Ep0 2304 256 =
    [2384, 2472] := by decide +kernel

private theorem Ep0_block10 : kernelBlock 12 Ep0 2560 256 =
    [2612, 2764] := by decide +kernel

private theorem Ep0_block11 : kernelBlock 12 Ep0 2816 256 =
    [] := by decide +kernel

private theorem Ep0_block12 : kernelBlock 12 Ep0 3072 256 =
    [3180, 3220] := by decide +kernel

private theorem Ep0_block13 : kernelBlock 12 Ep0 3328 256 =
    [] := by decide +kernel

private theorem Ep0_block14 : kernelBlock 12 Ep0 3584 256 =
    [] := by decide +kernel

private theorem Ep0_block15 : kernelBlock 12 Ep0 3840 256 =
    [3848, 4080] := by decide +kernel

theorem Ep0_kernel_eq_span : kernelCodes 12 Ep0 =
    sortCodes (spanCodes Epgenerators) := by
  rw [kernelCodes_eq_block]
  change kernelBlock 12 Ep0 0 4096 = sortCodes (spanCodes Epgenerators)
  rw [kernelBlock_add 12 Ep0 0 256 3840,
    kernelBlock_add 12 Ep0 256 256 3584,
    kernelBlock_add 12 Ep0 512 256 3328,
    kernelBlock_add 12 Ep0 768 256 3072,
    kernelBlock_add 12 Ep0 1024 256 2816,
    kernelBlock_add 12 Ep0 1280 256 2560,
    kernelBlock_add 12 Ep0 1536 256 2304,
    kernelBlock_add 12 Ep0 1792 256 2048,
    kernelBlock_add 12 Ep0 2048 256 1792,
    kernelBlock_add 12 Ep0 2304 256 1536,
    kernelBlock_add 12 Ep0 2560 256 1280,
    kernelBlock_add 12 Ep0 2816 256 1024,
    kernelBlock_add 12 Ep0 3072 256 768,
    kernelBlock_add 12 Ep0 3328 256 512,
    kernelBlock_add 12 Ep0 3584 256 256]
  rw [Ep0_block0, Ep0_block1, Ep0_block2, Ep0_block3, Ep0_block4, Ep0_block5, Ep0_block6, Ep0_block7, Ep0_block8, Ep0_block9, Ep0_block10, Ep0_block11, Ep0_block12, Ep0_block13, Ep0_block14, Ep0_block15]
  decide +kernel

theorem Ep0_semantic_kernel_eq_span {code : ℕ} (bound : code < 2 ^ 12) :
    Kernel 12 Ep0 code ↔
      vector 12 code ∈ Submodule.span (ZMod 2) (generatorSet 12 Epgenerators) :=
  kernel_iff_mem_span Ep0_kernel_eq_span Epgenerators_bounded bound

theorem Ep0_kernel_length : (kernelCodes 12 Ep0).length = 16 := by
  rw [Ep0_kernel_eq_span, length_sortCodes, length_spanCodes]
  decide +kernel

theorem Ep0_kernel_card :
    Fintype.card {code : Fin (2 ^ 12) // Kernel 12 Ep0 code} = 16 :=
  kernel_card Ep0_kernel_length

/-- The entire kernel submodule equals the supplied binary linear span. -/
theorem Ep0_kernelSubmodule_eq_span :
    kernelSubmodule 12 Ep0 = Submodule.span (ZMod 2) (generatorSet 12 Epgenerators) :=
  kernelSubmodule_eq_span Ep0_kernel_eq_span Epgenerators_bounded

/-- Exact dimension of the kernel in the binary vector space. -/
theorem Ep0_kernel_finrank : Module.finrank (ZMod 2) ↥(kernelSubmodule 12 Ep0) = 4 :=
  kernelSubmodule_finrank (by simpa using Ep0_kernel_length)

private theorem E1_block0 : kernelBlock 12 E1 0 256 =
    [0, 249] := by decide +kernel

private theorem E1_block1 : kernelBlock 12 E1 256 256 =
    [] := by decide +kernel

private theorem E1_block2 : kernelBlock 12 E1 512 256 =
    [] := by decide +kernel

private theorem E1_block3 : kernelBlock 12 E1 768 256 =
    [865, 920] := by decide +kernel

private theorem E1_block4 : kernelBlock 12 E1 1024 256 =
    [] := by decide +kernel

private theorem E1_block5 : kernelBlock 12 E1 1280 256 =
    [1360, 1449] := by decide +kernel

private theorem E1_block6 : kernelBlock 12 E1 1536 256 =
    [1585, 1736] := by decide +kernel

private theorem E1_block7 : kernelBlock 12 E1 1792 256 =
    [] := by decide +kernel

private theorem E1_block8 : kernelBlock 12 E1 2048 256 =
    [] := by decide +kernel

private theorem E1_block9 : kernelBlock 12 E1 2304 256 =
    [2361, 2496] := by decide +kernel

private theorem E1_block10 : kernelBlock 12 E1 2560 256 =
    [2648, 2721] := by decide +kernel

private theorem E1_block11 : kernelBlock 12 E1 2816 256 =
    [] := by decide +kernel

private theorem E1_block12 : kernelBlock 12 E1 3072 256 =
    [3177, 3216] := by decide +kernel

private theorem E1_block13 : kernelBlock 12 E1 3328 256 =
    [] := by decide +kernel

private theorem E1_block14 : kernelBlock 12 E1 3584 256 =
    [] := by decide +kernel

private theorem E1_block15 : kernelBlock 12 E1 3840 256 =
    [3848, 4081] := by decide +kernel

theorem E1_kernel_eq_span : kernelCodes 12 E1 =
    sortCodes (spanCodes Egenerators) := by
  rw [kernelCodes_eq_block]
  change kernelBlock 12 E1 0 4096 = sortCodes (spanCodes Egenerators)
  rw [kernelBlock_add 12 E1 0 256 3840,
    kernelBlock_add 12 E1 256 256 3584,
    kernelBlock_add 12 E1 512 256 3328,
    kernelBlock_add 12 E1 768 256 3072,
    kernelBlock_add 12 E1 1024 256 2816,
    kernelBlock_add 12 E1 1280 256 2560,
    kernelBlock_add 12 E1 1536 256 2304,
    kernelBlock_add 12 E1 1792 256 2048,
    kernelBlock_add 12 E1 2048 256 1792,
    kernelBlock_add 12 E1 2304 256 1536,
    kernelBlock_add 12 E1 2560 256 1280,
    kernelBlock_add 12 E1 2816 256 1024,
    kernelBlock_add 12 E1 3072 256 768,
    kernelBlock_add 12 E1 3328 256 512,
    kernelBlock_add 12 E1 3584 256 256]
  rw [E1_block0, E1_block1, E1_block2, E1_block3, E1_block4, E1_block5, E1_block6, E1_block7, E1_block8, E1_block9, E1_block10, E1_block11, E1_block12, E1_block13, E1_block14, E1_block15]
  decide +kernel

theorem E1_semantic_kernel_eq_span {code : ℕ} (bound : code < 2 ^ 12) :
    Kernel 12 E1 code ↔
      vector 12 code ∈ Submodule.span (ZMod 2) (generatorSet 12 Egenerators) :=
  kernel_iff_mem_span E1_kernel_eq_span Egenerators_bounded bound

theorem E1_kernel_length : (kernelCodes 12 E1).length = 16 := by
  rw [E1_kernel_eq_span, length_sortCodes, length_spanCodes]
  decide +kernel

theorem E1_kernel_card :
    Fintype.card {code : Fin (2 ^ 12) // Kernel 12 E1 code} = 16 :=
  kernel_card E1_kernel_length

/-- The entire kernel submodule equals the supplied binary linear span. -/
theorem E1_kernelSubmodule_eq_span :
    kernelSubmodule 12 E1 = Submodule.span (ZMod 2) (generatorSet 12 Egenerators) :=
  kernelSubmodule_eq_span E1_kernel_eq_span Egenerators_bounded

/-- Exact dimension of the kernel in the binary vector space. -/
theorem E1_kernel_finrank : Module.finrank (ZMod 2) ↥(kernelSubmodule 12 E1) = 4 :=
  kernelSubmodule_finrank (by simpa using E1_kernel_length)

private theorem Ep1_block0 : kernelBlock 12 Ep1 0 256 =
    [0, 248] := by decide +kernel

private theorem Ep1_block1 : kernelBlock 12 Ep1 256 256 =
    [] := by decide +kernel

private theorem Ep1_block2 : kernelBlock 12 Ep1 512 256 =
    [] := by decide +kernel

private theorem Ep1_block3 : kernelBlock 12 Ep1 768 256 =
    [868, 924] := by decide +kernel

private theorem Ep1_block4 : kernelBlock 12 Ep1 1024 256 =
    [] := by decide +kernel

private theorem Ep1_block5 : kernelBlock 12 Ep1 1280 256 =
    [1340, 1476] := by decide +kernel

private theorem Ep1_block6 : kernelBlock 12 Ep1 1536 256 =
    [1624, 1696] := by decide +kernel

private theorem Ep1_block7 : kernelBlock 12 Ep1 1792 256 =
    [] := by decide +kernel

private theorem Ep1_block8 : kernelBlock 12 Ep1 2048 256 =
    [] := by decide +kernel

private theorem Ep1_block9 : kernelBlock 12 Ep1 2304 256 =
    [2384, 2472] := by decide +kernel

private theorem Ep1_block10 : kernelBlock 12 Ep1 2560 256 =
    [2612, 2764] := by decide +kernel

private theorem Ep1_block11 : kernelBlock 12 Ep1 2816 256 =
    [] := by decide +kernel

private theorem Ep1_block12 : kernelBlock 12 Ep1 3072 256 =
    [3180, 3220] := by decide +kernel

private theorem Ep1_block13 : kernelBlock 12 Ep1 3328 256 =
    [] := by decide +kernel

private theorem Ep1_block14 : kernelBlock 12 Ep1 3584 256 =
    [] := by decide +kernel

private theorem Ep1_block15 : kernelBlock 12 Ep1 3840 256 =
    [3848, 4080] := by decide +kernel

theorem Ep1_kernel_eq_span : kernelCodes 12 Ep1 =
    sortCodes (spanCodes Epgenerators) := by
  rw [kernelCodes_eq_block]
  change kernelBlock 12 Ep1 0 4096 = sortCodes (spanCodes Epgenerators)
  rw [kernelBlock_add 12 Ep1 0 256 3840,
    kernelBlock_add 12 Ep1 256 256 3584,
    kernelBlock_add 12 Ep1 512 256 3328,
    kernelBlock_add 12 Ep1 768 256 3072,
    kernelBlock_add 12 Ep1 1024 256 2816,
    kernelBlock_add 12 Ep1 1280 256 2560,
    kernelBlock_add 12 Ep1 1536 256 2304,
    kernelBlock_add 12 Ep1 1792 256 2048,
    kernelBlock_add 12 Ep1 2048 256 1792,
    kernelBlock_add 12 Ep1 2304 256 1536,
    kernelBlock_add 12 Ep1 2560 256 1280,
    kernelBlock_add 12 Ep1 2816 256 1024,
    kernelBlock_add 12 Ep1 3072 256 768,
    kernelBlock_add 12 Ep1 3328 256 512,
    kernelBlock_add 12 Ep1 3584 256 256]
  rw [Ep1_block0, Ep1_block1, Ep1_block2, Ep1_block3, Ep1_block4, Ep1_block5, Ep1_block6, Ep1_block7, Ep1_block8, Ep1_block9, Ep1_block10, Ep1_block11, Ep1_block12, Ep1_block13, Ep1_block14, Ep1_block15]
  decide +kernel

theorem Ep1_semantic_kernel_eq_span {code : ℕ} (bound : code < 2 ^ 12) :
    Kernel 12 Ep1 code ↔
      vector 12 code ∈ Submodule.span (ZMod 2) (generatorSet 12 Epgenerators) :=
  kernel_iff_mem_span Ep1_kernel_eq_span Epgenerators_bounded bound

theorem Ep1_kernel_length : (kernelCodes 12 Ep1).length = 16 := by
  rw [Ep1_kernel_eq_span, length_sortCodes, length_spanCodes]
  decide +kernel

theorem Ep1_kernel_card :
    Fintype.card {code : Fin (2 ^ 12) // Kernel 12 Ep1 code} = 16 :=
  kernel_card Ep1_kernel_length

/-- The entire kernel submodule equals the supplied binary linear span. -/
theorem Ep1_kernelSubmodule_eq_span :
    kernelSubmodule 12 Ep1 = Submodule.span (ZMod 2) (generatorSet 12 Epgenerators) :=
  kernelSubmodule_eq_span Ep1_kernel_eq_span Epgenerators_bounded

/-- Exact dimension of the kernel in the binary vector space. -/
theorem Ep1_kernel_finrank : Module.finrank (ZMod 2) ↥(kernelSubmodule 12 Ep1) = 4 :=
  kernelSubmodule_finrank (by simpa using Ep1_kernel_length)

/-- Independence of the ordered known classes in the binary coordinates. -/
theorem Egenerators_linearIndependent :
    LinearIndependent (ZMod 2) (generatorFamily 12 Egenerators) :=
  generators_linearIndependent E0_kernel_eq_span Egenerators_bounded

theorem Epgenerators_linearIndependent :
    LinearIndependent (ZMod 2) (generatorFamily 12 Epgenerators) :=
  generators_linearIndependent Ep0_kernel_eq_span Epgenerators_bounded

end Rank6

namespace Rank7

def E0 : List ℕ := [4943, 8020, 195, 4, 4896, 219, 340, 3583, 7945, 7734, 466, 3121]
def Ep0 : List ℕ := [7705, 4117, 8, 7626, 16, 1, 5408, 6811, 2388, 6399, 5503, 5914, 5914, 5479]
def E1 : List ℕ := [4943, 8020, 195, 4, 3264, 7995, 7860, 4639, 233, 470, 7730, 5073]
def Ep1 : List ℕ := [7705, 4117, 8, 7626, 16, 1, 2752, 1403, 5812, 1823, 2719, 2298, 2298, 2695]
def Egenerators : List ℕ := [8163, 483, 6306, 3291, 6554]
def Epgenerators : List ℕ := [8164, 482, 1696, 2848]

theorem Egenerators_bounded : ∀ g ∈ Egenerators, g < 2 ^ 13 := by
  simp [Egenerators]

theorem Egenerators_span_nodup : (spanCodes Egenerators).Nodup := by decide +kernel

theorem Epgenerators_bounded : ∀ g ∈ Epgenerators, g < 2 ^ 13 := by
  simp [Epgenerators]

theorem Epgenerators_span_nodup : (spanCodes Epgenerators).Nodup := by decide +kernel

private theorem E0_block0 : kernelBlock 13 E0 0 256 =
    [0, 219] := by decide +kernel

private theorem E0_block1 : kernelBlock 13 E0 256 256 =
    [312, 483] := by decide +kernel

private theorem E0_block2 : kernelBlock 13 E0 512 256 =
    [] := by decide +kernel

private theorem E0_block3 : kernelBlock 13 E0 768 256 =
    [] := by decide +kernel

private theorem E0_block4 : kernelBlock 13 E0 1024 256 =
    [] := by decide +kernel

private theorem E0_block5 : kernelBlock 13 E0 1280 256 =
    [] := by decide +kernel

private theorem E0_block6 : kernelBlock 13 E0 1536 256 =
    [1657, 1698] := by decide +kernel

private theorem E0_block7 : kernelBlock 13 E0 1792 256 =
    [1857, 1946] := by decide +kernel

private theorem E0_block8 : kernelBlock 13 E0 2048 256 =
    [] := by decide +kernel

private theorem E0_block9 : kernelBlock 13 E0 2304 256 =
    [] := by decide +kernel

private theorem E0_block10 : kernelBlock 13 E0 2560 256 =
    [2681, 2722] := by decide +kernel

private theorem E0_block11 : kernelBlock 13 E0 2816 256 =
    [2881, 2970] := by decide +kernel

private theorem E0_block12 : kernelBlock 13 E0 3072 256 =
    [3072, 3291] := by decide +kernel

private theorem E0_block13 : kernelBlock 13 E0 3328 256 =
    [3384, 3555] := by decide +kernel

private theorem E0_block14 : kernelBlock 13 E0 3584 256 =
    [] := by decide +kernel

private theorem E0_block15 : kernelBlock 13 E0 3840 256 =
    [] := by decide +kernel

private theorem E0_block16 : kernelBlock 13 E0 4096 256 =
    [] := by decide +kernel

private theorem E0_block17 : kernelBlock 13 E0 4352 256 =
    [] := by decide +kernel

private theorem E0_block18 : kernelBlock 13 E0 4608 256 =
    [4608, 4827] := by decide +kernel

private theorem E0_block19 : kernelBlock 13 E0 4864 256 =
    [4920, 5091] := by decide +kernel

private theorem E0_block20 : kernelBlock 13 E0 5120 256 =
    [5241, 5282] := by decide +kernel

private theorem E0_block21 : kernelBlock 13 E0 5376 256 =
    [5441, 5530] := by decide +kernel

private theorem E0_block22 : kernelBlock 13 E0 5632 256 =
    [] := by decide +kernel

private theorem E0_block23 : kernelBlock 13 E0 5888 256 =
    [] := by decide +kernel

private theorem E0_block24 : kernelBlock 13 E0 6144 256 =
    [6265, 6306] := by decide +kernel

private theorem E0_block25 : kernelBlock 13 E0 6400 256 =
    [6465, 6554] := by decide +kernel

private theorem E0_block26 : kernelBlock 13 E0 6656 256 =
    [] := by decide +kernel

private theorem E0_block27 : kernelBlock 13 E0 6912 256 =
    [] := by decide +kernel

private theorem E0_block28 : kernelBlock 13 E0 7168 256 =
    [] := by decide +kernel

private theorem E0_block29 : kernelBlock 13 E0 7424 256 =
    [] := by decide +kernel

private theorem E0_block30 : kernelBlock 13 E0 7680 256 =
    [7680, 7899] := by decide +kernel

private theorem E0_block31 : kernelBlock 13 E0 7936 256 =
    [7992, 8163] := by decide +kernel

theorem E0_kernel_eq_span : kernelCodes 13 E0 =
    sortCodes (spanCodes Egenerators) := by
  rw [kernelCodes_eq_block]
  change kernelBlock 13 E0 0 8192 = sortCodes (spanCodes Egenerators)
  rw [kernelBlock_add 13 E0 0 256 7936,
    kernelBlock_add 13 E0 256 256 7680,
    kernelBlock_add 13 E0 512 256 7424,
    kernelBlock_add 13 E0 768 256 7168,
    kernelBlock_add 13 E0 1024 256 6912,
    kernelBlock_add 13 E0 1280 256 6656,
    kernelBlock_add 13 E0 1536 256 6400,
    kernelBlock_add 13 E0 1792 256 6144,
    kernelBlock_add 13 E0 2048 256 5888,
    kernelBlock_add 13 E0 2304 256 5632,
    kernelBlock_add 13 E0 2560 256 5376,
    kernelBlock_add 13 E0 2816 256 5120,
    kernelBlock_add 13 E0 3072 256 4864,
    kernelBlock_add 13 E0 3328 256 4608,
    kernelBlock_add 13 E0 3584 256 4352,
    kernelBlock_add 13 E0 3840 256 4096,
    kernelBlock_add 13 E0 4096 256 3840,
    kernelBlock_add 13 E0 4352 256 3584,
    kernelBlock_add 13 E0 4608 256 3328,
    kernelBlock_add 13 E0 4864 256 3072,
    kernelBlock_add 13 E0 5120 256 2816,
    kernelBlock_add 13 E0 5376 256 2560,
    kernelBlock_add 13 E0 5632 256 2304,
    kernelBlock_add 13 E0 5888 256 2048,
    kernelBlock_add 13 E0 6144 256 1792,
    kernelBlock_add 13 E0 6400 256 1536,
    kernelBlock_add 13 E0 6656 256 1280,
    kernelBlock_add 13 E0 6912 256 1024,
    kernelBlock_add 13 E0 7168 256 768,
    kernelBlock_add 13 E0 7424 256 512,
    kernelBlock_add 13 E0 7680 256 256]
  rw [E0_block0, E0_block1, E0_block2, E0_block3, E0_block4, E0_block5, E0_block6, E0_block7, E0_block8, E0_block9, E0_block10, E0_block11, E0_block12, E0_block13, E0_block14, E0_block15, E0_block16, E0_block17, E0_block18, E0_block19, E0_block20, E0_block21, E0_block22, E0_block23, E0_block24, E0_block25, E0_block26, E0_block27, E0_block28, E0_block29, E0_block30, E0_block31]
  decide +kernel

theorem E0_semantic_kernel_eq_span {code : ℕ} (bound : code < 2 ^ 13) :
    Kernel 13 E0 code ↔
      vector 13 code ∈ Submodule.span (ZMod 2) (generatorSet 13 Egenerators) :=
  kernel_iff_mem_span E0_kernel_eq_span Egenerators_bounded bound

theorem E0_kernel_length : (kernelCodes 13 E0).length = 32 := by
  rw [E0_kernel_eq_span, length_sortCodes, length_spanCodes]
  decide +kernel

theorem E0_kernel_card :
    Fintype.card {code : Fin (2 ^ 13) // Kernel 13 E0 code} = 32 :=
  kernel_card E0_kernel_length

/-- The entire kernel submodule equals the supplied binary linear span. -/
theorem E0_kernelSubmodule_eq_span :
    kernelSubmodule 13 E0 = Submodule.span (ZMod 2) (generatorSet 13 Egenerators) :=
  kernelSubmodule_eq_span E0_kernel_eq_span Egenerators_bounded

/-- Exact dimension of the kernel in the binary vector space. -/
theorem E0_kernel_finrank : Module.finrank (ZMod 2) ↥(kernelSubmodule 13 E0) = 5 :=
  kernelSubmodule_finrank (by simpa using E0_kernel_length)

private theorem Ep0_block0 : kernelBlock 13 Ep0 0 256 =
    [0] := by decide +kernel

private theorem Ep0_block1 : kernelBlock 13 Ep0 256 256 =
    [482] := by decide +kernel

private theorem Ep0_block2 : kernelBlock 13 Ep0 512 256 =
    [] := by decide +kernel

private theorem Ep0_block3 : kernelBlock 13 Ep0 768 256 =
    [] := by decide +kernel

private theorem Ep0_block4 : kernelBlock 13 Ep0 1024 256 =
    [] := by decide +kernel

private theorem Ep0_block5 : kernelBlock 13 Ep0 1280 256 =
    [] := by decide +kernel

private theorem Ep0_block6 : kernelBlock 13 Ep0 1536 256 =
    [1696] := by decide +kernel

private theorem Ep0_block7 : kernelBlock 13 Ep0 1792 256 =
    [1858] := by decide +kernel

private theorem Ep0_block8 : kernelBlock 13 Ep0 2048 256 =
    [] := by decide +kernel

private theorem Ep0_block9 : kernelBlock 13 Ep0 2304 256 =
    [] := by decide +kernel

private theorem Ep0_block10 : kernelBlock 13 Ep0 2560 256 =
    [2754] := by decide +kernel

private theorem Ep0_block11 : kernelBlock 13 Ep0 2816 256 =
    [2848] := by decide +kernel

private theorem Ep0_block12 : kernelBlock 13 Ep0 3072 256 =
    [3170] := by decide +kernel

private theorem Ep0_block13 : kernelBlock 13 Ep0 3328 256 =
    [3456] := by decide +kernel

private theorem Ep0_block14 : kernelBlock 13 Ep0 3584 256 =
    [] := by decide +kernel

private theorem Ep0_block15 : kernelBlock 13 Ep0 3840 256 =
    [] := by decide +kernel

private theorem Ep0_block16 : kernelBlock 13 Ep0 4096 256 =
    [] := by decide +kernel

private theorem Ep0_block17 : kernelBlock 13 Ep0 4352 256 =
    [] := by decide +kernel

private theorem Ep0_block18 : kernelBlock 13 Ep0 4608 256 =
    [4708] := by decide +kernel

private theorem Ep0_block19 : kernelBlock 13 Ep0 4864 256 =
    [4998] := by decide +kernel

private theorem Ep0_block20 : kernelBlock 13 Ep0 5120 256 =
    [5316] := by decide +kernel

private theorem Ep0_block21 : kernelBlock 13 Ep0 5376 256 =
    [5414] := by decide +kernel

private theorem Ep0_block22 : kernelBlock 13 Ep0 5632 256 =
    [] := by decide +kernel

private theorem Ep0_block23 : kernelBlock 13 Ep0 5888 256 =
    [] := by decide +kernel

private theorem Ep0_block24 : kernelBlock 13 Ep0 6144 256 =
    [6310] := by decide +kernel

private theorem Ep0_block25 : kernelBlock 13 Ep0 6400 256 =
    [6468] := by decide +kernel

private theorem Ep0_block26 : kernelBlock 13 Ep0 6656 256 =
    [] := by decide +kernel

private theorem Ep0_block27 : kernelBlock 13 Ep0 6912 256 =
    [] := by decide +kernel

private theorem Ep0_block28 : kernelBlock 13 Ep0 7168 256 =
    [] := by decide +kernel

private theorem Ep0_block29 : kernelBlock 13 Ep0 7424 256 =
    [] := by decide +kernel

private theorem Ep0_block30 : kernelBlock 13 Ep0 7680 256 =
    [7686] := by decide +kernel

private theorem Ep0_block31 : kernelBlock 13 Ep0 7936 256 =
    [8164] := by decide +kernel

theorem Ep0_kernel_eq_span : kernelCodes 13 Ep0 =
    sortCodes (spanCodes Epgenerators) := by
  rw [kernelCodes_eq_block]
  change kernelBlock 13 Ep0 0 8192 = sortCodes (spanCodes Epgenerators)
  rw [kernelBlock_add 13 Ep0 0 256 7936,
    kernelBlock_add 13 Ep0 256 256 7680,
    kernelBlock_add 13 Ep0 512 256 7424,
    kernelBlock_add 13 Ep0 768 256 7168,
    kernelBlock_add 13 Ep0 1024 256 6912,
    kernelBlock_add 13 Ep0 1280 256 6656,
    kernelBlock_add 13 Ep0 1536 256 6400,
    kernelBlock_add 13 Ep0 1792 256 6144,
    kernelBlock_add 13 Ep0 2048 256 5888,
    kernelBlock_add 13 Ep0 2304 256 5632,
    kernelBlock_add 13 Ep0 2560 256 5376,
    kernelBlock_add 13 Ep0 2816 256 5120,
    kernelBlock_add 13 Ep0 3072 256 4864,
    kernelBlock_add 13 Ep0 3328 256 4608,
    kernelBlock_add 13 Ep0 3584 256 4352,
    kernelBlock_add 13 Ep0 3840 256 4096,
    kernelBlock_add 13 Ep0 4096 256 3840,
    kernelBlock_add 13 Ep0 4352 256 3584,
    kernelBlock_add 13 Ep0 4608 256 3328,
    kernelBlock_add 13 Ep0 4864 256 3072,
    kernelBlock_add 13 Ep0 5120 256 2816,
    kernelBlock_add 13 Ep0 5376 256 2560,
    kernelBlock_add 13 Ep0 5632 256 2304,
    kernelBlock_add 13 Ep0 5888 256 2048,
    kernelBlock_add 13 Ep0 6144 256 1792,
    kernelBlock_add 13 Ep0 6400 256 1536,
    kernelBlock_add 13 Ep0 6656 256 1280,
    kernelBlock_add 13 Ep0 6912 256 1024,
    kernelBlock_add 13 Ep0 7168 256 768,
    kernelBlock_add 13 Ep0 7424 256 512,
    kernelBlock_add 13 Ep0 7680 256 256]
  rw [Ep0_block0, Ep0_block1, Ep0_block2, Ep0_block3, Ep0_block4, Ep0_block5, Ep0_block6, Ep0_block7, Ep0_block8, Ep0_block9, Ep0_block10, Ep0_block11, Ep0_block12, Ep0_block13, Ep0_block14, Ep0_block15, Ep0_block16, Ep0_block17, Ep0_block18, Ep0_block19, Ep0_block20, Ep0_block21, Ep0_block22, Ep0_block23, Ep0_block24, Ep0_block25, Ep0_block26, Ep0_block27, Ep0_block28, Ep0_block29, Ep0_block30, Ep0_block31]
  decide +kernel

theorem Ep0_semantic_kernel_eq_span {code : ℕ} (bound : code < 2 ^ 13) :
    Kernel 13 Ep0 code ↔
      vector 13 code ∈ Submodule.span (ZMod 2) (generatorSet 13 Epgenerators) :=
  kernel_iff_mem_span Ep0_kernel_eq_span Epgenerators_bounded bound

theorem Ep0_kernel_length : (kernelCodes 13 Ep0).length = 16 := by
  rw [Ep0_kernel_eq_span, length_sortCodes, length_spanCodes]
  decide +kernel

theorem Ep0_kernel_card :
    Fintype.card {code : Fin (2 ^ 13) // Kernel 13 Ep0 code} = 16 :=
  kernel_card Ep0_kernel_length

/-- The entire kernel submodule equals the supplied binary linear span. -/
theorem Ep0_kernelSubmodule_eq_span :
    kernelSubmodule 13 Ep0 = Submodule.span (ZMod 2) (generatorSet 13 Epgenerators) :=
  kernelSubmodule_eq_span Ep0_kernel_eq_span Epgenerators_bounded

/-- Exact dimension of the kernel in the binary vector space. -/
theorem Ep0_kernel_finrank : Module.finrank (ZMod 2) ↥(kernelSubmodule 13 Ep0) = 4 :=
  kernelSubmodule_finrank (by simpa using Ep0_kernel_length)

private theorem E1_block0 : kernelBlock 13 E1 0 256 =
    [0, 219] := by decide +kernel

private theorem E1_block1 : kernelBlock 13 E1 256 256 =
    [312, 483] := by decide +kernel

private theorem E1_block2 : kernelBlock 13 E1 512 256 =
    [] := by decide +kernel

private theorem E1_block3 : kernelBlock 13 E1 768 256 =
    [] := by decide +kernel

private theorem E1_block4 : kernelBlock 13 E1 1024 256 =
    [] := by decide +kernel

private theorem E1_block5 : kernelBlock 13 E1 1280 256 =
    [] := by decide +kernel

private theorem E1_block6 : kernelBlock 13 E1 1536 256 =
    [1657, 1698] := by decide +kernel

private theorem E1_block7 : kernelBlock 13 E1 1792 256 =
    [1857, 1946] := by decide +kernel

private theorem E1_block8 : kernelBlock 13 E1 2048 256 =
    [] := by decide +kernel

private theorem E1_block9 : kernelBlock 13 E1 2304 256 =
    [] := by decide +kernel

private theorem E1_block10 : kernelBlock 13 E1 2560 256 =
    [2681, 2722] := by decide +kernel

private theorem E1_block11 : kernelBlock 13 E1 2816 256 =
    [2881, 2970] := by decide +kernel

private theorem E1_block12 : kernelBlock 13 E1 3072 256 =
    [3072, 3291] := by decide +kernel

private theorem E1_block13 : kernelBlock 13 E1 3328 256 =
    [3384, 3555] := by decide +kernel

private theorem E1_block14 : kernelBlock 13 E1 3584 256 =
    [] := by decide +kernel

private theorem E1_block15 : kernelBlock 13 E1 3840 256 =
    [] := by decide +kernel

private theorem E1_block16 : kernelBlock 13 E1 4096 256 =
    [] := by decide +kernel

private theorem E1_block17 : kernelBlock 13 E1 4352 256 =
    [] := by decide +kernel

private theorem E1_block18 : kernelBlock 13 E1 4608 256 =
    [4608, 4827] := by decide +kernel

private theorem E1_block19 : kernelBlock 13 E1 4864 256 =
    [4920, 5091] := by decide +kernel

private theorem E1_block20 : kernelBlock 13 E1 5120 256 =
    [5241, 5282] := by decide +kernel

private theorem E1_block21 : kernelBlock 13 E1 5376 256 =
    [5441, 5530] := by decide +kernel

private theorem E1_block22 : kernelBlock 13 E1 5632 256 =
    [] := by decide +kernel

private theorem E1_block23 : kernelBlock 13 E1 5888 256 =
    [] := by decide +kernel

private theorem E1_block24 : kernelBlock 13 E1 6144 256 =
    [6265, 6306] := by decide +kernel

private theorem E1_block25 : kernelBlock 13 E1 6400 256 =
    [6465, 6554] := by decide +kernel

private theorem E1_block26 : kernelBlock 13 E1 6656 256 =
    [] := by decide +kernel

private theorem E1_block27 : kernelBlock 13 E1 6912 256 =
    [] := by decide +kernel

private theorem E1_block28 : kernelBlock 13 E1 7168 256 =
    [] := by decide +kernel

private theorem E1_block29 : kernelBlock 13 E1 7424 256 =
    [] := by decide +kernel

private theorem E1_block30 : kernelBlock 13 E1 7680 256 =
    [7680, 7899] := by decide +kernel

private theorem E1_block31 : kernelBlock 13 E1 7936 256 =
    [7992, 8163] := by decide +kernel

theorem E1_kernel_eq_span : kernelCodes 13 E1 =
    sortCodes (spanCodes Egenerators) := by
  rw [kernelCodes_eq_block]
  change kernelBlock 13 E1 0 8192 = sortCodes (spanCodes Egenerators)
  rw [kernelBlock_add 13 E1 0 256 7936,
    kernelBlock_add 13 E1 256 256 7680,
    kernelBlock_add 13 E1 512 256 7424,
    kernelBlock_add 13 E1 768 256 7168,
    kernelBlock_add 13 E1 1024 256 6912,
    kernelBlock_add 13 E1 1280 256 6656,
    kernelBlock_add 13 E1 1536 256 6400,
    kernelBlock_add 13 E1 1792 256 6144,
    kernelBlock_add 13 E1 2048 256 5888,
    kernelBlock_add 13 E1 2304 256 5632,
    kernelBlock_add 13 E1 2560 256 5376,
    kernelBlock_add 13 E1 2816 256 5120,
    kernelBlock_add 13 E1 3072 256 4864,
    kernelBlock_add 13 E1 3328 256 4608,
    kernelBlock_add 13 E1 3584 256 4352,
    kernelBlock_add 13 E1 3840 256 4096,
    kernelBlock_add 13 E1 4096 256 3840,
    kernelBlock_add 13 E1 4352 256 3584,
    kernelBlock_add 13 E1 4608 256 3328,
    kernelBlock_add 13 E1 4864 256 3072,
    kernelBlock_add 13 E1 5120 256 2816,
    kernelBlock_add 13 E1 5376 256 2560,
    kernelBlock_add 13 E1 5632 256 2304,
    kernelBlock_add 13 E1 5888 256 2048,
    kernelBlock_add 13 E1 6144 256 1792,
    kernelBlock_add 13 E1 6400 256 1536,
    kernelBlock_add 13 E1 6656 256 1280,
    kernelBlock_add 13 E1 6912 256 1024,
    kernelBlock_add 13 E1 7168 256 768,
    kernelBlock_add 13 E1 7424 256 512,
    kernelBlock_add 13 E1 7680 256 256]
  rw [E1_block0, E1_block1, E1_block2, E1_block3, E1_block4, E1_block5, E1_block6, E1_block7, E1_block8, E1_block9, E1_block10, E1_block11, E1_block12, E1_block13, E1_block14, E1_block15, E1_block16, E1_block17, E1_block18, E1_block19, E1_block20, E1_block21, E1_block22, E1_block23, E1_block24, E1_block25, E1_block26, E1_block27, E1_block28, E1_block29, E1_block30, E1_block31]
  decide +kernel

theorem E1_semantic_kernel_eq_span {code : ℕ} (bound : code < 2 ^ 13) :
    Kernel 13 E1 code ↔
      vector 13 code ∈ Submodule.span (ZMod 2) (generatorSet 13 Egenerators) :=
  kernel_iff_mem_span E1_kernel_eq_span Egenerators_bounded bound

theorem E1_kernel_length : (kernelCodes 13 E1).length = 32 := by
  rw [E1_kernel_eq_span, length_sortCodes, length_spanCodes]
  decide +kernel

theorem E1_kernel_card :
    Fintype.card {code : Fin (2 ^ 13) // Kernel 13 E1 code} = 32 :=
  kernel_card E1_kernel_length

/-- The entire kernel submodule equals the supplied binary linear span. -/
theorem E1_kernelSubmodule_eq_span :
    kernelSubmodule 13 E1 = Submodule.span (ZMod 2) (generatorSet 13 Egenerators) :=
  kernelSubmodule_eq_span E1_kernel_eq_span Egenerators_bounded

/-- Exact dimension of the kernel in the binary vector space. -/
theorem E1_kernel_finrank : Module.finrank (ZMod 2) ↥(kernelSubmodule 13 E1) = 5 :=
  kernelSubmodule_finrank (by simpa using E1_kernel_length)

private theorem Ep1_block0 : kernelBlock 13 Ep1 0 256 =
    [0] := by decide +kernel

private theorem Ep1_block1 : kernelBlock 13 Ep1 256 256 =
    [482] := by decide +kernel

private theorem Ep1_block2 : kernelBlock 13 Ep1 512 256 =
    [] := by decide +kernel

private theorem Ep1_block3 : kernelBlock 13 Ep1 768 256 =
    [] := by decide +kernel

private theorem Ep1_block4 : kernelBlock 13 Ep1 1024 256 =
    [] := by decide +kernel

private theorem Ep1_block5 : kernelBlock 13 Ep1 1280 256 =
    [] := by decide +kernel

private theorem Ep1_block6 : kernelBlock 13 Ep1 1536 256 =
    [1696] := by decide +kernel

private theorem Ep1_block7 : kernelBlock 13 Ep1 1792 256 =
    [1858] := by decide +kernel

private theorem Ep1_block8 : kernelBlock 13 Ep1 2048 256 =
    [] := by decide +kernel

private theorem Ep1_block9 : kernelBlock 13 Ep1 2304 256 =
    [] := by decide +kernel

private theorem Ep1_block10 : kernelBlock 13 Ep1 2560 256 =
    [2754] := by decide +kernel

private theorem Ep1_block11 : kernelBlock 13 Ep1 2816 256 =
    [2848] := by decide +kernel

private theorem Ep1_block12 : kernelBlock 13 Ep1 3072 256 =
    [3170] := by decide +kernel

private theorem Ep1_block13 : kernelBlock 13 Ep1 3328 256 =
    [3456] := by decide +kernel

private theorem Ep1_block14 : kernelBlock 13 Ep1 3584 256 =
    [] := by decide +kernel

private theorem Ep1_block15 : kernelBlock 13 Ep1 3840 256 =
    [] := by decide +kernel

private theorem Ep1_block16 : kernelBlock 13 Ep1 4096 256 =
    [] := by decide +kernel

private theorem Ep1_block17 : kernelBlock 13 Ep1 4352 256 =
    [] := by decide +kernel

private theorem Ep1_block18 : kernelBlock 13 Ep1 4608 256 =
    [4708] := by decide +kernel

private theorem Ep1_block19 : kernelBlock 13 Ep1 4864 256 =
    [4998] := by decide +kernel

private theorem Ep1_block20 : kernelBlock 13 Ep1 5120 256 =
    [5316] := by decide +kernel

private theorem Ep1_block21 : kernelBlock 13 Ep1 5376 256 =
    [5414] := by decide +kernel

private theorem Ep1_block22 : kernelBlock 13 Ep1 5632 256 =
    [] := by decide +kernel

private theorem Ep1_block23 : kernelBlock 13 Ep1 5888 256 =
    [] := by decide +kernel

private theorem Ep1_block24 : kernelBlock 13 Ep1 6144 256 =
    [6310] := by decide +kernel

private theorem Ep1_block25 : kernelBlock 13 Ep1 6400 256 =
    [6468] := by decide +kernel

private theorem Ep1_block26 : kernelBlock 13 Ep1 6656 256 =
    [] := by decide +kernel

private theorem Ep1_block27 : kernelBlock 13 Ep1 6912 256 =
    [] := by decide +kernel

private theorem Ep1_block28 : kernelBlock 13 Ep1 7168 256 =
    [] := by decide +kernel

private theorem Ep1_block29 : kernelBlock 13 Ep1 7424 256 =
    [] := by decide +kernel

private theorem Ep1_block30 : kernelBlock 13 Ep1 7680 256 =
    [7686] := by decide +kernel

private theorem Ep1_block31 : kernelBlock 13 Ep1 7936 256 =
    [8164] := by decide +kernel

theorem Ep1_kernel_eq_span : kernelCodes 13 Ep1 =
    sortCodes (spanCodes Epgenerators) := by
  rw [kernelCodes_eq_block]
  change kernelBlock 13 Ep1 0 8192 = sortCodes (spanCodes Epgenerators)
  rw [kernelBlock_add 13 Ep1 0 256 7936,
    kernelBlock_add 13 Ep1 256 256 7680,
    kernelBlock_add 13 Ep1 512 256 7424,
    kernelBlock_add 13 Ep1 768 256 7168,
    kernelBlock_add 13 Ep1 1024 256 6912,
    kernelBlock_add 13 Ep1 1280 256 6656,
    kernelBlock_add 13 Ep1 1536 256 6400,
    kernelBlock_add 13 Ep1 1792 256 6144,
    kernelBlock_add 13 Ep1 2048 256 5888,
    kernelBlock_add 13 Ep1 2304 256 5632,
    kernelBlock_add 13 Ep1 2560 256 5376,
    kernelBlock_add 13 Ep1 2816 256 5120,
    kernelBlock_add 13 Ep1 3072 256 4864,
    kernelBlock_add 13 Ep1 3328 256 4608,
    kernelBlock_add 13 Ep1 3584 256 4352,
    kernelBlock_add 13 Ep1 3840 256 4096,
    kernelBlock_add 13 Ep1 4096 256 3840,
    kernelBlock_add 13 Ep1 4352 256 3584,
    kernelBlock_add 13 Ep1 4608 256 3328,
    kernelBlock_add 13 Ep1 4864 256 3072,
    kernelBlock_add 13 Ep1 5120 256 2816,
    kernelBlock_add 13 Ep1 5376 256 2560,
    kernelBlock_add 13 Ep1 5632 256 2304,
    kernelBlock_add 13 Ep1 5888 256 2048,
    kernelBlock_add 13 Ep1 6144 256 1792,
    kernelBlock_add 13 Ep1 6400 256 1536,
    kernelBlock_add 13 Ep1 6656 256 1280,
    kernelBlock_add 13 Ep1 6912 256 1024,
    kernelBlock_add 13 Ep1 7168 256 768,
    kernelBlock_add 13 Ep1 7424 256 512,
    kernelBlock_add 13 Ep1 7680 256 256]
  rw [Ep1_block0, Ep1_block1, Ep1_block2, Ep1_block3, Ep1_block4, Ep1_block5, Ep1_block6, Ep1_block7, Ep1_block8, Ep1_block9, Ep1_block10, Ep1_block11, Ep1_block12, Ep1_block13, Ep1_block14, Ep1_block15, Ep1_block16, Ep1_block17, Ep1_block18, Ep1_block19, Ep1_block20, Ep1_block21, Ep1_block22, Ep1_block23, Ep1_block24, Ep1_block25, Ep1_block26, Ep1_block27, Ep1_block28, Ep1_block29, Ep1_block30, Ep1_block31]
  decide +kernel

theorem Ep1_semantic_kernel_eq_span {code : ℕ} (bound : code < 2 ^ 13) :
    Kernel 13 Ep1 code ↔
      vector 13 code ∈ Submodule.span (ZMod 2) (generatorSet 13 Epgenerators) :=
  kernel_iff_mem_span Ep1_kernel_eq_span Epgenerators_bounded bound

theorem Ep1_kernel_length : (kernelCodes 13 Ep1).length = 16 := by
  rw [Ep1_kernel_eq_span, length_sortCodes, length_spanCodes]
  decide +kernel

theorem Ep1_kernel_card :
    Fintype.card {code : Fin (2 ^ 13) // Kernel 13 Ep1 code} = 16 :=
  kernel_card Ep1_kernel_length

/-- The entire kernel submodule equals the supplied binary linear span. -/
theorem Ep1_kernelSubmodule_eq_span :
    kernelSubmodule 13 Ep1 = Submodule.span (ZMod 2) (generatorSet 13 Epgenerators) :=
  kernelSubmodule_eq_span Ep1_kernel_eq_span Epgenerators_bounded

/-- Exact dimension of the kernel in the binary vector space. -/
theorem Ep1_kernel_finrank : Module.finrank (ZMod 2) ↥(kernelSubmodule 13 Ep1) = 4 :=
  kernelSubmodule_finrank (by simpa using Ep1_kernel_length)

/-- Independence of the ordered known classes in the binary coordinates. -/
theorem Egenerators_linearIndependent :
    LinearIndependent (ZMod 2) (generatorFamily 13 Egenerators) :=
  generators_linearIndependent E0_kernel_eq_span Egenerators_bounded

theorem Epgenerators_linearIndependent :
    LinearIndependent (ZMod 2) (generatorFamily 13 Epgenerators) :=
  generators_linearIndependent Ep0_kernel_eq_span Epgenerators_bounded

end Rank7

end RankCertificates.MatrixCertificates

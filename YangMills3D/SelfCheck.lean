/- Self-check: axiom inventory for every main theorem of the library.
   A passing self-check = every listed theorem depends only on the three standard axioms
   [propext, Classical.choice, Quot.sound]. Run `lake build` and read the info output.
   (For unprovable-free defs — `TVv`, `mixOf`, `k2`, `nuRate`, `bar`, `n1`,
   `stencilSupp`, `DefectDecay`, `BoundedTV`, `animalCount`, `perimeter` — the key
   theorems are printed instead, since plain definitions carry no proof term.) -/
import YangMills3D.Animals
import YangMills3D.Entropy
import YangMills3D.Sign
import YangMills3D.Symbol
import YangMills3D.Window
import YangMills3D.Mixture
import YangMills3D.Decay
import YangMills3D.Floor
import YangMills3D.Coarsen
import YangMills3D.Fan

-- ## YangMills3D.Animals — the animal-entropy layer (W24-S)
#print axioms YangMills3D.card_dirs
#print axioms YangMills3D.dirs_cases
#print axioms YangMills3D.dirs_bdd
#print axioms YangMills3D.dirs_axis
#print axioms YangMills3D.negDir_mem_dirs
#print axioms YangMills3D.addDir_eq_iff
#print axioms YangMills3D.perimeter_le
#print axioms YangMills3D.mem_box_iff
#print axioms YangMills3D.card_box
#print axioms YangMills3D.evenCore_subset_box
#print axioms YangMills3D.core_step_mem_box
#print axioms YangMills3D.core_step_not_mem_core
#print axioms YangMills3D.perimeter_box_sdiff
#print axioms YangMills3D.perimeter_box_le

-- ## YangMills3D.Entropy — the entropy-impossibility layer (W24-S / W25-N2)
#print axioms YangMills3D.card_evens_ge
#print axioms YangMills3D.card_evenCore_ge
#print axioms YangMills3D.animal_family_card
#print axioms YangMills3D.box_gen_ge_binomial
#print axioms YangMills3D.generating_diverges
#print axioms YangMills3D.no_exponential_animal_tail

-- ## YangMills3D.Sign — the sign/TV currency layer (W25; defs TVv, mixOf)
#print axioms YangMills3D.tv_scale
#print axioms YangMills3D.tv_subadd
#print axioms YangMills3D.positive_mix_free
#print axioms YangMills3D.tv_fiber_additive
#print axioms YangMills3D.signed_mix_pays
#print axioms YangMills3D.tv_eq_one_forces_pure
#print axioms YangMills3D.int_char
#print axioms YangMills3D.link_char

-- ## YangMills3D.Symbol — the T-OP symbol core (def k2)
#print axioms YangMills3D.k2_nonneg
#print axioms YangMills3D.k2_eq_zero_iff
#print axioms YangMills3D.k2_le_twelve
#print axioms YangMills3D.k2_sq_le

-- ## YangMills3D.Window — the W23-IMG binding-window check (defs nuRate, bar)
#print axioms YangMills3D.window_check_edge
#print axioms YangMills3D.window_check_strong

-- ## YangMills3D.Mixture — T-OP transfer + W24-ASM assembly + W24-CEIL ceiling
#print axioms YangMills3D.n1_nonneg
#print axioms YangMills3D.n1_triangle
#print axioms YangMills3D.n1_rev_triangle
#print axioms YangMills3D.mem_stencilSupp
#print axioms YangMills3D.t_op_transfer
#print axioms YangMills3D.w24_assembly
#print axioms YangMills3D.w24_ceil
#print axioms YangMills3D.delivered_rate_clears_bar

-- ## YangMills3D.Decay — the W28T-CONV kernel-convexity layer (def UniformDecay)
#print axioms YangMills3D.uniform_decay_const_mul
#print axioms YangMills3D.uniform_decay_add
#print axioms YangMills3D.w28t_conv
#print axioms YangMills3D.w28t_conv_norm

-- ## YangMills3D.Floor — the W29-FLOOR / W29-DEC count-layer floors
#print axioms YangMills3D.perimeter_ge_shadows
#print axioms YangMills3D.xext_le_shadowXZ
#print axioms YangMills3D.xext_le_shadowXY
#print axioms YangMills3D.card_shadowYZ_pos
#print axioms YangMills3D.perimeter_ge_of_xext
#print axioms YangMills3D.perimeter_ge_of_layers
#print axioms YangMills3D.perimeter_union
#print axioms YangMills3D.perimeter_biUnion

-- ## YangMills3D.Coarsen — W26-PAR / W26-CANCEL (def mergeUnder)
#print axioms YangMills3D.tv_merge_conserved
#print axioms YangMills3D.z_even_half_abs
#print axioms YangMills3D.z_even_ratio

-- ## YangMills3D.Fan — the W30-FLOOR2 / W30-RATE / W30-FORM layer (def l1diam, TailFan)
#print axioms YangMills3D.span_le_card_image
#print axioms YangMills3D.perimeter_ge_two_r
#print axioms YangMills3D.vtxConnected_diagChain
#print axioms YangMills3D.perimeter_diagChain
#print axioms YangMills3D.l1diam_diagChain
#print axioms YangMills3D.w30_floor2_tight
#print axioms YangMills3D.connecting_perimeter_floor
#print axioms YangMills3D.connecting_perimeter_floor_real
#print axioms YangMills3D.nu2_eq_twice
#print axioms YangMills3D.nu2_le_of_F0_le
#print axioms YangMills3D.w30_rate_clears_bar
#print axioms YangMills3D.w30_conditional
#print axioms YangMills3D.cov_split

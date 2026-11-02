/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 30 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile032Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨32,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (8037/640)), 0, by norm_num⟩
  | 1 => ⟨(1, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_variable : Sound J_variable F_variable c := by
  have h := variable_sound 12 ((7/8), (8037/640))
  have he : value ((7/8), (8037/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/16), (8037/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_halfVariable : Sound J_halfVariable F_halfVariable c := by
  apply sound_round (sound_scale (A_variable hcre) S_variable)
  intro k
  fin_cases k <;> norm_num [J_halfVariable, J_variable, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(1, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q0 : Sound J_q0 F_q0 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (1, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_base : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((23/16), (8037/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_base : Sound J_base F_base c := by
  apply sound_round (sound_add (A_q0 hcre) (A_halfVariable hcre) S_q0 S_halfVariable)
  intro k
  fin_cases k <;> norm_num [J_base, J_q0, J_halfVariable, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(12, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q1 : Sound J_q1 F_q1 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (12, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_shift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((215/16), (8037/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_shift : Sound J_shift F_shift c := by
  apply sound_round (sound_add (A_base hcre) (A_q1 hcre) S_base S_q1)
  intro k
  fin_cases k <;> norm_num [J_shift, J_base, J_q1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftInv : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22016000/360433369), (-10287360/360433369)), 0, by norm_num⟩
  | 1 => ⟨((-189437240115200/129912213488690161), (226486517760000/129912213488690161)), 0, by norm_num⟩
  | 2 => ⟨((345778757/17592186044416), (-1302776267/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((257000105/562949953421312), (715562445/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-452357923/9007199254740992), (-320323205/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((734656609/288230376151711744), (104883769/72057594037927936)), (1/72057594037927936), by norm_num⟩
  | 6 => ⟨((-1819153055/18446744073709551616), (-37261971/4611686018427387904)), (3/4611686018427387904), by norm_num⟩
  | 7 => ⟨((922972987/295147905179352825856), (-171269871/147573952589676412928)), (9/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-745606599/9444732965739290427392), (378129481/4722366482869645213696)), (7/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((191666309/151115727451828646838272), (-1079594639/302231454903657293676544)), (21/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((59189365/4835703278458516698824704), (1230156299/9671406556917033397649408)), (31/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-677463881/309485009821345068724781056), (-574093715/154742504910672534362390528)), (23/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((593216157/4951760157141521099596496896), (812762911/9903520314283042199192993792)), (67/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((215/16), (8037/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((215/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((215/16), (8037/1280)))⁻¹=value ((22016000/360433369), (-10287360/360433369)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((22016000/360433369), (-10287360/360433369))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((723914987/268435456), (234677219/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((11008000/360433369), (-5143680/360433369)), 0, by norm_num⟩
  | 2 => ⟨((-47359310028800/129912213488690161), (56621629440000/129912213488690161)), 0, by norm_num⟩
  | 3 => ⟨((230519171/70368744177664), (-868517511/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((257000105/4503599627370496), (715562445/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((-723772677/144115188075855872), (-64064641/9007199254740992)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((979542145/4611686018427387904), (559380101/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-1039516031/147573952589676412928), (-85170219/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 8 => ⟨((922972987/4722366482869645213696), (-171269871/2361183241434822606848)), (9/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-662761421/151115727451828646838272), (168057547/37778931862957161709568)), (7/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((153333047/2417851639229258349412352), (-863675711/4835703278458516698824704)), (9/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((43046811/77371252455336267181195264), (1789318253/309485009821345068724781056)), (23/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-451642587/4951760157141521099596496896), (-765458287/4951760157141521099596496896)), (1/154742504910672534362390528), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-6959/276736), (171/20480)), 0, by norm_num⟩
  | 45 => ⟨((93744399497/4080638361600), (-675621/60293120)), 0, by norm_num⟩
  | 44 => ⟨((-50581663186717/2298215525253120), (2135709491243/197568495616000)), 0, by norm_num⟩
  | 43 => ⟨((774418173/34359738368), (-178126945/17179869184)), (1/34359738368), by norm_num⟩
  | 42 => ⟨((-802311621/34359738368), (360962481/34359738368)), (1/17179869184), by norm_num⟩
  | 41 => ⟨((824884521/34359738368), (-372662863/34359738368)), (1/17179869184), by norm_num⟩
  | 40 => ⟨((-211214793/8589934592), (383395073/34359738368)), (1/17179869184), by norm_num⟩
  | 39 => ⟨((216468013/8589934592), (-98238147/8589934592)), (1/17179869184), by norm_num⟩
  | 38 => ⟨((-888671433/34359738368), (402729403/34359738368)), (1/17179869184), by norm_num⟩
  | 37 => ⟨((912924101/34359738368), (-413242419/34359738368)), (1/17179869184), by norm_num⟩
  | 36 => ⟨((-938478277/34359738368), (424443659/34359738368)), (1/17179869184), by norm_num⟩
  | 35 => ⟨((965444851/34359738368), (-436265875/34359738368)), (1/17179869184), by norm_num⟩
  | 34 => ⟨((-496999017/17179869184), (448741813/34359738368)), (1/17179869184), by norm_num⟩
  | 33 => ⟨((1024298705/34359738368), (-461945085/34359738368)), (1/17179869184), by norm_num⟩
  | 32 => ⟨((-264126949/8589934592), (237975307/17179869184)), (1/17179869184), by norm_num⟩
  | 31 => ⟨((1090806903/34359738368), (-490833553/34359738368)), (1/17179869184), by norm_num⟩
  | 30 => ⟨((-1127405539/34359738368), (126669301/8589934592)), (1/17179869184), by norm_num⟩
  | 29 => ⟨((1166543441/34359738368), (-261788563/17179869184)), (1/17179869184), by norm_num⟩
  | 28 => ⟨((-604247253/17179869184), (541642705/34359738368)), (3/34359738368), by norm_num⟩
  | 27 => ⟨((1253573115/34359738368), (-280499473/17179869184)), (3/34359738368), by norm_num⟩
  | 26 => ⟨((-1302142231/34359738368), (290894621/17179869184)), (3/34359738368), by norm_num⟩
  | 25 => ⟨((1354623245/34359738368), (-604178995/34359738368)), (3/34359738368), by norm_num⟩
  | 24 => ⟨((-705754095/17179869184), (628360065/34359738368)), (3/34359738368), by norm_num⟩
  | 23 => ⟨((368343789/8589934592), (-327278133/17179869184)), (3/34359738368), by norm_num⟩
  | 22 => ⟨((-385226985/8589934592), (341515153/17179869184)), (1/8589934592), by norm_num⟩
  | 21 => ⟨((201865169/4294967296), (-178523151/8589934592)), (1/8589934592), by norm_num⟩
  | 20 => ⟨((-848197067/17179869184), (374056315/17179869184)), (1/8589934592), by norm_num⟩
  | 19 => ⟨((893256169/17179869184), (-392766823/17179869184)), (1/8589934592), by norm_num⟩
  | 18 => ⟨((-471681803/8589934592), (413446045/17179869184)), (1/8589934592), by norm_num⟩
  | 17 => ⟨((124927101/2147483648), (-6819089/268435456)), (1/8589934592), by norm_num⟩
  | 16 => ⟨((-531269495/8589934592), (57762305/2147483648)), (1/8589934592), by norm_num⟩
  | 15 => ⟨((1134154823/17179869184), (-30686367/1073741824)), (1/8589934592), by norm_num⟩
  | 14 => ⟨((-1216098675/17179869184), (523712053/17179869184)), (1/8589934592), by norm_num⟩
  | 13 => ⟨((655386511/8589934592), (-561111357/17179869184)), (1/8589934592), by norm_num⟩
  | 12 => ⟨((-1421386407/17179869184), (302127149/8589934592)), (1/8589934592), by norm_num⟩
  | 11 => ⟨((388080425/4294967296), (-327286051/8589934592)), (1/8589934592), by norm_num⟩
  | 10 => ⟨((-213715767/2147483648), (178503491/4294967296)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((237812001/2147483648), (-49081527/1073741824)), (1/4294967296), by norm_num⟩
  | 8 => ⟨((-134000123/1073741824), (436185521/8589934592)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((1227648171/8589934592), (-245272471/4294967296)), (1/4294967296), by norm_num⟩
  | 6 => ⟨((-89735371/536870912), (35020739/536870912)), (1/4294967296), by norm_num⟩
  | 5 => ⟨((864020935/4294967296), (-326590313/4294967296)), (1/4294967296), by norm_num⟩
  | 4 => ⟨((-1083955805/4294967296), (391374633/4294967296)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((1451670273/4294967296), (-1906483/16777216)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((-1094223833/2147483648), (323923575/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((1097806287/1073741824), (-60160805/268435456)), (1/1073741824), by norm_num⟩
  | 0 => ⟨((-162769049/2147483648), (234677219/536870912)), (1/1073741824), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-41/256), (8037/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-41/256), (8037/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-41/256), (8037/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((723914987/268435456), (234677219/536870912)), (1/536870912), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((215/16), (8037/1280))) (z:=((-41/256), (8037/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((723914987/268435456), (234677219/536870912))) (r:=(1/536870912)) (by norm_num) ?_ hs
  norm_num [J_shiftLog,RectangleLogInputs.log2Disk,logTable,inflate,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

set_option maxHeartbeats 5000000 in
theorem S_shiftLog : Sound J_shiftLog F_shiftLog c := by
  apply log_coefficients_sound (A_shift hcre) (L_shiftLog hcre) S_shift S_shiftInv
  · exact logValue
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftLog,J_shift,J_shiftInv,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1/2), 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q2 : Sound J_q2 F_q2 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact ((-1/2), 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_shiftMinusHalf : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((207/16), (8037/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_shiftMinusHalf : Sound J_shiftMinusHalf F_shiftMinusHalf c := by
  apply sound_round (sound_add (A_shift hcre) (A_q2 hcre) S_shift S_q2)
  intro k
  fin_cases k <;> norm_num [J_shiftMinusHalf, J_shift, J_q2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainLead : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((539305751/16777216), (757932825/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((123019019/67108864), (30292351/134217728)), (1/268435456), by norm_num⟩
  | 2 => ⟨((1015592286502400/129912213488690161), (-491799292584480/129912213488690161)), 0, by norm_num⟩
  | 3 => ⟨((-274420643/4398046511104), (173309583/2199023255552)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((26807083/70368744177664), (-957962815/562949953421312)), (7/281474976710656), by norm_num⟩
  | 5 => ⟨((296071667/36028797018963968), (159128649/4503599627370496)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-302478943/576460752303423488), (-376639343/576460752303423488)), (23/576460752303423488), by norm_num⟩
  | 7 => ⟨((1379355745/73786976294838206464), (330292051/36893488147419103232)), (63/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1270259275/2361183241434822606848), (29045/147573952589676412928)), (151/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((986110789/75557863725914323419136), (-236268661/37778931862957161709568)), (13/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-606875663/2417851639229258349412352), (188425769/604462909807314587353088)), (143/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((201506479/77371252455336267181195264), (-851792573/77371252455336267181195264)), (731/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((340612805/4951760157141521099596496896), (787803987/2475880078570760549798248448)), (123/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-215/16), (-8037/1280)), 0, by norm_num⟩
  | 1 => ⟨((-1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_negativeShift : Sound J_negativeShift F_negativeShift c := by
  apply sound_round (sound_scale (A_shift hcre) S_shift)
  intro k
  fin_cases k <;> norm_num [J_negativeShift, J_shift, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainMinusShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((313861911/16777216), (136811923/8388608)), (3/33554432), by norm_num⟩
  | 1 => ⟨((89464587/67108864), (30292351/134217728)), (1/268435456), by norm_num⟩
  | 2 => ⟨((1015592286502400/129912213488690161), (-491799292584480/129912213488690161)), 0, by norm_num⟩
  | 3 => ⟨((-274420643/4398046511104), (173309583/2199023255552)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((26807083/70368744177664), (-957962815/562949953421312)), (7/281474976710656), by norm_num⟩
  | 5 => ⟨((296071667/36028797018963968), (159128649/4503599627370496)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-302478943/576460752303423488), (-376639343/576460752303423488)), (23/576460752303423488), by norm_num⟩
  | 7 => ⟨((1379355745/73786976294838206464), (330292051/36893488147419103232)), (63/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1270259275/2361183241434822606848), (29045/147573952589676412928)), (151/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((986110789/75557863725914323419136), (-236268661/37778931862957161709568)), (13/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-606875663/2417851639229258349412352), (188425769/604462909807314587353088)), (143/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((201506479/77371252455336267181195264), (-851792573/77371252455336267181195264)), (731/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((340612805/4951760157141521099596496896), (787803987/2475880078570760549798248448)), (123/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainMinusShift : Sound J_mainMinusShift F_mainMinusShift c := by
  apply sound_round (sound_add (A_mainLead hcre) (A_negativeShift hcre) S_mainLead S_negativeShift)
  intro k
  fin_cases k <;> norm_num [J_mainMinusShift, J_mainLead, J_negativeShift, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((138629436111989/200000000000000), 0), (1/1000000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_log2 : Sound J_log2 F_log2 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log2_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logpi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5723649429247/5000000000000), 0), (3/500000000000000), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_logpi : Sound J_logpi F_logpi c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.logpi_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_logTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((986702737/536870912), 0), (1/1073741824), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_logTwoPi : Sound J_logTwoPi F_logTwoPi c := by
  apply sound_round (sound_add (A_log2 hcre) (A_logpi hcre) S_log2 S_logpi)
  intro k
  fin_cases k <;> norm_num [J_logTwoPi, J_log2, J_logpi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_halfLogTwoPi : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((986702737/1073741824), 0), (1/2147483648), by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_halfLogTwoPi : Sound J_halfLogTwoPi F_halfLogTwoPi c := by
  apply sound_round (sound_scale (A_logTwoPi hcre) S_logTwoPi)
  intro k
  fin_cases k <;> norm_num [J_halfLogTwoPi, J_logTwoPi, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainConstant : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((658558283/33554432), (136811923/8388608)), (1/8388608), by norm_num⟩
  | 1 => ⟨((89464587/67108864), (30292351/134217728)), (1/268435456), by norm_num⟩
  | 2 => ⟨((1015592286502400/129912213488690161), (-491799292584480/129912213488690161)), 0, by norm_num⟩
  | 3 => ⟨((-274420643/4398046511104), (173309583/2199023255552)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((26807083/70368744177664), (-957962815/562949953421312)), (7/281474976710656), by norm_num⟩
  | 5 => ⟨((296071667/36028797018963968), (159128649/4503599627370496)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-302478943/576460752303423488), (-376639343/576460752303423488)), (23/576460752303423488), by norm_num⟩
  | 7 => ⟨((1379355745/73786976294838206464), (330292051/36893488147419103232)), (63/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1270259275/2361183241434822606848), (29045/147573952589676412928)), (151/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((986110789/75557863725914323419136), (-236268661/37778931862957161709568)), (13/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-606875663/2417851639229258349412352), (188425769/604462909807314587353088)), (143/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((201506479/77371252455336267181195264), (-851792573/77371252455336267181195264)), (731/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((340612805/4951760157141521099596496896), (787803987/2475880078570760549798248448)), (123/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((378874480230400/129912213488690161), (-452973035520000/129912213488690161)), 0, by norm_num⟩
  | 1 => ⟨((-345778757/4398046511104), (1302776267/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-96375039/35184372088832), (-268335917/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((452357923/1125899906842624), (320323205/562949953421312)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-918320761/36028797018963968), (-524418845/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((1364364791/1152921504606846976), (55892957/576460752303423488)), (7/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-201900341/4611686018427387904), (149861137/9223372036854775808)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((745606599/590295810358705651712), (-378129481/295147905179352825856)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-431249195/18889465931478580854784), (1214543969/18889465931478580854784)), (15/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-147973413/604462909807314587353088), (-1537695375/604462909807314587353088)), (3/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((465756419/9671406556917033397649408), (394689429/4835703278458516698824704)), (19/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-222456059/77371252455336267181195264), (-304786091/154742504910672534362390528)), (7/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((155459323/1237940039285380274899124224), (51293055/2475880078570760549798248448)), (21/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((345778757/4398046511104), (-1302776267/4398046511104)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((96375039/17592186044416), (268335917/8796093022208)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-169634221/140737488355328), (-960969615/562949953421312)), (3/562949953421312), by norm_num⟩
  | 3 => ⟨((918320761/9007199254740992), (262209423/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-1705455989/288230376151711744), (-17466549/36028797018963968)), (7/288230376151711744), by norm_num⟩
  | 5 => ⟨((605701023/2305843009213693952), (-449583411/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((-326202887/36893488147419103232), (5169739/576460752303423488)), (7/73786976294838206464), by norm_num⟩
  | 7 => ⟨((431249195/2361183241434822606848), (-1214543969/2361183241434822606848)), (13/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((83235045/37778931862957161709568), (54059603/2361183241434822606848)), (21/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-145548881/302231454903657293676544), (-986723573/1208925819614629174706176)), (17/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((1223508325/38685626227668133590597632), (838161751/38685626227668133590597632)), (27/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-466377969/309485009821345068724781056), (-153879165/618970019642690137449562112)), (11/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((1145509593/19807040628566084398385987584), (-321498513/19807040628566084398385987584)), (17/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-257000105/70368744177664), (-715562445/35184372088832)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((226178961/140737488355328), (320323205/140737488355328)), (3/281474976710656), by norm_num⟩
  | 2 => ⟨((-918320761/4503599627370496), (-262209423/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((1136970659/72057594037927936), (93154929/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 4 => ⟨((-1009501705/1152921504606846976), (187326421/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 5 => ⟨((326202887/9223372036854775808), (-5169739/144115188075855872)), (7/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-503124061/590295810358705651712), (354241991/147573952589676412928)), (13/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-27745015/2361183241434822606848), (-1153271531/9444732965739290427392)), (13/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((436646643/151115727451828646838272), (740042679/151115727451828646838272)), (3/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-1019590271/4835703278458516698824704), (-349234063/2417851639229258349412352)), (5/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((855026277/77371252455336267181195264), (141055901/77371252455336267181195264)), (33/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-572754797/1237940039285380274899124224), (321498513/2475880078570760549798248448)), (27/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((607939501/39614081257132168796771975168), (-523325043/39614081257132168796771975168)), (11/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-452357923/562949953421312), (-320323205/281474976710656)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((114790095/562949953421312), (262209423/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 2 => ⟨((-1705455989/72057594037927936), (-139732393/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 3 => ⟨((1009501705/576460752303423488), (-187326421/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((-407753609/4611686018427387904), (827158239/9223372036854775808)), (9/9223372036854775808), by norm_num⟩
  | 5 => ⟨((188671523/73786976294838206464), (-1062725973/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 6 => ⟨((3034611/73786976294838206464), (504556295/1180591620717411303424)), (11/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-436646643/37778931862957161709568), (-92505335/4722366482869645213696)), (3/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((1147039055/1208925819614629174706176), (785776641/1208925819614629174706176)), (11/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-534391423/9671406556917033397649408), (-44079969/4835703278458516698824704)), (5/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((1575075691/618970019642690137449562112), (-55257557/77371252455336267181195264)), (35/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-227977313/2475880078570760549798248448), (784987565/9903520314283042199192993792)), (15/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((355161919/158456325028528675187087900672), (-789077513/158456325028528675187087900672)), (25/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-734656609/9007199254740992), (-104883769/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((1364364791/72057594037927936), (111785915/72057594037927936)), (11/72057594037927936), by norm_num⟩
  | 2 => ⟨((-605701023/288230376151711744), (224791705/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 3 => ⟨((326202887/2305843009213693952), (-661726591/4611686018427387904)), (5/2305843009213693952), by norm_num⟩
  | 4 => ⟨((-377343047/73786976294838206464), (1062725973/73786976294838206464)), (13/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-58264531/590295810358705651712), (-302733777/295147905179352825856)), (15/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((152826325/4722366482869645213696), (129507469/2361183241434822606848)), (17/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-229407811/75557863725914323419136), (-314310657/151115727451828646838272)), (19/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((480952281/2417851639229258349412352), (158687889/4835703278458516698824704)), (9/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-1575075691/154742504910672534362390528), (55257557/19342813113834066795298816)), (35/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((1003100177/2475880078570760549798248448), (-863486321/2475880078570760549798248448)), (33/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((-426194303/39614081257132168796771975168), (118361627/4951760157141521099596496896)), (29/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-11254793/633825300114114700748351602688), (-1586721695/1267650600228229401496703205376)), (51/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1819153055/288230376151711744), (-37261971/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 1 => ⟨((201900341/144115188075855872), (-299722273/576460752303423488)), (5/288230376151711744), by norm_num⟩
  | 2 => ⟨((-652405775/4611686018427387904), (661726591/4611686018427387904)), (11/4611686018427387904), by norm_num⟩
  | 3 => ⟨((251562031/36893488147419103232), (-1416967963/73786976294838206464)), (5/18446744073709551616), by norm_num⟩
  | 4 => ⟨((97107551/590295810358705651712), (504556295/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-611305299/9444732965739290427392), (-129507469/1180591620717411303424)), (5/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((133821223/18889465931478580854784), (733391533/151115727451828646838272)), (23/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-160317427/302231454903657293676544), (-211583853/2417851639229258349412352)), (27/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((1181306769/38685626227668133590597632), (-331545341/38685626227668133590597632)), (7/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-835916815/618970019642690137449562112), (359785967/309485009821345068724781056)), (29/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((390678111/9903520314283042199192993792), (-867985265/9903520314283042199192993792)), (7/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((11254793/158456325028528675187087900672), (49585053/9903520314283042199192993792)), (13/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-559950875/5070602400912917605986812821504), (-577666281/2535301200456458802993406410752)), (47/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-922972987/2305843009213693952), (171269871/1152921504606846976)), (9/2305843009213693952), by norm_num⟩
  | 1 => ⟨((745606599/9223372036854775808), (-756258961/9223372036854775808)), (17/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-431249197/73786976294838206464), (1214543969/73786976294838206464)), (21/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-110980059/590295810358705651712), (-1153271531/590295810358705651712)), (21/590295810358705651712), by norm_num⟩
  | 4 => ⟨((218323321/2361183241434822606848), (92505335/590295810358705651712)), (9/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((-917631243/75557863725914323419136), (-314310657/37778931862957161709568)), (25/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((1282539415/1208925819614629174706176), (211583853/1208925819614629174706176)), (31/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-1350064879/19342813113834066795298816), (378908961/19342813113834066795298816)), (37/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((1074750191/309485009821345068724781056), (-925163915/309485009821345068724781056)), (41/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((-558111589/4951760157141521099596496896), (619989475/2475880078570760549798248448)), (11/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-17686103/79228162514264337593543950336), (-77919369/4951760157141521099596496896)), (11/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((119989473/316912650057057350374175801344), (990285053/1267650600228229401496703205376)), (11/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-729361371/20282409603651670423947251286016), (-296335591/10141204801825835211973625643008)), (41/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-745606599/36893488147419103232), (378129481/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 1 => ⟨((107812299/36893488147419103232), (-37954499/4611686018427387904)), (27/147573952589676412928), by norm_num⟩
  | 2 => ⟨((20808761/147573952589676412928), (1729907297/1180591620717411303424)), (19/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-218323321/2361183241434822606848), (-92505335/590295810358705651712)), (21/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((573519527/37778931862957161709568), (785776643/75557863725914323419136)), (19/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((-961904561/604462909807314587353088), (-79343945/302231454903657293676544)), (29/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((1181306769/9671406556917033397649408), (-82886335/2417851639229258349412352)), (39/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-1074750191/154742504910672534362390528), (925163915/154742504910672534362390528)), (3/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((313937769/1237940039285380274899124224), (-697488159/1237940039285380274899124224)), (7/309485009821345068724781056), by norm_num⟩
  | 9 => ⟨((5526907/9903520314283042199192993792), (389596845/9903520314283042199192993792)), (63/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-329971051/316912650057057350374175801344), (-1361641949/633825300114114700748351602688)), (33/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((136755257/1267650600228229401496703205376), (889006773/10141204801825835211973625643008)), (17/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((-307333389/40564819207303340847894502572032), (-153843851/81129638414606681695789005144064)), (67/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-191666309/295147905179352825856), (1079594639/590295810358705651712)), (21/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-36993353/590295810358705651712), (-768847687/1180591620717411303424)), (21/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((582195523/9444732965739290427392), (986723573/9444732965739290427392)), (17/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-509795135/37778931862957161709568), (-698468127/75557863725914323419136)), (5/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((534391423/302231454903657293676544), (88159939/302231454903657293676544)), (39/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((-1575075691/9671406556917033397649408), (442060453/9671406556917033397649408)), (1/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((52244801/4835703278458516698824704), (-719571933/77371252455336267181195264)), (23/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((-558111589/1237940039285380274899124224), (1239978949/1237940039285380274899124224)), (15/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((-22107627/19807040628566084398385987584), (-389596845/4951760157141521099596496896)), (73/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((366634501/158456325028528675187087900672), (756467749/158456325028528675187087900672)), (11/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-668581257/2535301200456458802993406410752), (-543281917/2535301200456458802993406410752)), (47/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((1639111407/81129638414606681695789005144064), (410250269/81129638414606681695789005144064)), (101/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((-782806219/649037107316853453566312041152512), (152068091/649037107316853453566312041152512)), (103/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((59189365/4722366482869645213696), (1230156299/9444732965739290427392)), (31/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((-232878209/9444732965739290427392), (-394689429/9444732965739290427392)), (33/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((305877081/37778931862957161709568), (104770219/18889465931478580854784)), (59/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((-855026277/604462909807314587353088), (-70527951/302231454903657293676544)), (75/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((393768923/2417851639229258349412352), (-442060453/9671406556917033397649408)), (77/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-501550089/38685626227668133590597632), (863486319/77371252455336267181195264)), (17/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((390678113/618970019642690137449562112), (-54249079/38685626227668133590597632)), (13/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((8843051/4951760157141521099596496896), (77919369/618970019642690137449562112)), (9/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-164985525/39614081257132168796771975168), (-1361641949/158456325028528675187087900672)), (23/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((83572657/158456325028528675187087900672), (543281917/1267650600228229401496703205376)), (57/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((-450755637/10141204801825835211973625643008), (-14102353/1267650600228229401496703205376)), (65/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((469683731/162259276829213363391578010288128), (-182481709/324518553658426726783156020576256)), (9/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((-765162041/5192296858534827628530496329220096), (69588643/649037107316853453566312041152512)), (19/1298074214633706907132624082305024), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5504000/1081300107), (-857280/360433369)), 0, by norm_num⟩
  | 1 => ⟨((-47359310028800/389736640466070483), (18873876480000/129912213488690161)), 0, by norm_num⟩
  | 2 => ⟨((230519171/140737488355328), (-868517511/140737488355328)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((171333403/4503599627370496), (238520815/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-603143897/144115188075855872), (-854195213/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((979542145/4611686018427387904), (559380101/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-1212768703/147573952589676412928), (-12420657/18446744073709551616)), (9/147573952589676412928), by norm_num⟩
  | 7 => ⟨((1230630649/4722366482869645213696), (-57089957/590295810358705651712)), (13/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-248535533/37778931862957161709568), (1008345283/151115727451828646838272)), (19/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((511110157/4835703278458516698824704), (-1439459519/4835703278458516698824704)), (29/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((157838307/154742504910672534362390528), (1640208399/154742504910672534362390528)), (21/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-451642587/2475880078570760549798248448), (-765458287/2475880078570760549798248448)), (1/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((197738719/19807040628566084398385987584), (541841941/79228162514264337593543950336)), (45/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((658729081/33554432), (136791971/8388608)), (5/33554432), by norm_num⟩
  | 1 => ⟨((1431302915/1073741824), (242494803/1073741824)), (5/1073741824), by norm_num⟩
  | 2 => ⟨((1074657899/137438953472), (-521140891/137438953472)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-274253325/4398046511104), (43443861/549755813888)), (7/8796093022208), by norm_num⟩
  | 4 => ⟨((212100633/562949953421312), (-961299515/562949953421312)), (15/562949953421312), by norm_num⟩
  | 5 => ⟨((75931085/9007199254740992), (1277399349/36028797018963968)), (29/36028797018963968), by norm_num⟩
  | 6 => ⟨((-614432641/1152921504606846976), (-754054977/1152921504606846976)), (47/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1398584349/73786976294838206464), (653447857/73786976294838206464)), (127/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-642896373/1180591620717411303424), (16220115/2361183241434822606848)), (19/295147905179352825856), by norm_num⟩
  | 9 => ⟨((994096885/75557863725914323419136), (-495028877/75557863725914323419136)), (209/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-604409439/2417851639229258349412352), (194832833/604462909807314587353088)), (9/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((23424081/9671406556917033397649408), (-1751426289/154742504910672534362390528)), (367/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((390047485/4951760157141521099596496896), (1609473095/4951760157141521099596496896)), (247/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-61471779/281474976710656), (926418679/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 1 => ⟨((-68533361/4503599627370496), (-1526533217/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((241257559/72057594037927936), (683356171/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((-1306056193/4611686018427387904), (-745840137/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 4 => ⟨((1212768703/73786976294838206464), (99365257/73786976294838206464)), (3/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-861441455/1180591620717411303424), (319703759/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 6 => ⟨((463932995/18889465931478580854784), (-117640283/4722366482869645213696)), (11/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-153333047/302231454903657293676544), (863675711/604462909807314587353088)), (5/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-118378731/19342813113834066795298816), (-1230156299/19342813113834066795298816)), (1/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((207002853/154742504910672534362390528), (43854381/19342813113834066795298816)), (13/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((-217512591/2475880078570760549798248448), (-298013067/4951760157141521099596496896)), (5/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((1326586223/316912650057057350374175801344), (3419537/4951760157141521099596496896)), (1/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-1629169199/10141204801825835211973625643008), (228621165/5070602400912917605986812821504)), (49/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((329364537/16777216), (68395989/4194304)), (3/16777216), by norm_num⟩
  | 1 => ⟨((1431302899/1073741824), (30311839/134217728)), (3/536870912), by norm_num⟩
  | 2 => ⟨((1074658359/137438953472), (-521140239/137438953472)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((-548509141/8796093022208), (695100353/8796093022208)), (1/1099511627776), by norm_num⟩
  | 4 => ⟨((106054943/281474976710656), (-961298757/562949953421312)), (1/35184372088832), by norm_num⟩
  | 5 => ⟨((303698051/36028797018963968), (638704553/18014398509481984)), (15/18014398509481984), by norm_num⟩
  | 6 => ⟨((-614404325/1152921504606846976), (-377041849/576460752303423488)), (3/72057594037927936), by norm_num⟩
  | 7 => ⟨((699273457/36893488147419103232), (326776643/36893488147419103232)), (1/576460752303423488), by norm_num⟩
  | 8 => ⟨((-1285807197/2361183241434822606848), (16069949/2361183241434822606848)), (153/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((994197961/75557863725914323419136), (-494857571/75557863725914323419136)), (105/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-302310927/1208925819614629174706176), (389592909/1208925819614629174706176)), (289/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((375433043/154742504910672534362390528), (-437829857/38685626227668133590597632)), (735/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((48656499/618970019642690137449562112), (804848179/2475880078570760549798248448)), (989/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-183815283/288230376151711744), (-1041304641/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 1 => ⟨((364413/2251799813685248), (106548591/1152921504606846976)), (3/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-1386021375/73786976294838206464), (-56780147/36893488147419103232)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((820420433/590295810358705651712), (-152239885/295147905179352825856)), (7/590295810358705651712), by norm_num⟩
  | 4 => ⟨((-331380711/4722366482869645213696), (168057547/2361183241434822606848)), (1/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((306666095/151115727451828646838272), (-863675711/151115727451828646838272)), (5/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((157838307/4835703278458516698824704), (102513025/302231454903657293676544)), (19/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-709724067/77371252455336267181195264), (-1202863023/77371252455336267181195264)), (21/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((932196819/1237940039285380274899124224), (638599429/1237940039285380274899124224)), (19/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((-1737196245/39614081257132168796771975168), (-286589767/39614081257132168796771975168)), (33/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((640030757/316912650057057350374175801344), (-359261831/633825300114114700748351602688)), (29/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-370553601/5070602400912917605986812821504), (159489537/2535301200456458802993406410752)), (25/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((36079941/20282409603651670423947251286016), (-1282564085/324518553658426726783156020576256)), (21/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((329364537/16777216), (68395989/4194304)), (7/33554432), by norm_num⟩
  | 1 => ⟨((1431302899/1073741824), (30311839/134217728)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((268664589/34359738368), (-521140239/137438953472)), (3/137438953472), by norm_num⟩
  | 3 => ⟨((-548509129/8796093022208), (173775087/2199023255552)), (9/8796093022208), by norm_num⟩
  | 4 => ⟨((106054923/281474976710656), (-961298717/562949953421312)), (17/562949953421312), by norm_num⟩
  | 5 => ⟨((75924531/9007199254740992), (319352225/9007199254740992)), (31/36028797018963968), by norm_num⟩
  | 6 => ⟨((-614404287/1152921504606846976), (-754083307/1152921504606846976)), (49/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1398546237/73786976294838206464), (653552139/73786976294838206464)), (129/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1285805419/2361183241434822606848), (16071167/2361183241434822606848)), (77/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((124274331/9444732965739290427392), (-247429059/37778931862957161709568)), (211/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-604616971/2417851639229258349412352), (12174757/37778931862957161709568)), (145/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((375421735/154742504910672534362390528), (-875654847/77371252455336267181195264)), (23/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((389260801/4951760157141521099596496896), (402419197/1237940039285380274899124224)), (495/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((277204275/73786976294838206464), (45424117/147573952589676412928)), (1/36893488147419103232), by norm_num⟩
  | 1 => ⟨((-123063065/147573952589676412928), (365375723/1180591620717411303424)), (13/1180591620717411303424), by norm_num⟩
  | 2 => ⟨((795313707/9444732965739290427392), (-806676225/9444732965739290427392)), (7/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-306666095/75557863725914323419136), (863675711/75557863725914323419136)), (13/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((-118378729/1208925819614629174706176), (-307539075/302231454903657293676544)), (5/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((745210269/19342813113834066795298816), (631503087/9671406556917033397649408)), (25/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((-652537773/154742504910672534362390528), (-447019601/154742504910672534362390528)), (15/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((1563476621/4951760157141521099596496896), (32241349/618970019642690137449562112)), (17/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((-360017301/19807040628566084398385987584), (404169559/79228162514264337593543950336)), (35/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((1019022403/1267650600228229401496703205376), (-877192453/1267650600228229401496703205376)), (9/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-476255221/20282409603651670423947251286016), (1058115371/20282409603651670423947251286016)), (35/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-27440257/649037107316853453566312041152512), (-967144653/324518553658426726783156020576256)), (65/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((682606781/10384593717069655257060992658440192), (1408405409/10384593717069655257060992658440192)), (29/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((329364537/16777216), (68395989/4194304)), (1/4194304), by norm_num⟩
  | 1 => ⟨((1431302899/1073741824), (30311839/134217728)), (1/134217728), by norm_num⟩
  | 2 => ⟨((268664589/34359738368), (-521140239/137438953472)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((-548509129/8796093022208), (173775087/2199023255552)), (5/4398046511104), by norm_num⟩
  | 4 => ⟨((106054923/281474976710656), (-480649359/281474976710656)), (9/281474976710656), by norm_num⟩
  | 5 => ⟨((303698125/36028797018963968), (638704451/18014398509481984)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-153601073/288230376151711744), (-377041655/576460752303423488)), (25/576460752303423488), by norm_num⟩
  | 7 => ⟨((349636565/18446744073709551616), (653552143/73786976294838206464)), (65/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-642902731/1180591620717411303424), (16071179/2361183241434822606848)), (155/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((994194709/75557863725914323419136), (-247429085/37778931862957161709568)), (53/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-151154257/604462909807314587353088), (389592287/1208925819614629174706176)), (291/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((11731929/4835703278458516698824704), (-1751310155/154742504910672534362390528)), (737/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((194630563/2475880078570760549798248448), (402419365/1237940039285380274899124224)), (991/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-321338871/18889465931478580854784), (651859577/37778931862957161709568)), (13/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((371716479/151115727451828646838272), (-1046879649/151115727451828646838272)), (3/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((143489369/1208925819614629174706176), (745549273/604462909807314587353088)), (17/604462909807314587353088), by norm_num⟩
  | 3 => ⟨((-752737645/9671406556917033397649408), (-318940953/2417851639229258349412352)), (37/9671406556917033397649408), by norm_num⟩
  | 4 => ⟨((988693595/77371252455336267181195264), (338651213/38685626227668133590597632)), (17/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((-1658232779/1237940039285380274899124224), (-136781481/618970019642690137449562112)), (51/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((509115375/4951760157141521099596496896), (-285776455/9903520314283042199192993792)), (35/9903520314283042199192993792), by norm_num⟩
  | 7 => ⟨((-926384003/158456325028528675187087900672), (199361921/39614081257132168796771975168)), (21/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((541199117/2535301200456458802993406410752), (-601201915/1267650600228229401496703205376)), (49/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((19055733/40564819207303340847894502572032), (671628231/20282409603651670423947251286016)), (55/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((-71104873/81129638414606681695789005144064), (-1173671175/649037107316853453566312041152512)), (29/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((943012681/10384593717069655257060992658440192), (191570483/2596148429267413814265248164610048)), (15/2596148429267413814265248164610048), by norm_num⟩
  | 12 => ⟨((-1059627577/166153499473114484112975882535043072), (-265212295/166153499473114484112975882535043072)), (59/166153499473114484112975882535043072), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((329364537/16777216), (68395989/4194304)), (9/33554432), by norm_num⟩
  | 1 => ⟨((1431302899/1073741824), (30311839/134217728)), (9/1073741824), by norm_num⟩
  | 2 => ⟨((268664589/34359738368), (-521140239/137438953472)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((-548509129/8796093022208), (173775087/2199023255552)), (11/8796093022208), by norm_num⟩
  | 4 => ⟨((106054923/281474976710656), (-480649359/281474976710656)), (19/562949953421312), by norm_num⟩
  | 5 => ⟨((303698125/36028797018963968), (638704451/18014398509481984)), (33/36028797018963968), by norm_num⟩
  | 6 => ⟨((-153601073/288230376151711744), (-377041655/576460752303423488)), (51/1152921504606846976), by norm_num⟩
  | 7 => ⟨((349636565/18446744073709551616), (653552143/73786976294838206464)), (131/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1285805461/2361183241434822606848), (8035589/1180591620717411303424)), (39/590295810358705651712), by norm_num⟩
  | 9 => ⟨((994194709/75557863725914323419136), (-494858167/75557863725914323419136)), (213/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-302308515/1208925819614629174706176), (389592285/1208925819614629174706176)), (73/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((187710871/77371252455336267181195264), (-27364221/2417851639229258349412352)), (369/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((194630547/2475880078570760549798248448), (402419363/1237940039285380274899124224)), (31/154742504910672534362390528), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-116221133/4835703278458516698824704), (-603867601/2417851639229258349412352)), (1/151115727451828646838272), by norm_num⟩
  | 1 => ⟨((28579215/604462909807314587353088), (774991467/9671406556917033397649408)), (33/9671406556917033397649408), by norm_num⟩
  | 2 => ⟨((-600604197/38685626227668133590597632), (-822885233/77371252455336267181195264)), (59/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((1678884763/618970019642690137449562112), (276969973/618970019642690137449562112)), (37/309485009821345068724781056), by norm_num⟩
  | 4 => ⟨((-1546368019/4951760157141521099596496896), (434003363/4951760157141521099596496896)), (77/4951760157141521099596496896), by norm_num⟩
  | 5 => ⟨((984817455/39614081257132168796771975168), (-847748229/39614081257132168796771975168)), (17/9903520314283042199192993792), by norm_num⟩
  | 6 => ⟨((-47944691/39614081257132168796771975168), (852165175/316912650057057350374175801344)), (13/79228162514264337593543950336), by norm_num⟩
  | 7 => ⟨((-17363751/5070602400912917605986812821504), (-1223987097/5070602400912917605986812821504)), (9/633825300114114700748351602688), by norm_num⟩
  | 8 => ⟨((647913851/81129638414606681695789005144064), (668412183/40564819207303340847894502572032)), (91/81129638414606681695789005144064), by norm_num⟩
  | 9 => ⟨((-164098887/162259276829213363391578010288128), (-266689971/324518553658426726783156020576256)), (57/649037107316853453566312041152512), by norm_num⟩
  | 10 => ⟨((885080133/10384593717069655257060992658440192), (221525127/10384593717069655257060992658440192)), (65/10384593717069655257060992658440192), by norm_num⟩
  | 11 => ⟨((-461123173/83076749736557242056487941267521536), (89577879/83076749736557242056487941267521536)), (9/20769187434139310514121985316880384), by norm_num⟩
  | 12 => ⟨((751216031/2658455991569831745807614120560689152), (-273281221/1329227995784915872903807060280344576)), (19/664613997892457936451903530140172288), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((329364537/16777216), (68395989/4194304)), (5/16777216), by norm_num⟩
  | 1 => ⟨((1431302899/1073741824), (30311839/134217728)), (5/536870912), by norm_num⟩
  | 2 => ⟨((268664589/34359738368), (-521140239/137438953472)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((-548509129/8796093022208), (173775087/2199023255552)), (3/2199023255552), by norm_num⟩
  | 4 => ⟨((106054923/281474976710656), (-480649359/281474976710656)), (5/140737488355328), by norm_num⟩
  | 5 => ⟨((303698125/36028797018963968), (638704451/18014398509481984)), (17/18014398509481984), by norm_num⟩
  | 6 => ⟨((-153601073/288230376151711744), (-377041655/576460752303423488)), (13/288230376151711744), by norm_num⟩
  | 7 => ⟨((349636565/18446744073709551616), (653552143/73786976294838206464)), (33/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-1285805461/2361183241434822606848), (8035589/1180591620717411303424)), (157/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((994194709/75557863725914323419136), (-494858167/75557863725914323419136)), (107/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-302308515/1208925819614629174706176), (389592285/1208925819614629174706176)), (293/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((375421741/154742504910672534362390528), (-27364221/2417851639229258349412352)), (739/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((389261095/4951760157141521099596496896), (1609677451/4951760157141521099596496896)), (993/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-581438219598189/2097152), (-793709288277593/4194304)), (617001431/2097152), by norm_num⟩
  | 1 => ⟨((-653680715/2), -314865865), (927/2), by norm_num⟩
  | 2 => ⟨((-370341005/2), (-494388327/2)), 368, by norm_num⟩
  | 3 => ⟨((-529090525/8), (-249203813/2)), (1571/8), by norm_num⟩
  | 4 => ⟨((-258624497/16), (-734038507/16)), (1267/16), by norm_num⟩
  | 5 => ⟨((-167351153/64), (-1695955623/128)), (3297/128), by norm_num⟩
  | 6 => ⟨((-89942873/512), (-200947243/64)), (3605/512), by norm_num⟩
  | 7 => ⟨((101387621/2048), (-1289491461/2048)), (3407/2048), by norm_num⟩
  | 8 => ⟨((5918137/256), (-223746533/2048)), (2843/8192), by norm_num⟩
  | 9 => ⟨((189976709/32768), (-273237635/16384)), (4255/65536), by norm_num⟩
  | 10 => ⟨((584478837/524288), (-1189083891/524288)), (2891/262144), by norm_num⟩
  | 11 => ⟨((377543719/2097152), (-581814351/2097152)), (3603/2097152), by norm_num⟩
  | 12 => ⟨((426597255/16777216), (-1031569371/33554432)), (8305/33554432), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((804774095615053/5070602400912917605986812821504), (-828031606415/2535301200456458802993406410752)), (194105/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((906411015038161/316912650057057350374175801344), (-4060147254255/633825300114114700748351602688)), (119453/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((241011317648409/4951760157141521099596496896), (-4579234655143/39614081257132168796771975168)), (269565/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((965149563518603/1237940039285380274899124224), (-4875408137103/2475880078570760549798248448)), (574157/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((453001651617649/38685626227668133590597632), (-2443285175075/77371252455336267181195264)), (143911/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((793931120337635/4835703278458516698824704), (-4593053689983/9671406556917033397649408)), (135313/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1292352885998193/604462909807314587353088), (-2015428246473/302231454903657293676544)), (475187/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((242802070218623/9444732965739290427392), (-1643151388999/18889465931478580854784)), (96897/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((20915318776281/73786976294838206464), (-4949196885535/4722366482869645213696)), (292009/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1677997723205927/590295810358705651712), (-53417120853/4611686018427387904)), (201833/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1894339777163161/73786976294838206464), (-4297698175923/36893488147419103232)), (1015669/73786976294838206464), by norm_num⟩
  | 7 => ⟨((475656566744375/2305843009213693952), (-608574755615/576460752303423488)), (1151643/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1674184059343589/1152921504606846976), (-9822128362353/1152921504606846976)), (290755/288230376151711744), by norm_num⟩
  | 5 => ⟨((1265104493160965/144115188075855872), (-1086362629045/18014398509481984)), (1030591/144115188075855872), by norm_num⟩
  | 4 => ⟨((1598129556695063/36028797018963968), (-13231931465699/36028797018963968)), (786081/18014398509481984), by norm_num⟩
  | 3 => ⟨((1623622865950735/9007199254740992), (-4221971719757/2251799813685248)), (2012051/9007199254740992), by norm_num⟩
  | 2 => ⟨((1250241568696951/2251799813685248), (-2177682062679/281474976710656)), (260511/281474976710656), by norm_num⟩
  | 1 => ⟨((164663284709761/140737488355328), (-27507640915457/1125899906842624)), (1656275/562949953421312), by norm_num⟩
  | 0 => ⟨((1528883669736405/1125899906842624), (-60773605170553/1125899906842624)), (926249/140737488355328), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1528883669736405/1125899906842624), (-60773605170553/1125899906842624)), (3533359528124761537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((2072823552358143/1125899906842624), (-165051567961901/1125899906842624)), (10462163/562949953421312), by norm_num⟩
  | 2 => ⟨((947987346205703/281474976710656), (-18991629237301/35184372088832)), (41589869/562949953421312), by norm_num⟩
  | 3 => ⟨((777685792897881/70368744177664), (-511699460070975/140737488355328)), (81260413/140737488355328), by norm_num⟩
  | 4 => ⟨((958053384387323/8796093022208), (-706885928157977/8796093022208)), (149188263/8796093022208), by norm_num⟩
  | 5 => ⟨((371417183149915/68719476736), (-75188128595141/4294967296)), (441228237/68719476736), by norm_num⟩
  | 6 => ⟨((-581438219598189/2097152), (-793709288277593/4194304)), (617001431/2097152), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((329364537/16777216), (68395989/4194304)), (5/16777216), by norm_num⟩, 3, gammaExpValuePoly, gammaExpValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem gammaExpValue_checks : CertifiedScalarExp.Checks gammaExpValue := by
  constructor
  · norm_num [gammaExpValue, CertifiedScalarExp.reduced, gammaExpValuePoly, gammaExpValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        gammaExpValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue, gammaExpValueSquares, gammaExpValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [gammaExpValue, CertifiedScalarExp.roundingCheck, gammaExpValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_gammaExp : Sound J_gammaExp F_gammaExp c := by
  apply exp_sound (A_mainCorr6 hcre) S_mainCorr6 gammaExpValue gammaExpValue_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [gammaExpValue,J_mainCorr6]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaExp,J_mainCorr6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse0 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2355200/67978969), (-10287360/67978969)), 0, by norm_num⟩
  | 1 => ⟨((50141404364800/4621140226302961), (24228790272000/4621140226302961)), 0, by norm_num⟩
  | 2 => ⟨((-642862749/1099511627776), (401421603/549755813888)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((-198445691/4398046511104), (-250201407/4398046511104)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((1431638653/281474976710656), (-341801691/140737488355328)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((107700331/1125899906842624), (961344671/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 6 => ⟨((-1223556109/36028797018963968), (-5678793/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 7 => ⟨((173002867/288230376151711744), (-369931691/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 8 => ⟨((211941567/1152921504606846976), (207256395/2305843009213693952)), (5/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-736804515/73786976294838206464), (911460281/73786976294838206464)), (1/4611686018427387904), by norm_num⟩
  | 10 => ⟨((-899242593/1180591620717411303424), (-143080201/147573952589676412928)), (25/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((817502039/9444732965739290427392), (-385705901/9444732965739290427392)), (5/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((240370183/151115727451828646838272), (34269247/4722366482869645213696)), (31/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((23/16), (8037/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((23/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((23/16), (8037/1280)))⁻¹=value ((2355200/67978969), (-10287360/67978969)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2355200/67978969), (-10287360/67978969))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((39/16), (8037/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor1 : Sound J_gammaFactor1 F_gammaFactor1 c := by
  apply sound_round (sound_add (A_base hcre) (A_q0 hcre) S_base S_q0)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor1, J_base, J_q0, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1331200/24775923), (-1143040/8258641)), 0, by norm_num⟩
  | 1 => ⟨((4993385267200/613846360501929), (1521614848000/204615453500643)), 0, by norm_num⟩
  | 2 => ⟨((-806114509/1099511627776), (399294251/1099511627776)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((-47809039/8796093022208), (-1064195717/17592186044416)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((304855775/70368744177664), (175778957/140737488355328)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((-913412689/4503599627370496), (299771213/1125899906842624)), (7/4503599627370496), by norm_num⟩
  | 6 => ⟨((-58441231/4503599627370496), (-381695041/18014398509481984)), (7/36028797018963968), by norm_num⟩
  | 7 => ⟨((65388723/36028797018963968), (-94767985/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 8 => ⟨((-239841205/9223372036854775808), (1239888493/9223372036854775808)), (19/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-634882473/73786976294838206464), (-399255977/73786976294838206464)), (15/73786976294838206464), by norm_num⟩
  | 10 => ⟨((357484515/590295810358705651712), (-531354131/1180591620717411303424)), (3/147573952589676412928), by norm_num⟩
  | 11 => ⟨((281018085/18889465931478580854784), (63752483/1180591620717411303424)), (19/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-1250223423/302231454903657293676544), (-63647623/151115727451828646838272)), (15/75557863725914323419136), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((39/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((39/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((39/16), (8037/1280)))⁻¹=value ((1331200/24775923), (-1143040/8258641)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((1331200/24775923), (-1143040/8258641))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-32141349683200/1684241701563387), (-7256932352000/561413900521129)), 0, by norm_num⟩
  | 1 => ⟨((746528573/274877906944), (-301462467/137438953472)), (1/274877906944), by norm_num⟩
  | 2 => ⟨((10203235/68719476736), (807097911/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-1396329373/35184372088832), (7923761/2199023255552)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((212215555/281474976710656), (-64697581/17592186044416)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((336053503/1125899906842624), (180901123/1125899906842624)), (7/4503599627370496), by norm_num⟩
  | 6 => ⟨((-756026263/36028797018963968), (94713911/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 7 => ⟨((-87526729/72057594037927936), (-322547699/144115188075855872)), (7/288230376151711744), by norm_num⟩
  | 8 => ⟨((120960859/576460752303423488), (-205431455/4611686018427387904)), (13/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-25480511/18446744073709551616), (655358129/36893488147419103232)), (21/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-807105811/590295810358705651712), (-76660935/147573952589676412928)), (9/295147905179352825856), by norm_num⟩
  | 11 => ⟨((338496499/4722366482869645213696), (-223931441/2361183241434822606848)), (29/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((865481893/151115727451828646838272), (145032941/18889465931478580854784)), (3/9444732965739290427392), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct1 : Sound J_gammaProduct1 F_gammaProduct1 c := by
  apply sound_round (sound_mul (A_gammaInverse0 hcre) (A_gammaInverse1 hcre) S_gammaInverse0 S_gammaInverse1)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct1, J_gammaInverse0, J_gammaInverse1, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(2, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q3 : Sound J_q3 F_q3 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (2, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((55/16), (8037/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor2 : Sound J_gammaFactor2 F_gammaFactor2 c := by
  apply sound_round (sound_add (A_base hcre) (A_q3 hcre) S_base S_q3)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor2, J_base, J_q3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5632000/83953369), (-10287360/83953369)), 0, by norm_num⟩
  | 1 => ⟨((37055175884800/7048168166450161), (57938411520000/7048168166450161)), 0, by norm_num⟩
  | 2 => ⟨((-1495321503/2199023255552), (50998219/1099511627776)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((351260549/17592186044416), (-380148045/8796093022208)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((139199659/70368744177664), (752373027/281474976710656)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((-1036367901/4503599627370496), (8877685/281474976710656)), (7/4503599627370496), by norm_num⟩
  | 6 => ⟨((208476539/36028797018963968), (-1092175409/72057594037927936)), (11/72057594037927936), by norm_num⟩
  | 7 => ⟨((423440869/576460752303423488), (994883559/1152921504606846976)), (9/576460752303423488), by norm_num⟩
  | 8 => ⟨((-714890347/9223372036854775808), (296259045/18446744073709551616)), (29/18446744073709551616), by norm_num⟩
  | 9 => ⟨((476912503/295147905179352825856), (-780299819/147573952589676412928)), (45/295147905179352825856), by norm_num⟩
  | 10 => ⟨((636947831/2361183241434822606848), (326263685/1180591620717411303424)), (35/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-490752153/18889465931478580854784), (274197691/37778931862957161709568)), (27/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((257958619/604462909807314587353088), (-1109317677/604462909807314587353088)), (83/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((55/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((55/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((55/16), (8037/1280)))⁻¹=value ((5632000/83953369), (-10287360/83953369)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((5632000/83953369), (-10287360/83953369))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-787290973/274877906944), (404423927/274877906944)), (1/274877906944), by norm_num⟩
  | 1 => ⟨((-22170317/274877906944), (-774902173/1099511627776)), (3/2199023255552), by norm_num⟩
  | 2 => ⟨((443411035/4398046511104), (221011695/8796093022208)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-251286059/35184372088832), (734579429/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((-112602227/140737488355328), (-317173091/281474976710656)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((610629399/4503599627370496), (-41679675/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-160039751/144115188075855872), (975013665/72057594037927936)), (17/144115188075855872), by norm_num⟩
  | 7 => ⟨((-661496265/576460752303423488), (-301606523/576460752303423488)), (17/1152921504606846976), by norm_num⟩
  | 8 => ⟨((182540575/2305843009213693952), (-187827735/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 9 => ⟨((652188555/147573952589676412928), (1319822325/147573952589676412928)), (7/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-125669171/147573952589676412928), (122165169/1180591620717411303424)), (25/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((145553939/9444732965739290427392), (-1337196205/18889465931478580854784)), (21/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((388770815/75557863725914323419136), (473290865/151115727451828646838272)), (9/37778931862957161709568), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct2 : Sound J_gammaProduct2 F_gammaProduct2 c := by
  apply sound_round (sound_mul (A_gammaProduct1 hcre) (A_gammaInverse2 hcre) S_gammaProduct1 S_gammaInverse2)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct2, J_gammaProduct1, J_gammaInverse2, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(3, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q4 : Sound J_q4 F_q4 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (3, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((71/16), (8037/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor3 : Sound J_gammaFactor3 F_gammaFactor3 c := by
  apply sound_round (sound_add (A_base hcre) (A_q4 hcre) S_base S_q4)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor3, J_base, J_q4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7270400/96855769), (-10287360/96855769)), 0, by norm_num⟩
  | 1 => ⟨((26485529804800/9381039988581361), (74793222144000/9381039988581361)), 0, by norm_num⟩
  | 2 => ⟨((-291025969/549755813888), (-328314367/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((15281729/549755813888), (-395994125/17592186044416)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((85636131/562949953421312), (1306637693/562949953421312)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((-1161682895/9007199254740992), (-711888125/9007199254740992)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((1302501557/144115188075855872), (-559589897/144115188075855872)), (3/36028797018963968), by norm_num⟩
  | 7 => ⟨((-76670799/576460752303423488), (90174003/144115188075855872)), (9/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-520887069/18446744073709551616), (-563500873/18446744073709551616)), (7/9223372036854775808), by norm_num⟩
  | 9 => ⟨((791609527/295147905179352825856), (-208421419/590295810358705651712)), (41/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-96705955/1180591620717411303424), (735214913/4722366482869645213696)), (31/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-392423219/75557863725914323419136), (-385096417/37778931862957161709568)), (23/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1780185087/2417851639229258349412352), (258134101/2417851639229258349412352)), (67/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((71/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((71/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((71/16), (8037/1280)))⁻¹=value ((7270400/96855769), (-10287360/96855769)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7270400/96855769), (-10287360/96855769))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-129137647/2199023255552), (455913757/1099511627776)), (1/1099511627776), by norm_num⟩
  | 1 => ⟨((-886001931/8796093022208), (-554309713/8796093022208)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((1221871589/70368744177664), (-830802197/70368744177664)), (5/70368744177664), by norm_num⟩
  | 3 => ⟨((308468213/562949953421312), (1636732671/562949953421312)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((-798737067/2251799813685248), (-358605029/4503599627370496)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((214259043/9007199254740992), (-297497423/9007199254740992)), (13/36028797018963968), by norm_num⟩
  | 6 => ⟨((79806277/36028797018963968), (262041937/72057594037927936)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((-60235815/144115188075855872), (73503491/1152921504606846976)), (7/1152921504606846976), by norm_num⟩
  | 8 => ⟨((176942881/18446744073709551616), (-1443000595/36893488147419103232)), (27/36893488147419103232), by norm_num⟩
  | 9 => ⟨((442541633/147573952589676412928), (643220773/295147905179352825856)), (25/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-332003663/1180591620717411303424), (25925169/147573952589676412928)), (3/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-379037/73786976294838206464), (-1075895413/37778931862957161709568)), (5/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((732637571/302231454903657293676544), (36619761/75557863725914323419136)), (69/604462909807314587353088), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct3 : Sound J_gammaProduct3 F_gammaProduct3 c := by
  apply sound_round (sound_mul (A_gammaProduct2 hcre) (A_gammaInverse3 hcre) S_gammaProduct2 S_gammaInverse3)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct3, J_gammaProduct2, J_gammaInverse3, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(4, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q5 : Sound J_q5 F_q5 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (4, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((87/16), (8037/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor4 : Sound J_gammaFactor4 F_gammaFactor4 c := by
  apply sound_round (sound_add (A_base hcre) (A_q5 hcre) S_base S_q5)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor4, J_base, J_q5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2969600/37678323), (-1143040/12559441)), 0, by norm_num⟩
  | 1 => ⟨((1470169907200/1419656024092329), (3394371584000/473218674697443)), 0, by norm_num⟩
  | 2 => ⟨((-807516147/2199023255552), (-517962001/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((221567919/8796093022208), (-261355541/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((-368520193/562949953421312), (405034305/281474976710656)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-357439455/9007199254740992), (-97384369/1125899906842624)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((1585205883/288230376151711744), (230973803/144115188075855872)), (5/72057594037927936), by norm_num⟩
  | 7 => ⟨((-166979331/576460752303423488), (431448245/2305843009213693952)), (15/2305843009213693952), by norm_num⟩
  | 8 => ⟨((214005057/73786976294838206464), (-758334677/36893488147419103232)), (21/36893488147419103232), by norm_num⟩
  | 9 => ⟨((121166003/147573952589676412928), (1112098399/1180591620717411303424)), (29/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-355219385/4722366482869645213696), (2277671/9444732965739290427392)), (5/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((892569901/302231454903657293676544), (-1037389511/302231454903657293676544)), (109/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((192526093/4835703278458516698824704), (162994547/604462909807314587353088)), (149/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((87/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((87/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((87/16), (8037/1280)))⁻¹=value ((2969600/37678323), (-1143040/12559441)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((2969600/37678323), (-1143040/12559441))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((291231519/8796093022208), (83618145/2199023255552)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((-1175797495/70368744177664), (296157097/70368744177664)), (7/70368744177664), by norm_num⟩
  | 2 => ⟨((107095767/140737488355328), (-120929001/35184372088832)), (3/140737488355328), by norm_num⟩
  | 3 => ⟨((244436495/562949953421312), (786663609/2251799813685248)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-1228784757/18014398509481984), (72054017/2251799813685248)), (13/18014398509481984), by norm_num⟩
  | 5 => ⟨((7260483/72057594037927936), (-1316204707/144115188075855872)), (15/144115188075855872), by norm_num⟩
  | 6 => ⟨((16522327/18014398509481984), (259125767/576460752303423488)), (17/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-772348969/9223372036854775808), (618763873/9223372036854775808)), (9/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-377279975/147573952589676412928), (-1536222119/147573952589676412928)), (9/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1191378405/1180591620717411303424), (28441799/147573952589676412928)), (35/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-516752081/9444732965739290427392), (91809451/1180591620717411303424)), (17/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-330895391/75557863725914323419136), (-1107873883/151115727451828646838272)), (59/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((1792483417/2417851639229258349412352), (-224370007/2417851639229258349412352)), (13/302231454903657293676544), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct4 : Sound J_gammaProduct4 F_gammaProduct4 c := by
  apply sound_round (sound_mul (A_gammaProduct3 hcre) (A_gammaInverse4 hcre) S_gammaProduct3 S_gammaInverse4)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct4, J_gammaProduct3, J_gammaInverse4, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(5, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q6 : Sound J_q6 F_q6 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (5, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((103/16), (8037/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor5 : Sound J_gammaFactor5 F_gammaFactor5 c := by
  apply sound_round (sound_add (A_base hcre) (A_q6 hcre) S_base S_q6)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor5, J_base, J_q6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10547200/132490969), (-10287360/132490969)), 0, by norm_num⟩
  | 1 => ⟨((-2706826035200/17553856866558961), (108502843392000/17553856866558961)), 0, by norm_num⟩
  | 2 => ⟨((-514201697/2199023255552), (-1108383949/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((41982335/2199023255552), (67071213/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-897236121/1125899906842624), (6185791/8796093022208)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((9947773/2251799813685248), (-530791383/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 6 => ⟨((76092091/36028797018963968), (181377137/72057594037927936)), (9/288230376151711744), by norm_num⟩
  | 7 => ⟨((-1676677073/9223372036854775808), (-41958781/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 8 => ⟨((293013613/36893488147419103232), (-934608005/147573952589676412928)), (1/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-165882625/2361183241434822606848), (1323250561/2361183241434822606848)), (41/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-358157473/18889465931478580854784), (-945760015/37778931862957161709568)), (53/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1043663029/604462909807314587353088), (157361989/604462909807314587353088)), (17/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((-762410433/9671406556917033397649408), (274035551/4835703278458516698824704)), (43/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((103/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((103/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((103/16), (8037/1280)))⁻¹=value ((10547200/132490969), (-10287360/132490969)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((10547200/132490969), (-10287360/132490969))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((393235371/70368744177664), (128430361/281474976710656)), (11/281474976710656), by norm_num⟩
  | 1 => ⟨((-87504937/70368744177664), (1030882917/562949953421312)), (11/562949953421312), by norm_num⟩
  | 2 => ⟨((-256579063/1125899906842624), (-15968811/35184372088832)), (5/1125899906842624), by norm_num⟩
  | 3 => ⟨((1592152345/18014398509481984), (29852363/9007199254740992)), (15/18014398509481984), by norm_num⟩
  | 4 => ⟨((-475013517/72057594037927936), (802933505/72057594037927936)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((-502286901/576460752303423488), (-826833473/576460752303423488)), (15/576460752303423488), by norm_num⟩
  | 6 => ⟨((1828834597/9223372036854775808), (-28054405/2305843009213693952)), (33/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-655018407/73786976294838206464), (1477558157/73786976294838206464)), (37/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-423794619/295147905179352825856), (-261483019/147573952589676412928)), (19/295147905179352825856), by norm_num⟩
  | 9 => ⟨((130597609/590295810358705651712), (-56940399/1180591620717411303424)), (19/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-396761825/75557863725914323419136), (1582777155/75557863725914323419136)), (37/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-460031495/302231454903657293676544), (-774464449/604462909807314587353088)), (17/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((784054527/4835703278458516698824704), (-176612589/2417851639229258349412352)), (61/4835703278458516698824704), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct5 : Sound J_gammaProduct5 F_gammaProduct5 c := by
  apply sound_round (sound_mul (A_gammaProduct4 hcre) (A_gammaInverse5 hcre) S_gammaProduct4 S_gammaInverse5)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct5, J_gammaProduct4, J_gammaInverse5, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(6, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q7 : Sound J_q7 F_q7 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (6, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((119/16), (8037/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor6 : Sound J_gammaFactor6 F_gammaFactor6 c := by
  apply sound_round (sound_add (A_base hcre) (A_q7 hcre) S_base S_q7)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor6, J_base, J_q7, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((12185600/155223769), (-10287360/155223769)), 0, by norm_num⟩
  | 1 => ⟨((-21329535795200/24094418462565361), (125357654016000/24094418462565361)), 0, by norm_num⟩
  | 2 => ⟨((-605424525/4398046511104), (-513586729/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((924825591/70368744177664), (162050049/35184372088832)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-1505304421/2251799813685248), (286794203/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((641258859/36028797018963968), (-72395895/2251799813685248)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((211414951/576460752303423488), (533729069/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 7 => ⟨((-698735471/9223372036854775808), (-558301927/9223372036854775808)), (13/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1469668101/295147905179352825856), (-1239821/9223372036854775808)), (31/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-901956921/4722366482869645213696), (50257959/295147905179352825856)), (37/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((140109407/75557863725914323419136), (-491613619/37778931862957161709568)), (11/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((54163711/151115727451828646838272), (172944773/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((-1277816579/38685626227668133590597632), (-204717645/19342813113834066795298816)), (121/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((119/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((119/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((119/16), (8037/1280)))⁻¹=value ((12185600/155223769), (-10287360/155223769)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12185600/155223769), (-10287360/155223769))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1055943699/2251799813685248), (-47081753/140737488355328)), (7/1125899906842624), by norm_num⟩
  | 1 => ⟨((4622175/281474976710656), (17932807/70368744177664)), (15/4503599627370496), by norm_num⟩
  | 2 => ⟨((-128484559/2251799813685248), (-540166793/18014398509481984)), (15/18014398509481984), by norm_num⟩
  | 3 => ⟨((748767453/72057594037927936), (-56845179/9007199254740992)), (13/72057594037927936), by norm_num⟩
  | 4 => ⟨((12822689/576460752303423488), (1097411941/576460752303423488)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((-1048780759/4611686018427387904), (-594167325/4611686018427387904)), (25/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1031374513/36893488147419103232), (-152877481/9223372036854775808)), (15/18446744073709551616), by norm_num⟩
  | 7 => ⟨((24256229/295147905179352825856), (551527377/147573952589676412928)), (33/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-843462609/2361183241434822606848), (-443687351/2361183241434822606848)), (35/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((650175831/18889465931478580854784), (-432765051/18889465931478580854784)), (9/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((7257703/18889465931478580854784), (304675699/75557863725914323419136)), (71/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-853760483/2417851639229258349412352), (-175595761/1208925819614629174706176)), (67/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((513757339/19342813113834066795298816), (-869638667/38685626227668133590597632)), (123/38685626227668133590597632), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct6 : Sound J_gammaProduct6 F_gammaProduct6 c := by
  apply sound_round (sound_mul (A_gammaProduct5 hcre) (A_gammaInverse6 hcre) S_gammaProduct5 S_gammaInverse6)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct6, J_gammaProduct5, J_gammaInverse6, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(7, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q8 : Sound J_q8 F_q8 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (7, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((135/16), (8037/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor7 : Sound J_gammaFactor7 F_gammaFactor7 c := by
  apply sound_round (sound_add (A_base hcre) (A_q8 hcre) S_base S_q8)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor7, J_base, J_q8, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((512000/6712347), (-1143040/20137041)), 0, by norm_num⟩
  | 1 => ⟨((-526377779200/405500420235681), (585236480000/135166806745227)), 0, by norm_num⟩
  | 2 => ⟨((-322715063/4398046511104), (-888283349/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1200600415/140737488355328), (49437601/8796093022208)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-545913121/1125899906842624), (31256989/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((637864969/36028797018963968), (-533950361/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((-293535855/1152921504606846976), (1230967691/1152921504606846976)), (7/576460752303423488), by norm_num⟩
  | 7 => ⟨((-94966707/4611686018427387904), (-884455505/18446744073709551616)), (1/1152921504606846976), by norm_num⟩
  | 8 => ⟨((633437045/295147905179352825856), (367212115/295147905179352825856)), (35/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-553287819/4722366482869645213696), (63566865/4722366482869645213696)), (19/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((308760605/75557863725914323419136), (-580080311/151115727451828646838272)), (21/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-226811937/4835703278458516698824704), (1268790029/4835703278458516698824704)), (91/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-218879153/38685626227668133590597632), (-877235777/77371252455336267181195264)), (97/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((135/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((135/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((135/16), (8037/1280)))⁻¹=value ((512000/6712347), (-1143040/20137041)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((512000/6712347), (-1143040/20137041))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((302276105/18014398509481984), (-117398929/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((596558685/36028797018963968), (755561785/36028797018963968)), (9/18014398509481984), by norm_num⟩
  | 2 => ⟨((-262326365/36028797018963968), (89603875/144115188075855872)), (5/36028797018963968), by norm_num⟩
  | 3 => ⟨((400306835/576460752303423488), (-375157825/288230376151711744)), (9/288230376151711744), by norm_num⟩
  | 4 => ⟨((277193883/2305843009213693952), (983657401/4611686018427387904)), (7/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-1302290221/36893488147419103232), (-15141037/9223372036854775808)), (37/36893488147419103232), by norm_num⟩
  | 6 => ⟨((762766867/295147905179352825856), (-1118715787/295147905179352825856)), (23/147573952589676412928), by norm_num⟩
  | 7 => ⟨((268491635/1180591620717411303424), (1176608423/2361183241434822606848)), (13/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-573583647/9444732965739290427392), (-124797227/18889465931478580854784)), (57/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((578575931/151115727451828646838272), (-390859587/75557863725914323419136)), (59/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((626203227/2417851639229258349412352), (715348409/1208925819614629174706176)), (119/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-1196361663/19342813113834066795298816), (-60472695/9671406556917033397649408)), (115/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((254266523/77371252455336267181195264), (-366684707/77371252455336267181195264)), (27/38685626227668133590597632), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct7 : Sound J_gammaProduct7 F_gammaProduct7 c := by
  apply sound_round (sound_mul (A_gammaProduct6 hcre) (A_gammaInverse7 hcre) S_gammaProduct6 S_gammaInverse7)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct7, J_gammaProduct6, J_gammaInverse7, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(8, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q9 : Sound J_q9 F_q9 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (8, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((151/16), (8037/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor8 : Sound J_gammaFactor8 F_gammaFactor8 c := by
  apply sound_round (sound_add (A_base hcre) (A_q9 hcre) S_base S_q9)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor8, J_base, J_q9, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((15462400/210519769), (-10287360/210519769)), 0, by norm_num⟩
  | 1 => ⟨((-66628018995200/44318573139813361), (159067275264000/44318573139813361)), 0, by norm_num⟩
  | 2 => ⟨((-285735103/8796093022208), (-741259369/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((93432339/17592186044416), (379704727/70368744177664)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-736076203/2251799813685248), (-154015593/2251799813685248)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((985440453/72057594037927936), (-197257681/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-849611641/2305843009213693952), (9641455/18014398509481984)), (13/2305843009213693952), by norm_num⟩
  | 7 => ⟨((16771437/36893488147419103232), (-528644037/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 8 => ⟨((403472849/590295810358705651712), (1255615661/1180591620717411303424)), (29/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-482506467/9444732965739290427392), (-105581445/4722366482869645213696)), (29/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1464264067/604462909807314587353088), (-258200193/604462909807314587353088)), (29/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-759447475/9671406556917033397649408), (724143157/9671406556917033397649408)), (29/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((326305453/309485009821345068724781056), (-180597773/38685626227668133590597632)), (57/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((151/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((151/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((151/16), (8037/1280)))⁻¹=value ((15462400/210519769), (-10287360/210519769)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((15462400/210519769), (-10287360/210519769))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-379091149/288230376151711744), (-670028351/144115188075855872)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((1385137119/576460752303423488), (62674161/72057594037927936)), (39/576460752303423488), by norm_num⟩
  | 2 => ⟨((-353884829/576460752303423488), (246858651/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((-4778293/9223372036854775808), (-1478136917/9223372036854775808)), (11/2305843009213693952), by norm_num⟩
  | 4 => ⟨((855460023/36893488147419103232), (144481583/9223372036854775808)), (9/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-1153183031/295147905179352825856), (235470709/147573952589676412928)), (49/295147905179352825856), by norm_num⟩
  | 6 => ⟨((257598271/2361183241434822606848), (-1319303561/2361183241434822606848)), (31/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((957697275/18889465931478580854784), (919394991/18889465931478580854784)), (9/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-1183927439/151115727451828646838272), (292218449/151115727451828646838272)), (81/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((325079115/1208925819614629174706176), (-1002783415/1208925819614629174706176)), (43/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((70516391/1208925819614629174706176), (328042091/4835703278458516698824704)), (11/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-334553157/38685626227668133590597632), (57914571/38685626227668133590597632)), (43/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((359989739/1237940039285380274899124224), (-479678425/618970019642690137449562112)), (41/309485009821345068724781056), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct8 : Sound J_gammaProduct8 F_gammaProduct8 c := by
  apply sound_round (sound_mul (A_gammaProduct7 hcre) (A_gammaInverse8 hcre) S_gammaProduct7 S_gammaInverse8)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct8, J_gammaProduct7, J_gammaInverse8, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(9, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q10 : Sound J_q10 F_q10 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (9, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((167/16), (8037/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor9 : Sound J_gammaFactor9 F_gammaFactor9 c := by
  apply sound_round (sound_add (A_base hcre) (A_q10 hcre) S_base S_q10)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor9, J_base, J_q10, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((17100800/243082969), (-10287360/243082969)), 0, by norm_num⟩
  | 1 => ⟨((-93303792435200/59089329817854961), (175922085888000/59089329817854961)), 0, by norm_num⟩
  | 2 => ⟨((-32794007/4398046511104), (-1215055551/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((448285503/140737488355328), (661624121/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-952590389/4503599627370496), (-441174629/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((1370961037/144115188075855872), (-148439929/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((-90164587/288230376151711744), (547698141/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 7 => ⟨((55131173/9223372036854775808), (-1104908071/73786976294838206464)), (15/73786976294838206464), by norm_num⟩
  | 8 => ⟨((251719143/2361183241434822606848), (771162071/1180591620717411303424)), (7/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-165960145/9444732965739290427392), (-782792849/37778931862957161709568)), (27/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((319316107/302231454903657293676544), (431603543/1208925819614629174706176)), (25/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-1729931449/38685626227668133590597632), (379058271/38685626227668133590597632)), (91/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((422632699/309485009821345068724781056), (-199755889/154742504910672534362390528)), (83/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((167/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((167/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((167/16), (8037/1280)))⁻¹=value ((17100800/243082969), (-10287360/243082969)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((17100800/243082969), (-10287360/243082969))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-333522463/1152921504606846976), (-312916937/1152921504606846976)), (29/2305843009213693952), by norm_num⟩
  | 1 => ⟨((1022716277/4611686018427387904), (-170975755/4611686018427387904)), (19/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-591776673/18446744073709551616), (1145594117/18446744073709551616)), (25/9223372036854775808), by norm_num⟩
  | 3 => ⟨((-516832929/73786976294838206464), (-1041546161/73786976294838206464)), (49/73786976294838206464), by norm_num⟩
  | 4 => ⟨((1675980267/590295810358705651712), (276855855/590295810358705651712)), (81/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-374403659/1180591620717411303424), (47398267/147573952589676412928)), (29/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((-219356753/18889465931478580854784), (-1169877565/18889465931478580854784)), (75/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((555013801/75557863725914323419136), (485260929/151115727451828646838272)), (89/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((-961882505/1208925819614629174706176), (616649001/1208925819614629174706176)), (51/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((9733433/9671406556917033397649408), (-2021552793/19342813113834066795298816)), (55/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((707983893/77371252455336267181195264), (232163571/38685626227668133590597632)), (115/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-1230366601/1237940039285380274899124224), (561820903/1237940039285380274899124224)), (57/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((64458039/4951760157141521099596496896), (-257044081/2475880078570760549798248448)), (55/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct9 : Sound J_gammaProduct9 F_gammaProduct9 c := by
  apply sound_round (sound_mul (A_gammaProduct8 hcre) (A_gammaInverse9 hcre) S_gammaProduct8 S_gammaInverse9)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct9, J_gammaProduct8, J_gammaInverse9, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(10, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q11 : Sound J_q11 F_q11 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (10, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((183/16), (8037/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor10 : Sound J_gammaFactor10 F_gammaFactor10 c := by
  apply sound_round (sound_add (A_base hcre) (A_q11 hcre) S_base S_q11)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor10, J_base, J_q11, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6246400/92974323), (-1143040/30991441)), 0, by norm_num⟩
  | 1 => ⟨((-13629324492800/8644224737308329), (7139885056000/2881408245769443)), 0, by norm_num⟩
  | 2 => ⟨((63936533/8796093022208), (-1975857913/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((257133685/140737488355328), (1099700695/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-1201764121/9007199254740992), (-878640163/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1810334143/288230376151711744), (235307037/288230376151711744)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((-521217767/2305843009213693952), (101921283/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((879979403/147573952589676412928), (-1053400681/147573952589676412928)), (7/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-162149371/2361183241434822606848), (1651641731/4722366482869645213696)), (3/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-156515387/37778931862957161709568), (-491700239/37778931862957161709568)), (21/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((458407311/1208925819614629174706176), (54523577/151115727451828646838272)), (9/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-1500332873/77371252455336267181195264), (-396728853/77371252455336267181195264)), (61/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((230861807/309485009821345068724781056), (-229456415/1237940039285380274899124224)), (13/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((183/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((183/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((183/16), (8037/1280)))⁻¹=value ((6246400/92974323), (-1143040/30991441)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((6246400/92974323), (-1143040/30991441))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-271588485/9223372036854775808), (-279101853/36893488147419103232)), (49/36893488147419103232), by norm_num⟩
  | 1 => ⟨((540874345/36893488147419103232), (-808630281/73786976294838206464)), (17/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-45795389/295147905179352825856), (1769120121/295147905179352825856)), (47/147573952589676412928), by norm_num⟩
  | 3 => ⟨((-647274675/590295810358705651712), (-527852451/590295810358705651712)), (49/590295810358705651712), by norm_num⟩
  | 4 => ⟨((617151815/2361183241434822606848), (-149675197/2361183241434822606848)), (83/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-322468555/18889465931478580854784), (759818911/18889465931478580854784)), (31/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((-244259349/75557863725914323419136), (-203954821/37778931862957161709568)), (41/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((991431329/1208925819614629174706176), (20114977/302231454903657293676544)), (99/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-76667739/1208925819614629174706176), (739887977/9671406556917033397649408)), (115/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-474671703/154742504910672534362390528), (-835458231/77371252455336267181195264)), (253/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((1409124483/1237940039285380274899124224), (230170037/618970019642690137449562112)), (67/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-942115505/9903520314283042199192993792), (749172621/9903520314283042199192993792)), (271/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-91428673/79228162514264337593543950336), (-465487607/39614081257132168796771975168)), (33/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct10 : Sound J_gammaProduct10 F_gammaProduct10 c := by
  apply sound_round (sound_mul (A_gammaProduct9 hcre) (A_gammaInverse10 hcre) S_gammaProduct9 S_gammaInverse10)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct10, J_gammaProduct9, J_gammaInverse10, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_q12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨(11, 0), 0, by norm_num⟩
  | 1 => ⟨(0, 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

theorem S_q12 : Sound J_q12 F_q12 c := by
  have h := constant_sound (d:=12) (c:=c) (contains_exact (11, 0))
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_gammaFactor11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((199/16), (8037/1280)), 0, by norm_num⟩
  | 1 => ⟨((1/2), 0), 0, by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
  | 5 => ⟨(0, 0), 0, by norm_num⟩
  | 6 => ⟨(0, 0), 0, by norm_num⟩
  | 7 => ⟨(0, 0), 0, by norm_num⟩
  | 8 => ⟨(0, 0), 0, by norm_num⟩
  | 9 => ⟨(0, 0), 0, by norm_num⟩
  | 10 => ⟨(0, 0), 0, by norm_num⟩
  | 11 => ⟨(0, 0), 0, by norm_num⟩
  | 12 => ⟨(0, 0), 0, by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFactor11 : Sound J_gammaFactor11 F_gammaFactor11 c := by
  apply sound_round (sound_add (A_base hcre) (A_q12 hcre) S_base S_q12)
  intro k
  fin_cases k <;> norm_num [J_gammaFactor11, J_base, J_q12, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaInverse11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((20377600/318039769), (-10287360/318039769)), 0, by norm_num⟩
  | 1 => ⟨((-154708402995200/101149294665573361), (209631707136000/101149294665573361)), 0, by norm_num⟩
  | 2 => ⟨((272343841/17592186044416), (-400802137/4398046511104)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((275262925/281474976710656), (111530837/35184372088832)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-185990083/2251799813685248), (-772236379/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1162340157/288230376151711744), (101659441/72057594037927936)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-1402035069/9223372036854775808), (184686837/9223372036854775808)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((670863771/147573952589676412928), (-457470185/147573952589676412928)), (5/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-450984259/4722366482869645213696), (204044439/1180591620717411303424)), (1/295147905179352825856), by norm_num⟩
  | 9 => ⟨((9981927/37778931862957161709568), (-535057143/75557863725914323419136)), (25/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((512892841/4835703278458516698824704), (1117702313/4835703278458516698824704)), (5/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-1104250895/154742504910672534362390528), (-440190921/77371252455336267181195264)), (31/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((1587664993/4951760157141521099596496896), (165519993/2475880078570760549798248448)), (97/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((199/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((199/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((199/16), (8037/1280)))⁻¹=value ((20377600/318039769), (-10287360/318039769)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((20377600/318039769), (-10287360/318039769))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1258132333/590295810358705651712), (138052877/295147905179352825856)), (77/590295810358705651712), by norm_num⟩
  | 1 => ⟨((23817153/36893488147419103232), (-723604089/590295810358705651712)), (7/73786976294838206464), by norm_num⟩
  | 2 => ⟨((432298735/2361183241434822606848), (1036044697/2361183241434822606848)), (81/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-1059164877/9444732965739290427392), (-155470619/4722366482869645213696)), (11/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((355529387/18889465931478580854784), (-501514939/37778931862957161709568)), (39/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-27347679/151115727451828646838272), (36448717/9444732965739290427392)), (119/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-529959229/1208925819614629174706176), (-889520859/2417851639229258349412352)), (81/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((352723/4722366482869645213696), (-339781245/19342813113834066795298816)), (25/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((-572166479/154742504910672534362390528), (1349942697/154742504910672534362390528)), (59/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-351855025/618970019642690137449562112), (-1153654115/1237940039285380274899124224)), (33/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((585514797/4951760157141521099596496896), (75943881/9903520314283042199192993792)), (283/9903520314283042199192993792), by norm_num⟩
  | 11 => ⟨((-598995827/79228162514264337593543950336), (759850781/79228162514264337593543950336)), (291/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-232568517/633825300114114700748351602688), (-1451566459/1267650600228229401496703205376)), (575/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((747046935/1099511627776), (601753707/2199023255552)), (227/274877906944), by norm_num⟩
  | 1 => ⟨((238008839/549755813888), (202286985/274877906944)), (259/137438953472), by norm_num⟩
  | 2 => ⟨((-14956049/274877906944), (1058464115/2199023255552)), (4707/2199023255552), by norm_num⟩
  | 3 => ⟨((-264184309/2199023255552), (288808677/2199023255552)), (223/137438953472), by norm_num⟩
  | 4 => ⟨((-204102341/4398046511104), (370707057/35184372088832)), (16305/17592186044416), by norm_num⟩
  | 5 => ⟨((-1303430801/140737488355328), (-240926061/70368744177664)), (15015/35184372088832), by norm_num⟩
  | 6 => ⟨((-586618755/562949953421312), (-364069567/281474976710656)), (92987/562949953421312), by norm_num⟩
  | 7 => ⟨((-198221331/4503599627370496), (-1039182405/4503599627370496)), (249201/4503599627370496), by norm_num⟩
  | 8 => ⟨((254214859/36028797018963968), (-505679377/18014398509481984)), (590559/36028797018963968), by norm_num⟩
  | 9 => ⟨((273080817/144115188075855872), (-748361043/288230376151711744)), (157247/36028797018963968), by norm_num⟩
  | 10 => ⟨((157521669/576460752303423488), (-845860355/4611686018427387904)), (1219915/1152921504606846976), by norm_num⟩
  | 11 => ⟨((1113228369/36893488147419103232), (-299261513/36893488147419103232)), (8706627/36893488147419103232), by norm_num⟩
  | 12 => ⟨((1621007723/590295810358705651712), (75904333/590295810358705651712)), (7206737/147573952589676412928), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((747046935/1099511627776), (601753707/2199023255552)), (1817/2199023255552), by norm_num⟩
  | 1 => ⟨((238008839/549755813888), (202286985/274877906944)), (2073/1099511627776), by norm_num⟩
  | 2 => ⟨((-14956049/274877906944), (1058464115/2199023255552)), (1177/549755813888), by norm_num⟩
  | 3 => ⟨((-264184309/2199023255552), (288808677/2199023255552)), (7137/4398046511104), by norm_num⟩
  | 4 => ⟨((-204102341/4398046511104), (370707057/35184372088832)), (8153/8796093022208), by norm_num⟩
  | 5 => ⟨((-1303430801/140737488355328), (-240926061/70368744177664)), (30033/70368744177664), by norm_num⟩
  | 6 => ⟨((-586618755/562949953421312), (-364069567/281474976710656)), (46505/281474976710656), by norm_num⟩
  | 7 => ⟨((-198221331/4503599627370496), (-1039182405/4503599627370496)), (124691/2251799813685248), by norm_num⟩
  | 8 => ⟨((254214859/36028797018963968), (-505679377/18014398509481984)), (592001/36028797018963968), by norm_num⟩
  | 9 => ⟨((273080817/144115188075855872), (-748361043/288230376151711744)), (634753/144115188075855872), by norm_num⟩
  | 10 => ⟨((157521669/576460752303423488), (-845860355/4611686018427387904)), (79127/72057594037927936), by norm_num⟩
  | 11 => ⟨((1113228369/36893488147419103232), (-299261513/36893488147419103232)), (10182367/36893488147419103232), by norm_num⟩
  | 12 => ⟨((1621007723/590295810358705651712), (75904333/590295810358705651712)), (52438781/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨32,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile032Gamma

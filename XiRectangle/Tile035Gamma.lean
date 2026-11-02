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
namespace Reinmann.XiRectangle.Tile035Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨35,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (8601/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (8601/640))
  have he : value ((5/8), (8601/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((213/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7270400/121446267), (-3669760/121446267)), 0, by norm_num⟩
  | 1 => ⟨((-6565262950400/4916398589411763), (26680623104000/14749195768235289)), 0, by norm_num⟩
  | 2 => ⟨((222376845/17592186044416), (-1307492931/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((104784337/140737488355328), (1359885851/562949953421312)), (3/562949953421312), by norm_num⟩
  | 4 => ⟨((-529468781/9007199254740992), (-549957167/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((773037925/288230376151711744), (541575539/576460752303423488)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((-217841889/2305843009213693952), (114371997/9223372036854775808)), (15/18446744073709551616), by norm_num⟩
  | 7 => ⟨((779336975/295147905179352825856), (-265417131/147573952589676412928)), (3/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-489837331/9444732965739290427392), (55327819/590295810358705651712)), (19/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((10298423/75557863725914323419136), (-542374609/151115727451828646838272)), (7/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((484991397/9671406556917033397649408), (529467517/4835703278458516698824704)), (21/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-976513359/309485009821345068724781056), (-779812095/309485009821345068724781056)), (61/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((1312365207/9903520314283042199192993792), (274817991/9903520314283042199192993792)), (89/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((213/16), (8601/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((213/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((213/16), (8601/1280)))⁻¹=value ((7270400/121446267), (-3669760/121446267)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((7270400/121446267), (-3669760/121446267))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((90670183/33554432), (62739163/134217728)), (1/268435456), by norm_num⟩
  | 1 => ⟨((3635200/121446267), (-1834880/121446267)), 0, by norm_num⟩
  | 2 => ⟨((-1641315737600/4916398589411763), (6670155776000/14749195768235289)), 0, by norm_num⟩
  | 3 => ⟨((74125615/35184372088832), (-435830977/35184372088832)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((104784337/1125899906842624), (1359885851/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((-423575025/72057594037927936), (-879931467/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((1030717233/4611686018427387904), (361050359/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((-995848635/147573952589676412928), (65355427/73786976294838206464)), (5/73786976294838206464), by norm_num⟩
  | 8 => ⟨((779336975/4722366482869645213696), (-265417131/2361183241434822606848)), (3/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-435410961/151115727451828646838272), (786884537/151115727451828646838272)), (9/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((65909907/9671406556917033397649408), (-1735598749/9671406556917033397649408)), (23/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((44090127/19342813113834066795298816), (385067285/77371252455336267181195264)), (31/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-325504453/2475880078570760549798248448), (-259937365/2475880078570760549798248448)), (41/4951760157141521099596496896), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-7005/276736), (183/20480)), 0, by norm_num⟩
  | 45 => ⟨((92717555873/4080638361600), (-731451/60293120)), 0, by norm_num⟩
  | 44 => ⟨((-246470258335723/11491077626265600), (6863542799453/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((377876003/17179869184), (-188170511/17179869184)), (1/34359738368), by norm_num⟩
  | 42 => ⟨((-786979525/34359738368), (1486747/134217728)), (1/17179869184), by norm_num⟩
  | 41 => ⟨((810386479/34359738368), (-394438465/34359738368)), (3/34359738368), by norm_num⟩
  | 40 => ⟨((-51841279/2147483648), (406591915/34359738368)), (3/34359738368), by norm_num⟩
  | 39 => ⟨((849585677/34359738368), (-208321915/17179869184)), (3/34359738368), by norm_num⟩
  | 38 => ⟨((-871929283/34359738368), (426784237/34359738368)), (3/34359738368), by norm_num⟩
  | 37 => ⟨((895861573/34359738368), (-437871169/34359738368)), (3/34359738368), by norm_num⟩
  | 36 => ⟨((-921020863/34359738368), (14055759/1073741824)), (3/34359738368), by norm_num⟩
  | 35 => ⟨((473756655/17179869184), (-115587871/8589934592)), (1/17179869184), by norm_num⟩
  | 34 => ⟨((-975559089/34359738368), (29724277/2147483648)), (1/17179869184), by norm_num⟩
  | 33 => ⟨((502667213/17179869184), (-489590231/34359738368)), (1/17179869184), by norm_num⟩
  | 32 => ⟨((-1036993037/34359738368), (504446865/34359738368)), (1/17179869184), by norm_num⟩
  | 31 => ⟨((1070708177/34359738368), (-130059501/8589934592)), (1/17179869184), by norm_num⟩
  | 30 => ⟨((-553342703/17179869184), (537049793/34359738368)), (1/17179869184), by norm_num⟩
  | 29 => ⟨((572580975/17179869184), (-554983031/34359738368)), (3/34359738368), by norm_num⟩
  | 28 => ⟨((-1186408321/34359738368), (574154275/34359738368)), (3/34359738368), by norm_num⟩
  | 27 => ⟨((1230734451/34359738368), (-594696713/34359738368)), (3/34359738368), by norm_num⟩
  | 26 => ⟨((-1278498129/34359738368), (154190719/8589934592)), (3/34359738368), by norm_num⟩
  | 25 => ⟨((1330114929/34359738368), (-80066081/4294967296)), (3/34359738368), by norm_num⟩
  | 24 => ⟨((-1386070241/34359738368), (333099049/17179869184)), (3/34359738368), by norm_num⟩
  | 23 => ⟨((723467235/17179869184), (-694009355/34359738368)), (3/34359738368), by norm_num⟩
  | 22 => ⟨((-756691233/17179869184), (362120985/17179869184)), (1/8589934592), by norm_num⟩
  | 21 => ⟨((793109285/17179869184), (-189306579/8589934592)), (1/8589934592), by norm_num⟩
  | 20 => ⟨((-104150575/2147483648), (396677843/17179869184)), (1/8589934592), by norm_num⟩
  | 19 => ⟨((109695363/2147483648), (-416551003/17179869184)), (1/8589934592), by norm_num⟩
  | 18 => ⟨((-926901103/17179869184), (438518261/17179869184)), (1/8589934592), by norm_num⟩
  | 17 => ⟨((982106137/17179869184), (-14466521/536870912)), (1/8589934592), by norm_num⟩
  | 16 => ⟨((-261072121/4294967296), (490213355/17179869184)), (1/8589934592), by norm_num⟩
  | 15 => ⟨((278714299/4294967296), (-520911093/17179869184)), (1/8589934592), by norm_num⟩
  | 14 => ⟨((-1195627285/17179869184), (277852073/8589934592)), (1/8589934592), by norm_num⟩
  | 13 => ⟨((644488479/8589934592), (-297734681/8589934592)), (1/8589934592), by norm_num⟩
  | 12 => ⟨((-1398083927/17179869184), (160338201/4294967296)), (1/8589934592), by norm_num⟩
  | 11 => ⟨((95455707/1073741824), (-347440759/8589934592)), (1/4294967296), by norm_num⟩
  | 10 => ⟨((-420673563/4294967296), (379067993/8589934592)), (1/4294967296), by norm_num⟩
  | 9 => ⟨((468279875/4294967296), (-417012721/8589934592)), (1/4294967296), by norm_num⟩
  | 8 => ⟨((-1055921469/8589934592), (231686381/4294967296)), (1/4294967296), by norm_num⟩
  | 7 => ⟨((604946169/4294967296), (-521288225/8589934592)), (1/4294967296), by norm_num⟩
  | 6 => ⟨((-1415954087/8589934592), (595679467/8589934592)), (3/8589934592), by norm_num⟩
  | 5 => ⟨((213206879/1073741824), (-43419673/536870912)), (1/2147483648), by norm_num⟩
  | 4 => ⟨((-1071110271/4294967296), (416507757/4294967296)), (1/2147483648), by norm_num⟩
  | 3 => ⟨((1436647763/4294967296), (-519795221/4294967296)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((-542624203/1073741824), (172664831/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((1092371563/1073741824), (-64222141/268435456)), (1/536870912), by norm_num⟩
  | 0 => ⟨((-75598615/1073741824), (1003826609/2147483648)), (3/2147483648), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-43/256), (8601/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-43/256), (8601/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-43/256), (8601/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((90670183/33554432), (62739163/134217728)), (1/268435456), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((213/16), (8601/1280))) (z:=((-43/256), (8601/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((90670183/33554432), (62739163/134217728))) (r:=(1/268435456)) (by norm_num) ?_ hs
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
  | 0 => ⟨((205/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((528158639/16777216), (405111255/16777216)), (3/33554432), by norm_num⟩
  | 1 => ⟨((492880977/268435456), (129534003/536870912)), (1/268435456), by norm_num⟩
  | 2 => ⟨((12536926784000/1638799529803921), (-59044909486240/14749195768235289)), 0, by norm_num⟩
  | 3 => ⟨((-498687841/8796093022208), (179366921/2199023255552)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((122055145/562949953421312), (-956654819/562949953421312)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((110300909/9007199254740992), (1197900115/36028797018963968)), (21/18014398509481984), by norm_num⟩
  | 6 => ⟨((-173401589/288230376151711744), (-631752273/1152921504606846976)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((178365589/9223372036854775808), (379951269/73786976294838206464)), (81/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-595341439/1180591620717411303424), (65854855/590295810358705651712)), (99/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((801596713/75557863725914323419136), (-334286905/37778931862957161709568)), (273/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-356567509/2417851639229258349412352), (846457473/2417851639229258349412352)), (369/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-32106509/38685626227668133590597632), (-411830231/38685626227668133590597632)), (975/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((397899571/2475880078570760549798248448), (643391727/2475880078570760549798248448)), (649/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-213/16), (-8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((304811951/16777216), (73094057/4194304)), (1/8388608), by norm_num⟩
  | 1 => ⟨((358663249/268435456), (129534003/536870912)), (1/268435456), by norm_num⟩
  | 2 => ⟨((12536926784000/1638799529803921), (-59044909486240/14749195768235289)), 0, by norm_num⟩
  | 3 => ⟨((-498687841/8796093022208), (179366921/2199023255552)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((122055145/562949953421312), (-956654819/562949953421312)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((110300909/9007199254740992), (1197900115/36028797018963968)), (21/18014398509481984), by norm_num⟩
  | 6 => ⟨((-173401589/288230376151711744), (-631752273/1152921504606846976)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((178365589/9223372036854775808), (379951269/73786976294838206464)), (81/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-595341439/1180591620717411303424), (65854855/590295810358705651712)), (99/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((801596713/75557863725914323419136), (-334286905/37778931862957161709568)), (273/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-356567509/2417851639229258349412352), (846457473/2417851639229258349412352)), (369/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-32106509/38685626227668133590597632), (-411830231/38685626227668133590597632)), (975/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((397899571/2475880078570760549798248448), (643391727/2475880078570760549798248448)), (649/2475880078570760549798248448), by norm_num⟩
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
  | 0 => ⟨((640458363/33554432), (73094057/4194304)), (5/33554432), by norm_num⟩
  | 1 => ⟨((358663249/268435456), (129534003/536870912)), (1/268435456), by norm_num⟩
  | 2 => ⟨((12536926784000/1638799529803921), (-59044909486240/14749195768235289)), 0, by norm_num⟩
  | 3 => ⟨((-498687841/8796093022208), (179366921/2199023255552)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((122055145/562949953421312), (-956654819/562949953421312)), (3/140737488355328), by norm_num⟩
  | 5 => ⟨((110300909/9007199254740992), (1197900115/36028797018963968)), (21/18014398509481984), by norm_num⟩
  | 6 => ⟨((-173401589/288230376151711744), (-631752273/1152921504606846976)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((178365589/9223372036854775808), (379951269/73786976294838206464)), (81/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-595341439/1180591620717411303424), (65854855/590295810358705651712)), (99/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((801596713/75557863725914323419136), (-334286905/37778931862957161709568)), (273/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-356567509/2417851639229258349412352), (846457473/2417851639229258349412352)), (369/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-32106509/38685626227668133590597632), (-411830231/38685626227668133590597632)), (975/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((397899571/2475880078570760549798248448), (643391727/2475880078570760549798248448)), (649/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13130525900800/4916398589411763), (-53361246208000/14749195768235289)), 0, by norm_num⟩
  | 1 => ⟨((-222376845/4398046511104), (1307492931/4398046511104)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-314353011/70368744177664), (-254978597/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((264734391/562949953421312), (549957167/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-483148703/18014398509481984), (-338484711/36028797018963968)), (5/36028797018963968), by norm_num⟩
  | 5 => ⟨((653525667/576460752303423488), (-42889499/288230376151711744)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((-681919853/18446744073709551616), (464479979/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 7 => ⟨((489837331/590295810358705651712), (-55327819/36893488147419103232)), (3/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5792863/2361183241434822606848), (610171435/9444732965739290427392)), (5/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-303119623/302231454903657293676544), (-165458599/75557863725914323419136)), (31/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((335676467/4835703278458516698824704), (536120815/9671406556917033397649408)), (3/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-984273905/309485009821345068724781056), (-206113493/309485009821345068724781056)), (37/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((1129299173/9903520314283042199192993792), (-150825435/4951760157141521099596496896)), (55/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((222376845/4398046511104), (-1307492931/4398046511104)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((314353011/35184372088832), (254978597/8796093022208)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-198550793/140737488355328), (-412467875/281474976710656)), (3/562949953421312), by norm_num⟩
  | 3 => ⟨((966297407/9007199254740992), (338484711/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 4 => ⟨((-204226771/36028797018963968), (26805937/36028797018963968)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((255719945/1152921504606846976), (-696719969/4611686018427387904)), (9/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-26787979/4611686018427387904), (387294733/36893488147419103232)), (9/73786976294838206464), by norm_num⟩
  | 7 => ⟨((5792863/295147905179352825856), (-610171435/1180591620717411303424)), (15/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((42626197/4722366482869645213696), (46535231/2361183241434822606848)), (7/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-6556181/9444732965739290427392), (-670151019/1208925819614629174706176)), (11/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((1353376619/38685626227668133590597632), (283406053/38685626227668133590597632)), (35/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-1693948759/1237940039285380274899124224), (452476305/1237940039285380274899124224)), (55/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((818869021/19807040628566084398385987584), (-730556105/19807040628566084398385987584)), (43/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-104784337/17592186044416), (-1359885851/70368744177664)), (3/70368744177664), by norm_num⟩
  | 1 => ⟨((529468781/281474976710656), (549957167/281474976710656)), (3/281474976710656), by norm_num⟩
  | 2 => ⟨((-483148703/2251799813685248), (-338484711/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((1089209445/72057594037927936), (-142964997/72057594037927936)), (7/72057594037927936), by norm_num⟩
  | 4 => ⟨((-852399817/1152921504606846976), (580599975/1152921504606846976)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((26787979/1152921504606846976), (-387294733/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-1689585/18446744073709551616), (1423733349/590295810358705651712)), (17/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-454679435/9444732965739290427392), (-496375797/4722366482869645213696)), (15/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((19668543/4722366482869645213696), (31413329/9444732965739290427392)), (7/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-563906925/2417851639229258349412352), (-118085855/2417851639229258349412352)), (25/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((1552786363/154742504910672534362390528), (-207384973/77371252455336267181195264)), (41/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-818869021/2475880078570760549798248448), (730556105/2475880078570760549798248448)), (17/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((538928011/79228162514264337593543950336), (-684787445/39614081257132168796771975168)), (55/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-529468781/562949953421312), (-549957167/562949953421312)), (3/562949953421312), by norm_num⟩
  | 1 => ⟨((483148703/2251799813685248), (42310589/562949953421312)), (3/2251799813685248), by norm_num⟩
  | 2 => ⟨((-1633814167/72057594037927936), (214447495/72057594037927936)), (5/36028797018963968), by norm_num⟩
  | 3 => ⟨((106549977/72057594037927936), (-580599975/576460752303423488)), (9/576460752303423488), by norm_num⟩
  | 4 => ⟨((-133939895/2305843009213693952), (968236833/9223372036854775808)), (11/9223372036854775808), by norm_num⟩
  | 5 => ⟨((5068755/18446744073709551616), (-1067800011/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 6 => ⟨((198922253/1180591620717411303424), (868657645/2361183241434822606848)), (13/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-19668543/1180591620717411303424), (-31413329/2361183241434822606848)), (7/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((1268790581/1208925819614629174706176), (132846587/604462909807314587353088)), (25/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-970491477/19342813113834066795298816), (259231217/19342813113834066795298816)), (3/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((140743113/77371252455336267181195264), (-1004514645/618970019642690137449562112)), (21/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-50524501/1237940039285380274899124224), (1027181167/9903520314283042199192993792)), (9/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-145946215/316912650057057350374175801344), (-786197487/158456325028528675187087900672)), (15/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-773037925/9007199254740992), (-541575539/18014398509481984)), (5/9007199254740992), by norm_num⟩
  | 1 => ⟨((653525667/36028797018963968), (-171557995/72057594037927936)), (11/72057594037927936), by norm_num⟩
  | 2 => ⟨((-255719945/144115188075855872), (696719969/576460752303423488)), (11/576460752303423488), by norm_num⟩
  | 3 => ⟨((26787979/288230376151711744), (-387294733/2305843009213693952)), (5/2305843009213693952), by norm_num⟩
  | 4 => ⟨((-5068755/9223372036854775808), (1067800011/73786976294838206464)), (7/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-477413407/1180591620717411303424), (-1042389173/1180591620717411303424)), (9/590295810358705651712), by norm_num⟩
  | 6 => ⟨((881150727/18889465931478580854784), (703658569/18889465931478580854784)), (5/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((-1015032465/302231454903657293676544), (-212554539/302231454903657293676544)), (21/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((873442329/4835703278458516698824704), (-233308095/4835703278458516698824704)), (21/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((-140743113/19342813113834066795298816), (502257323/77371252455336267181195264)), (41/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((444615609/2475880078570760549798248448), (-282474821/618970019642690137449562112)), (19/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((87567729/39614081257132168796771975168), (117929623/4951760157141521099596496896)), (17/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-765005265/1267650600228229401496703205376), (-610106849/633825300114114700748351602688)), (15/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-217841889/36028797018963968), (114371997/144115188075855872)), (15/288230376151711744), by norm_num⟩
  | 1 => ⟨((340959927/288230376151711744), (-464479979/576460752303423488)), (5/288230376151711744), by norm_num⟩
  | 2 => ⟨((-26787979/288230376151711744), (387294733/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 3 => ⟨((1689585/2305843009213693952), (-355933337/18446744073709551616)), (21/73786976294838206464), by norm_num⟩
  | 4 => ⟨((198922253/295147905179352825856), (217164411/147573952589676412928)), (17/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-440575363/4722366482869645213696), (-703658569/9444732965739290427392)), (23/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((592102271/75557863725914323419136), (247980295/151115727451828646838272)), (27/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-291147443/604462909807314587353088), (311077461/2417851639229258349412352)), (15/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((844458677/38685626227668133590597632), (-1471457/75557863725914323419136)), (33/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-370513007/618970019642690137449562112), (941582737/618970019642690137449562112)), (33/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((-160540837/19807040628566084398385987584), (-1729634471/19807040628566084398385987584)), (63/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((382502633/158456325028528675187087900672), (610106849/158456325028528675187087900672)), (15/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-248005623/1267650600228229401496703205376), (-599184093/5070602400912917605986812821504)), (55/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-779336975/2305843009213693952), (265417131/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 1 => ⟨((122459333/2305843009213693952), (-55327819/576460752303423488)), (17/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-46342903/73786976294838206464), (610171435/36893488147419103232)), (11/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-454679435/590295810358705651712), (-496375797/295147905179352825856)), (11/295147905179352825856), by norm_num⟩
  | 4 => ⟨((19668543/147573952589676412928), (502613263/4722366482869645213696)), (19/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-63439529/4722366482869645213696), (-212554539/75557863725914323419136)), (27/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((1164589771/1208925819614629174706176), (-311077461/1208925819614629174706176)), (35/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-965095631/19342813113834066795298816), (430506277/9671406556917033397649408)), (41/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((238186933/154742504910672534362390528), (-151325797/38685626227668133590597632)), (23/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((114672027/4951760157141521099596496896), (1235453193/4951760157141521099596496896)), (49/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((-300537783/39614081257132168796771975168), (-479369667/39614081257132168796771975168)), (25/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((850304993/1267650600228229401496703205376), (513586365/1267650600228229401496703205376)), (49/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((-841354947/20282409603651670423947251286016), (-63993723/20282409603651670423947251286016)), (93/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-489837331/36893488147419103232), (55327819/2305843009213693952)), (19/36893488147419103232), by norm_num⟩
  | 1 => ⟨((46342905/147573952589676412928), (-1220342871/147573952589676412928)), (7/36893488147419103232), by norm_num⟩
  | 2 => ⟨((42626197/73786976294838206464), (744563695/590295810358705651712)), (21/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-19668543/147573952589676412928), (-31413329/295147905179352825856)), (11/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((317197645/18889465931478580854784), (265693173/75557863725914323419136)), (5/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-109180291/75557863725914323419136), (233308095/604462909807314587353088)), (31/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((844458677/9671406556917033397649408), (-1471457/18889465931478580854784)), (43/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-238186933/77371252455336267181195264), (151325797/19342813113834066795298816)), (53/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((-64503015/1237940039285380274899124224), (-694942421/1237940039285380274899124224)), (31/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((375672229/19807040628566084398385987584), (1198424167/39614081257132168796771975168)), (69/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-584584683/316912650057057350374175801344), (-176545313/158456325028528675187087900672)), (37/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((315508105/2535301200456458802993406410752), (11998823/1267650600228229401496703205376)), (75/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-261507775/40564819207303340847894502572032), (107961769/40564819207303340847894502572032)), (75/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-10298423/147573952589676412928), (542374609/295147905179352825856)), (7/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-303119623/1180591620717411303424), (-661834397/1180591620717411303424)), (45/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((6556181/73786976294838206464), (335075509/4722366482869645213696)), (19/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-563906925/37778931862957161709568), (-118085855/37778931862957161709568)), (43/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((242622869/151115727451828646838272), (-259231217/604462909807314587353088)), (41/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((-562972451/4835703278458516698824704), (1004514645/9671406556917033397649408)), (67/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((370513007/77371252455336267181195264), (-58848921/4835703278458516698824704)), (25/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((114672027/1237940039285380274899124224), (1235453193/1237940039285380274899124224)), (65/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((-375672229/9903520314283042199192993792), (-1198424167/19807040628566084398385987584)), (81/19807040628566084398385987584), by norm_num⟩
  | 9 => ⟨((1299077073/316912650057057350374175801344), (784645835/316912650057057350374175801344)), (93/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((-771242035/2535301200456458802993406410752), (-117321825/5070602400912917605986812821504)), (13/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((1394708133/81129638414606681695789005144064), (-287898051/40564819207303340847894502572032)), (55/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((-1807299/2535301200456458802993406410752), (268149801/324518553658426726783156020576256)), (57/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((484991397/9444732965739290427392), (529467517/4722366482869645213696)), (21/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((-671352935/18889465931478580854784), (-33507551/1180591620717411303424)), (9/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((338344155/37778931862957161709568), (70851513/37778931862957161709568)), (33/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((-1552786363/1208925819614629174706176), (414769947/1208925819614629174706176)), (5/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((1125944903/9671406556917033397649408), (-502257323/4835703278458516698824704)), (41/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((-55576951/9671406556917033397649408), (282474821/19342813113834066795298816)), (71/77371252455336267181195264), by norm_num⟩
  | 6 => ⟨((-160540837/1237940039285380274899124224), (-1729634469/1237940039285380274899124224)), (111/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((300537783/4951760157141521099596496896), (958739333/9903520314283042199192993792)), (77/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((-584584683/79228162514264337593543950336), (-176545313/39614081257132168796771975168)), (25/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((1542484069/2535301200456458802993406410752), (3666307/79228162514264337593543950336)), (121/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-767089473/20282409603651670423947251286016), (19792991/1267650600228229401496703205376)), (35/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((555202253/324518553658426726783156020576256), (-643559523/324518553658426726783156020576256)), (39/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-202264135/5192296858534827628530496329220096), (405558429/2596148429267413814265248164610048)), (83/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1817600/364338801), (-917440/364338801)), 0, by norm_num⟩
  | 1 => ⟨((-1641315737600/14749195768235289), (6670155776000/44247587304705867)), 0, by norm_num⟩
  | 2 => ⟨((74125615/70368744177664), (-435830977/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((279424899/4503599627370496), (906590567/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((-705958375/144115188075855872), (-733276223/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((1030717233/4611686018427387904), (361050359/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((-72613963/9223372036854775808), (38123999/36893488147419103232)), (5/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1039115967/4722366482869645213696), (-88472377/590295810358705651712)), (17/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-653116441/151115727451828646838272), (1180326805/151115727451828646838272)), (13/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((54924923/4835703278458516698824704), (-1446332291/4835703278458516698824704)), (19/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((161663799/38685626227668133590597632), (1411913379/154742504910672534362390528)), (57/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-325504453/1237940039285380274899124224), (-259937365/1237940039285380274899124224)), (41/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((437455069/39614081257132168796771975168), (91605997/39614081257132168796771975168)), (119/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((320312879/16777216), (584667963/33554432)), (3/16777216), by norm_num⟩
  | 1 => ⟨((358633377/268435456), (259229869/1073741824)), (5/1073741824), by norm_num⟩
  | 2 => ⟨((262890507/34359738368), (-137763877/34359738368)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-498142089/8796093022208), (719238369/8796093022208)), (5/8796093022208), by norm_num⟩
  | 4 => ⟨((119297495/562949953421312), (-959519179/562949953421312)), (13/562949953421312), by norm_num⟩
  | 5 => ⟨((224628057/18014398509481984), (1200720821/36028797018963968)), (43/36028797018963968), by norm_num⟩
  | 6 => ⟨((-702683101/1152921504606846976), (-315280449/576460752303423488)), (65/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1443160899/73786976294838206464), (184446111/36893488147419103232)), (163/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-600443911/1180591620717411303424), (140931013/1180591620717411303424)), (25/295147905179352825856), by norm_num⟩
  | 9 => ⟨((802454915/75557863725914323419136), (-43198297/4722366482869645213696)), (137/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-173231761/1208925819614629174706176), (217129655/604462909807314587353088)), (371/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-169114093/154742504910672534362390528), (-1679813095/154742504910672534362390528)), (979/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((425240513/2475880078570760549798248448), (324558551/1237940039285380274899124224)), (163/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-158134645/1125899906842624), (929772751/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 1 => ⟨((-223539919/9007199254740992), (-1450544907/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((141191675/36028797018963968), (293310489/72057594037927936)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((-687144823/2305843009213693952), (-240700239/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 4 => ⟨((72613963/4611686018427387904), (-152495997/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-727381177/1180591620717411303424), (495445311/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((38098459/2361183241434822606848), (-68852397/2361183241434822606848)), (7/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-16477477/302231454903657293676544), (433899687/302231454903657293676544)), (11/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((-484991397/19342813113834066795298816), (-529467517/9671406556917033397649408)), (21/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((149189541/77371252455336267181195264), (953103671/618970019642690137449562112)), (1/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-962401151/9903520314283042199192993792), (-201533193/9903520314283042199192993792)), (13/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((150573223/39614081257132168796771975168), (-10055029/9903520314283042199192993792)), (5/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-582306859/5070602400912917605986812821504), (129876641/1267650600228229401496703205376)), (1/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((640625753/33554432), (584667991/33554432)), (7/33554432), by norm_num⟩
  | 1 => ⟨((1434533481/1073741824), (259229783/1073741824)), (3/536870912), by norm_num⟩
  | 2 => ⟨((1051562567/137438953472), (-551054949/137438953472)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((-249072355/4398046511104), (719237451/8796093022208)), (3/4398046511104), by norm_num⟩
  | 4 => ⟨((119306359/562949953421312), (-479760171/281474976710656)), (7/281474976710656), by norm_num⟩
  | 5 => ⟨((112308479/9007199254740992), (1200735941/36028797018963968)), (11/9007199254740992), by norm_num⟩
  | 6 => ⟨((-351332249/576460752303423488), (-630594517/1152921504606846976)), (33/576460752303423488), by norm_num⟩
  | 7 => ⟨((360789219/18446744073709551616), (368998155/73786976294838206464)), (41/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-1200947025/2361183241434822606848), (281732761/2361183241434822606848)), (201/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((25081269/2361183241434822606848), (-345528203/37778931862957161709568)), (275/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-346698483/2417851639229258349412352), (434234709/1208925819614629174706176)), (93/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-42131479/38685626227668133590597632), (-1679970205/154742504910672534362390528)), (245/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((424956183/2475880078570760549798248448), (649370767/2475880078570760549798248448)), (653/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-215149219/288230376151711744), (-893898633/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 1 => ⟨((49081773/288230376151711744), (68771497/1152921504606846976)), (11/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-331949545/18446744073709551616), (174281139/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 3 => ⟨((692743977/590295810358705651712), (-235926339/295147905179352825856)), (1/73786976294838206464), by norm_num⟩
  | 4 => ⟨((-27213185/590295810358705651712), (786884537/9444732965739290427392)), (5/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((32954953/151115727451828646838272), (-433899687/75557863725914323419136)), (11/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((646655197/4835703278458516698824704), (1411913379/4835703278458516698824704)), (11/2417851639229258349412352), by norm_num⟩
  | 7 => ⟨((-1023013995/77371252455336267181195264), (-204236501/19342813113834066795298816)), (3/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((1031144091/1237940039285380274899124224), (215928421/1237940039285380274899124224)), (21/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((-788716883/19807040628566084398385987584), (421353597/39614081257132168796771975168)), (5/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((228763409/158456325028528675187087900672), (-408183729/316912650057057350374175801344)), (35/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((-164244727/5070602400912917605986812821504), (104348563/1267650600228229401496703205376)), (15/5070602400912917605986812821504), by norm_num⟩
  | 12 => ⟨((-118610257/324518553658426726783156020576256), (-319470725/81129638414606681695789005144064)), (25/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((640625753/33554432), (584667991/33554432)), (1/4194304), by norm_num⟩
  | 1 => ⟨((1434533481/1073741824), (259229783/1073741824)), (7/1073741824), by norm_num⟩
  | 2 => ⟨((1051562565/137438953472), (-551054949/137438953472)), (3/137438953472), by norm_num⟩
  | 3 => ⟨((-124536175/2199023255552), (179809361/2199023255552)), (7/8796093022208), by norm_num⟩
  | 4 => ⟨((119306333/562949953421312), (-959520295/562949953421312)), (15/562949953421312), by norm_num⟩
  | 5 => ⟨((112308481/9007199254740992), (600367867/18014398509481984)), (45/36028797018963968), by norm_num⟩
  | 6 => ⟨((-87833043/144115188075855872), (-157648545/288230376151711744)), (67/1152921504606846976), by norm_num⟩
  | 7 => ⟨((360788975/18446744073709551616), (360349/72057594037927936)), (165/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-600472529/1180591620717411303424), (281733173/2361183241434822606848)), (101/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((802597599/75557863725914323419136), (-345527801/37778931862957161709568)), (69/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-21668437/151115727451828646838272), (6784893/18889465931478580854784)), (373/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-10533183/9671406556917033397649408), (-1679957467/154742504910672534362390528)), (981/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((212477639/1237940039285380274899124224), (324680509/1237940039285380274899124224)), (327/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((66389909/18446744073709551616), (-139424911/295147905179352825856)), (5/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-415646387/590295810358705651712), (141555803/295147905179352825856)), (7/590295810358705651712), by norm_num⟩
  | 2 => ⟨((16327911/295147905179352825856), (-236065361/2361183241434822606848)), (1/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-32954953/75557863725914323419136), (433899687/37778931862957161709568)), (13/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((-242495699/604462909807314587353088), (-1058935033/1208925819614629174706176)), (11/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((1074164695/19342813113834066795298816), (857793303/19342813113834066795298816)), (29/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((-1443601727/309485009821345068724781056), (-75574947/77371252455336267181195264)), (17/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((1419690389/4951760157141521099596496896), (-189609119/2475880078570760549798248448)), (19/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((-257358835/19807040628566084398385987584), (459206695/39614081257132168796771975168)), (41/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((451672999/1267650600228229401496703205376), (-573917097/633825300114114700748351602688)), (41/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((97853463/20282409603651670423947251286016), (65890837/1267650600228229401496703205376)), (39/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-116572231/81129638414606681695789005144064), (-371874651/162259276829213363391578010288128)), (37/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((1209322657/10384593717069655257060992658440192), (365216971/5192296858534827628530496329220096)), (17/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((640625753/33554432), (584667991/33554432)), (9/33554432), by norm_num⟩
  | 1 => ⟨((1434533481/1073741824), (259229783/1073741824)), (1/134217728), by norm_num⟩
  | 2 => ⟨((1051562565/137438953472), (-551054949/137438953472)), (1/34359738368), by norm_num⟩
  | 3 => ⟨((-124536175/2199023255552), (179809361/2199023255552)), (1/1099511627776), by norm_num⟩
  | 4 => ⟨((119306333/562949953421312), (-959520295/562949953421312)), (1/35184372088832), by norm_num⟩
  | 5 => ⟨((224616963/18014398509481984), (150091967/4503599627370496)), (23/18014398509481984), by norm_num⟩
  | 6 => ⟨((-702664349/1152921504606846976), (-630594181/1152921504606846976)), (17/288230376151711744), by norm_num⟩
  | 7 => ⟨((1443155921/73786976294838206464), (184498685/36893488147419103232)), (83/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1200945089/2361183241434822606848), (17608325/147573952589676412928)), (203/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((401298813/37778931862957161709568), (-345527835/37778931862957161709568)), (277/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-86673745/604462909807314587353088), (434233215/1208925819614629174706176)), (187/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-84265575/77371252455336267181195264), (-839978911/77371252455336267181195264)), (491/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((212477783/1237940039285380274899124224), (81170149/309485009821345068724781056)), (655/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-422216689/37778931862957161709568), (763039551/37778931862957161709568)), (17/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((4993175/18889465931478580854784), (-525939015/75557863725914323419136)), (25/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((73483545/151115727451828646838272), (80222351/75557863725914323419136)), (37/1208925819614629174706176), by norm_num⟩
  | 3 => ⟨((-1085014843/9671406556917033397649408), (-866457883/9671406556917033397649408)), (39/9671406556917033397649408), by norm_num⟩
  | 4 => ⟨((136704709/9671406556917033397649408), (229014991/77371252455336267181195264)), (35/77371252455336267181195264), by norm_num⟩
  | 5 => ⟨((-1505732229/1237940039285380274899124224), (50275145/154742504910672534362390528)), (55/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((727883573/9903520314283042199192993792), (-649383205/9903520314283042199192993792)), (19/4951760157141521099596496896), by norm_num⟩
  | 7 => ⟨((-410611817/158456325028528675187087900672), (521742815/79228162514264337593543950336)), (47/158456325028528675187087900672), by norm_num⟩
  | 8 => ⟨((-111197117/2535301200456458802993406410752), (-1198015217/2535301200456458802993406410752)), (55/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((323811753/20282409603651670423947251286016), (1032985141/40564819207303340847894502572032)), (61/40564819207303340847894502572032), by norm_num⟩
  | 10 => ⟨((-1007768881/649037107316853453566312041152512), (-608694951/649037107316853453566312041152512)), (65/649037107316853453566312041152512), by norm_num⟩
  | 11 => ⟨((135976557/1298074214633706907132624082305024), (82739359/10384593717069655257060992658440192)), (33/5192296858534827628530496329220096), by norm_num⟩
  | 12 => ⟨((-225407375/41538374868278621028243970633760768), (372231823/166153499473114484112975882535043072)), (33/83076749736557242056487941267521536), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((640625753/33554432), (584667991/33554432)), (5/16777216), by norm_num⟩
  | 1 => ⟨((1434533481/1073741824), (259229783/1073741824)), (9/1073741824), by norm_num⟩
  | 2 => ⟨((1051562565/137438953472), (-551054949/137438953472)), (5/137438953472), by norm_num⟩
  | 3 => ⟨((-124536175/2199023255552), (179809361/2199023255552)), (9/8796093022208), by norm_num⟩
  | 4 => ⟨((119306333/562949953421312), (-959520295/562949953421312)), (17/562949953421312), by norm_num⟩
  | 5 => ⟨((224616963/18014398509481984), (150091967/4503599627370496)), (47/36028797018963968), by norm_num⟩
  | 6 => ⟨((-702664349/1152921504606846976), (-630594181/1152921504606846976)), (69/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1443155921/73786976294838206464), (184498685/36893488147419103232)), (167/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1200945089/2361183241434822606848), (281733199/2361183241434822606848)), (51/590295810358705651712), by norm_num⟩
  | 9 => ⟨((802597627/75557863725914323419136), (-172763917/18889465931478580854784)), (139/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-43336873/302231454903657293676544), (217116607/604462909807314587353088)), (375/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-84265567/77371252455336267181195264), (-1679957821/154742504910672534362390528)), (983/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((424955553/2475880078570760549798248448), (324680599/1237940039285380274899124224)), (41/154742504910672534362390528), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-238075919/2417851639229258349412352), (-1039634653/4835703278458516698824704)), (21/2417851639229258349412352), by norm_num⟩
  | 1 => ⟨((329558355/4835703278458516698824704), (526349361/9671406556917033397649408)), (9/2417851639229258349412352), by norm_num⟩
  | 2 => ⟨((-664354841/38685626227668133590597632), (-278240631/77371252455336267181195264)), (33/38685626227668133590597632), by norm_num⟩
  | 3 => ⟨((381121235/154742504910672534362390528), (-407210259/618970019642690137449562112)), (5/38685626227668133590597632), by norm_num⟩
  | 4 => ⟨((-1105423185/4951760157141521099596496896), (986206143/4951760157141521099596496896)), (41/2475880078570760549798248448), by norm_num⟩
  | 5 => ⟨((436511947/39614081257132168796771975168), (-1109305493/39614081257132168796771975168)), (35/19807040628566084398385987584), by norm_num⟩
  | 6 => ⟨((157614785/633825300114114700748351602688), (849054887/316912650057057350374175801344)), (55/316912650057057350374175801344), by norm_num⟩
  | 7 => ⟨((-73765029/633825300114114700748351602688), (-941265141/5070602400912917605986812821504)), (77/5070602400912917605986812821504), by norm_num⟩
  | 8 => ⟨((573929915/40564819207303340847894502572032), (346655119/40564819207303340847894502572032)), (99/81129638414606681695789005144064), by norm_num⟩
  | 9 => ⟨((-757185209/649037107316853453566312041152512), (-115183491/1298074214633706907132624082305024)), (15/162259276829213363391578010288128), by norm_num⟩
  | 10 => ⟨((753108333/10384593717069655257060992658440192), (-155457917/5192296858534827628530496329220096)), (69/10384593717069655257060992658440192), by norm_num⟩
  | 11 => ⟨((-68135377/20769187434139310514121985316880384), (631829867/166153499473114484112975882535043072)), (39/83076749736557242056487941267521536), by norm_num⟩
  | 12 => ⟨((397155249/5316911983139663491615228241121378304), (-796333265/2658455991569831745807614120560689152)), (41/1329227995784915872903807060280344576), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((640625753/33554432), (584667991/33554432)), (11/33554432), by norm_num⟩
  | 1 => ⟨((1434533481/1073741824), (259229783/1073741824)), (5/536870912), by norm_num⟩
  | 2 => ⟨((1051562565/137438953472), (-551054949/137438953472)), (3/68719476736), by norm_num⟩
  | 3 => ⟨((-124536175/2199023255552), (179809361/2199023255552)), (5/4398046511104), by norm_num⟩
  | 4 => ⟨((119306333/562949953421312), (-959520295/562949953421312)), (9/281474976710656), by norm_num⟩
  | 5 => ⟨((224616963/18014398509481984), (150091967/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((-702664349/1152921504606846976), (-630594181/1152921504606846976)), (35/576460752303423488), by norm_num⟩
  | 7 => ⟨((1443155921/73786976294838206464), (184498685/36893488147419103232)), (21/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-1200945089/2361183241434822606848), (281733199/2361183241434822606848)), (205/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((802597627/75557863725914323419136), (-172763917/18889465931478580854784)), (279/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-43336873/302231454903657293676544), (217116607/604462909807314587353088)), (47/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-168531135/154742504910672534362390528), (-419989455/38685626227668133590597632)), (123/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((424955553/2475880078570760549798248448), (649361197/2475880078570760549798248448)), (657/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((59590041624595/2097152), (-6345013063273/32768)), (1341211381/8388608), by norm_num⟩
  | 1 => ⟨((169421949/2), (-503676249/2)), (509/2), by norm_num⟩
  | 2 => ⟨((172857481/2), -159599266), (817/4), by norm_num⟩
  | 3 => ⟨((817711631/16), (-524943143/8)), (1763/16), by norm_num⟩
  | 4 => ⟨((168420679/8), (-78399887/4)), (1439/32), by norm_num⟩
  | 5 => ⟨((13254885/2), (-71902647/16)), (1895/128), by norm_num⟩
  | 6 => ⟨((53923889/32), (-206919405/256)), (131/32), by norm_num⟩
  | 7 => ⟨((735150499/2048), (-230211289/2048)), (501/512), by norm_num⟩
  | 8 => ⟨((1077027705/16384), (-44627665/4096)), (3381/16384), by norm_num⟩
  | 9 => ⟨((1382635173/131072), (-40492647/131072)), (639/16384), by norm_num⟩
  | 10 => ⟨((1578089217/1048576), (161053609/1048576)), (3507/524288), by norm_num⟩
  | 11 => ⟨((1619598993/8388608), (188700197/4194304)), (4413/4194304), by norm_num⟩
  | 12 => ⟨((753978381/33554432), (554956257/67108864)), (10269/67108864), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((804422702439201/5070602400912917605986812821504), (-928170697721/5070602400912917605986812821504)), (213515/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1811966535417423/633825300114114700748351602688), (-2273627127669/633825300114114700748351602688)), (262105/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((963563187948697/19807040628566084398385987584), (-2564089204303/39614081257132168796771975168)), (591319/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1929273088115435/2475880078570760549798248448), (-2729771728215/2475880078570760549798248448)), (78703/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((905489377565311/77371252455336267181195264), (-2735848383959/154742504910672534362390528)), (157783/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1586896700291591/9671406556917033397649408), (-321416559837/1208925819614629174706176)), (593293/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((322876525948179/151115727451828646838272), (-564103018225/151115727451828646838272)), (65093/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((485259225972447/18889465931478580854784), (-229930992965/4722366482869645213696)), (849245/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((668771233126055/2361183241434822606848), (-2769916085243/4722366482869645213696)), (319801/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((209570669549567/73786976294838206464), (-1913090461525/295147905179352825856)), (883813/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1892541477716677/73786976294838206464), (-4809198789195/73786976294838206464)), (555673/36893488147419103232), by norm_num⟩
  | 7 => ⟨((950296172864041/4611686018427387904), (-5446999072265/9223372036854775808)), (314845/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1672136515145423/1152921504606846976), (-5493190862411/1152921504606846976)), (1270875/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1263297455617645/144115188075855872), (-607379163371/18014398509481984)), (35159/4503599627370496), by norm_num⟩
  | 4 => ⟨((199423481191243/4503599627370496), (-3697430416151/18014398509481984)), (1714133/36028797018963968), by norm_num⟩
  | 3 => ⟨((810070293746735/4503599627370496), (-294770274263/281474976710656)), (1094927/4503599627370496), by norm_num⟩
  | 2 => ⟨((311668825129705/562949953421312), (-4861208472073/1125899906842624)), (141393/140737488355328), by norm_num⟩
  | 1 => ⟨((1311742391808537/1125899906842624), (-1916258448677/140737488355328)), (223777/70368744177664), by norm_num⟩
  | 0 => ⟨((758435237507957/562949953421312), (-16890916130881/562949953421312)), (7945451/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((758435237507957/562949953421312), (-16890916130881/562949953421312)), (30309490208152389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((127662037928913/70368744177664), (-11378157072041/140737488355328)), (21885839/1125899906842624), by norm_num⟩
  | 2 => ⟨((1849142599164021/562949953421312), (-82568403723373/281474976710656)), (10368599/140737488355328), by norm_num⟩
  | 3 => ⟨((1506376439972253/140737488355328), (-8475484351559/4398046511104)), (74199335/140737488355328), by norm_num⟩
  | 4 => ⟨((487523828389705/4398046511104), (-362867636583303/8796093022208)), (29286827/2199023255552), by norm_num⟩
  | 5 => ⟨((727458103809889/68719476736), (-628498566562343/68719476736)), (278414061/68719476736), by norm_num⟩
  | 6 => ⟨((59590041624595/2097152), (-6345013063273/32768)), (1341211381/8388608), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((640625753/33554432), (584667991/33554432)), (11/33554432), by norm_num⟩, 3, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((716800/25599867), (-3669760/25599867)), 0, by norm_num⟩
  | 1 => ⟨((2158889369600/218451063472563), (2630483968000/655353190417689)), 0, by norm_num⟩
  | 2 => ⟨((-7319523/17179869184), (717049945/1099511627776)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((-358691961/8796093022208), (-174460167/4398046511104)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((960982669/281474976710656), (-333191517/140737488355328)), (1/70368744177664), by norm_num⟩
  | 5 => ⟨((274475399/2251799813685248), (1251331225/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 6 => ⟨((-778999861/36028797018963968), (349240395/72057594037927936)), (5/36028797018963968), by norm_num⟩
  | 7 => ⟨((-51517215/1152921504606846976), (-1864953619/1152921504606846976)), (15/1152921504606846976), by norm_num⟩
  | 8 => ⟨((1075139919/9223372036854775808), (89667883/4611686018427387904)), (11/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-223247959/73786976294838206464), (1192805445/147573952589676412928)), (1/9223372036854775808), by norm_num⟩
  | 10 => ⟨((-633950393/1180591620717411303424), (-779233987/2361183241434822606848)), (23/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((588820715/18889465931478580854784), (-159935857/4722366482869645213696)), (17/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((601765049/302231454903657293676544), (818566377/302231454903657293676544)), (25/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((21/16), (8601/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((21/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((21/16), (8601/1280)))⁻¹=value ((716800/25599867), (-3669760/25599867)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((716800/25599867), (-3669760/25599867))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((37/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3788800/82738801), (-11009280/82738801)), 0, by norm_num⟩
  | 1 => ⟨((53424620339200/6845709190917601), (41711960064000/6845709190917601)), 0, by norm_num⟩
  | 2 => ⟨((-321092293/549755813888), (417484359/1099511627776)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-418298205/35184372088832), (-52283539/1099511627776)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((967100313/281474976710656), (83819337/281474976710656)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-110877609/1125899906842624), (998757855/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-900688183/72057594037927936), (-209498427/18014398509481984)), (7/72057594037927936), by norm_num⟩
  | 7 => ⟨((610994339/576460752303423488), (-651780085/1152921504606846976)), (11/1152921504606846976), by norm_num⟩
  | 8 => ⟨((123074481/9223372036854775808), (1539561097/18446744073709551616)), (17/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-1729014021/295147905179352825856), (-150989195/147573952589676412928)), (25/295147905179352825856), by norm_num⟩
  | 10 => ⟨((477427899/2361183241434822606848), (-864941891/2361183241434822606848)), (19/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((745817783/37778931862957161709568), (103134553/4722366482869645213696)), (7/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-287875861/151115727451828646838272), (491654913/604462909807314587353088)), (41/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((37/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((37/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((37/16), (8601/1280)))⁻¹=value ((3788800/82738801), (-11009280/82738801)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3788800/82738801), (-11009280/82738801))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-37685603532800/2118102301339467), (-21795438592000/2118102301339467)), 0, by norm_num⟩
  | 1 => ⟨((571364195/274877906944), (-71444625/34359738368)), (1/274877906944), by norm_num⟩
  | 2 => ⟨((86867557/549755813888), (1198262343/4398046511104)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-1016469639/35184372088832), (277391913/35184372088832)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((-12235289/562949953421312), (-1500404743/562949953421312)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((496230617/2251799813685248), (126286685/2251799813685248)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((-657311539/72057594037927936), (148404263/9007199254740992)), (9/72057594037927936), by norm_num⟩
  | 7 => ⟨((-636752947/576460752303423488), (-606586767/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 8 => ⟨((476032719/4611686018427387904), (-590444783/9223372036854775808)), (3/2305843009213693952), by norm_num⟩
  | 9 => ⟨((418011093/147573952589676412928), (83987165/9223372036854775808)), (5/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-436332171/590295810358705651712), (42853953/1180591620717411303424)), (15/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((215911823/18889465931478580854784), (-131535205/2361183241434822606848)), (3/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((1177516771/302231454903657293676544), (572738919/302231454903657293676544)), (35/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((53/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5427200/91954801), (-11009280/91954801)), 0, by norm_num⟩
  | 1 => ⟨((45874873139200/8455685426949601), (59749564416000/8455685426949601)), 0, by norm_num⟩
  | 2 => ⟨((-1282255597/2199023255552), (255633957/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((360586873/35184372088832), (-1348844201/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((1121666407/562949953421312), (982243361/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-1470400669/9007199254740992), (610552863/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((54740419/72057594037927936), (-1696628775/144115188075855872)), (11/144115188075855872), by norm_num⟩
  | 7 => ⟨((786668521/1152921504606846976), (226486247/576460752303423488)), (9/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-805292019/18446744073709551616), (269796971/9223372036854775808)), (7/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-34148515/73786976294838206464), (-513042035/147573952589676412928)), (21/295147905179352825856), by norm_num⟩
  | 10 => ⟨((1047277139/4722366482869645213696), (353648633/4722366482869645213696)), (31/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-416604645/37778931862957161709568), (209025419/18889465931478580854784)), (23/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-407407461/1208925819614629174706176), (-149102877/151115727451828646838272)), (67/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((53/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((53/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((53/16), (8601/1280)))⁻¹=value ((5427200/91954801), (-11009280/91954801)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((5427200/91954801), (-11009280/91954801))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1254585089/549755813888), (418595219/274877906944)), (1/549755813888), by norm_num⟩
  | 1 => ⟨((-330033293/2199023255552), (-608176279/1099511627776)), (3/2199023255552), by norm_num⟩
  | 2 => ⟨((1398335213/17592186044416), (39592821/8796093022208)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-118792281/35184372088832), (18800655/2199023255552)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((-824769507/1125899906842624), (-685800057/1125899906842624)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((700771337/9007199254740992), (-220454027/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((149058531/72057594037927936), (1176913425/144115188075855872)), (5/72057594037927936), by norm_num⟩
  | 7 => ⟨((-1708826051/2305843009213693952), (-108420957/2305843009213693952)), (17/2305843009213693952), by norm_num⟩
  | 8 => ⟨((106586237/4611686018427387904), (-136303545/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 9 => ⟨((75888817/18446744073709551616), (122717725/36893488147419103232)), (13/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-849559007/2361183241434822606848), (17616783/73786976294838206464)), (21/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-365299391/37778931862957161709568), (-4905447/147573952589676412928)), (33/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((1651416627/604462909807314587353088), (28705709/604462909807314587353088)), (13/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((69/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2355200/34815867), (-3669760/34815867)), 0, by norm_num⟩
  | 1 => ⟨((440009523200/134682732773521), (8643018752000/1212144594961689)), 0, by norm_num⟩
  | 2 => ⟨((-1069360635/2199023255552), (-151722607/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((706653371/35184372088832), (-25613033/1099511627776)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((308707031/562949953421312), (1039436499/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-521779255/4503599627370496), (-151103533/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((409792053/72057594037927936), (-716420751/144115188075855872)), (5/72057594037927936), by norm_num⟩
  | 7 => ⟨((80286121/1152921504606846976), (1078816419/2305843009213693952)), (15/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-996597807/36893488147419103232), (-448431593/36893488147419103232)), (11/18446744073709551616), by norm_num⟩
  | 9 => ⟨((917472135/590295810358705651712), (-597688101/590295810358705651712)), (31/590295810358705651712), by norm_num⟩
  | 10 => ⟨((3738699/4722366482869645213696), (548551907/4722366482869645213696)), (11/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-929166799/151115727451828646838272), (-9178497/2361183241434822606848)), (31/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((499091755/1208925819614629174706176), (-465608075/2417851639229258349412352)), (87/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((69/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((69/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((69/16), (8601/1280)))⁻¹=value ((2355200/34815867), (-3669760/34815867)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((2355200/34815867), (-3669760/34815867))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13498349/2199023255552), (1510983965/4398046511104)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((-1526464737/17592186044416), (-289351987/8796093022208)), (3/8796093022208), by norm_num⟩
  | 2 => ⟨((740279553/70368744177664), (-25363631/2199023255552)), (5/70368744177664), by norm_num⟩
  | 3 => ⟨((520624045/562949953421312), (264415241/140737488355328)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((-1099125799/4503599627370496), (95481987/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 5 => ⟨((260880479/36028797018963968), (-226003171/9007199254740992)), (9/36028797018963968), by norm_num⟩
  | 6 => ⟨((1197992039/576460752303423488), (901984979/576460752303423488)), (1/36028797018963968), by norm_num⟩
  | 7 => ⟨((-958509205/4611686018427387904), (303298635/2305843009213693952)), (15/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-337162799/73786976294838206464), (-402835689/18446744073709551616)), (27/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1141843993/590295810358705651712), (85356317/295147905179352825856)), (3/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-377046041/4722366482869645213696), (1381192455/9444732965739290427392)), (5/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((-346222359/37778931862957161709568), (-196142305/18889465931478580854784)), (33/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((632897227/604462909807314587353088), (-503554831/1208925819614629174706176)), (53/1208925819614629174706176), by norm_num⟩
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
  | 0 => ⟨((85/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8704000/120217201), (-11009280/120217201)), 0, by norm_num⟩
  | 1 => ⟨((22722315059200/14452175416274401), (95824773120000/14452175416274401)), 0, by norm_num⟩
  | 2 => ⟨((-792793027/2199023255552), (-369522019/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((182480407/8796093022208), (-183393415/17592186044416)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((-154066401/562949953421312), (747209155/562949953421312)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-458186735/9007199254740992), (-545670241/9007199254740992)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((665162305/144115188075855872), (-19617311/144115188075855872)), (13/288230376151711744), by norm_num⟩
  | 7 => ⟨((-370902013/2305843009213693952), (997355729/4611686018427387904)), (9/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-150511115/36893488147419103232), (-1121151539/73786976294838206464)), (25/73786976294838206464), by norm_num⟩
  | 9 => ⟨((995742279/1180591620717411303424), (26803423/73786976294838206464)), (17/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-890942255/18889465931478580854784), (60138263/2361183241434822606848)), (23/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((163579225/302231454903657293676544), (-116424107/37778931862957161709568)), (31/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((587614491/4835703278458516698824704), (659322149/4835703278458516698824704)), (41/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((85/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((85/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((85/16), (8601/1280)))⁻¹=value ((8704000/120217201), (-11009280/120217201)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8704000/120217201), (-11009280/120217201))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((561311515/17592186044416), (855411047/35184372088832)), (3/35184372088832), by norm_num⟩
  | 1 => ⟨((-406841211/35184372088832), (432440003/70368744177664)), (5/70368744177664), by norm_num⟩
  | 2 => ⟨((-88600799/562949953421312), (-717881761/281474976710656)), (9/562949953421312), by norm_num⟩
  | 3 => ⟨((814011611/2251799813685248), (307274247/2251799813685248)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-631644329/18014398509481984), (319735037/9007199254740992)), (9/18014398509481984), by norm_num⟩
  | 5 => ⟨((-306914413/144115188075855872), (-773950125/144115188075855872)), (11/144115188075855872), by norm_num⟩
  | 6 => ⟨((177768077/288230376151711744), (45815667/2305843009213693952)), (21/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-484037527/18446744073709551616), (1034471849/18446744073709551616)), (5/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-291354677/73786976294838206464), (-324238983/73786976294838206464)), (19/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1205830395/2361183241434822606848), (-420130025/2361183241434822606848)), (17/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-1610689/590295810358705651712), (1803009285/37778931862957161709568)), (29/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-559273895/151115727451828646838272), (-533495941/302231454903657293676544)), (49/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((38151977/151115727451828646838272), (-17499649/75557863725914323419136)), (41/2417851639229258349412352), by norm_num⟩
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
  | 0 => ⟨((101/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((10342400/139263601), (-11009280/139263601)), 0, by norm_num⟩
  | 1 => ⟨((7119504179200/19394350563487201), (113862377472000/19394350563487201)), 0, by norm_num⟩
  | 2 => ⟨((-135068895/549755813888), (-223740909/1099511627776)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1207976667/70368744177664), (-151655901/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-310885415/562949953421312), (427030157/562949953421312)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((-341451633/36028797018963968), (-56289951/1125899906842624)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((83877653/36028797018963968), (213557675/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 7 => ⟨((-83598315/576460752303423488), (341230613/9223372036854775808)), (1/576460752303423488), by norm_num⟩
  | 8 => ⟨((289437067/73786976294838206464), (-524325365/73786976294838206464)), (21/147573952589676412928), by norm_num⟩
  | 9 => ⟨((39909507/295147905179352825856), (15455001/36893488147419103232)), (27/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-407617793/18889465931478580854784), (-385736161/37778931862957161709568)), (17/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((1456595387/1208925819614629174706176), (-572809449/1208925819614629174706176)), (21/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((-503130607/19342813113834066795298816), (78844331/1208925819614629174706176)), (13/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((101/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((101/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((101/16), (8601/1280)))⁻¹=value ((10342400/139263601), (-11009280/139263601)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((10342400/139263601), (-11009280/139263601))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1207958203/281474976710656), (-50440575/70368744177664)), (5/281474976710656), by norm_num⟩
  | 1 => ⟨((-283696077/562949953421312), (881993977/562949953421312)), (7/562949953421312), by norm_num⟩
  | 2 => ⟨((-288820303/1125899906842624), (-574347397/2251799813685248)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((64447467/1125899906842624), (-344289067/18014398509481984)), (13/18014398509481984), by norm_num⟩
  | 4 => ⟨((-168299983/144115188075855872), (1207732887/144115188075855872)), (17/144115188075855872), by norm_num⟩
  | 5 => ⟨((-1003718819/1152921504606846976), (-677704963/1152921504606846976)), (21/1152921504606846976), by norm_num⟩
  | 6 => ⟨((949413657/9223372036854775808), (-8627555/144115188075855872)), (11/4611686018427387904), by norm_num⟩
  | 7 => ⟨((151791997/147573952589676412928), (462301461/36893488147419103232)), (21/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-1386151027/1180591620717411303424), (-518077141/1180591620717411303424)), (41/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((800945421/9444732965739290427392), (-790525041/9444732965739290427392)), (19/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((281804063/75557863725914323419136), (1544404761/151115727451828646838272)), (67/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-1156762275/1208925819614629174706176), (-42669509/604462909807314587353088)), (29/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((93717771/2417851639229258349412352), (-174952751/2417851639229258349412352)), (49/9671406556917033397649408), by norm_num⟩
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
  | 0 => ⟨((117/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1331200/17954089), (-3669760/53862267)), 0, by norm_num⟩
  | 1 => ⟨((-1240851251200/2901143806379289), (4885184512000/967047935459763)), 0, by norm_num⟩
  | 2 => ⟨((-343561981/2199023255552), (-443865821/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((891438205/70368744177664), (76020941/35184372088832)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-1223269665/2251799813685248), (395701103/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((147115499/18014398509481984), (-35505607/1125899906842624)), (3/18014398509481984), by norm_num⟩
  | 6 => ⟨((444758835/576460752303423488), (834306257/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 7 => ⟨((-1437115185/18446744073709551616), (-252455365/9223372036854775808)), (19/18446744073709551616), by norm_num⟩
  | 8 => ⟨((1127641271/295147905179352825856), (-3779845/2305843009213693952)), (11/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-405158485/4722366482869645213696), (225402953/1180591620717411303424)), (13/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-251108337/75557863725914323419136), (-188908177/18889465931478580854784)), (15/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((1121621395/2417851639229258349412352), (622680795/2417851639229258349412352)), (69/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-1004695369/38685626227668133590597632), (242001445/38685626227668133590597632)), (79/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((117/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((117/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((117/16), (8601/1280)))⁻¹=value ((1331200/17954089), (-3669760/53862267)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((1331200/17954089), (-3669760/53862267))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((75817133/281474976710656), (-389042267/1125899906842624)), (7/2251799813685248), by norm_num⟩
  | 1 => ⟨((320502989/4503599627370496), (388403863/2251799813685248)), (9/4503599627370496), by norm_num⟩
  | 2 => ⟨((-1618126409/36028797018963968), (-194699253/36028797018963968)), (11/18014398509481984), by norm_num⟩
  | 3 => ⟨((345231849/72057594037927936), (-957881221/144115188075855872)), (19/144115188075855872), by norm_num⟩
  | 4 => ⟨((614730339/1152921504606846976), (160045953/144115188075855872)), (27/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-374001359/2305843009213693952), (-67098109/9223372036854775808)), (17/4611686018427387904), by norm_num⟩
  | 6 => ⟨((181039963/18446744073709551616), (-616405503/36893488147419103232)), (19/36893488147419103232), by norm_num⟩
  | 7 => ⟨((670187453/590295810358705651712), (535023717/295147905179352825856)), (39/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-521338227/2361183241434822606848), (22352093/1180591620717411303424)), (19/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((613942801/75557863725914323419136), (-1526820531/75557863725914323419136)), (9/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((411035175/302231454903657293676544), (115572201/75557863725914323419136)), (65/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-431055663/2417851639229258349412352), (239769913/4835703278458516698824704)), (29/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((110799383/38685626227668133590597632), (-1231546963/77371252455336267181195264)), (99/77371252455336267181195264), by norm_num⟩
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
  | 0 => ⟨((133/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13619200/187186801), (-11009280/187186801)), 0, by norm_num⟩
  | 1 => ⟨((-32139181260800/35038898468613601), (149937586176000/35038898468613601)), 0, by norm_num⟩
  | 2 => ⟨((-203344835/2199023255552), (-803277219/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((1229342385/140737488355328), (552400713/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-60966355/140737488355328), (128447491/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((111725601/9007199254740992), (-1216994773/72057594037927936)), (5/36028797018963968), by norm_num⟩
  | 6 => ⟨((52368213/1152921504606846976), (1128910477/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 7 => ⟨((-561650913/18446744073709551616), (-158112871/4611686018427387904)), (7/9223372036854775808), by norm_num⟩
  | 8 => ⟨((624491535/295147905179352825856), (6491139/18446744073709551616)), (15/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-412357253/4722366482869645213696), (58345313/1180591620717411303424)), (33/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((260412921/151115727451828646838272), (-164930911/37778931862957161709568)), (35/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((158834561/2417851639229258349412352), (506525757/2417851639229258349412352)), (75/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-330779029/38685626227668133590597632), (-440186715/77371252455336267181195264)), (5/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((133/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((133/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((133/16), (8601/1280)))⁻¹=value ((13619200/187186801), (-11009280/187186801)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13619200/187186801), (-11009280/187186801))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-13060789/18014398509481984), (-1476550711/36028797018963968)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((298211363/18014398509481984), (354292453/36028797018963968)), (21/72057594037927936), by norm_num⟩
  | 2 => ⟨((-1290378947/288230376151711744), (342615207/144115188075855872)), (7/72057594037927936), by norm_num⟩
  | 3 => ⟨((29179183/576460752303423488), (-566956479/576460752303423488)), (25/1152921504606846976), by norm_num⟩
  | 4 => ⟨((1210018931/9223372036854775808), (799739285/9223372036854775808)), (19/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-721314125/36893488147419103232), (179189281/18446744073709551616)), (25/36893488147419103232), by norm_num⟩
  | 6 => ⟨((92670965/590295810358705651712), (-1606282345/590295810358705651712)), (29/295147905179352825856), by norm_num⟩
  | 7 => ⟨((622240937/2361183241434822606848), (796772813/4722366482869645213696)), (61/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-1114457579/37778931862957161709568), (603525805/37778931862957161709568)), (31/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((3669111/604462909807314587353088), (-2053224107/604462909807314587353088)), (15/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((87218085/302231454903657293676544), (374886191/2417851639229258349412352)), (111/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-485750571/19342813113834066795298816), (655290473/38685626227668133590597632)), (101/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-96666119/309485009821345068724781056), (-1659620749/618970019642690137449562112)), (11/38685626227668133590597632), by norm_num⟩
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
  | 0 => ⟨((149/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((15257600/216063601), (-11009280/216063601)), 0, by norm_num⟩
  | 1 => ⟨((-55795055820800/46683479677087201), (167975190528000/46683479677087201)), 0, by norm_num⟩
  | 2 => ⟨((-54393875/1099511627776), (-1385333387/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((810534785/140737488355328), (605235251/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-44038005/140737488355328), (-23032697/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((805497263/72057594037927936), (-561428451/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-452387685/2305843009213693952), (1291026943/2305843009213693952)), (13/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-270695359/36893488147419103232), (-913747073/36893488147419103232)), (13/36893488147419103232), by norm_num⟩
  | 8 => ⟨((525395627/590295810358705651712), (811718497/1180591620717411303424)), (13/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-924505145/18889465931478580854784), (-15114457/9444732965739290427392)), (13/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1069205787/604462909807314587353088), (-44972477/37778931862957161709568)), (13/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-155355751/4835703278458516698824704), (26323197/302231454903657293676544)), (51/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-335669345/309485009821345068724781056), (-602520065/154742504910672534362390528)), (25/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((149/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((149/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((149/16), (8601/1280)))⁻¹=value ((15257600/216063601), (-11009280/216063601)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((15257600/216063601), (-11009280/216063601))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-308322415/144115188075855872), (-823499757/288230376151711744)), (17/288230376151711744), by norm_num⟩
  | 1 => ⟨((1048221013/576460752303423488), (-29604019/288230376151711744)), (23/576460752303423488), by norm_num⟩
  | 2 => ⟨((-147915401/576460752303423488), (1028289721/2305843009213693952)), (31/2305843009213693952), by norm_num⟩
  | 3 => ⟨((-450478653/9223372036854775808), (-434946455/4611686018427387904)), (15/4611686018427387904), by norm_num⟩
  | 4 => ⟨((1314116667/73786976294838206464), (112455077/73786976294838206464)), (47/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-229230863/147573952589676412928), (1229050467/590295810358705651712)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-148479709/1180591620717411303424), (-739629769/2361183241434822606848)), (39/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((46784119/1180591620717411303424), (239620453/37778931862957161709568)), (85/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-213822241/75557863725914323419136), (1032683549/302231454903657293676544)), (89/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-193165185/1208925819614629174706176), (-65420615/151115727451828646838272)), (11/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((1738913485/38685626227668133590597632), (288572807/38685626227668133590597632)), (167/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-831711109/309485009821345068724781056), (259778291/77371252455336267181195264)), (77/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-369724243/2475880078570760549798248448), (-892409347/2475880078570760549798248448)), (137/2475880078570760549798248448), by norm_num⟩
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
  | 0 => ⟨((165/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5632000/82739067), (-3669760/82739067)), 0, by norm_num⟩
  | 1 => ⟨((-3042047590400/2281917736010163), (20668088320000/6845753208030489)), 0, by norm_num⟩
  | 2 => ⟨((-94918303/4398046511104), (-1163886281/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((258177583/70368744177664), (141610317/35184372088832)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-964345571/4503599627370496), (-125241701/2251799813685248)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((1228035743/144115188075855872), (-411548133/144115188075855872)), (5/72057594037927936), by norm_num⟩
  | 6 => ⟨((-255227/1125899906842624), (164962835/576460752303423488)), (5/1152921504606846976), by norm_num⟩
  | 7 => ⟨((25254233/18446744073709551616), (-1089591067/73786976294838206464)), (19/73786976294838206464), by norm_num⟩
  | 8 => ⟨((331607351/1180591620717411303424), (1258372379/2361183241434822606848)), (35/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-807661979/37778931862957161709568), (-449926703/37778931862957161709568)), (1/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1198925829/1208925819614629174706176), (-41570537/604462909807314587353088)), (59/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-77922591/2417851639229258349412352), (235343267/9671406556917033397649408)), (27/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((172452865/309485009821345068724781056), (-955014727/618970019642690137449562112)), (49/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((165/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((165/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((165/16), (8601/1280)))⁻¹=value ((5632000/82739067), (-3669760/82739067)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((5632000/82739067), (-3669760/82739067))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-627997427/2305843009213693952), (-459277521/4611686018427387904)), (1/144115188075855872), by norm_num⟩
  | 1 => ⟨((602738393/4611686018427387904), (-832803881/9223372036854775808)), (45/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-2445619/18446744073709551616), (13750841/288230376151711744)), (1/576460752303423488), by norm_num⟩
  | 3 => ⟨((-1263412289/147573952589676412928), (-867778279/147573952589676412928)), (65/147573952589676412928), by norm_num⟩
  | 4 => ⟨((1004488699/590295810358705651712), (-398981433/590295810358705651712)), (53/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-33241247/590295810358705651712), (40046225/147573952589676412928)), (75/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((-250812113/9444732965739290427392), (-990897821/37778931862957161709568)), (47/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((1349234151/302231454903657293676544), (-308913079/302231454903657293676544)), (53/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((-411888773/2417851639229258349412352), (594657949/1208925819614629174706176)), (57/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-680639351/19342813113834066795298816), (-414910299/9671406556917033397649408)), (115/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((1714416911/309485009821345068724781056), (-249496317/309485009821345068724781056)), (111/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-253370189/1237940039285380274899124224), (1233061661/2475880078570760549798248448)), (13/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-299387197/9903520314283042199192993792), (-390207911/9903520314283042199192993792)), (189/19807040628566084398385987584), by norm_num⟩
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
  | 0 => ⟨((181/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((18534400/283647601), (-11009280/283647601)), 0, by norm_num⟩
  | 1 => ⟨((-111159868620800/80455961553055201), (204050399232000/80455961553055201)), 0, by norm_num⟩
  | 2 => ⟨((-71755307/17592186044416), (-1929393971/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((636597805/281474976710656), (986299485/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-1278059421/9007199254740992), (-158957603/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((1731054983/288230376151711744), (-64468131/144115188075855872)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-864863865/4611686018427387904), (604903413/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 7 => ⟨((66069177/18446744073709551616), (-1169510347/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 8 => ⟨((86841459/2361183241434822606848), (387736967/1180591620717411303424)), (11/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-572370165/75557863725914323419136), (-378409889/37778931862957161709568)), (19/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1068400557/2417851639229258349412352), (435798057/2417851639229258349412352)), (1/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-346909137/19342813113834066795298816), (207867247/77371252455336267181195264)), (27/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((660835263/1237940039285380274899124224), (-67441339/154742504910672534362390528)), (23/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((181/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((181/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((181/16), (8601/1280)))⁻¹=value ((18534400/283647601), (-11009280/283647601)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18534400/283647601), (-11009280/283647601))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1598345313/73786976294838206464), (292791/72057594037927936)), (27/36893488147419103232), by norm_num⟩
  | 1 => ⟨((208983855/36893488147419103232), (-850465161/73786976294838206464)), (5/9223372036854775808), by norm_num⟩
  | 2 => ⟨((69420361/36893488147419103232), (1065194539/295147905179352825856)), (15/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-271289363/295147905179352825856), (-78712305/590295810358705651712)), (1/18446744073709551616), by norm_num⟩
  | 4 => ⟨((277620053/2361183241434822606848), (-292064331/2361183241434822606848)), (27/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((204456731/37778931862957161709568), (495668281/18889465931478580854784)), (79/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-1039469309/302231454903657293676544), (-216918555/151115727451828646838272)), (51/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((237107043/604462909807314587353088), (-628415375/2417851639229258349412352)), (119/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((3647549/19342813113834066795298816), (2122197369/38685626227668133590597632)), (65/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-97394577/19342813113834066795298816), (-249608499/77371252455336267181195264)), (67/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((690520687/1237940039285380274899124224), (-643729081/2475880078570760549798248448)), (33/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-143047853/19807040628566084398385987584), (1184585559/19807040628566084398385987584)), (251/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-175462823/39614081257132168796771975168), (-553861403/158456325028528675187087900672)), (231/158456325028528675187087900672), by norm_num⟩
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
  | 0 => ⟨((197/16), (8601/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((20172800/322354801), (-11009280/322354801)), 0, by norm_num⟩
  | 1 => ⟨((-142868806860800/103912617727749601), (222088003584000/103912617727749601)), 0, by norm_num⟩
  | 2 => ⟨((114763413/17592186044416), (-1589496089/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((188414853/140737488355328), (413557349/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-414639957/4503599627370496), (-77781349/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((9143431/2251799813685248), (169888135/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-316170473/2305843009213693952), (58678775/1152921504606846976)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((504886821/147573952589676412928), (-580551827/147573952589676412928)), (11/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-376581157/9444732965739290427392), (857182023/4722366482869645213696)), (35/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-279870935/151115727451828646838272), (-961162305/151115727451828646838272)), (7/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((201361795/1208925819614629174706176), (809451321/4835703278458516698824704)), (11/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-624395257/77371252455336267181195264), (-185174995/77371252455336267181195264)), (69/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((1452753943/4951760157141521099596496896), (-311571629/4951760157141521099596496896)), (27/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((197/16), (8601/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((197/16), (8601/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((197/16), (8601/1280)))⁻¹=value ((20172800/322354801), (-11009280/322354801)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((20172800/322354801), (-11009280/322354801))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-718272415/590295810358705651712), (586801853/590295810358705651712)), (43/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-10661515/590295810358705651712), (-570597509/590295810358705651712)), (33/590295810358705651712), by norm_num⟩
  | 2 => ⟨((609377851/2361183241434822606848), (904449595/4722366482869645213696)), (103/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-1386878185/18889465931478580854784), (405399257/18889465931478580854784)), (115/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((382642697/75557863725914323419136), (-1033749171/75557863725914323419136)), (25/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((791864435/604462909807314587353088), (595956299/302231454903657293676544)), (151/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-1638904521/4835703278458516698824704), (-56558295/4835703278458516698824704)), (201/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((512107547/19342813113834066795298816), (-678605407/19342813113834066795298816)), (121/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((512512085/309485009821345068724781056), (1540108121/309485009821345068724781056)), (135/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-1391627439/2475880078570760549798248448), (-389589473/2475880078570760549798248448)), (71/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((458544913/9903520314283042199192993792), (-396096995/9903520314283042199192993792)), (285/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((130697387/158456325028528675187087900672), (477857269/79228162514264337593543950336)), (137/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-1331951081/2535301200456458802993406410752), (-306899973/1267650600228229401496703205376)), (511/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((173627427/1099511627776), (145059169/549755813888)), (1627/4398046511104), by norm_num⟩
  | 1 => ⟨((-177746615/4398046511104), (806331589/2199023255552)), (1665/2199023255552), by norm_num⟩
  | 2 => ⟨((-323381971/2199023255552), (347996987/2199023255552)), (897/1099511627776), by norm_num⟩
  | 3 => ⟨((-709201667/8796093022208), (282221379/17592186044416)), (10649/17592186044416), by norm_num⟩
  | 4 => ⟨((-1472905873/70368744177664), (-642940309/70368744177664)), (12107/35184372088832), by norm_num⟩
  | 5 => ⟨((-188855385/70368744177664), (-1166811471/281474976710656)), (44715/281474976710656), by norm_num⟩
  | 6 => ⟨((-39856723/2251799813685248), (-1951220897/2251799813685248)), (17407/281474976710656), by norm_num⟩
  | 7 => ⟨((545679883/9007199254740992), (-1010890499/9007199254740992)), (187779/9007199254740992), by norm_num⟩
  | 8 => ⟨((479864127/36028797018963968), (-665737269/72057594037927936)), (447299/72057594037927936), by norm_num⟩
  | 9 => ⟨((1038158949/576460752303423488), (-194885001/576460752303423488)), (955795/576460752303423488), by norm_num⟩
  | 10 => ⟨((855725357/4611686018427387904), (167495219/4611686018427387904)), (3710289/9223372036854775808), by norm_num⟩
  | 11 => ⟨((1142870485/73786976294838206464), (689465219/73786976294838206464)), (3304847/36893488147419103232), by norm_num⟩
  | 12 => ⟨((305753909/295147905179352825856), (728393561/590295810358705651712)), (10902187/590295810358705651712), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((173627427/1099511627776), (145059169/549755813888)), (407/1099511627776), by norm_num⟩
  | 1 => ⟨((-177746615/4398046511104), (806331589/2199023255552)), (3331/4398046511104), by norm_num⟩
  | 2 => ⟨((-323381971/2199023255552), (347996987/2199023255552)), (3589/4398046511104), by norm_num⟩
  | 3 => ⟨((-709201667/8796093022208), (282221379/17592186044416)), (5325/8796093022208), by norm_num⟩
  | 4 => ⟨((-1472905873/70368744177664), (-642940309/70368744177664)), (24217/70368744177664), by norm_num⟩
  | 5 => ⟨((-188855385/70368744177664), (-1166811471/281474976710656)), (44727/281474976710656), by norm_num⟩
  | 6 => ⟨((-39856723/2251799813685248), (-1951220897/2251799813685248)), (139347/2251799813685248), by norm_num⟩
  | 7 => ⟨((545679883/9007199254740992), (-1010890499/9007199254740992)), (47035/2251799813685248), by norm_num⟩
  | 8 => ⟨((479864127/36028797018963968), (-665737269/72057594037927936)), (225091/36028797018963968), by norm_num⟩
  | 9 => ⟨((1038158949/576460752303423488), (-194885001/576460752303423488)), (489427/288230376151711744), by norm_num⟩
  | 10 => ⟨((855725357/4611686018427387904), (167495219/4611686018427387904)), (509903/1152921504606846976), by norm_num⟩
  | 11 => ⟨((1142870485/73786976294838206464), (689465219/73786976294838206464)), (4780587/36893488147419103232), by norm_num⟩
  | 12 => ⟨((305753909/295147905179352825856), (728393561/590295810358705651712)), (8628505/147573952589676412928), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨35,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile035Gamma

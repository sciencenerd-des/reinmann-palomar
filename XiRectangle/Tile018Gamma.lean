/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile018Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨18,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (5217/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (5217/640))
  have he : value ((3/4), (5217/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (5217/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (5217/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (5217/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21913600/320311489), (-6677760/320311489)), 0, by norm_num⟩
  | 1 => ⟨((-217806693171200/102599449985397121), (146333761536000/102599449985397121)), 0, by norm_num⟩
  | 2 => ⟨((4063773695/70368744177664), (-4990295907/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-5567371987/4503599627370496), (13635952103/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((48302275/4503599627370496), (-16783181897/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((1953168911/2305843009213693952), (9443346987/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((-10575842145/147573952589676412928), (-19370638091/147573952589676412928)), (3/36893488147419103232), by norm_num⟩
  | 7 => ⟨((9018902139/2361183241434822606848), (8837834205/2361183241434822606848)), (5/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-6410099131/37778931862957161709568), (-6665646623/75557863725914323419136)), (15/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((4064147509/604462909807314587353088), (3019965691/2417851639229258349412352)), (23/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-9401024451/38685626227668133590597632), (2116903725/77371252455336267181195264)), (17/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((9937436963/1237940039285380274899124224), (-8588867147/2475880078570760549798248448)), (25/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-4722598555/19807040628566084398385987584), (8015513605/39614081257132168796771975168)), (37/39614081257132168796771975168), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (5217/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (5217/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (5217/1280)))⁻¹=value ((21913600/320311489), (-6677760/320311489)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/320311489), (-6677760/320311489))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2832302101/1073741824), (317603997/1073741824)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((10956800/320311489), (-3338880/320311489)), 0, by norm_num⟩
  | 2 => ⟨((-54451673292800/102599449985397121), (36583440384000/102599449985397121)), 0, by norm_num⟩
  | 3 => ⟨((10836729853/1125899906842624), (-1663431969/140737488355328)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-5567371987/36028797018963968), (13635952103/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((9660455/9007199254740992), (-26853091035/2305843009213693952)), (9/2305843009213693952), by norm_num⟩
  | 6 => ⟨((5208450429/73786976294838206464), (3147782329/9223372036854775808)), (11/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-12086676737/2361183241434822606848), (-2767234013/295147905179352825856)), (7/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((9018902139/37778931862957161709568), (8837834205/37778931862957161709568)), (5/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-2848932947/302231454903657293676544), (-1481254805/302231454903657293676544)), (15/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((13005272029/38685626227668133590597632), (2415972553/38685626227668133590597632)), (19/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-27348434767/2475880078570760549798248448), (3079132691/2475880078570760549798248448)), (25/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((13249915951/39614081257132168796771975168), (-5725911431/39614081257132168796771975168)), (17/19807040628566084398385987584), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (111/20480)), 0, by norm_num⟩
  | 45 => ⟨((101937769457/4080638361600), (-220557/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-47806713952951/1915179604377600), (4483126129109/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((6988594517/274877906944), (-261122669/34359738368)), (1/549755813888), by norm_num⟩
  | 42 => ⟨((-7159138919/274877906944), (2122972409/274877906944)), (1/549755813888), by norm_num⟩
  | 41 => ⟨((14676174453/549755813888), (-4343985843/549755813888)), (1/549755813888), by norm_num⟩
  | 40 => ⟨((-15045134215/549755813888), (139101249/17179869184)), (1/274877906944), by norm_num⟩
  | 39 => ⟨((15430752727/549755813888), (-4562823803/549755813888)), (1/274877906944), by norm_num⟩
  | 38 => ⟨((-3959137287/137438953472), (2339680785/274877906944)), (1/549755813888), by norm_num⟩
  | 37 => ⟨((4066111425/137438953472), (-2400926069/274877906944)), (1/274877906944), by norm_num⟩
  | 36 => ⟨((-16716174271/549755813888), (4930949043/549755813888)), (1/549755813888), by norm_num⟩
  | 35 => ⟨((2149214307/68719476736), (-5067200681/549755813888)), (1/274877906944), by norm_num⟩
  | 34 => ⟨((-8849666163/274877906944), (5211201299/549755813888)), (1/274877906944), by norm_num⟩
  | 33 => ⟨((18235581513/549755813888), (-670453205/68719476736)), (1/274877906944), by norm_num⟩
  | 32 => ⟨((-18805333975/549755813888), (5525234907/549755813888)), (1/274877906944), by norm_num⟩
  | 31 => ⟨((9705915283/274877906944), (-2848442789/274877906944)), (1/274877906944), by norm_num⟩
  | 30 => ⟨((-20058743535/549755813888), (5879543731/549755813888)), (1/274877906944), by norm_num⟩
  | 29 => ⟨((20750251261/549755813888), (-3037151659/274877906944)), (1/274877906944), by norm_num⟩
  | 28 => ⟨((-21491128585/549755813888), (3141204101/274877906944)), (1/274877906944), by norm_num⟩
  | 27 => ⟨((22286857127/549755813888), (-6505278779/549755813888)), (1/274877906944), by norm_num⟩
  | 26 => ⟨((-2892970131/68719476736), (3372272225/274877906944)), (1/274877906944), by norm_num⟩
  | 25 => ⟨((6017293841/137438953472), (-1750520883/137438953472)), (1/274877906944), by norm_num⟩
  | 24 => ⟨((-3133957035/68719476736), (7280072683/549755813888)), (1/274877906944), by norm_num⟩
  | 23 => ⟨((26161246315/549755813888), (-7581048585/549755813888)), (1/274877906944), by norm_num⟩
  | 22 => ⟨((-3418726453/68719476736), (988498201/68719476736)), (1/137438953472), by norm_num⟩
  | 21 => ⟨((14325737767/274877906944), (-2066098619/137438953472)), (1/137438953472), by norm_num⟩
  | 20 => ⟨((-3760397737/68719476736), (2163612223/137438953472)), (1/137438953472), by norm_num⟩
  | 19 => ⟨((15832718009/274877906944), (-1135393727/68719476736)), (1/137438953472), by norm_num⟩
  | 18 => ⟨((-16711646013/274877906944), (4778270583/274877906944)), (1/137438953472), by norm_num⟩
  | 17 => ⟨((17693843965/274877906944), (-630124795/34359738368)), (1/137438953472), by norm_num⟩
  | 16 => ⟨((-18798640047/274877906944), (5334303635/274877906944)), (1/137438953472), by norm_num⟩
  | 15 => ⟨((10025252379/137438953472), (-5663855729/274877906944)), (1/137438953472), by norm_num⟩
  | 14 => ⟨((-671277573/8589934592), (3018409145/137438953472)), (1/137438953472), by norm_num⟩
  | 13 => ⟨((11565432357/137438953472), (-403898537/17179869184)), (1/137438953472), by norm_num⟩
  | 12 => ⟨((-25055197653/274877906944), (6952505203/274877906944)), (1/137438953472), by norm_num⟩
  | 11 => ⟨((13664231675/137438953472), (-1880778609/68719476736)), (1/137438953472), by norm_num⟩
  | 10 => ⟨((-15027478083/137438953472), (4097906685/137438953472)), (1/68719476736), by norm_num⟩
  | 9 => ⟨((16692554751/137438953472), (-4500357403/137438953472)), (1/68719476736), by norm_num⟩
  | 8 => ⟨((-1173255433/8589934592), (4990539991/137438953472)), (1/68719476736), by norm_num⟩
  | 7 => ⟨((21442659889/137438953472), (-5600692963/137438953472)), (1/68719476736), by norm_num⟩
  | 6 => ⟨((-24997728673/137438953472), (6381088135/137438953472)), (1/68719476736), by norm_num⟩
  | 5 => ⟨((14981742797/68719476736), (-3707363443/68719476736)), (1/68719476736), by norm_num⟩
  | 4 => ⟨((-18693411211/68719476736), (553079183/8589934592)), (1/68719476736), by norm_num⟩
  | 3 => ⟨((6211566285/17179869184), (-42873495/536870912)), (1/68719476736), by norm_num⟩
  | 2 => ⟨((-18519067423/34359738368), (451849359/4294967296)), (1/34359738368), by norm_num⟩
  | 1 => ⟨((18238601647/17179869184), (-82977055/536870912)), (1/17179869184), by norm_num⟩
  | 0 => ⟨((-9263511731/68719476736), (10163327905/34359738368)), (3/68719476736), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (5217/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (5217/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (5217/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((2832302101/1073741824), (317603997/1073741824)), (1/8589934592), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (5217/1280))) (z:=((-21/128), (5217/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((2832302101/1073741824), (317603997/1073741824))) (r:=(1/8589934592)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (5217/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((17585702567/536870912), (7816497629/536870912)), (1/268435456), by norm_num⟩
  | 1 => ⟨((15477259029/8589934592), (2630372195/17179869184)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((904623067315200/102599449985397121), (-285662126290080/102599449985397121)), 0, by norm_num⟩
  | 3 => ⟨((-13126016893/140737488355328), (4597704253/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((1441581419/1125899906842624), (-7505974883/4503599627370496)), (11/4503599627370496), by norm_num⟩
  | 5 => ⟨((-2304232435/144115188075855872), (12587079871/288230376151711744)), (1/9007199254740992), by norm_num⟩
  | 6 => ⟨((997661347/18446744073709551616), (-10524921509/9223372036854775808)), (83/18446744073709551616), by norm_num⟩
  | 7 => ⟨((2243545989/295147905179352825856), (2144637011/73786976294838206464)), (13/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-2074515975/4722366482869645213696), (-3319598651/4722366482869645213696)), (71/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((169777107/9444732965739290427392), (9337107435/604462909807314587353088)), (13/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-12367903433/19342813113834066795298816), (-5344008507/19342813113834066795298816)), (141/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((25753868007/1237940039285380274899124224), (1372179363/618970019642690137449562112)), (729/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-24857247817/39614081257132168796771975168), (4915710851/39614081257132168796771975168)), (977/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-5217/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((10405054119/536870912), (351770577/33554432)), (5/1073741824), by norm_num⟩
  | 1 => ⟨((11182291733/8589934592), (2630372195/17179869184)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((904623067315200/102599449985397121), (-285662126290080/102599449985397121)), 0, by norm_num⟩
  | 3 => ⟨((-13126016893/140737488355328), (4597704253/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((1441581419/1125899906842624), (-7505974883/4503599627370496)), (11/4503599627370496), by norm_num⟩
  | 5 => ⟨((-2304232435/144115188075855872), (12587079871/288230376151711744)), (1/9007199254740992), by norm_num⟩
  | 6 => ⟨((997661347/18446744073709551616), (-10524921509/9223372036854775808)), (83/18446744073709551616), by norm_num⟩
  | 7 => ⟨((2243545989/295147905179352825856), (2144637011/73786976294838206464)), (13/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-2074515975/4722366482869645213696), (-3319598651/4722366482869645213696)), (71/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((169777107/9444732965739290427392), (9337107435/604462909807314587353088)), (13/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-12367903433/19342813113834066795298816), (-5344008507/19342813113834066795298816)), (141/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((25753868007/1237940039285380274899124224), (1372179363/618970019642690137449562112)), (729/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-24857247817/39614081257132168796771975168), (4915710851/39614081257132168796771975168)), (977/39614081257132168796771975168), by norm_num⟩
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
  | 0 => ⟨((31574487577/17179869184), 0), (1/17179869184), by norm_num⟩
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
  | 0 => ⟨((31574487577/34359738368), 0), (1/34359738368), by norm_num⟩
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
  | 0 => ⟨((21796810975/1073741824), (351770577/33554432)), (3/536870912), by norm_num⟩
  | 1 => ⟨((11182291733/8589934592), (2630372195/17179869184)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((904623067315200/102599449985397121), (-285662126290080/102599449985397121)), 0, by norm_num⟩
  | 3 => ⟨((-13126016893/140737488355328), (4597704253/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((1441581419/1125899906842624), (-7505974883/4503599627370496)), (11/4503599627370496), by norm_num⟩
  | 5 => ⟨((-2304232435/144115188075855872), (12587079871/288230376151711744)), (1/9007199254740992), by norm_num⟩
  | 6 => ⟨((997661347/18446744073709551616), (-10524921509/9223372036854775808)), (83/18446744073709551616), by norm_num⟩
  | 7 => ⟨((2243545989/295147905179352825856), (2144637011/73786976294838206464)), (13/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-2074515975/4722366482869645213696), (-3319598651/4722366482869645213696)), (71/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((169777107/9444732965739290427392), (9337107435/604462909807314587353088)), (13/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-12367903433/19342813113834066795298816), (-5344008507/19342813113834066795298816)), (141/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((25753868007/1237940039285380274899124224), (1372179363/618970019642690137449562112)), (729/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-24857247817/39614081257132168796771975168), (4915710851/39614081257132168796771975168)), (977/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((435613386342400/102599449985397121), (-292667523072000/102599449985397121)), 0, by norm_num⟩
  | 1 => ⟨((-4063773695/17592186044416), (4990295907/17592186044416)), (1/35184372088832), by norm_num⟩
  | 2 => ⟨((8351057981/1125899906842624), (-20453928155/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-48302275/562949953421312), (16783181897/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((-4882922277/576460752303423488), (-23608367467/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 5 => ⟨((991485201/1152921504606846976), (1815997321/1152921504606846976)), (1/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-7891539371/147573952589676412928), (-15466209859/295147905179352825856)), (7/147573952589676412928), by norm_num⟩
  | 7 => ⟨((12820198261/4722366482869645213696), (6665646623/4722366482869645213696)), (3/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-9144331895/75557863725914323419136), (-1698730701/75557863725914323419136)), (19/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((23502561127/4835703278458516698824704), (-330766207/604462909807314587353088)), (15/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-853998489/4835703278458516698824704), (5904846163/77371252455336267181195264)), (3/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((14167795665/2475880078570760549798248448), (-12023270407/2475880078570760549798248448)), (37/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((-6227949377/39614081257132168796771975168), (19377261481/79228162514264337593543950336)), (7/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4063773695/17592186044416), (-4990295907/17592186044416)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((-8351057981/562949953421312), (20453928155/562949953421312)), (1/281474976710656), by norm_num⟩
  | 2 => ⟨((2318509201/9007199254740992), (-25174772845/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((4882922277/144115188075855872), (23608367467/144115188075855872)), (7/144115188075855872), by norm_num⟩
  | 4 => ⟨((-4957426005/1152921504606846976), (-9079986605/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 5 => ⟨((92478977/288230376151711744), (5799828697/18446744073709551616)), (5/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-22435346957/1180591620717411303424), (-11664881591/1180591620717411303424)), (9/590295810358705651712), by norm_num⟩
  | 7 => ⟨((18288663789/18889465931478580854784), (3397461403/18889465931478580854784)), (1/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-26440381267/604462909807314587353088), (1488447931/302231454903657293676544)), (7/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((17079969779/9671406556917033397649408), (-922632213/1208925819614629174706176)), (3/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-304386235/4835703278458516698824704), (2066499601/38685626227668133590597632)), (21/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((4670962033/2475880078570760549798248448), (-7266473055/2475880078570760549798248448)), (33/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((-3137252967/79228162514264337593543950336), (86698357/618970019642690137449562112)), (51/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5567371987/562949953421312), (-13635952103/562949953421312)), (3/562949953421312), by norm_num⟩
  | 1 => ⟨((-48302275/140737488355328), (16783181897/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 2 => ⟨((-4882922277/72057594037927936), (-23608367467/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 3 => ⟨((1652475335/144115188075855872), (12106648807/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 4 => ⟨((-4932212107/4611686018427387904), (-4833190581/4611686018427387904)), (7/9223372036854775808), by norm_num⟩
  | 5 => ⟨((5608836739/73786976294838206464), (11664881591/295147905179352825856)), (1/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-21336774421/4722366482869645213696), (-1981852485/2361183241434822606848)), (9/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((17626920845/75557863725914323419136), (-1984597241/75557863725914323419136)), (9/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-6404988667/604462909807314587353088), (5535793277/1208925819614629174706176)), (17/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((4058483133/9671406556917033397649408), (-6888332003/19342813113834066795298816)), (15/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-4281715197/309485009821345068724781056), (13321867267/618970019642690137449562112)), (27/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((3137252967/9903520314283042199192993792), (-22194779391/19807040628566084398385987584)), (45/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((334499297/316912650057057350374175801344), (8246147587/158456325028528675187087900672)), (37/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((48302275/281474976710656), (-16783181897/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 1 => ⟨((2441461139/36028797018963968), (23608367467/72057594037927936)), (7/72057594037927936), by norm_num⟩
  | 2 => ⟨((-4957426005/288230376151711744), (-9079986605/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 3 => ⟨((4932212107/2305843009213693952), (4833190581/2305843009213693952)), (7/4611686018427387904), by norm_num⟩
  | 4 => ⟨((-1752761481/9223372036854775808), (-7290550995/73786976294838206464)), (5/36893488147419103232), by norm_num⟩
  | 5 => ⟨((16002580815/1180591620717411303424), (371597341/147573952589676412928)), (13/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((-15423555739/18889465931478580854784), (868261293/9444732965739290427392)), (29/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((12809977335/302231454903657293676544), (-5535793277/302231454903657293676544)), (17/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-18263174099/9671406556917033397649408), (15498747007/9671406556917033397649408)), (33/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((1338035999/19342813113834066795298816), (-4163083521/38685626227668133590597632)), (31/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((-2156861415/1237940039285380274899124224), (15258910831/2475880078570760549798248448)), (29/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((-501748945/79228162514264337593543950336), (-3092305345/9903520314283042199192993792)), (53/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((2933686161/633825300114114700748351602688), (4485282181/316912650057057350374175801344)), (23/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1953168911/72057594037927936), (-9443346987/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 1 => ⟨((7931881609/576460752303423488), (1815997321/72057594037927936)), (7/576460752303423488), by norm_num⟩
  | 2 => ⟨((-92478977/36028797018963968), (-5799828697/2305843009213693952)), (7/4611686018427387904), by norm_num⟩
  | 3 => ⟨((22435346957/73786976294838206464), (11664881591/73786976294838206464)), (15/73786976294838206464), by norm_num⟩
  | 4 => ⟨((-1000161301/36893488147419103232), (-371597341/73786976294838206464)), (13/590295810358705651712), by norm_num⟩
  | 5 => ⟨((18508266887/9444732965739290427392), (-2083827103/9444732965739290427392)), (9/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((-4483492067/37778931862957161709568), (1937527647/37778931862957161709568)), (11/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((913158705/151115727451828646838272), (-12398997605/2417851639229258349412352)), (27/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((-9633859193/38685626227668133590597632), (14987100675/38685626227668133590597632)), (29/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((2156861415/309485009821345068724781056), (-15258910831/618970019642690137449562112)), (29/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((551923839/19807040628566084398385987584), (6803071759/4951760157141521099596496896)), (57/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((-3520423393/158456325028528675187087900672), (-21529354469/316912650057057350374175801344)), (27/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((2636490277/1267650600228229401496703205376), (7514628789/2535301200456458802993406410752)), (25/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-10575842145/2305843009213693952), (-19370638091/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 1 => ⟨((15783078743/9223372036854775808), (15466209859/9223372036854775808)), (13/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-5608836739/18446744073709551616), (-11664881591/73786976294838206464)), (15/73786976294838206464), by norm_num⟩
  | 3 => ⟨((21336774421/590295810358705651712), (1981852485/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 4 => ⟨((-30847111479/9444732965739290427392), (868261293/2361183241434822606848)), (29/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((4483492067/18889465931478580854784), (-1937527647/18889465931478580854784)), (23/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((-17045629159/1208925819614629174706176), (7232748603/604462909807314587353088)), (31/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((12845145591/19342813113834066795298816), (-4995700225/4835703278458516698824704)), (39/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((-6470584245/309485009821345068724781056), (22888366247/309485009821345068724781056)), (23/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-459936533/4951760157141521099596496896), (-2834613233/618970019642690137449562112)), (49/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((3227054777/39614081257132168796771975168), (4933810399/19807040628566084398385987584)), (51/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-10545961107/1267650600228229401496703205376), (-7514628789/633825300114114700748351602688)), (51/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((6208864055/10141204801825835211973625643008), (2425030795/5070602400912917605986812821504)), (49/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-9018902139/18446744073709551616), (-8837834205/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 1 => ⟨((6410099131/36893488147419103232), (6665646623/73786976294838206464)), (3/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-18288663789/590295810358705651712), (-3397461403/590295810358705651712)), (15/590295810358705651712), by norm_num⟩
  | 3 => ⟨((17626920845/4722366482869645213696), (-1984597241/4722366482869645213696)), (17/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((-12809977335/37778931862957161709568), (2767896639/18889465931478580854784)), (17/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((14610539279/604462909807314587353088), (-12398997605/604462909807314587353088)), (27/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((-12845145591/9671406556917033397649408), (4995700225/2417851639229258349412352)), (5/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((7394953423/154742504910672534362390528), (-26158132853/154742504910672534362390528)), (53/154742504910672534362390528), by norm_num⟩
  | 8 => ⟨((591346971/2475880078570760549798248448), (29156021825/2475880078570760549798248448)), (33/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((-4610078253/19807040628566084398385987584), (-3524150285/4951760157141521099596496896)), (39/19807040628566084398385987584), by norm_num⟩
  | 10 => ⟨((8286112299/316912650057057350374175801344), (5904351191/158456325028528675187087900672)), (21/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((-10643766951/5070602400912917605986812821504), (-8314391297/5070602400912917605986812821504)), (11/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((11419156351/81129638414606681695789005144064), (8788581645/162259276829213363391578010288128)), (11/20282409603651670423947251286016), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6410099131/147573952589676412928), (-6665646623/295147905179352825856)), (15/295147905179352825856), by norm_num⟩
  | 1 => ⟨((9144331895/590295810358705651712), (1698730701/590295810358705651712)), (5/295147905179352825856), by norm_num⟩
  | 2 => ⟨((-26440381267/9444732965739290427392), (1488447931/4722366482869645213696)), (7/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((12809977335/37778931862957161709568), (-5535793277/37778931862957161709568)), (9/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((-4565793525/151115727451828646838272), (121083961/4722366482869645213696)), (9/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((9633859193/4835703278458516698824704), (-14987100675/4835703278458516698824704)), (31/4835703278458516698824704), by norm_num⟩
  | 6 => ⟨((-6470584245/77371252455336267181195264), (22888366247/77371252455336267181195264)), (49/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((-295673485/618970019642690137449562112), (-455562841/19342813113834066795298816)), (69/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((2593169017/4951760157141521099596496896), (15858676283/9903520314283042199192993792)), (45/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((-10357640373/158456325028528675187087900672), (-7380438989/79228162514264337593543950336)), (7/19807040628566084398385987584), by norm_num⟩
  | 10 => ⟨((7317589779/1267650600228229401496703205376), (11432288033/2535301200456458802993406410752)), (1/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((-8564367263/20282409603651670423947251286016), (-3295718117/20282409603651670423947251286016)), (71/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((4364171341/162259276829213363391578010288128), (1251303593/649037107316853453566312041152512)), (75/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4064147509/1180591620717411303424), (-3019965691/4722366482869645213696)), (23/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((23502561127/18889465931478580854784), (-330766207/2361183241434822606848)), (33/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((-17079969779/75557863725914323419136), (922632213/9444732965739290427392)), (13/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((16233932533/604462909807314587353088), (-6888332003/302231454903657293676544)), (35/604462909807314587353088), by norm_num⟩
  | 4 => ⟨((-10704287993/4835703278458516698824704), (16652334085/4835703278458516698824704)), (37/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((2156861415/19342813113834066795298816), (-15258910831/38685626227668133590597632)), (17/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((459936533/618970019642690137449562112), (2834613233/77371252455336267181195264)), (57/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((-1152519563/1237940039285380274899124224), (-3524150285/1237940039285380274899124224)), (43/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((10357640373/79228162514264337593543950336), (7380438989/39614081257132168796771975168)), (59/79228162514264337593543950336), by norm_num⟩
  | 9 => ⟨((-4065327655/316912650057057350374175801344), (-3175635565/316912650057057350374175801344)), (19/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((2616889997/2535301200456458802993406410752), (8056199841/20282409603651670423947251286016)), (93/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-23275580485/324518553658426726783156020576256), (-1668404791/324518553658426726783156020576256)), (107/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((11390009089/2596148429267413814265248164610048), (-5195417113/5192296858534827628530496329220096)), (119/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-9401024451/37778931862957161709568), (2116903725/75557863725914323419136)), (17/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((853998489/9444732965739290427392), (-5904846163/151115727451828646838272)), (27/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((-9740359519/604462909807314587353088), (2066499601/151115727451828646838272)), (3/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((4281715197/2417851639229258349412352), (-13321867267/4835703278458516698824704)), (33/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((-2156861415/19342813113834066795298816), (953681927/2417851639229258349412352)), (37/38685626227668133590597632), by norm_num⟩
  | 5 => ⟨((-551923839/618970019642690137449562112), (-27212287037/618970019642690137449562112)), (73/618970019642690137449562112), by norm_num⟩
  | 6 => ⟨((3227054777/2475880078570760549798248448), (19735241597/4951760157141521099596496896)), (1/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((-4143056149/19807040628566084398385987584), (-5904351191/19807040628566084398385987584)), (51/39614081257132168796771975168), by norm_num⟩
  | 8 => ⟨((7317589779/316912650057057350374175801344), (5716144017/316912650057057350374175801344)), (37/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((-2616889997/1267650600228229401496703205376), (-4028099921/5070602400912917605986812821504)), (25/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((25603138533/162259276829213363391578010288128), (917622635/81129638414606681695789005144064)), (127/162259276829213363391578010288128), by norm_num⟩
  | 11 => ⟨((-13668010907/1298074214633706907132624082305024), (779312567/324518553658426726783156020576256)), (77/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((12761285713/20769187434139310514121985316880384), (-7307056421/20769187434139310514121985316880384)), (89/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/960934467), (-556480/320311489)), 0, by norm_num⟩
  | 1 => ⟨((-54451673292800/307798349956191363), (12194480128000/102599449985397121)), 0, by norm_num⟩
  | 2 => ⟨((10836729853/2251799813685248), (-1663431969/281474976710656)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-7423162649/72057594037927936), (18181269471/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 4 => ⟨((2060897067/2305843009213693952), (-22377575863/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 5 => ⟨((5208450429/73786976294838206464), (3147782329/9223372036854775808)), (11/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-3525280715/590295810358705651712), (-12913758727/1180591620717411303424)), (9/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((3006300713/9444732965739290427392), (2945944735/9444732965739290427392)), (7/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-17093597683/1208925819614629174706176), (-8887528831/1208925819614629174706176)), (21/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((21675453381/38685626227668133590597632), (4026620921/38685626227668133590597632)), (1/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-3133674817/154742504910672534362390528), (705634575/309485009821345068724781056)), (23/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((13249915951/19807040628566084398385987584), (-5725911431/19807040628566084398385987584)), (17/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((-12593596147/633825300114114700748351602688), (10687351473/633825300114114700748351602688)), (25/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((21802932503/1073741824), (11254793043/1073741824)), (7/1073741824), by norm_num⟩
  | 1 => ⟨((22361544227/17179869184), (82262941/536870912)), (3/17179869184), by norm_num⟩
  | 2 => ⟨((19399450451/2199023255552), (-6135617653/2199023255552)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-6570257629/70368744177664), (4615459399/70368744177664)), (7/140737488355328), by norm_num⟩
  | 4 => ⟨((11540701731/9007199254740992), (-3774840543/2251799813685248)), (23/9007199254740992), by norm_num⟩
  | 5 => ⟨((-4588119361/288230376151711744), (12685448069/288230376151711744)), (33/288230376151711744), by norm_num⟩
  | 6 => ⟨((887496325/18446744073709551616), (-10625810249/9223372036854775808)), (21/4611686018427387904), by norm_num⟩
  | 7 => ⟨((4674985773/590295810358705651712), (8670608817/295147905179352825856)), (105/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-2141287841/4722366482869645213696), (-6708631121/9444732965739290427392)), (143/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((11204413807/604462909807314587353088), (9400023387/604462909807314587353088)), (209/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-12759612785/19342813113834066795298816), (-2649953173/9671406556917033397649408)), (283/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((13290993877/618970019642690137449562112), (1193244631/618970019642690137449562112)), (183/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-3205543447/4951760157141521099596496896), (2791835159/19807040628566084398385987584)), (981/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5779589255/9007199254740992), (14194619469/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((742316265/18014398509481984), (-14545015577/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 2 => ⟨((-824358827/1152921504606846976), (8951030345/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 3 => ⟨((-1736150143/18446744073709551616), (-16788172421/36893488147419103232)), (3/18446744073709551616), by norm_num⟩
  | 4 => ⟨((7050561429/590295810358705651712), (12913758727/590295810358705651712)), (7/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-16835283991/18889465931478580854784), (-4124322629/4722366482869645213696)), (15/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((15954024503/302231454903657293676544), (8295026909/302231454903657293676544)), (7/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-26010544055/9671406556917033397649408), (-2415972553/4835703278458516698824704)), (3/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((18802048901/154742504910672534362390528), (-529225931/38685626227668133590597632)), (21/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-12145756287/2475880078570760549798248448), (5248752145/2475880078570760549798248448)), (9/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((6926477881/39614081257132168796771975168), (-11756086619/79228162514264337593543950336)), (31/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-13286292005/2535301200456458802993406410752), (161477179/19807040628566084398385987584)), (47/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((2230935443/20282409603651670423947251286016), (-7891477117/20282409603651670423947251286016)), (37/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10901465907/536870912), (11254793889/1073741824)), (1/134217728), by norm_num⟩
  | 1 => ⟨((22361544935/17179869184), (1316206189/8589934592)), (1/4294967296), by norm_num⟩
  | 2 => ⟨((19399448879/2199023255552), (-1533900145/549755813888)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((-1642566063/17592186044416), (2307713689/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((5770404657/4503599627370496), (-3774791281/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((-4588376247/288230376151711744), (3171299085/72057594037927936)), (17/144115188075855872), by norm_num⟩
  | 6 => ⟨((888470081/18446744073709551616), (-10625557105/9223372036854775808)), (85/18446744073709551616), by norm_num⟩
  | 7 => ⟨((4673398215/590295810358705651712), (17340922715/590295810358705651712)), (53/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-33448657/73786976294838206464), (-13417520653/18889465931478580854784)), (9/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((5600724267/302231454903657293676544), (9401304821/604462909807314587353088)), (105/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-3189057679/4835703278458516698824704), (-1325694121/4835703278458516698824704)), (71/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((26575500307/1237940039285380274899124224), (1198290793/618970019642690137449562112)), (733/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-3204998785/4951760157141521099596496896), (5568257277/39614081257132168796771975168)), (491/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1256165831/9223372036854775808), (-27279330575/18446744073709551616)), (9/18446744073709551616), by norm_num⟩
  | 1 => ⟨((3968343185/73786976294838206464), (19186482767/73786976294838206464)), (7/73786976294838206464), by norm_num⟩
  | 2 => ⟨((-8057784491/590295810358705651712), (-7379290701/295147905179352825856)), (3/295147905179352825856), by norm_num⟩
  | 3 => ⟨((8016801901/4722366482869645213696), (7855852627/4722366482869645213696)), (3/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((-2848932947/18889465931478580854784), (-5925019221/75557863725914323419136)), (9/75557863725914323419136), by norm_num⟩
  | 5 => ⟨((26010544055/2417851639229258349412352), (4831945107/2417851639229258349412352)), (11/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((-25069398535/38685626227668133590597632), (2822538299/38685626227668133590597632)), (25/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((10410648247/309485009821345068724781056), (-4498930409/309485009821345068724781056)), (29/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-14842452601/9903520314283042199192993792), (12595807091/9903520314283042199192993792)), (7/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((2174839465/39614081257132168796771975168), (-6766662739/79228162514264337593543950336)), (13/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((-3505755697/2535301200456458802993406410752), (3100223153/633825300114114700748351602688)), (3/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-407770571/81129638414606681695789005144064), (-5026223291/20282409603651670423947251286016)), (11/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((4768404173/1298074214633706907132624082305024), (3645181709/324518553658426726783156020576256)), (19/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10901465907/536870912), (11254793887/1073741824)), (9/1073741824), by norm_num⟩
  | 1 => ⟨((2795193117/2147483648), (1316206191/8589934592)), (5/17179869184), by norm_num⟩
  | 2 => ⟨((19399448849/2199023255552), (-6135600635/2199023255552)), (3/2199023255552), by norm_num⟩
  | 3 => ⟨((-13140528265/140737488355328), (4615427495/70368744177664)), (9/140737488355328), by norm_num⟩
  | 4 => ⟨((2885201989/2251799813685248), (-7549582915/4503599627370496)), (25/9007199254740992), by norm_num⟩
  | 5 => ⟨((-2294186573/144115188075855872), (3171299229/72057594037927936)), (35/288230376151711744), by norm_num⟩
  | 6 => ⟨((888458127/18446744073709551616), (-664097277/576460752303423488)), (43/9223372036854775808), by norm_num⟩
  | 7 => ⟨((584177259/73786976294838206464), (8670457067/295147905179352825856)), (107/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-4281442251/9444732965739290427392), (-3354374157/4722366482869645213696)), (145/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((11201481719/604462909807314587353088), (9401253195/604462909807314587353088)), (211/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-12756257463/19342813113834066795298816), (-5302681873/19342813113834066795298816)), (285/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((26575494085/1237940039285380274899124224), (1198137405/618970019642690137449562112)), (367/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-3204980595/4951760157141521099596496896), (5568702245/39614081257132168796771975168)), (983/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6446227593/2361183241434822606848), (5903432561/1180591620717411303424)), (1/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-9620162281/9444732965739290427392), (-589188947/590295810358705651712)), (9/9444732965739290427392), by norm_num⟩
  | 2 => ⟨((13674878145/75557863725914323419136), (7110023065/75557863725914323419136)), (5/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-3251318007/151115727451828646838272), (-2415972553/604462909807314587353088)), (5/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((18802048901/9671406556917033397649408), (-529225931/2417851639229258349412352)), (19/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-21862361317/154742504910672534362390528), (2361938465/38685626227668133590597632)), (29/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((10389716821/1237940039285380274899124224), (-2204266241/309485009821345068724781056)), (5/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((-7829422075/19807040628566084398385987584), (6089996465/9903520314283042199192993792)), (25/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((3943975159/316912650057057350374175801344), (-13951004189/316912650057057350374175801344)), (29/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((560684535/10141204801825835211973625643008), (27644228101/10141204801825835211973625643008)), (61/10141204801825835211973625643008), by norm_num⟩
  | 10 => ⟨((-7867866885/162259276829213363391578010288128), (-24058199279/162259276829213363391578010288128)), (63/162259276829213363391578010288128), by norm_num⟩
  | 11 => ⟨((6428014389/1298074214633706907132624082305024), (18321380667/2596148429267413814265248164610048)), (63/2596148429267413814265248164610048), by norm_num⟩
  | 12 => ⟨((-7568900943/20769187434139310514121985316880384), (-11824912067/41538374868278621028243970633760768)), (61/41538374868278621028243970633760768), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10901465907/536870912), (11254793887/1073741824)), (5/536870912), by norm_num⟩
  | 1 => ⟨((2795193117/2147483648), (1316206191/8589934592)), (3/8589934592), by norm_num⟩
  | 2 => ⟨((19399448849/2199023255552), (-6135600635/2199023255552)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-3285132067/35184372088832), (9230854989/140737488355328)), (5/70368744177664), by norm_num⟩
  | 4 => ⟨((5770403987/4503599627370496), (-1887395729/1125899906842624)), (13/4503599627370496), by norm_num⟩
  | 5 => ⟨((-4588373187/288230376151711744), (6342598467/144115188075855872)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((444229141/9223372036854775808), (-21251112995/18446744073709551616)), (87/18446744073709551616), by norm_num⟩
  | 7 => ⟨((4673417839/590295810358705651712), (17340914497/590295810358705651712)), (27/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-8562884267/18889465931478580854784), (-3354374365/4722366482869645213696)), (73/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((1400185219/75557863725914323419136), (9401254843/604462909807314587353088)), (53/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-12756258401/19342813113834066795298816), (-5302684741/19342813113834066795298816)), (143/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((26575500215/1237940039285380274899124224), (1198141773/618970019642690137449562112)), (735/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-25639859197/39614081257132168796771975168), (696086371/4951760157141521099596496896)), (123/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-22100813165/604462909807314587353088), (-11490946367/604462909807314587353088)), (27/604462909807314587353088), by norm_num⟩
  | 1 => ⟨((15763966095/1208925819614629174706176), (2928451579/1208925819614629174706176)), (9/604462909807314587353088), by norm_num⟩
  | 2 => ⟨((-356099411/151115727451828646838272), (641485977/2417851639229258349412352)), (25/9671406556917033397649408), by norm_num⟩
  | 3 => ⟨((22083193251/77371252455336267181195264), (-9543185717/77371252455336267181195264)), (1/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((-983874699/38685626227668133590597632), (3339797335/154742504910672534362390528)), (1/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((8303932503/4951760157141521099596496896), (-12918174319/4951760157141521099596496896)), (27/4951760157141521099596496896), by norm_num⟩
  | 6 => ⟨((-348583663/4951760157141521099596496896), (2466086599/9903520314283042199192993792)), (43/79228162514264337593543950336), by norm_num⟩
  | 7 => ⟨((-509713213/1267650600228229401496703205376), (-12565558227/633825300114114700748351602688)), (61/1267650600228229401496703205376), by norm_num⟩
  | 8 => ⟨((4470378911/10141204801825835211973625643008), (13669431409/10141204801825835211973625643008)), (5/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((-8927797763/162259276829213363391578010288128), (-6361590509/81129638414606681695789005144064)), (49/162259276829213363391578010288128), by norm_num⟩
  | 10 => ⟨((12614834905/2596148429267413814265248164610048), (9854093389/2596148429267413814265248164610048)), (7/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((-7382080873/20769187434139310514121985316880384), (-2840753663/20769187434139310514121985316880384)), (31/20769187434139310514121985316880384), by norm_num⟩
  | 12 => ⟨((30093679819/1329227995784915872903807060280344576), (1078564713/664613997892457936451903530140172288)), (131/1329227995784915872903807060280344576), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10901465907/536870912), (11254793887/1073741824)), (11/1073741824), by norm_num⟩
  | 1 => ⟨((2795193117/2147483648), (1316206191/8589934592)), (7/17179869184), by norm_num⟩
  | 2 => ⟨((19399448849/2199023255552), (-6135600635/2199023255552)), (5/2199023255552), by norm_num⟩
  | 3 => ⟨((-3285132067/35184372088832), (9230854989/140737488355328)), (11/140737488355328), by norm_num⟩
  | 4 => ⟨((5770403987/4503599627370496), (-1887395729/1125899906842624)), (27/9007199254740992), by norm_num⟩
  | 5 => ⟨((-4588373187/288230376151711744), (12685196933/288230376151711744)), (37/288230376151711744), by norm_num⟩
  | 6 => ⟨((888458281/18446744073709551616), (-10625556495/9223372036854775808)), (11/2305843009213693952), by norm_num⟩
  | 7 => ⟨((4673417839/590295810358705651712), (17340914485/590295810358705651712)), (109/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-8562884259/18889465931478580854784), (-13417497435/18889465931478580854784)), (147/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((11201481719/604462909807314587353088), (2350313699/151115727451828646838272)), (213/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-12756258307/19342813113834066795298816), (-1325671167/4835703278458516698824704)), (287/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((26575499775/1237940039285380274899124224), (2396283377/1237940039285380274899124224)), (23/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-6409964575/9903520314283042199192993792), (696086379/4951760157141521099596496896)), (985/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((288427479/604462909807314587353088), (-32473759/604462909807314587353088)), (35/38685626227668133590597632), by norm_num⟩
  | 1 => ⟨((-13414933219/77371252455336267181195264), (1449305787/19342813113834066795298816)), (27/77371252455336267181195264), by norm_num⟩
  | 2 => ⟨((9562829601/309485009821345068724781056), (-8115340513/309485009821345068724781056)), (3/38685626227668133590597632), by norm_num⟩
  | 3 => ⟨((-8407351443/2475880078570760549798248448), (13079060007/2475880078570760549798248448)), (33/2475880078570760549798248448), by norm_num⟩
  | 4 => ⟨((529387497/2475880078570760549798248448), (-14980798593/19807040628566084398385987584)), (37/19807040628566084398385987584), by norm_num⟩
  | 5 => ⟨((541864355/316912650057057350374175801344), (26716309955/316912650057057350374175801344)), (73/316912650057057350374175801344), by norm_num⟩
  | 6 => ⟨((-6336475545/2535301200456458802993406410752), (-19375542777/2535301200456458802993406410752)), (1/39614081257132168796771975168), by norm_num⟩
  | 7 => ⟨((8135087807/20282409603651670423947251286016), (11593474395/20282409603651670423947251286016)), (51/20282409603651670423947251286016), by norm_num⟩
  | 8 => ⟨((-7184217791/162259276829213363391578010288128), (-11223920657/324518553658426726783156020576256)), (37/162259276829213363391578010288128), by norm_num⟩
  | 9 => ⟨((20553551911/5192296858534827628530496329220096), (3954682893/2596148429267413814265248164610048)), (99/5192296858534827628530496329220096), by norm_num⟩
  | 10 => ⟨((-25136490143/83076749736557242056487941267521536), (-1801795689/83076749736557242056487941267521536)), (63/41538374868278621028243970633760768), by norm_num⟩
  | 11 => ⟨((26837789515/1329227995784915872903807060280344576), (-6120869169/1329227995784915872903807060280344576)), (19/166153499473114484112975882535043072), by norm_num⟩
  | 12 => ⟨((-12528695735/10633823966279326983230456482242756608), (112091819/166153499473114484112975882535043072)), (11/1329227995784915872903807060280344576), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((10901465907/536870912), (11254793887/1073741824)), (3/268435456), by norm_num⟩
  | 1 => ⟨((2795193117/2147483648), (1316206191/8589934592)), (1/2147483648), by norm_num⟩
  | 2 => ⟨((19399448849/2199023255552), (-6135600635/2199023255552)), (3/1099511627776), by norm_num⟩
  | 3 => ⟨((-3285132067/35184372088832), (9230854989/140737488355328)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((5770403987/4503599627370496), (-1887395729/1125899906842624)), (7/2251799813685248), by norm_num⟩
  | 5 => ⟨((-4588373187/288230376151711744), (12685196933/288230376151711744)), (19/144115188075855872), by norm_num⟩
  | 6 => ⟨((888458281/18446744073709551616), (-10625556495/9223372036854775808)), (89/18446744073709551616), by norm_num⟩
  | 7 => ⟨((4673417839/590295810358705651712), (17340914485/590295810358705651712)), (55/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-2140721065/4722366482869645213696), (-3354374359/4722366482869645213696)), (37/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((11201481721/604462909807314587353088), (9401254797/604462909807314587353088)), (107/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-12756258313/19342813113834066795298816), (-1325671167/4835703278458516698824704)), (9/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((3321937475/154742504910672534362390528), (2396283371/1237940039285380274899124224)), (737/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-25639858347/39614081257132168796771975168), (5568691059/39614081257132168796771975168)), (493/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-84838926004715/262144), (-1202819797122513/2097152)), (11203883/524288), by norm_num⟩
  | 1 => ⟨((-666728779/2), (-6369029139/8)), (505/16), by norm_num⟩
  | 2 => ⟨((-5133346045/32), (-17530326399/32)), (47/2), by norm_num⟩
  | 3 => ⟨((-2879592223/64), (-7997043547/32)), (377/32), by norm_num⟩
  | 4 => ⟨((-1658537851/256), (-21810628885/256)), (1143/256), by norm_num⟩
  | 5 => ⟨((528234085/1024), (-23741531907/1024)), (1399/1024), by norm_num⟩
  | 6 => ⟨((2520238835/4096), (-5377129803/1024)), (1441/4096), by norm_num⟩
  | 7 => ⟨((1757773701/8192), (-16690508951/16384)), (1285/16384), by norm_num⟩
  | 8 => ⟨((1723613741/32768), (-22658324783/131072)), (1013/65536), by norm_num⟩
  | 9 => ⟨((5463113043/524288), (-13669069221/524288)), (1435/524288), by norm_num⟩
  | 10 => ⟨((7396224771/4194304), (-7420500827/2097152)), (1847/4194304), by norm_num⟩
  | 11 => ⟨((8816600879/33554432), (-457645093/1048576)), (2183/33554432), by norm_num⟩
  | 12 => ⟨((9434282123/268435456), (-13239566473/268435456)), (2389/268435456), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((402606507377059/2535301200456458802993406410752), (-21213508979/79228162514264337593543950336)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1813901396551889/633825300114114700748351602688), (-833035355849/158456325028528675187087900672)), (17925/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((241163535319843/4951760157141521099596496896), (-3758581477701/39614081257132168796771975168)), (10113/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1931595892735951/2475880078570760549798248448), (-4001968073869/2475880078570760549798248448)), (21541/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((906653316329961/77371252455336267181195264), (-2005725583287/77371252455336267181195264)), (21597/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1589084490241681/9671406556917033397649408), (-235677575579/604462909807314587353088)), (20307/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1293425842231075/604462909807314587353088), (-1654813754417/302231454903657293676544)), (17829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((972083341409001/37778931862957161709568), (-1349309049011/18889465931478580854784)), (14543/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1339898766358071/4722366482869645213696), (-4064708837919/4722366482869645213696)), (21915/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((419954977295805/147573952589676412928), (-5616389352405/590295810358705651712)), (30295/590295810358705651712), by norm_num⟩
  | 8 => ⟨((948315876516077/36893488147419103232), (-3530931535689/36893488147419103232)), (38115/73786976294838206464), by norm_num⟩
  | 7 => ⟨((476306118598271/2305843009213693952), (-8001904669737/9223372036854775808)), (43221/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1676807161706275/1152921504606846976), (-1009271246107/144115188075855872)), (43653/1152921504606846976), by norm_num⟩
  | 5 => ⟨((316857007360233/36028797018963968), (-7147071010243/144115188075855872)), (1209/4503599627370496), by norm_num⟩
  | 4 => ⟨((400418075313923/9007199254740992), (-10887161089909/36028797018963968)), (59027/36028797018963968), by norm_num⟩
  | 3 => ⟨((814076817939065/4503599627370496), (-6952732577471/4503599627370496)), (75561/9007199254740992), by norm_num⟩
  | 2 => ⟨((1254929552326573/2251799813685248), (-14360501947869/2251799813685248)), (78295/2251799813685248), by norm_num⟩
  | 1 => ⟨((1324744560892003/1125899906842624), (-22715098433435/1125899906842624)), (15565/140737488355328), by norm_num⟩
  | 0 => ⟨((1545467615633955/1125899906842624), (-12588705669277/281474976710656)), (278861/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1545467615633955/1125899906842624), (-12588705669277/281474976710656)), (1063770298484420421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1059567785868891/562949953421312), (-8639949615581/70368744177664)), (395251/562949953421312), by norm_num⟩
  | 2 => ⟨((1985800633569707/562949953421312), (-130094865144769/281474976710656)), (1584919/562949953421312), by norm_num⟩
  | 3 => ⟨((1721158975581763/140737488355328), (-458908405726973/140737488355328)), (3161661/140737488355328), by norm_num⟩
  | 4 => ⟨((1222040821592959/8796093022208), (-701531563051547/8796093022208)), (3060945/4398046511104), by norm_num⟩
  | 5 => ⟨((444638652866501/34359738368), (-95179442958771/4294967296)), (2614775/8589934592), by norm_num⟩
  | 6 => ⟨((-84838926004715/262144), (-1202819797122513/2097152)), (11203883/524288), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((10901465907/536870912), (11254793887/1073741824)), (3/268435456), by norm_num⟩, 2, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2252800/30314689), (-6677760/30314689)), 0, by norm_num⟩
  | 1 => ⟨((19758685388800/918980369166721), (15043657728000/918980369166721)), 0, by norm_num⟩
  | 2 => ⟨((-2860813351/1099511627776), (7739860949/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-3418220465/35184372088832), (-24767308969/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((11927635429/281474976710656), (669225527/281474976710656)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-4135223627/2251799813685248), (10310810775/2251799813685248)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((-15711799115/36028797018963968), (-13417185429/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 7 => ⟨((16492636321/288230376151711744), (-9855735393/288230376151711744)), (9/288230376151711744), by norm_num⟩
  | 8 => ⟨((3781615503/2305843009213693952), (17461748371/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 9 => ⟨((-16510093599/18446744073709551616), (-929259475/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 10 => ⟨((6545299853/147573952589676412928), (-6997503497/73786976294838206464)), (5/36893488147419103232), by norm_num⟩
  | 11 => ⟨((10385730349/1180591620717411303424), (9927318509/1180591620717411303424)), (25/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-5917212199/4722366482869645213696), (3100091283/4722366482869645213696)), (15/4722366482869645213696), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (5217/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (5217/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (5217/1280)))⁻¹=value ((2252800/30314689), (-6677760/30314689)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/30314689), (-6677760/30314689))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (5217/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3891200/36458689), (-6677760/36458689)), 0, by norm_num⟩
  | 1 => ⟨((14725520588800/1329236003598721), (25984499712000/1329236003598721)), 0, by norm_num⟩
  | 2 => ⟨((-20947235773/8796093022208), (-126027117/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((9127376085/70368744177664), (-7619572921/35184372088832)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((7268161805/562949953421312), (6596451739/281474976710656)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-25537048651/9007199254740992), (-614654211/9007199254740992)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((2838123911/18014398509481984), (-18447019807/72057594037927936)), (5/36028797018963968), by norm_num⟩
  | 7 => ⟨((67722145/4503599627370496), (4048151177/144115188075855872)), (13/576460752303423488), by norm_num⟩
  | 8 => ⟨((-3891004983/1152921504606846976), (-1124107973/9223372036854775808)), (31/9223372036854775808), by norm_num⟩
  | 9 => ⟨((441019533/2305843009213693952), (-5581425337/18446744073709551616)), (19/36893488147419103232), by norm_num⟩
  | 10 => ⟨((10331762485/590295810358705651712), (19870653295/590295810358705651712)), (45/590295810358705651712), by norm_num⟩
  | 11 => ⟨((-18968801421/4722366482869645213696), (-228413475/1180591620717411303424)), (53/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((547966505/2361183241434822606848), (-13507221099/37778931862957161709568)), (63/37778931862957161709568), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (5217/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (5217/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (5217/1280)))⁻¹=value ((3891200/36458689), (-6677760/36458689)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/36458689), (-6677760/36458689))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-35826383257600/1105233818382721), (-41028157440000/1105233818382721)), 0, by norm_num⟩
  | 1 => ⟨((11459635021/1099511627776), (-6989600945/2199023255552)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((-1939271035/8796093022208), (15731776131/8796093022208)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-15963817015/70368744177664), (-9528163127/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((16587109053/562949953421312), (-11854452423/562949953421312)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((4498077071/4503599627370496), (20928948655/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 6 => ⟨((-2673505867/4503599627370496), (-4193675525/36028797018963968)), (9/36028797018963968), by norm_num⟩
  | 7 => ⟨((379950595/9007199254740992), (-8976018873/144115188075855872)), (13/288230376151711744), by norm_num⟩
  | 8 => ⟨((11563625469/2305843009213693952), (17742775363/2305843009213693952)), (17/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-10019124931/9223372036854775808), (930726597/4611686018427387904)), (23/18446744073709551616), by norm_num⟩
  | 10 => ⟨((3962359231/147573952589676412928), (-18962670317/147573952589676412928)), (29/147573952589676412928), by norm_num⟩
  | 11 => ⟨((15127930705/1180591620717411303424), (10155731983/1180591620717411303424)), (37/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-14026290417/9444732965739290427392), (9576987841/9444732965739290427392)), (23/4722366482869645213696), by norm_num⟩
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
  | 0 => ⟨((27/8), (5217/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((614400/5097721), (-2225920/15293163)), 0, by norm_num⟩
  | 1 => ⟨((778666803200/233880834544569), (455868416000/25986759393841)), 0, by norm_num⟩
  | 2 => ⟨((-6497130089/4398046511104), (-111991849/137438953472)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((10437410165/70368744177664), (-8219666551/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-5278214497/1125899906842624), (8058002057/562949953421312)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-6838122609/9007199254740992), (-10842466531/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 6 => ⟨((19218256259/144115188075855872), (2491947771/144115188075855872)), (3/36028797018963968), by norm_num⟩
  | 7 => ⟨((-5357945419/576460752303423488), (9987506925/1152921504606846976)), (7/576460752303423488), by norm_num⟩
  | 8 => ⟨((-1297239255/18446744073709551616), (-5526873479/4611686018427387904)), (31/18446744073709551616), by norm_num⟩
  | 9 => ⟨((13496379853/147573952589676412928), (9902721101/147573952589676412928)), (17/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-24543878751/2361183241434822606848), (1541756445/590295810358705651712)), (37/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((8242106957/18889465931478580854784), (-17262556479/18889465931478580854784)), (79/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((6076759445/151115727451828646838272), (6560397587/75557863725914323419136)), (85/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (5217/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (5217/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (5217/1280)))⁻¹=value ((614400/5097721), (-2225920/15293163)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((614400/5097721), (-2225920/15293163))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-20472661387/2199023255552), (8382451/34359738368)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((5879363667/4398046511104), (-2850272515/1099511627776)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((6013704559/17592186044416), (17632704057/35184372088832)), (3/35184372088832), by norm_num⟩
  | 3 => ⟨((-29307565869/281474976710656), (1601149439/140737488355328)), (7/281474976710656), by norm_num⟩
  | 4 => ⟨((6679839999/1125899906842624), (-4247338461/281474976710656)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((3461885023/2251799813685248), (7907521247/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 6 => ⟨((-22259730693/72057594037927936), (2826410661/36028797018963968)), (13/72057594037927936), by norm_num⟩
  | 7 => ⟨((2572614525/288230376151711744), (-23551463369/576460752303423488)), (9/288230376151711744), by norm_num⟩
  | 8 => ⟨((1198967533/288230376151711744), (953772851/288230376151711744)), (13/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-5469839661/9223372036854775808), (10542171863/36893488147419103232)), (33/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-154573813/295147905179352825856), (-11772447265/147573952589676412928)), (43/295147905179352825856), by norm_num⟩
  | 11 => ⟨((20385262745/2361183241434822606848), (4652617839/1180591620717411303424)), (27/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((-3959589743/4722366482869645213696), (13773842815/18889465931478580854784)), (69/18889465931478580854784), by norm_num⟩
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
  | 0 => ⟨((35/8), (5217/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7168000/58577089), (-6677760/58577089)), 0, by norm_num⟩
  | 1 => ⟨((-3393872691200/3431275355713921), (47866183680000/3431275355713921)), 0, by norm_num⟩
  | 2 => ⟨((-12923703159/17592186044416), (-8003546855/8796093022208)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((13625029017/140737488355328), (3883765505/281474976710656)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-15109202161/2251799813685248), (10524969337/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((5192411231/36028797018963968), (-3010368201/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((2110055813/72057594037927936), (7077860429/144115188075855872)), (9/288230376151711744), by norm_num⟩
  | 7 => ⟨((-10586256807/2305843009213693952), (-6160281797/4611686018427387904)), (9/2305843009213693952), by norm_num⟩
  | 8 => ⟨((13172485301/36893488147419103232), (-6639323753/36893488147419103232)), (9/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-3420078731/295147905179352825856), (9256408635/295147905179352825856)), (35/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-2546862715/2361183241434822606848), (-12180653367/4722366482869645213696)), (17/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((16095207969/75557863725914323419136), (3639392009/37778931862957161709568)), (65/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-22394615545/1208925819614629174706176), (7553207313/1208925819614629174706176)), (31/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (5217/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (5217/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (5217/1280)))⁻¹=value ((7168000/58577089), (-6677760/58577089)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/58577089), (-6677760/58577089))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2444054075/2199023255552), (2399521517/2199023255552)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((-554737597/4398046511104), (-21101023965/35184372088832)), (5/35184372088832), by norm_num⟩
  | 2 => ⟨((9912362073/70368744177664), (1824664297/35184372088832)), (5/140737488355328), by norm_num⟩
  | 3 => ⟨((-6479235465/281474976710656), (5099791569/281474976710656)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-696411921/1125899906842624), (-22263327389/4503599627370496)), (9/4503599627370496), by norm_num⟩
  | 5 => ⟨((12752593603/18014398509481984), (5526847513/18014398509481984)), (9/18014398509481984), by norm_num⟩
  | 6 => ⟨((-6460626097/72057594037927936), (9568560003/144115188075855872)), (3/36028797018963968), by norm_num⟩
  | 7 => ⟨((-2149101033/1152921504606846976), (-17512663099/1152921504606846976)), (17/1152921504606846976), by norm_num⟩
  | 8 => ⟨((8605966783/4611686018427387904), (848753/1125899906842624)), (3/1152921504606846976), by norm_num⟩
  | 9 => ⟨((-14546443349/73786976294838206464), (93858083/576460752303423488)), (31/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-3764213573/590295810358705651712), (-18240689475/590295810358705651712)), (21/295147905179352825856), by norm_num⟩
  | 11 => ⟨((17270825897/4722366482869645213696), (2420699531/2361183241434822606848)), (53/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((-11397114751/37778931862957161709568), (12487825369/37778931862957161709568)), (67/37778931862957161709568), by norm_num⟩
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
  | 0 => ⟨((43/8), (5217/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8806400/74551489), (-6677760/74551489)), 0, by norm_num⟩
  | 1 => ⟨((-16480101171200/5557924512117121), (58807025664000/5557924512117121)), 0, by norm_num⟩
  | 2 => ⟨((-5255533767/17592186044416), (-13330024259/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((14518506571/281474976710656), (1103859005/35184372088832)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-20048020271/4503599627370496), (2058487219/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 5 => ⟨((17470320637/72057594037927936), (-2038909373/9007199254740992)), (11/72057594037927936), by norm_num⟩
  | 6 => ⟨((-301320957/72057594037927936), (27933040517/1152921504606846976)), (19/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-1932534099/2305843009213693952), (-14925733411/9223372036854775808)), (17/9223372036854775808), by norm_num⟩
  | 8 => ⟨((18000460187/147573952589676412928), (8565568217/147573952589676412928)), (29/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-23148357121/2361183241434822606848), (4804296593/2361183241434822606848)), (49/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((4608137405/9444732965739290427392), (-10563852361/18889465931478580854784)), (21/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-284885839/75557863725914323419136), (8293520775/151115727451828646838272)), (35/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((-10809067325/4835703278458516698824704), (-16491337389/4835703278458516698824704)), (117/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (5217/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (5217/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (5217/1280)))⁻¹=value ((8806400/74551489), (-6677760/74551489)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/74551489), (-6677760/74551489))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-590184215/17592186044416), (16075634525/70368744177664)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((-5409131727/70368744177664), (-5245288841/70368744177664)), (3/70368744177664), by norm_num⟩
  | 2 => ⟨((4104343099/140737488355328), (-3114015715/562949953421312)), (3/281474976710656), by norm_num⟩
  | 3 => ⟨((-2894610447/1125899906842624), (6569484833/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-2816273409/4503599627370496), (-17803745265/18014398509481984)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((3464161941/18014398509481984), (460731325/144115188075855872)), (23/144115188075855872), by norm_num⟩
  | 6 => ⟨((-9306785411/576460752303423488), (14006548621/576460752303423488)), (17/576460752303423488), by norm_num⟩
  | 7 => ⟨((-3955502473/2305843009213693952), (-8728681047/2305843009213693952)), (25/4611686018427387904), by norm_num⟩
  | 8 => ⟨((322133977/576460752303423488), (2532602563/36893488147419103232)), (35/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-1652188385/36893488147419103232), (17078436423/295147905179352825856)), (47/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-1023474945/295147905179352825856), (-20075316031/2361183241434822606848)), (63/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((1309788335/1180591620717411303424), (662897143/4722366482869645213696)), (81/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-11762922273/151115727451828646838272), (16239636323/151115727451828646838272)), (103/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((51/8), (5217/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3481600/31267563), (-2225920/31267563)), 0, by norm_num⟩
  | 1 => ⟨((-398156595200/108628943995441), (7749763072000/977660495958969)), 0, by norm_num⟩
  | 2 => ⟨((-2747592867/35184372088832), (-5029487919/8796093022208)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((3476252391/140737488355328), (16356052729/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-5425363415/2251799813685248), (-3325336777/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((5779769171/36028797018963968), (-6434966405/144115188075855872)), (7/144115188075855872), by norm_num⟩
  | 6 => ⟨((-8464702793/1152921504606846976), (9449434125/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 7 => ⟨((1079332577/9223372036854775808), (-6619115291/9223372036854775808)), (19/36893488147419103232), by norm_num⟩
  | 8 => ⟨((5616461665/295147905179352825856), (13021862825/295147905179352825856)), (15/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-12419234037/4722366482869645213696), (-8401070019/4722366482869645213696)), (23/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((31694911433/151115727451828646838272), (102658717/18889465931478580854784)), (17/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-3587650383/302231454903657293676544), (4329790879/604462909807314587353088)), (51/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((7851591905/19342813113834066795298816), (-992921815/1208925819614629174706176)), (75/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (5217/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (5217/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (5217/1280)))⁻¹=value ((3481600/31267563), (-2225920/31267563)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/31267563), (-2225920/31267563))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7052403783/562949953421312), (15664473897/562949953421312)), (7/562949953421312), by norm_num⟩
  | 1 => ⟨((-1094484755/70368744177664), (-2212941825/562949953421312)), (5/562949953421312), by norm_num⟩
  | 2 => ⟨((8690453055/2251799813685248), (-13631549749/4503599627370496)), (3/1125899906842624), by norm_num⟩
  | 3 => ⟨((198018377/9007199254740992), (160245953/140737488355328)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((-3273940551/18014398509481984), (-1154166333/9007199254740992)), (13/72057594037927936), by norm_num⟩
  | 5 => ⟨((20936588101/576460752303423488), (-3651506295/288230376151711744)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-3779443771/2305843009213693952), (3373976695/576460752303423488)), (19/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-10654356867/18446744073709551616), (-394060037/576460752303423488)), (29/18446744073709551616), by norm_num⟩
  | 8 => ⟨((9119925413/73786976294838206464), (-540060667/36893488147419103232)), (41/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-8532571179/1180591620717411303424), (17526527057/1180591620717411303424)), (7/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-5276927895/4722366482869645213696), (-8422914887/4722366482869645213696)), (75/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((4896657371/18889465931478580854784), (-288806873/75557863725914323419136)), (49/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-4628157757/302231454903657293676544), (16288704313/604462909807314587353088)), (63/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((59/8), (5217/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12083200/116330689), (-6677760/116330689)), 0, by norm_num⟩
  | 1 => ⟨((-50705621811200/13532829203214721), (80688709632000/13532829203214721)), 0, by norm_num⟩
  | 2 => ⟨((1650872133/70368744177664), (-29357745443/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((6055019929/562949953421312), (12576548485/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-2701732287/2251799813685248), (-3834963301/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((12502304725/144115188075855872), (705271433/72057594037927936)), (9/288230376151711744), by norm_num⟩
  | 6 => ⟨((-11036614091/2305843009213693952), (9138571349/4611686018427387904)), (13/4611686018427387904), by norm_num⟩
  | 7 => ⟨((7072597827/36893488147419103232), (-17730344951/73786976294838206464)), (9/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-3611789135/1180591620717411303424), (21228965701/1180591620717411303424)), (3/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-6747658309/18889465931478580854784), (-19298948663/18889465931478580854784)), (1/590295810358705651712), by norm_num⟩
  | 10 => ⟨((1808697723/37778931862957161709568), (12937862939/302231454903657293676544)), (21/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-17964978733/4835703278458516698824704), (-2052988477/2417851639229258349412352)), (55/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((8406832687/38685626227668133590597632), (-604762821/9671406556917033397649408)), (9/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (5217/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (5217/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (5217/1280)))⁻¹=value ((12083200/116330689), (-6677760/116330689)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/116330689), (-6677760/116330689))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13053766241/4503599627370496), (9777829897/4503599627370496)), (5/2251799813685248), by norm_num⟩
  | 1 => ⟨((-18501133339/9007199254740992), (2048927001/4503599627370496)), (15/9007199254740992), by norm_num⟩
  | 2 => ⟨((361116767/1125899906842624), (-11142153243/18014398509481984)), (5/9007199254740992), by norm_num⟩
  | 3 => ⟨((9906303497/144115188075855872), (22818243091/144115188075855872)), (13/72057594037927936), by norm_num⟩
  | 4 => ⟨((-9899892517/288230376151711744), (-5261496799/576460752303423488)), (3/72057594037927936), by norm_num⟩
  | 5 => ⟨((5869527751/1152921504606846976), (-4510839259/1152921504606846976)), (11/1152921504606846976), by norm_num⟩
  | 6 => ⟨((251302611/18446744073709551616), (1212116219/1152921504606846976)), (35/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-2400198899/18446744073709551616), (-13585535205/147573952589676412928)), (27/73786976294838206464), by norm_num⟩
  | 8 => ⟨((25261708099/1180591620717411303424), (-8935728371/1180591620717411303424)), (79/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-233920719/295147905179352825856), (6998787787/2361183241434822606848)), (55/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((-2477979267/9444732965739290427392), (-11250822461/37778931862957161709568)), (75/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((29546015801/604462909807314587353088), (-2218777797/302231454903657293676544)), (49/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((-1433521957/604462909807314587353088), (6603445159/1208925819614629174706176)), (127/2417851639229258349412352), by norm_num⟩
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
  | 0 => ⟨((67/8), (5217/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13721600/142135489), (-6677760/142135489)), 0, by norm_num⟩
  | 1 => ⟨((-71844913971200/20202497233269121), (91629551616000/20202497233269121)), 0, by norm_num⟩
  | 2 => ⟨((1145492639/17592186044416), (-21284273349/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((2230528141/562949953421312), (2270028317/140737488355328)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-10270902251/18014398509481984), (-771790011/1125899906842624)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((12573606737/288230376151711744), (5676638905/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((-5922158805/2305843009213693952), (85424967/1152921504606846976)), (13/9223372036854775808), by norm_num⟩
  | 7 => ⟨((35230733/288230376151711744), (-2357811687/36893488147419103232)), (1/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-5193142861/1180591620717411303424), (14063546577/2361183241434822606848)), (5/590295810358705651712), by norm_num⟩
  | 9 => ⟨((2735613447/37778931862957161709568), (-14765150401/37778931862957161709568)), (3/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((6873569741/1208925819614629174706176), (1553934625/75557863725914323419136)), (7/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-14653354547/19342813113834066795298816), (-8309239659/9671406556917033397649408)), (65/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((17563055555/309485009821345068724781056), (7327123823/309485009821345068724781056)), (19/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (5217/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (5217/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (5217/1280)))⁻¹=value ((13721600/142135489), (-6677760/142135489)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/142135489), (-6677760/142135489))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3439148969/9007199254740992), (5290451019/72057594037927936)), (3/9007199254740992), by norm_num⟩
  | 1 => ⟨((-7100380161/36028797018963968), (10509468557/72057594037927936)), (19/72057594037927936), by norm_num⟩
  | 2 => ⟨((575835147/72057594037927936), (-12458585157/144115188075855872)), (7/72057594037927936), by norm_num⟩
  | 3 => ⟨((566363525/36028797018963968), (9463422245/576460752303423488)), (19/576460752303423488), by norm_num⟩
  | 4 => ⟨((-22546841031/4611686018427387904), (1426904901/4611686018427387904)), (37/4611686018427387904), by norm_num⟩
  | 5 => ⟨((1236823911/2305843009213693952), (-13773782399/18446744073709551616)), (17/9223372036854775808), by norm_num⟩
  | 6 => ⟨((3125468765/73786976294838206464), (22061916615/147573952589676412928)), (7/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-13247810943/590295810358705651712), (-5309945625/590295810358705651712)), (11/147573952589676412928), by norm_num⟩
  | 8 => ⟨((14189281313/4722366482869645213696), (-4318539565/2361183241434822606848)), (65/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-1485650909/37778931862957161709568), (18218998117/37778931862957161709568)), (23/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-3683470609/75557863725914323419136), (-12278267509/302231454903657293676544)), (127/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((4643101091/604462909807314587353088), (-5293636993/2417851639229258349412352)), (21/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((-5641667653/19342813113834066795298816), (8944708881/9671406556917033397649408)), (219/19342813113834066795298816), by norm_num⟩
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
  | 0 => ⟨((75/8), (5217/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5120000/57072363), (-2225920/57072363)), 0, by norm_num⟩
  | 1 => ⟨((-3543280025600/1085751539467923), (11396710400000/3257254618403769)), 0, by norm_num⟩
  | 2 => ⟨((5499424825/70368744177664), (-15522132889/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((448130801/562949953421312), (12855903667/1125899906842624)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-2327226051/9007199254740992), (-4473424039/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((12263942977/576460752303423488), (9937538177/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 6 => ⟨((-23804601333/18446744073709551616), (-3305507363/9223372036854775808)), (11/18446744073709551616), by norm_num⟩
  | 7 => ⟨((9573470699/147573952589676412928), (-670683385/73786976294838206464)), (3/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-6452215039/2361183241434822606848), (7899466931/4722366482869645213696)), (13/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((3398289331/37778931862957161709568), (-9695691021/75557863725914323419136)), (7/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-3705233005/2417851639229258349412352), (18158162725/2417851639229258349412352)), (15/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-3006404285/38685626227668133590597632), (-7093965631/19342813113834066795298816)), (1/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((13168963029/1237940039285380274899124224), (18488862677/1237940039285380274899124224)), (67/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (5217/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (5217/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (5217/1280)))⁻¹=value ((5120000/57072363), (-2225920/57072363)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/57072363), (-2225920/57072363))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5349127125/144115188075855872), (-4787613867/576460752303423488)), (13/288230376151711744), by norm_num⟩
  | 1 => ⟨((-7778964607/576460752303423488), (1575665513/72057594037927936)), (11/288230376151711744), by norm_num⟩
  | 2 => ⟨((-5708971257/2305843009213693952), (-5367453139/576460752303423488)), (17/1152921504606846976), by norm_num⟩
  | 3 => ⟨((21611531469/9223372036854775808), (11335520671/9223372036854775808)), (47/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-10249051769/18446744073709551616), (7710931619/36893488147419103232)), (49/36893488147419103232), by norm_num⟩
  | 5 => ⟨((1469978139/36893488147419103232), (-1994364797/18446744073709551616)), (23/73786976294838206464), by norm_num⟩
  | 6 => ⟨((5874470023/590295810358705651712), (2565718625/147573952589676412928)), (77/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((-14873625367/4722366482869645213696), (-2443671425/4722366482869645213696)), (31/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((6603536821/18889465931478580854784), (-12069449649/37778931862957161709568)), (23/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((1762002501/302231454903657293676544), (2491309957/37778931862957161709568)), (33/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-18146852945/2417851639229258349412352), (-11091781943/2417851639229258349412352)), (185/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((19919715055/19342813113834066795298816), (-263901231/604462909807314587353088)), (31/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-2148894917/77371252455336267181195264), (20737232095/154742504910672534362390528)), (163/77371252455336267181195264), by norm_num⟩
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
  | 0 => ⟨((83/8), (5217/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((16998400/203575489), (-6677760/203575489)), 0, by norm_num⟩
  | 1 => ⟨((-122176561971200/41442979721589121), (113511235584000/41442979721589121)), 0, by norm_num⟩
  | 2 => ⟨((10999780491/140737488355328), (-22898394757/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-1338812813/2251799813685248), (9091270661/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((-7754251509/72057594037927936), (-24994315975/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 5 => ⟨((11738777149/1152921504606846976), (14661189397/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((-5844403667/9223372036854775808), (-6713107799/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 7 => ⟨((9569700027/295147905179352825856), (2833900425/590295810358705651712)), (7/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-27057346557/18889465931478580854784), (6259028335/18889465931478580854784)), (27/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((16431656393/302231454903657293676544), (-11281355539/302231454903657293676544)), (13/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-4007902607/2417851639229258349412352), (5923928333/2417851639229258349412352)), (25/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((4490813333/154742504910672534362390528), (-20035593199/154742504910672534362390528)), (3/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1128942227/1237940039285380274899124224), (29124260717/4951760157141521099596496896)), (45/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (5217/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (5217/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (5217/1280)))⁻¹=value ((16998400/203575489), (-6677760/203575489)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/203575489), (-6677760/203575489))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((13036377821/4611686018427387904), (-4406473987/2305843009213693952)), (25/4611686018427387904), by norm_num⟩
  | 1 => ⟨((-2288145749/4611686018427387904), (11043378155/4611686018427387904)), (11/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-4895013379/9223372036854775808), (-14837903543/18446744073709551616)), (37/18446744073709551616), by norm_num⟩
  | 3 => ⟨((10009692875/36893488147419103232), (934104467/18446744073709551616)), (51/73786976294838206464), by norm_num⟩
  | 4 => ⟨((-15257448585/295147905179352825856), (11219338803/295147905179352825856)), (7/36893488147419103232), by norm_num⟩
  | 5 => ⟨((3105602199/2361183241434822606848), (-30150728139/2361183241434822606848)), (107/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((7346984147/4722366482869645213696), (7933399895/4722366482869645213696)), (93/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-14071566057/37778931862957161709568), (1170053805/75557863725914323419136)), (151/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((10278092059/302231454903657293676544), (-13569827441/302231454903657293676544)), (115/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((2377391289/1208925819614629174706176), (18731922249/2417851639229258349412352)), (167/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((-9539286167/9671406556917033397649408), (-4139848537/9671406556917033397649408)), (235/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((18548723835/154742504910672534362390528), (-1325788767/19342813113834066795298816)), (5/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-69769461/38685626227668133590597632), (10478206229/618970019642690137449562112)), (53/154742504910672534362390528), by norm_num⟩
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
  | 0 => ⟨((91/8), (5217/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((18636800/239210689), (-6677760/239210689)), 0, by norm_num⟩
  | 1 => ⟨((-151368917811200/57221753731854721), (124452077568000/57221753731854721)), 0, by norm_num⟩
  | 2 => ⟨((5115108349/70368744177664), (-17120149803/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-2552870905/2251799813685248), (25910530425/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((-1302109283/36028797018963968), (-17289671929/72057594037927936)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((5484389711/1152921504606846976), (20389310361/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((-711878451/2305843009213693952), (-2564639767/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 7 => ⟨((9390161539/590295810358705651712), (7700435729/1180591620717411303424)), (15/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-13425045127/18889465931478580854784), (-1210714483/37778931862957161709568)), (13/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((4251353691/151115727451828646838272), (-2620863067/302231454903657293676544)), (23/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-18856918205/19342813113834066795298816), (7064804035/9671406556917033397649408)), (5/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((8597558335/309485009821345068724781056), (-13017901681/309485009821345068724781056)), (35/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-2451413935/4951760157141521099596496896), (20067629081/9903520314283042199192993792)), (15/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (5217/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (5217/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (5217/1280)))⁻¹=value ((18636800/239210689), (-6677760/239210689)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18636800/239210689), (-6677760/239210689))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((12314206559/73786976294838206464), (-8404271639/36893488147419103232)), (43/73786976294838206464), by norm_num⟩
  | 1 => ⟨((458794333/18446744073709551616), (7807408385/36893488147419103232)), (5/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-2498617095/36893488147419103232), (-1028382179/18446744073709551616)), (9/36893488147419103232), by norm_num⟩
  | 3 => ⟨((30657425745/1180591620717411303424), (-709055943/295147905179352825856)), (25/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-9313364829/2361183241434822606848), (11476938193/2361183241434822606848)), (57/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((-1588479181/9444732965739290427392), (-1506401047/1180591620717411303424)), (7/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((7271294675/37778931862957161709568), (10186093963/75557863725914323419136)), (25/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-5737272017/151115727451828646838272), (5463869665/604462909807314587353088)), (41/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((6646441581/2417851639229258349412352), (-12885784689/2417851639229258349412352)), (127/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((6514461421/19342813113834066795298816), (7685582287/9671406556917033397649408)), (187/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-8743425309/77371252455336267181195264), (-4962607211/154742504910672534362390528)), (133/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((3799006503/309485009821345068724781056), (-11159185067/1237940039285380274899124224)), (365/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-201011747/9903520314283042199192993792), (18734709437/9903520314283042199192993792)), (489/9903520314283042199192993792), by norm_num⟩
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
  | 0 => ⟨((99/8), (5217/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2252800/30902521), (-2225920/92707563)), 0, by norm_num⟩
  | 1 => ⟨((-20360625356800/8594692237398969), (5014552576000/2864897412466323)), 0, by norm_num⟩
  | 2 => ⟨((9195289941/140737488355328), (-12981609331/140737488355328)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-5738375187/4503599627370496), (18674271619/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((-480685671/144115188075855872), (-23986196061/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 5 => ⟨((2443814409/1152921504606846976), (13896457583/2305843009213693952)), (3/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-11039436507/73786976294838206464), (-7165615879/36893488147419103232)), (5/36893488147419103232), by norm_num⟩
  | 7 => ⟨((4595487127/590295810358705651712), (12475063197/2361183241434822606848)), (1/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-13116604389/37778931862957161709568), (-3744654169/37778931862957161709568)), (13/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((4184450829/302231454903657293676544), (-83890487/151115727451828646838272)), (21/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-19265207405/38685626227668133590597632), (3606414281/19342813113834066795298816)), (17/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((4925026381/309485009821345068724781056), (-7907013241/618970019642690137449562112)), (27/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-4225779739/9903520314283042199192993792), (13006781375/19807040628566084398385987584)), (43/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (5217/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (5217/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (5217/1280)))⁻¹=value ((2252800/30902521), (-2225920/92707563)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/30902521), (-2225920/92707563))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3953063545/590295810358705651712), (-24336188849/1180591620717411303424)), (17/295147905179352825856), by norm_num⟩
  | 1 => ⟨((1017894229/147573952589676412928), (1155633581/73786976294838206464)), (33/590295810358705651712), by norm_num⟩
  | 2 => ⟨((-15855690713/2361183241434822606848), (-3454494113/1180591620717411303424)), (63/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((19978212801/9444732965739290427392), (-3648429853/4722366482869645213696)), (89/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((-2254142503/9444732965739290427392), (4746955505/9444732965739290427392)), (13/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-6079603529/151115727451828646838272), (-16647744969/151115727451828646838272)), (105/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((757728371/37778931862957161709568), (2641247687/302231454903657293676544)), (3/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-16377040347/4835703278458516698824704), (1804650703/1208925819614629174706176)), (5/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((6884482415/38685626227668133590597632), (-5315285063/9671406556917033397649408)), (251/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((1692239425/38685626227668133590597632), (11143661109/154742504910672534362390528)), (47/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((-14195658129/1237940039285380274899124224), (-4269431093/2475880078570760549798248448)), (537/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((691460253/618970019642690137449562112), (-2541948891/2475880078570760549798248448)), (373/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((2463570589/158456325028528675187087900672), (14992191543/79228162514264337593543950336)), (1005/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-60087401/4294967296), (1556000399/549755813888)), (175/274877906944), by norm_num⟩
  | 1 => ⟨((-13076479887/1099511627776), (-8229191303/1099511627776)), (1605/1099511627776), by norm_num⟩
  | 2 => ⟨((-3743729419/2199023255552), (-13800642511/2199023255552)), (3713/2199023255552), by norm_num⟩
  | 3 => ⟨((7054116031/8796093022208), (-14766283799/8796093022208)), (11551/8796093022208), by norm_num⟩
  | 4 => ⟨((11384359199/35184372088832), (-1491576763/8796093022208)), (13635/17592186044416), by norm_num⟩
  | 5 => ⟨((29863307799/562949953421312), (158896277/140737488355328)), (208777/562949953421312), by norm_num⟩
  | 6 => ⟨((14335800161/2251799813685248), (2324856669/1125899906842624)), (21117/140737488355328), by norm_num⟩
  | 7 => ⟨((6848345511/9007199254740992), (8343551243/18014398509481984)), (951757/18014398509481984), by norm_num⟩
  | 8 => ⟨((4753428201/72057594037927936), (6170669325/72057594037927936)), (297801/18014398509481984), by norm_num⟩
  | 9 => ⟨((3412360715/1152921504606846976), (22163577741/2305843009213693952)), (2691897/576460752303423488), by norm_num⟩
  | 10 => ⟨((843033221/4611686018427387904), (15288429973/18446744073709551616)), (5560401/4611686018427387904), by norm_num⟩
  | 11 => ⟨((636234399/73786976294838206464), (27731473555/295147905179352825856)), (84832527/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-3842698883/1180591620717411303424), (18851638643/2361183241434822606848)), (150603485/2361183241434822606848), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-60087401/4294967296), (1556000399/549755813888)), (701/1099511627776), by norm_num⟩
  | 1 => ⟨((-13076479887/1099511627776), (-8229191303/1099511627776)), (803/549755813888), by norm_num⟩
  | 2 => ⟨((-3743729419/2199023255552), (-13800642511/2199023255552)), (1857/1099511627776), by norm_num⟩
  | 3 => ⟨((7054116031/8796093022208), (-14766283799/8796093022208)), (361/274877906944), by norm_num⟩
  | 4 => ⟨((11384359199/35184372088832), (-1491576763/8796093022208)), (3409/4398046511104), by norm_num⟩
  | 5 => ⟨((29863307799/562949953421312), (158896277/140737488355328)), (6525/17592186044416), by norm_num⟩
  | 6 => ⟨((14335800161/2251799813685248), (2324856669/1125899906842624)), (337963/2251799813685248), by norm_num⟩
  | 7 => ⟨((6848345511/9007199254740992), (8343551243/18014398509481984)), (476239/9007199254740992), by norm_num⟩
  | 8 => ⟨((4753428201/72057594037927936), (6170669325/72057594037927936)), (2388173/144115188075855872), by norm_num⟩
  | 9 => ⟨((3412360715/1152921504606846976), (22163577741/2305843009213693952)), (5429911/1152921504606846976), by norm_num⟩
  | 10 => ⟨((843033221/4611686018427387904), (15288429973/18446744073709551616)), (11489737/9223372036854775808), by norm_num⟩
  | 11 => ⟨((636234399/73786976294838206464), (27731473555/295147905179352825856)), (24159611/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-3842698883/1180591620717411303424), (18851638643/2361183241434822606848)), (245050815/2361183241434822606848), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile018Gamma

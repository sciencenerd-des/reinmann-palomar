/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile023Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨23,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6627/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (6627/640))
  have he : value ((3/4), (6627/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (6627/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (6627/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (6627/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21913600/337011529), (-8482560/337011529)), 0, by norm_num⟩
  | 1 => ⟨((-204126020403200/113576770678917841), (185883426816000/113576770678917841)), 0, by norm_num⟩
  | 2 => ⟨((2662375861/70368744177664), (-5335919223/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((-620986931/2251799813685248), (3311767117/1125899906842624)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-1010682749/36028797018963968), (-446314223/4503599627370496)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((2489400647/1152921504606846976), (3307643937/1152921504606846976)), (3/576460752303423488), by norm_num⟩
  | 6 => ⟨((-3921955711/36893488147419103232), (-1219326733/18446744073709551616)), (5/18446744073709551616), by norm_num⟩
  | 7 => ⟨((5062387905/1180591620717411303424), (478831143/590295810358705651712)), (15/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-706554887/4722366482869645213696), (260598573/9444732965739290427392)), (23/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((1365212847/302231454903657293676544), (-1680411719/604462909807314587353088)), (17/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-270490825/2417851639229258349412352), (711962231/4835703278458516698824704)), (25/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((552203603/309485009821345068724781056), (-3834278769/618970019642690137449562112)), (37/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((197570973/9903520314283042199192993792), (4433844831/19807040628566084398385987584)), (27/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (6627/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (6627/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (6627/1280)))⁻¹=value ((21913600/337011529), (-8482560/337011529)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/337011529), (-8482560/337011529))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2859587607/1073741824), (793127433/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((10956800/337011529), (-4241280/337011529)), 0, by norm_num⟩
  | 2 => ⟨((-51031505100800/113576770678917841), (46470856704000/113576770678917841)), 0, by norm_num⟩
  | 3 => ⟨((1774917241/281474976710656), (-1778639741/140737488355328)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-620986931/18014398509481984), (3311767117/9007199254740992)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((-808546199/288230376151711744), (-2856411027/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((3319200863/18446744073709551616), (1102547979/4611686018427387904)), (9/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-2241117549/295147905179352825856), (-2787032533/590295810358705651712)), (13/590295810358705651712), by norm_num⟩
  | 8 => ⟨((5062387905/18889465931478580854784), (478831143/9444732965739290427392)), (15/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-1256097577/151115727451828646838272), (28955397/18889465931478580854784)), (21/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((2184340555/9671406556917033397649408), (-1344329375/9671406556917033397649408)), (7/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-24590075/4835703278458516698824704), (1035581427/154742504910672534362390528)), (37/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((1472542941/19807040628566084398385987584), (-1278092923/4951760157141521099596496896)), (25/9903520314283042199192993792), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (141/20480)), 0, by norm_num⟩
  | 45 => ⟨((98480861177/4080638361600), (-280167/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-45350455369711/1915179604377600), (5532307150519/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((1657541183/68719476736), (-631783363/68719476736)), (1/137438953472), by norm_num⟩
  | 42 => ⟨((-851841695/34359738368), (1280011477/137438953472)), (1/137438953472), by norm_num⟩
  | 41 => ⟨((3496999495/137438953472), (-656285601/68719476736)), (1/68719476736), by norm_num⟩
  | 40 => ⟨((-3584973297/137438953472), (1346916743/137438953472)), (1/68719476736), by norm_num⟩
  | 39 => ⟨((3676394725/137438953472), (-1381018471/137438953472)), (1/68719476736), by norm_num⟩
  | 38 => ⟨((-3773097615/137438953472), (354048949/34359738368)), (1/68719476736), by norm_num⟩
  | 37 => ⟨((3875331859/137438953472), (-726629291/68719476736)), (1/68719476736), by norm_num⟩
  | 36 => ⟨((-1991647069/68719476736), (93276285/8589934592)), (1/68719476736), by norm_num⟩
  | 35 => ⟨((4097413045/137438953472), (-383445109/34359738368)), (1/68719476736), by norm_num⟩
  | 34 => ⟨((-1054561801/34359738368), (394373273/34359738368)), (1/68719476736), by norm_num⟩
  | 33 => ⟨((2173210727/68719476736), (-811882349/68719476736)), (1/68719476736), by norm_num⟩
  | 32 => ⟨((-4482627815/137438953472), (418207817/34359738368)), (1/68719476736), by norm_num⟩
  | 31 => ⟨((4627644347/137438953472), (-1724955449/137438953472)), (1/68719476736), by norm_num⟩
  | 30 => ⟨((-4782353393/137438953472), (1780432099/137438953472)), (1/68719476736), by norm_num⟩
  | 29 => ⟨((4947759799/137438953472), (-1839595107/137438953472)), (1/68719476736), by norm_num⟩
  | 28 => ⟨((-1281253095/34359738368), (951412201/68719476736)), (1/68719476736), by norm_num⟩
  | 27 => ⟨((1328857613/34359738368), (-985277027/68719476736)), (1/68719476736), by norm_num⟩
  | 26 => ⟨((-5520536671/137438953472), (2043282189/137438953472)), (1/68719476736), by norm_num⟩
  | 25 => ⟨((5742097795/137438953472), (-530395809/34359738368)), (1/68719476736), by norm_num⟩
  | 24 => ⟨((-747771953/17179869184), (2206123133/137438953472)), (1/68719476736), by norm_num⟩
  | 23 => ⟨((390199453/8589934592), (-574419575/34359738368)), (1/68719476736), by norm_num⟩
  | 22 => ⟨((-3264003411/68719476736), (1198579773/68719476736)), (1/34359738368), by norm_num⟩
  | 21 => ⟨((213750961/4294967296), (-1252821223/68719476736)), (1/34359738368), by norm_num⟩
  | 20 => ⟨((-1795838613/34359738368), (82012699/4294967296)), (1/34359738368), by norm_num⟩
  | 19 => ⟨((3781466175/68719476736), (-688746281/34359738368)), (1/34359738368), by norm_num⟩
  | 18 => ⟨((-1996205485/34359738368), (1449616765/68719476736)), (1/34359738368), by norm_num⟩
  | 17 => ⟨((4228254317/68719476736), (-1529707999/68719476736)), (1/34359738368), by norm_num⟩
  | 16 => ⟨((-4493676261/68719476736), (1619163097/68719476736)), (1/34359738368), by norm_num⟩
  | 15 => ⟨((1198651741/17179869184), (-1719725615/68719476736)), (1/34359738368), by norm_num⟩
  | 14 => ⟨((-5138673591/68719476736), (1833600509/68719476736)), (1/34359738368), by norm_num⟩
  | 13 => ⟨((5535853473/68719476736), (-981808779/34359738368)), (1/34359738368), by norm_num⟩
  | 12 => ⟨((-5999453829/68719476736), (2113469529/68719476736)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((1636906415/17179869184), (-572017067/17179869184)), (1/17179869184), by norm_num⟩
  | 10 => ⟨((-3602892631/34359738368), (311761625/8589934592)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((4005324005/34359738368), (-1370431919/34359738368)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((-4508640945/34359738368), (1520895187/34359738368)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((5156095633/34359738368), (-427111467/8589934592)), (1/17179869184), by norm_num⟩
  | 6 => ⟨((-376232455/2147483648), (1948721869/34359738368)), (1/17179869184), by norm_num⟩
  | 5 => ⟨((3614491341/17179869184), (-566899233/8589934592)), (1/8589934592), by norm_num⟩
  | 4 => ⟨((-4521090757/17179869184), (169450665/2147483648)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((6029712343/17179869184), (-1685356559/17179869184)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((-4516914941/8589934592), (556905539/4294967296)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((2242644881/2147483648), (-411083991/2147483648)), (1/2147483648), by norm_num⟩
  | 0 => ⟨((-1879309841/17179869184), (6345019467/17179869184)), (5/17179869184), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (6627/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (6627/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (6627/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((2859587607/1073741824), (793127433/2147483648)), (1/1073741824), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (6627/1280))) (z:=((-21/128), (6627/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((2859587607/1073741824), (793127433/2147483648))) (r:=(1/1073741824)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (6627/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2172752735/67108864), (1244426617/67108864)), (3/134217728), by norm_num⟩
  | 1 => ⟨((3898420315/2147483648), (410076725/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((948657732787200/113576770678917841), (-380575492781280/113576770678917841)), 0, by norm_num⟩
  | 3 => ⟨((-2745730877/35184372088832), (655414623/8796093022208)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((906864463/1125899906842624), (-3971250371/2251799813685248)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-294652991/144115188075855872), (6012930145/144115188075855872)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((-746480851/2305843009213693952), (-2179911013/2305843009213693952)), (33/2305843009213693952), by norm_num⟩
  | 7 => ⟨((2456965597/147573952589676412928), (2868488731/147573952589676412928)), (3/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-718479009/1180591620717411303424), (-756612027/2361183241434822606848)), (121/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((5755997933/302231454903657293676544), (619612191/302231454903657293676544)), (311/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-5111682531/9671406556917033397649408), (1413422849/9671406556917033397649408)), (211/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((3964105023/309485009821345068724781056), (-1495484803/154742504910672534362390528)), (559/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-616622201/2475880078570760549798248448), (4039643393/9903520314283042199192993792)), (187/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-6627/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1275171679/67108864), (1793961919/134217728)), (1/33554432), by norm_num⟩
  | 1 => ⟨((2824678491/2147483648), (410076725/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((948657732787200/113576770678917841), (-380575492781280/113576770678917841)), 0, by norm_num⟩
  | 3 => ⟨((-2745730877/35184372088832), (655414623/8796093022208)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((906864463/1125899906842624), (-3971250371/2251799813685248)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-294652991/144115188075855872), (6012930145/144115188075855872)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((-746480851/2305843009213693952), (-2179911013/2305843009213693952)), (33/2305843009213693952), by norm_num⟩
  | 7 => ⟨((2456965597/147573952589676412928), (2868488731/147573952589676412928)), (3/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-718479009/1180591620717411303424), (-756612027/2361183241434822606848)), (121/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((5755997933/302231454903657293676544), (619612191/302231454903657293676544)), (311/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-5111682531/9671406556917033397649408), (1413422849/9671406556917033397649408)), (211/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((3964105023/309485009821345068724781056), (-1495484803/154742504910672534362390528)), (559/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-616622201/2475880078570760549798248448), (4039643393/9903520314283042199192993792)), (187/2475880078570760549798248448), by norm_num⟩
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
  | 0 => ⟨((3946810947/2147483648), 0), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((3946810947/4294967296), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((167105075/8388608), (1793961919/134217728)), (5/134217728), by norm_num⟩
  | 1 => ⟨((2824678491/2147483648), (410076725/2147483648)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((948657732787200/113576770678917841), (-380575492781280/113576770678917841)), 0, by norm_num⟩
  | 3 => ⟨((-2745730877/35184372088832), (655414623/8796093022208)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((906864463/1125899906842624), (-3971250371/2251799813685248)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-294652991/144115188075855872), (6012930145/144115188075855872)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((-746480851/2305843009213693952), (-2179911013/2305843009213693952)), (33/2305843009213693952), by norm_num⟩
  | 7 => ⟨((2456965597/147573952589676412928), (2868488731/147573952589676412928)), (3/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-718479009/1180591620717411303424), (-756612027/2361183241434822606848)), (121/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((5755997933/302231454903657293676544), (619612191/302231454903657293676544)), (311/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-5111682531/9671406556917033397649408), (1413422849/9671406556917033397649408)), (211/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((3964105023/309485009821345068724781056), (-1495484803/154742504910672534362390528)), (559/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-616622201/2475880078570760549798248448), (4039643393/9903520314283042199192993792)), (187/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((408252040806400/113576770678917841), (-371766853632000/113576770678917841)), 0, by norm_num⟩
  | 1 => ⟨((-2662375861/17592186044416), (5335919223/17592186044416)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((465740199/281474976710656), (-4967650675/281474976710656)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((1010682749/4503599627370496), (446314223/562949953421312)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((-3111750809/144115188075855872), (-4134554921/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((2941466783/2305843009213693952), (1828990099/2305843009213693952)), (5/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-4429589417/73786976294838206464), (-209488625/18446744073709551616)), (5/36893488147419103232), by norm_num⟩
  | 7 => ⟨((706554887/295147905179352825856), (-1042394291/2361183241434822606848)), (1/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-1535864453/18889465931478580854784), (1890463183/37778931862957161709568)), (13/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((1352454125/604462909807314587353088), (-3559811155/1208925819614629174706176)), (21/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-1518559909/38685626227668133590597632), (5272133307/38685626227668133590597632)), (1/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-592712919/1237940039285380274899124224), (-6650767247/1237940039285380274899124224)), (25/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((1784809521/19807040628566084398385987584), (1809323753/9903520314283042199192993792)), (19/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2662375861/17592186044416), (-5335919223/17592186044416)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((-465740199/140737488355328), (4967650675/140737488355328)), (1/70368744177664), by norm_num⟩
  | 2 => ⟨((-1516024123/2251799813685248), (-5355770675/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 3 => ⟨((388968851/4503599627370496), (4134554921/36028797018963968)), (5/36028797018963968), by norm_num⟩
  | 4 => ⟨((-3676833479/576460752303423488), (-285779703/72057594037927936)), (3/288230376151711744), by norm_num⟩
  | 5 => ⟨((6644384125/18446744073709551616), (628465875/9223372036854775808)), (11/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-4945884209/295147905179352825856), (912095005/295147905179352825856)), (11/295147905179352825856), by norm_num⟩
  | 7 => ⟨((1535864453/2361183241434822606848), (-1890463183/4722366482869645213696)), (11/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-1521510891/75557863725914323419136), (4004787549/151115727451828646838272)), (9/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((949099943/2417851639229258349412352), (-6590166633/4835703278458516698824704)), (31/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((407490131/77371252455336267181195264), (2286201241/38685626227668133590597632)), (25/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-2677214281/2475880078570760549798248448), (-2713985629/1237940039285380274899124224)), (41/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((2899894713/39614081257132168796771975168), (2665219687/39614081257132168796771975168)), (33/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((620986931/281474976710656), (-3311767117/140737488355328)), (3/281474976710656), by norm_num⟩
  | 1 => ⟨((1010682749/1125899906842624), (3570513783/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 2 => ⟨((-388968851/2251799813685248), (-4134554921/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((2451222319/144115188075855872), (95259901/9007199254740992)), (7/288230376151711744), by norm_num⟩
  | 4 => ⟨((-2768493385/2305843009213693952), (-1047443125/4611686018427387904)), (9/4611686018427387904), by norm_num⟩
  | 5 => ⟨((309117763/4611686018427387904), (-912095005/73786976294838206464)), (5/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-3583683723/1180591620717411303424), (551385095/295147905179352825856)), (11/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((507170297/4722366482869645213696), (-1334929183/9444732965739290427392)), (11/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-1423649915/604462909807314587353088), (4942624975/604462909807314587353088)), (5/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-679150219/19342813113834066795298816), (-7620670803/19342813113834066795298816)), (9/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((2454113091/309485009821345068724781056), (19436095/1208925819614629174706176)), (31/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-362486839/618970019642690137449562112), (-2665219687/4951760157141521099596496896)), (27/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((5112882573/158456325028528675187087900672), (250777973/19807040628566084398385987584)), (11/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1010682749/2251799813685248), (-446314223/281474976710656)), (3/2251799813685248), by norm_num⟩
  | 1 => ⟨((388968851/2251799813685248), (4134554921/18014398509481984)), (3/9007199254740992), by norm_num⟩
  | 2 => ⟨((-1838416739/72057594037927936), (-285779703/18014398509481984)), (5/144115188075855872), by norm_num⟩
  | 3 => ⟨((2768493385/1152921504606846976), (1047443125/2305843009213693952)), (9/2305843009213693952), by norm_num⟩
  | 4 => ⟨((-1545588815/9223372036854775808), (285029689/9223372036854775808)), (3/9223372036854775808), by norm_num⟩
  | 5 => ⟨((335970349/36893488147419103232), (-1654155285/295147905179352825856)), (1/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-1775096039/4722366482869645213696), (1168063035/2361183241434822606848)), (9/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((1423649915/151115727451828646838272), (-2471312487/75557863725914323419136)), (19/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((191010999/1208925819614629174706176), (4286627327/2417851639229258349412352)), (19/2417851639229258349412352), by norm_num⟩
  | 9 => ⟨((-766910341/19342813113834066795298816), (-97180475/1208925819614629174706176)), (9/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((3987355229/1237940039285380274899124224), (3664677069/1237940039285380274899124224)), (33/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-1917330965/9903520314283042199192993792), (-752333919/9903520314283042199192993792)), (15/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((1531812013/158456325028528675187087900672), (14082659/316912650057057350374175801344)), (51/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2489400647/36028797018963968), (-3307643937/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 1 => ⟨((2941466783/144115188075855872), (1828990099/144115188075855872)), (3/72057594037927936), by norm_num⟩
  | 2 => ⟨((-1661096031/576460752303423488), (-1256931751/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((309117763/1152921504606846976), (-912095005/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 4 => ⟨((-335970349/18446744073709551616), (1654155285/147573952589676412928)), (1/18446744073709551616), by norm_num⟩
  | 5 => ⟨((2130115247/2361183241434822606848), (-700837821/590295810358705651712)), (11/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((-249138735/9444732965739290427392), (1729918741/18889465931478580854784)), (13/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-152808799/302231454903657293676544), (-3429301861/604462909807314587353088)), (15/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((2760877227/19342813113834066795298816), (174924855/604462909807314587353088)), (1/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-3987355229/309485009821345068724781056), (-3664677069/309485009821345068724781056)), (1/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((2109064061/2475880078570760549798248448), (1655134621/4951760157141521099596496896)), (31/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-7352697663/158456325028528675187087900672), (-16899191/79228162514264337593543950336)), (29/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((2714034875/1267650600228229401496703205376), (-129532405/158456325028528675187087900672)), (53/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3921955711/576460752303423488), (-1219326733/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 1 => ⟨((553698677/288230376151711744), (209488625/576460752303423488)), (11/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-309117763/1152921504606846976), (912095005/18446744073709551616)), (13/18446744073709551616), by norm_num⟩
  | 3 => ⟨((3583683723/147573952589676412928), (-551385095/36893488147419103232)), (11/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-1775096039/1180591620717411303424), (1168063035/590295810358705651712)), (19/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((249138735/4722366482869645213696), (-1729918741/9444732965739290427392)), (7/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((356553865/302231454903657293676544), (4000852171/302231454903657293676544)), (9/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-920292409/2417851639229258349412352), (-58308285/75557863725914323419136)), (11/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((1495258211/38685626227668133590597632), (1374253901/38685626227668133590597632)), (25/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-219694173/77371252455336267181195264), (-1379278851/1237940039285380274899124224)), (27/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((6739972857/39614081257132168796771975168), (15490925/19807040628566084398385987584)), (53/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((-2714034875/316912650057057350374175801344), (129532405/39614081257132168796771975168)), (13/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((1804714881/5070602400912917605986812821504), (-3256634047/10141204801825835211973625643008)), (25/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5062387905/9223372036854775808), (-478831143/4611686018427387904)), (15/9223372036854775808), by norm_num⟩
  | 1 => ⟨((5652439095/36893488147419103232), (-1042394291/36893488147419103232)), (19/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-3071728905/147573952589676412928), (1890463183/147573952589676412928)), (13/147573952589676412928), by norm_num⟩
  | 3 => ⟨((507170297/295147905179352825856), (-1334929183/590295810358705651712)), (13/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((-711824957/9444732965739290427392), (2471312487/9444732965739290427392)), (11/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-611235197/302231454903657293676544), (-3429301861/151115727451828646838272)), (33/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((920292409/1208925819614629174706176), (3731730239/2417851639229258349412352)), (3/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-3417733053/38685626227668133590597632), (-1570575887/19342813113834066795298816)), (31/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((1129855747/154742504910672534362390528), (1773358523/618970019642690137449562112)), (9/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-2407133163/4951760157141521099596496896), (-22129893/9903520314283042199192993792)), (41/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((2132455973/79228162514264337593543950336), (-1628407377/158456325028528675187087900672)), (43/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((-3093796939/2535301200456458802993406410752), (697850153/633825300114114700748351602688)), (11/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((103636675/2535301200456458802993406410752), (-3285438815/40564819207303340847894502572032)), (11/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-706554887/18446744073709551616), (260598573/36893488147419103232)), (23/147573952589676412928), by norm_num⟩
  | 1 => ⟨((1535864453/147573952589676412928), (-1890463183/295147905179352825856)), (1/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-3043021781/2361183241434822606848), (1001196887/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 3 => ⟨((1423649915/18889465931478580854784), (-4942624975/18889465931478580854784)), (27/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((191010999/75557863725914323419136), (2143313663/75557863725914323419136)), (3/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-2760877227/2417851639229258349412352), (-5597595359/2417851639229258349412352)), (39/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((1495258211/9671406556917033397649408), (2748507801/19342813113834066795298816)), (15/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-1129855747/77371252455336267181195264), (-1773358523/309485009821345068724781056)), (5/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((5416049617/4951760157141521099596496896), (12448065/2475880078570760549798248448)), (25/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((-5331139933/79228162514264337593543950336), (2035509221/79228162514264337593543950336)), (59/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((4253970791/1267650600228229401496703205376), (-3838175841/1267650600228229401496703205376)), (65/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((-310910025/2535301200456458802993406410752), (2464079111/10141204801825835211973625643008)), (35/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((251264709/162259276829213363391578010288128), (-5107330381/324518553658426726783156020576256)), (73/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1365212847/590295810358705651712), (1680411719/1180591620717411303424)), (17/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((2704908251/4722366482869645213696), (-1779905577/2361183241434822606848)), (27/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((-949099943/18889465931478580854784), (823770829/4722366482869645213696)), (43/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-339575109/151115727451828646838272), (-7620670803/302231454903657293676544)), (13/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((1533820681/1208925819614629174706176), (97180475/37778931862957161709568)), (13/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((-3987355229/19342813113834066795298816), (-3664677069/19342813113834066795298816)), (11/4835703278458516698824704), by norm_num⟩
  | 6 => ⟨((219694173/9671406556917033397649408), (689639425/77371252455336267181195264)), (9/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((-2407133163/1237940039285380274899124224), (-22129893/2475880078570760549798248448)), (25/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((5331139933/39614081257132168796771975168), (-2035509221/39614081257132168796771975168)), (65/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((-1181658553/158456325028528675187087900672), (266539989/39614081257132168796771975168)), (41/316912650057057350374175801344), by norm_num⟩
  | 10 => ⟨((1520004567/5070602400912917605986812821504), (-3011652247/5070602400912917605986812821504)), (3/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-670039225/162259276829213363391578010288128), (425610865/10141204801825835211973625643008)), (105/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-223708523/324518553658426726783156020576256), (-6435222907/2596148429267413814265248164610048)), (113/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-270490825/2361183241434822606848), (711962231/4722366482869645213696)), (25/18889465931478580854784), by norm_num⟩
  | 1 => ⟨((759279955/37778931862957161709568), (-2636066653/37778931862957161709568)), (11/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((407490131/302231454903657293676544), (4572402481/302231454903657293676544)), (19/151115727451828646838272), by norm_num⟩
  | 3 => ⟨((-1227056545/1208925819614629174706176), (-19436095/9444732965739290427392)), (49/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((996838807/4835703278458516698824704), (1832338535/9671406556917033397649408)), (53/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((-2109064061/77371252455336267181195264), (-1655134621/154742504910672534362390528)), (3/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((842496607/309485009821345068724781056), (30981849/2475880078570760549798248448)), (5/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((-2132455973/9903520314283042199192993792), (1628407377/19807040628566084398385987584)), (15/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((4253970791/316912650057057350374175801344), (-3838175841/316912650057057350374175801344)), (41/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((-760002283/1267650600228229401496703205376), (3011652247/2535301200456458802993406410752)), (27/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((737043147/81129638414606681695789005144064), (-7490751225/81129638414606681695789005144064)), (131/81129638414606681695789005144064), by norm_num⟩
  | 11 => ⟨((536900455/324518553658426726783156020576256), (241320859/40564819207303340847894502572032)), (19/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-1224714907/5192296858534827628530496329220096), (-1642931643/5192296858534827628530496329220096)), (85/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/1011034587), (-706880/337011529)), 0, by norm_num⟩
  | 1 => ⟨((-51031505100800/340730312036753523), (15490285568000/113576770678917841)), 0, by norm_num⟩
  | 2 => ⟨((1774917241/562949953421312), (-1778639741/281474976710656)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-413991287/18014398509481984), (4415689489/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((-1347576999/576460752303423488), (-4760685045/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 5 => ⟨((3319200863/18446744073709551616), (1102547979/4611686018427387904)), (9/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-5229274281/590295810358705651712), (-3251537955/590295810358705651712)), (7/295147905179352825856), by norm_num⟩
  | 7 => ⟨((1687462635/4722366482869645213696), (159610381/2361183241434822606848)), (5/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-3768292731/302231454903657293676544), (86866191/37778931862957161709568)), (1/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((455070949/1208925819614629174706176), (-2240548959/9671406556917033397649408)), (23/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-2885235467/309485009821345068724781056), (3797131899/309485009821345068724781056)), (17/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((1472542941/9903520314283042199192993792), (-1278092923/2475880078570760549798248448)), (25/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((65856991/39614081257132168796771975168), (1477948277/79228162514264337593543950336)), (9/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2674408473/134217728), (896840199/67108864)), (3/67108864), by norm_num⟩
  | 1 => ⟨((5648713721/4294967296), (102592403/536870912)), (5/4294967296), by norm_num⟩
  | 2 => ⟨((2296803147/274877906944), (-230700943/68719476736)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-1373269727/17592186044416), (1315141443/17592186044416)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((1808464953/2251799813685248), (-3989846797/2251799813685248)), (13/2251799813685248), by norm_num⟩
  | 5 => ⟨((-134360867/72057594037927936), (6047384769/144115188075855872)), (41/144115188075855872), by norm_num⟩
  | 6 => ⟨((-1533815407/4611686018427387904), (-2192612333/2305843009213693952)), (67/4611686018427387904), by norm_num⟩
  | 7 => ⟨((627424701/36893488147419103232), (719616095/36893488147419103232)), (97/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-1466397805/2361183241434822606848), (-375591445/1180591620717411303424)), (61/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((2934882835/151115727451828646838272), (137398759/75557863725914323419136)), (39/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-5201846139/9671406556917033397649408), (1532083221/9671406556917033397649408)), (53/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((2005060995/154742504910672534362390528), (-3150731221/309485009821345068724781056)), (281/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-612506139/2475880078570760549798248448), (264024183/618970019642690137449562112)), (751/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1893245057/4503599627370496), (3794431447/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((662386061/72057594037927936), (-3532551591/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 2 => ⟨((1078061599/576460752303423488), (952137009/144115188075855872)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((-2212800575/9223372036854775808), (-367515993/1152921504606846976)), (5/9223372036854775808), by norm_num⟩
  | 4 => ⟨((5229274281/295147905179352825856), (1625768977/147573952589676412928)), (9/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-2362447689/2361183241434822606848), (-893818133/4722366482869645213696)), (9/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((7034146431/151115727451828646838272), (-1297201785/151115727451828646838272)), (17/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-4368681111/2417851639229258349412352), (2688658749/2417851639229258349412352)), (17/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((2163926601/38685626227668133590597632), (-711962231/9671406556917033397649408)), (7/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-674915515/618970019642690137449562112), (4686340717/1237940039285380274899124224)), (23/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-36221345/2475880078570760549798248448), (-6502972419/39614081257132168796771975168)), (37/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((951898411/316912650057057350374175801344), (241243167/39614081257132168796771975168)), (15/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-4124294703/20282409603651670423947251286016), (-1895267333/10141204801825835211973625643008)), (3/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2674408417/134217728), (1793680511/134217728)), (7/134217728), by norm_num⟩
  | 1 => ⟨((176522305/134217728), (820738803/4294967296)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((2296803661/274877906944), (-230700489/68719476736)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((-2746547895/35184372088832), (1315135835/17592186044416)), (5/35184372088832), by norm_num⟩
  | 4 => ⟨((1808504849/2251799813685248), (-1994910995/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((-134432963/72057594037927936), (1511839373/36028797018963968)), (21/72057594037927936), by norm_num⟩
  | 6 => ⟨((-766800371/2305843009213693952), (-4385264253/4611686018427387904)), (17/1152921504606846976), by norm_num⟩
  | 7 => ⟨((2509432161/147573952589676412928), (2878628483/147573952589676412928)), (49/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-2932531459/4722366482869645213696), (-751356709/2361183241434822606848)), (123/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((5869436121/302231454903657293676544), (275369581/151115727451828646838272)), (313/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-5201987629/9671406556917033397649408), (1530495581/9671406556917033397649408)), (425/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((2005525789/154742504910672534362390528), (-3148846509/309485009821345068724781056)), (563/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-613009593/2475880078570760549798248448), (4222536081/9903520314283042199192993792)), (47/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-410690133/1152921504606846976), (-2901750885/2305843009213693952)), (3/2305843009213693952), by norm_num⟩
  | 1 => ⟨((1264457471/9223372036854775808), (1680073111/9223372036854775808)), (3/9223372036854775808), by norm_num⟩
  | 2 => ⟨((-2988156731/147573952589676412928), (-232252711/18446744073709551616)), (5/147573952589676412928), by norm_num⟩
  | 3 => ⟨((4499900359/2361183241434822606848), (851255365/2361183241434822606848)), (1/295147905179352825856), by norm_num⟩
  | 4 => ⟨((-5024390307/37778931862957161709568), (926572703/37778931862957161709568)), (11/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((2184340555/302231454903657293676544), (-2688658749/604462909807314587353088)), (7/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-2885235467/9671406556917033397649408), (1898565949/4835703278458516698824704)), (1/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((578499013/77371252455336267181195264), (-4016863471/154742504910672534362390528)), (1/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((620937343/4951760157141521099596496896), (6967470449/4951760157141521099596496896)), (1/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-2493067267/79228162514264337593543950336), (-2527309369/39614081257132168796771975168)), (15/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((3240517265/1267650600228229401496703205376), (2978277237/1267650600228229401496703205376)), (7/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((-194776479/1267650600228229401496703205376), (-305710291/5070602400912917605986812821504)), (13/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((2489802383/324518553658426726783156020576256), (22889909/649037107316853453566312041152512)), (21/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2674408417/134217728), (1793680511/134217728)), (1/16777216), by norm_num⟩
  | 1 => ⟨((5648713761/4294967296), (205184701/1073741824)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((4593607311/549755813888), (-1845603919/549755813888)), (3/549755813888), by norm_num⟩
  | 3 => ⟨((-686636957/8796093022208), (2630271683/35184372088832)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((904252275/1125899906842624), (-3989821935/2251799813685248)), (15/2251799813685248), by norm_num⟩
  | 5 => ⟨((-67216221/36028797018963968), (6047356851/144115188075855872)), (43/144115188075855872), by norm_num⟩
  | 6 => ⟨((-766801059/2305843009213693952), (-2192631221/2305843009213693952)), (69/4611686018427387904), by norm_num⟩
  | 7 => ⟨((156839579/9223372036854775808), (719656163/36893488147419103232)), (99/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2932530867/4722366482869645213696), (-1502706773/4722366482869645213696)), (31/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((5869426611/302231454903657293676544), (68839985/37778931862957161709568)), (157/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-2600981453/4835703278458516698824704), (1530518303/9671406556917033397649408)), (213/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((4011004025/309485009821345068724781056), (-196804073/19342813113834066795298816)), (141/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-2451962389/9903520314283042199192993792), (2111268215/4951760157141521099596496896)), (753/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1195262693/295147905179352825856), (2972834701/1180591620717411303424)), (7/590295810358705651712), by norm_num⟩
  | 1 => ⟨((-5399880431/4722366482869645213696), (-510753219/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((376829273/2361183241434822606848), (-277971811/9444732965739290427392)), (17/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-2184340555/151115727451828646838272), (2688658749/302231454903657293676544)), (7/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((270490825/302231454903657293676544), (-2847848923/2417851639229258349412352)), (13/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((-1214847927/38685626227668133590597632), (4217706645/38685626227668133590597632)), (9/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((-108664035/154742504910672534362390528), (-4877229313/618970019642690137449562112)), (23/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((560940135/2475880078570760549798248448), (555317/1208925819614629174706176)), (27/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((-911395481/39614081257132168796771975168), (-837640473/39614081257132168796771975168)), (31/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((535635317/316912650057057350374175801344), (1681406599/2535301200456458802993406410752)), (17/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((-1027043483/10141204801825835211973625643008), (-18884175/40564819207303340847894502572032)), (33/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((413567219/81129638414606681695789005144064), (-1263249359/649037107316853453566312041152512)), (33/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((-4400066757/20769187434139310514121985316880384), (3969991981/20769187434139310514121985316880384)), (31/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2674408417/134217728), (1793680511/134217728)), (9/134217728), by norm_num⟩
  | 1 => ⟨((5648713761/4294967296), (205184701/1073741824)), (1/536870912), by norm_num⟩
  | 2 => ⟨((4593607311/549755813888), (-1845603919/549755813888)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-2746547829/35184372088832), (2630271683/35184372088832)), (7/35184372088832), by norm_num⟩
  | 4 => ⟨((226063069/281474976710656), (-1994910969/1125899906842624)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-268864889/144115188075855872), (6047356867/144115188075855872)), (11/36028797018963968), by norm_num⟩
  | 6 => ⟨((-1533602121/4611686018427387904), (-2192631239/2305843009213693952)), (35/2305843009213693952), by norm_num⟩
  | 7 => ⟨((2509433297/147573952589676412928), (179914045/9223372036854775808)), (25/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-91641593/147573952589676412928), (-1502706873/4722366482869645213696)), (125/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((2934713561/151115727451828646838272), (34420005/18889465931478580854784)), (315/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-5201963885/9671406556917033397649408), (765259149/4835703278458516698824704)), (427/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((4011005603/309485009821345068724781056), (-1574432885/154742504910672534362390528)), (565/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-2451964487/9903520314283042199192993792), (4222538323/9903520314283042199192993792)), (377/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-609017007/18889465931478580854784), (898494743/151115727451828646838272)), (21/151115727451828646838272), by norm_num⟩
  | 1 => ⟨((5295371043/604462909807314587353088), (-1629490151/302231454903657293676544)), (7/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((-2622941333/2417851639229258349412352), (3451938089/2417851639229258349412352)), (11/1208925819614629174706176), by norm_num⟩
  | 3 => ⟨((1227119119/19342813113834066795298816), (-4260309743/19342813113834066795298816)), (3/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((658569909/309485009821345068724781056), (923717673/38685626227668133590597632)), (21/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((-2379746027/2475880078570760549798248448), (-1206215835/618970019642690137449562112)), (35/2475880078570760549798248448), by norm_num⟩
  | 6 => ⟨((2577684189/19807040628566084398385987584), (2369084165/19807040628566084398385987584)), (27/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((-3895529579/316912650057057350374175801344), (-764275727/158456325028528675187087900672)), (35/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((1167094867/1267650600228229401496703205376), (21459291/5070602400912917605986812821504)), (11/1267650600228229401496703205376), by norm_num⟩
  | 9 => ⟨((-4595191323/81129638414606681695789005144064), (1754512999/81129638414606681695789005144064)), (13/20282409603651670423947251286016), by norm_num⟩
  | 10 => ⟨((1833361149/649037107316853453566312041152512), (-3308326651/1298074214633706907132624082305024)), (57/1298074214633706907132624082305024), by norm_num⟩
  | 11 => ⟨((-2143918287/20769187434139310514121985316880384), (1061960021/5192296858534827628530496329220096)), (61/20769187434139310514121985316880384), by norm_num⟩
  | 12 => ⟨((216578335/166153499473114484112975882535043072), (-4402278039/332306998946228968225951765070086144)), (1/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2674408417/134217728), (1793680511/134217728)), (5/67108864), by norm_num⟩
  | 1 => ⟨((5648713761/4294967296), (205184701/1073741824)), (9/4294967296), by norm_num⟩
  | 2 => ⟨((4593607311/549755813888), (-1845603919/549755813888)), (5/549755813888), by norm_num⟩
  | 3 => ⟨((-2746547829/35184372088832), (2630271683/35184372088832)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((226063069/281474976710656), (-1994910969/1125899906842624)), (17/2251799813685248), by norm_num⟩
  | 5 => ⟨((-268864889/144115188075855872), (6047356867/144115188075855872)), (45/144115188075855872), by norm_num⟩
  | 6 => ⟨((-191700265/576460752303423488), (-4385262477/4611686018427387904)), (71/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2509433295/147573952589676412928), (2878624719/147573952589676412928)), (101/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-733132743/1180591620717411303424), (-1502706873/4722366482869645213696)), (63/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((5869427105/302231454903657293676544), (550720087/302231454903657293676544)), (79/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-2600981929/4835703278458516698824704), (1530518273/9671406556917033397649408)), (107/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((4011005571/309485009821345068724781056), (-3148865707/309485009821345068724781056)), (283/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-1225982237/4951760157141521099596496896), (263908637/618970019642690137449562112)), (755/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1062243201/4835703278458516698824704), (-174746463/604462909807314587353088)), (13/4835703278458516698824704), by norm_num⟩
  | 1 => ⟨((-745441153/19342813113834066795298816), (2588021127/19342813113834066795298816)), (11/9671406556917033397649408), by norm_num⟩
  | 2 => ⟨((-400063127/154742504910672534362390528), (-1122266219/38685626227668133590597632)), (19/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((2409383889/1237940039285380274899124224), (2442476607/618970019642690137449562112)), (49/1237940039285380274899124224), by norm_num⟩
  | 4 => ⟨((-3914680821/9903520314283042199192993792), (-1798941933/4951760157141521099596496896)), (53/9903520314283042199192993792), by norm_num⟩
  | 5 => ⟨((2070623799/39614081257132168796771975168), (50780243/2475880078570760549798248448)), (3/4951760157141521099596496896), by norm_num⟩
  | 6 => ⟨((-103392635/19807040628566084398385987584), (-30417167/1267650600228229401496703205376)), (79/1267650600228229401496703205376), by norm_num⟩
  | 7 => ⟨((2093589365/5070602400912917605986812821504), (-1598727669/10141204801825835211973625643008)), (15/2535301200456458802993406410752), by norm_num⟩
  | 8 => ⟨((-4176436991/162259276829213363391578010288128), (3768220411/162259276829213363391578010288128)), (41/81129638414606681695789005144064), by norm_num⟩
  | 9 => ⟨((1492300631/1298074214633706907132624082305024), (-23099697/10141204801825835211973625643008)), (27/649037107316853453566312041152512), by norm_num⟩
  | 10 => ⟨((-361804819/20769187434139310514121985316880384), (3677111579/20769187434139310514121985316880384)), (65/20769187434139310514121985316880384), by norm_num⟩
  | 11 => ⟨((-263557395/83076749736557242056487941267521536), (-1895379939/166153499473114484112975882535043072)), (19/83076749736557242056487941267521536), by norm_num⟩
  | 12 => ⟨((601196493/1329227995784915872903807060280344576), (3225974425/5316911983139663491615228241121378304)), (85/5316911983139663491615228241121378304), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2674408417/134217728), (1793680511/134217728)), (11/134217728), by norm_num⟩
  | 1 => ⟨((5648713761/4294967296), (205184701/1073741824)), (5/2147483648), by norm_num⟩
  | 2 => ⟨((4593607311/549755813888), (-1845603919/549755813888)), (3/274877906944), by norm_num⟩
  | 3 => ⟨((-2746547829/35184372088832), (2630271683/35184372088832)), (9/35184372088832), by norm_num⟩
  | 4 => ⟨((226063069/281474976710656), (-1994910969/1125899906842624)), (9/1125899906842624), by norm_num⟩
  | 5 => ⟨((-268864889/144115188075855872), (6047356867/144115188075855872)), (23/72057594037927936), by norm_num⟩
  | 6 => ⟨((-191700265/576460752303423488), (-4385262477/4611686018427387904)), (9/576460752303423488), by norm_num⟩
  | 7 => ⟨((2509433295/147573952589676412928), (2878624719/147573952589676412928)), (51/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-733132743/1180591620717411303424), (-1502706873/4722366482869645213696)), (127/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((5869427105/302231454903657293676544), (275360043/151115727451828646838272)), (317/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-2600981929/4835703278458516698824704), (1530518275/9671406556917033397649408)), (429/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((2005502785/154742504910672534362390528), (-3148865711/309485009821345068724781056)), (567/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-1225982235/4951760157141521099596496896), (2111269099/4951760157141521099596496896)), (189/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((82484276768277/262144), (21130143345385/65536)), (72026437/1048576), by norm_num⟩
  | 1 => ⟨((2817733637/8), (968346421/2)), 105, by norm_num⟩
  | 2 => ⟨(189067056, (2829452737/8)), 81, by norm_num⟩
  | 3 => ⟨(63354863, (338007083/2)), (1343/32), by norm_num⟩
  | 4 => ⟨((451000155/32), (3823752991/64)), (1053/64), by norm_num⟩
  | 5 => ⟨((470698041/256), (4281783023/256)), (1331/256), by norm_num⟩
  | 6 => ⟨((-32600773/1024), (7928224183/2048)), (707/512), by norm_num⟩
  | 7 => ⟨((-765339443/8192), (3125692895/4096)), (1299/4096), by norm_num⟩
  | 8 => ⟨((-1011647349/32768), (4289689169/32768)), (2109/32768), by norm_num⟩
  | 9 => ⟨((-228669277/32768), (5207411169/262144)), (3073/262144), by norm_num⟩
  | 10 => ⟨((-2670957609/2097152), (2831202561/1048576)), (1017/524288), by norm_num⟩
  | 11 => ⟨((-835809181/4194304), (2785003011/8388608)), (2471/8388608), by norm_num⟩
  | 12 => ⟨((-1850027829/67108864), (2497710145/67108864)), (1389/33554432), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((804965735339877/5070602400912917605986812821504), (1038950805319/10141204801825835211973625643008)), (53379/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1813299395732865/633825300114114700748351602688), (637093862079/316912650057057350374175801344)), (16387/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1928629821146291/39614081257132168796771975168), (5613936923/154742504910672534362390528)), (36971/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((965436947686779/1237940039285380274899124224), (1530169793661/2475880078570760549798248448)), (39367/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((906291681489231/77371252455336267181195264), (1533727410327/154742504910672534362390528)), (157849/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1588405070288905/9671406556917033397649408), (1441660488677/9671406556917033397649408)), (148389/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1292829992001385/604462909807314587353088), (1265257154325/604462909807314587353088)), (16281/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((1943195873681887/75557863725914323419136), (2063203961311/75557863725914323419136)), (53105/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1339168419350269/4722366482869645213696), (776848606115/2361183241434822606848)), (79995/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((839406014593681/295147905179352825856), (536653783501/147573952589676412928)), (221087/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1895366401621671/73786976294838206464), (337348124757/9223372036854775808)), (278023/73786976294838206464), by norm_num⟩
  | 7 => ⟨((118987084596109/576460752303423488), (1528810673239/4611686018427387904)), (315079/9223372036854775808), by norm_num⟩
  | 6 => ⟨((837683242944113/576460752303423488), (1542356955645/576460752303423488)), (158993/576460752303423488), by norm_num⟩
  | 5 => ⟨((633078306874757/72057594037927936), (2729926258265/144115188075855872)), (281543/144115188075855872), by norm_num⟩
  | 4 => ⟨((99983958779361/2251799813685248), (2078653976425/18014398509481984)), (53627/4503599627370496), by norm_num⟩
  | 3 => ⟨((812851896362301/4503599627370496), (5307727856249/9007199254740992)), (274103/4503599627370496), by norm_num⟩
  | 2 => ⟨((156552610635035/281474976710656), (5478153478779/2251799813685248)), (566535/2251799813685248), by norm_num⟩
  | 1 => ⟨((1320831456094645/1125899906842624), (4328422797589/562949953421312)), (897137/1125899906842624), by norm_num⟩
  | 0 => ⟨((1537022483337945/1125899906842624), (19155908613077/1125899906842624)), (1992999/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1537022483337945/1125899906842624), (19155908613077/1125899906842624)), (7602687839988326671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2097940634949991/1125899906842624), (817209139999/17592186044416)), (5509305/1125899906842624), by norm_num⟩
  | 2 => ⟨((976689723076883/281474976710656), (97455555422609/562949953421312)), (164401/8796093022208), by norm_num⟩
  | 3 => ⟨((1690289541832819/140737488355328), (21135058023261/17592186044416)), (9582645/70368744177664), by norm_num⟩
  | 4 => ⟨((1256102125362099/8796093022208), (126918449235617/4398046511104)), (31650563/8796093022208), by norm_num⟩
  | 5 => ⟨((672066570534507/34359738368), (283191308327915/34359738368)), (42446421/34359738368), by norm_num⟩
  | 6 => ⟨((82484276768277/262144), (21130143345385/65536)), (72026437/1048576), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((2674408417/134217728), (1793680511/134217728)), (11/134217728), by norm_num⟩, 2, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2252800/47014729), (-8482560/47014729)), 0, by norm_num⟩
  | 1 => ⟨((33439358156800/2210384742943441), (19109511168000/2210384742943441)), 0, by norm_num⟩
  | 2 => ⟨((-2512078293/2199023255552), (1272817885/1099511627776)), (1/2199023255552), by norm_num⟩
  | 3 => ⟨((-2711371269/35184372088832), (-2300867297/17592186044416)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((240045343/17592186044416), (-537388263/140737488355328)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((39516977/2251799813685248), (5955655463/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 6 => ⟨((-2156654035/18014398509481984), (-1084467837/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 7 => ⟨((1609375131/288230376151711744), (-2905030495/288230376151711744)), (9/288230376151711744), by norm_num⟩
  | 8 => ⟨((3576155069/4611686018427387904), (859138157/1152921504606846976)), (9/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-3165571879/36893488147419103232), (961106643/18446744073709551616)), (9/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-1561023857/590295810358705651712), (-5305999401/590295810358705651712)), (17/295147905179352825856), by norm_num⟩
  | 11 => ⟨((4128504735/4722366482869645213696), (-219186303/9444732965739290427392)), (63/9444732965739290427392), by norm_num⟩
  | 12 => ⟨((-1424415737/75557863725914323419136), (6001043729/75557863725914323419136)), (59/75557863725914323419136), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (6627/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (6627/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (6627/1280)))⁻¹=value ((2252800/47014729), (-8482560/47014729)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/47014729), (-8482560/47014729))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (6627/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3891200/53158729), (-8482560/53158729)), 0, by norm_num⟩
  | 1 => ⟨((28406193356800/2825850468895441), (33007337472000/2825850468895441)), 0, by norm_num⟩
  | 2 => ⟨((-5716764975/4398046511104), (1647146621/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((622517203/35184372088832), (-2065594113/17592186044416)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((2454589391/281474976710656), (3213894621/562949953421312)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((-872192607/1125899906842624), (1096207429/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 6 => ⟨((-188935559/18014398509481984), (-2868754005/36028797018963968)), (3/18014398509481984), by norm_num⟩
  | 7 => ⟨((242714137/36028797018963968), (1197557775/576460752303423488)), (3/144115188075855872), by norm_num⟩
  | 8 => ⟨((-475360193/1152921504606846976), (1064038189/2305843009213693952)), (23/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-1603145813/73786976294838206464), (-3673504871/73786976294838206464)), (23/73786976294838206464), by norm_num⟩
  | 10 => ⟨((1407064735/295147905179352825856), (13084617/147573952589676412928)), (11/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-13396559/73786976294838206464), (890441253/2361183241434822606848)), (21/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((-3542660029/151115727451828646838272), (-2137379229/75557863725914323419136)), (79/151115727451828646838272), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (6627/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (6627/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (6627/1280)))⁻¹=value ((3891200/53158729), (-8482560/53158729)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/53158729), (-8482560/53158729))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-63187728793600/2499243237919441), (-52116848640000/2499243237919441)), 0, by norm_num⟩
  | 1 => ⟨((2790579279/549755813888), (-834299607/274877906944)), (1/549755813888), by norm_num⟩
  | 2 => ⟨((1385216777/8796093022208), (6888249839/8796093022208)), (3/8796093022208), by norm_num⟩
  | 3 => ⟨((-3333888473/35184372088832), (-941092737/70368744177664)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((2772272195/562949953421312), (-5363447675/562949953421312)), (3/281474976710656), by norm_num⟩
  | 5 => ⟨((3567804383/4503599627370496), (1881620303/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 6 => ⟨((-3935436953/36028797018963968), (223035771/4503599627370496)), (9/36028797018963968), by norm_num⟩
  | 7 => ⟨((-664675929/576460752303423488), (-7007618765/576460752303423488)), (5/144115188075855872), by norm_num⟩
  | 8 => ⟨((2738797921/2305843009213693952), (654238125/2305843009213693952)), (11/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-590999743/9223372036854775808), (1879482861/18446744073709551616)), (11/18446744073709551616), by norm_num⟩
  | 10 => ⟨((-273447083/36893488147419103232), (-1339584467/147573952589676412928)), (23/295147905179352825856), by norm_num⟩
  | 11 => ⟨((4985884511/4722366482869645213696), (-945237829/2361183241434822606848)), (45/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((346914279/75557863725914323419136), (4069211479/37778931862957161709568)), (11/9444732965739290427392), by norm_num⟩
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
  | 0 => ⟨((27/8), (6627/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((614400/6953281), (-2827520/20859843)), 0, by norm_num⟩
  | 1 => ⟨((2298741555200/435133049984649), (579076096000/48348116664961)), 0, by norm_num⟩
  | 2 => ⟨((-4596602255/4398046511104), (-752592109/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((4065390719/70368744177664), (-2226250127/35184372088832)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((977227939/562949953421312), (3777942535/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((-4787546911/9007199254740992), (-805446549/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((2565549303/72057594037927936), (-1013208631/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 7 => ⟨((383862855/1152921504606846976), (4214503153/1152921504606846976)), (15/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-1210376125/4611686018427387904), (-1281465505/9223372036854775808)), (7/4611686018427387904), by norm_num⟩
  | 9 => ⟨((1550404745/73786976294838206464), (-429795007/36893488147419103232)), (13/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-2559931/18446744073709551616), (4577750073/2361183241434822606848)), (47/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-73944207/590295810358705651712), (-1795642607/18889465931478580854784)), (85/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((904956205/75557863725914323419136), (-1296573793/302231454903657293676544)), (77/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (6627/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (6627/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (6627/1280)))⁻¹=value ((614400/6953281), (-2827520/20859843)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((614400/6953281), (-2827520/20859843))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5564201961/1099511627776), (1742107657/1099511627776)), (1/1099511627776), by norm_num⟩
  | 1 => ⟨((674260599/4398046511104), (-6021892719/4398046511104)), (3/4398046511104), by norm_num⟩
  | 2 => ⟨((453192777/2199023255552), (522193095/4398046511104)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-1923710317/70368744177664), (717195865/35184372088832)), (5/140737488355328), by norm_num⟩
  | 4 => ⟨((-1159678647/1125899906842624), (-2399699881/562949953421312)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((1165700339/2251799813685248), (765379201/9007199254740992)), (9/9007199254740992), by norm_num⟩
  | 6 => ⟨((-142174449/4503599627370496), (1819915771/36028797018963968)), (11/72057594037927936), by norm_num⟩
  | 7 => ⟨((-1089042673/288230376151711744), (-1524481241/288230376151711744)), (13/576460752303423488), by norm_num⟩
  | 8 => ⟨((771082561/1152921504606846976), (-1460332879/9223372036854775808)), (7/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-787223693/73786976294838206464), (2582961575/36893488147419103232)), (15/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-3635600295/590295810358705651712), (-2133119409/590295810358705651712)), (1/18446744073709551616), by norm_num⟩
  | 11 => ⟨((2625855315/4722366482869645213696), (-257516801/590295810358705651712)), (33/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((1511600249/75557863725914323419136), (4975829369/75557863725914323419136)), (65/75557863725914323419136), by norm_num⟩
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
  | 0 => ⟨((35/8), (6627/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7168000/75277129), (-8482560/75277129)), 0, by norm_num⟩
  | 1 => ⟨((10286800076800/5666646150482641), (60802990080000/5666646150482641)), 0, by norm_num⟩
  | 2 => ⟨((-1519480321/2199023255552), (-898483185/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((491864467/8796093022208), (-1370669813/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-1761883035/1125899906842624), (4591367457/1125899906842624)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-1398425933/9007199254740992), (-5085868829/18014398509481984)), (7/18014398509481984), by norm_num⟩
  | 6 => ⟨((1678837185/72057594037927936), (676489349/144115188075855872)), (13/288230376151711744), by norm_num⟩
  | 7 => ⟨((-791905105/576460752303423488), (627882571/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 8 => ⟨((148921391/36893488147419103232), (-2384372515/18446744073709551616)), (21/36893488147419103232), by norm_num⟩
  | 9 => ⟨((4185462207/590295810358705651712), (58858513/9223372036854775808)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-3292087755/4722366482869645213696), (56471161/590295810358705651712)), (15/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((2100560975/75557863725914323419136), (-1655940633/37778931862957161709568)), (51/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((1385431209/1208925819614629174706176), (4416502061/1208925819614629174706176)), (43/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (6627/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (6627/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (6627/1280)))⁻¹=value ((7168000/75277129), (-8482560/75277129)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((7168000/75277129), (-8482560/75277129))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1334092693/4398046511104), (3171539907/4398046511104)), (1/2199023255552), by norm_num⟩
  | 1 => ⟨((-2918175421/17592186044416), (-437778669/2199023255552)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((3667445907/70368744177664), (-414637705/35184372088832)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((-298863113/140737488355328), (4795772289/562949953421312)), (7/562949953421312), by norm_num⟩
  | 4 => ⟨((-4311280043/4503599627370496), (-917697681/1125899906842624)), (11/4503599627370496), by norm_num⟩
  | 5 => ⟨((2708825227/18014398509481984), (-1177641031/18014398509481984)), (7/18014398509481984), by norm_num⟩
  | 6 => ⟨((-113859571/144115188075855872), (2875363965/144115188075855872)), (9/144115188075855872), by norm_num⟩
  | 7 => ⟨((-2354609641/1152921504606846976), (-618143693/576460752303423488)), (11/1152921504606846976), by norm_num⟩
  | 8 => ⟨((1876911279/9223372036854775808), (-2849187755/18446744073709551616)), (25/18446744073709551616), by norm_num⟩
  | 9 => ⟨((434387523/73786976294838206464), (1969217173/73786976294838206464)), (7/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-204951139/73786976294838206464), (-1390782273/2361183241434822606848)), (59/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((3196465355/18889465931478580854784), (-4394653363/18889465931478580854784)), (63/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((67894307/4722366482869645213696), (1860786615/75557863725914323419136)), (1/2361183241434822606848), by norm_num⟩
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
  | 0 => ⟨((43/8), (6627/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8806400/91251529), (-8482560/91251529)), 0, by norm_num⟩
  | 1 => ⟨((-2799428403200/8326841544837841), (74700816384000/8326841544837841)), 0, by norm_num⟩
  | 2 => ⟨((-1762493689/4398046511104), (-1972575315/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((5655350785/140737488355328), (13264593/4398046511104)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-4681902721/2251799813685248), (3877969113/2251799813685248)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((365390149/18014398509481984), (-1618942033/9007199254740992)), (5/18014398509481984), by norm_num⟩
  | 6 => ⟨((1062898313/144115188075855872), (1385776061/144115188075855872)), (9/288230376151711744), by norm_num⟩
  | 7 => ⟨((-7404671117/9223372036854775808), (-1117824413/9223372036854775808)), (7/2305843009213693952), by norm_num⟩
  | 8 => ⟨((204628101/4611686018427387904), (-1160891411/36893488147419103232)), (11/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-801120029/1180591620717411303424), (4227336995/1180591620717411303424)), (17/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-157825609/1180591620717411303424), (-3859500851/18889465931478580854784)), (53/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((1204943199/75557863725914323419136), (550919651/151115727451828646838272)), (81/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((-4540527985/4835703278458516698824704), (170850695/302231454903657293676544)), (31/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (6627/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (6627/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (6627/1280)))⁻¹=value ((8806400/91251529), (-8482560/91251529)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/91251529), (-8482560/91251529))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((664283605/17592186044416), (3440720021/35184372088832)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-179799707/4398046511104), (-950875981/140737488355328)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((3502072867/562949953421312), (-4253746305/562949953421312)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((359158865/562949953421312), (3767930445/2251799813685248)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-2492404083/9007199254740992), (-367145979/9007199254740992)), (13/18014398509481984), by norm_num⟩
  | 5 => ⟨((3412899121/144115188075855872), (-2246856963/72057594037927936)), (9/72057594037927936), by norm_num⟩
  | 6 => ⟨((2403832687/1152921504606846976), (2654167375/576460752303423488)), (23/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-2819512487/4611686018427387904), (-358784629/9223372036854775808)), (29/9223372036854775808), by norm_num⟩
  | 8 => ⟨((674971469/18446744073709551616), (-2226962769/36893488147419103232)), (17/36893488147419103232), by norm_num⟩
  | 9 => ⟨((301711119/73786976294838206464), (980136843/147573952589676412928)), (39/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-3913972471/4722366482869645213696), (669851861/9444732965739290427392)), (21/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((2372580405/75557863725914323419136), (-6054267019/75557863725914323419136)), (45/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((3557779333/604462909807314587353088), (3848095703/604462909807314587353088)), (47/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((51/8), (6627/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3481600/36834243), (-2827520/36834243)), 0, by norm_num⟩
  | 1 => ⟨((-687778201600/452253819127683), (9844293632000/1356761457383049)), 0, by norm_num⟩
  | 2 => ⟨((-28396875/137438953472), (-3529683085/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((3541858451/140737488355328), (1552948387/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-3631908929/2251799813685248), (15637387/35184372088832)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((1065866081/18014398509481984), (-373393183/4503599627370496)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((27810395/72057594037927936), (7135777855/1152921504606846976)), (5/288230376151711744), by norm_num⟩
  | 7 => ⟨((-2359299127/9223372036854775808), (-640321915/2305843009213693952)), (15/9223372036854775808), by norm_num⟩
  | 8 => ⟨((6713851749/295147905179352825856), (975793595/295147905179352825856)), (21/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-709503441/590295810358705651712), (423145037/590295810358705651712)), (29/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((1106584327/37778931862957161709568), (-377839385/4722366482869645213696)), (81/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((2039017161/1208925819614629174706176), (5930470357/1208925819614629174706176)), (7/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((-323986103/1208925819614629174706176), (-3232245341/19342813113834066795298816)), (155/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (6627/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (6627/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (6627/1280)))⁻¹=value ((3481600/36834243), (-2827520/36834243)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/36834243), (-2827520/36834243))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((389698365/35184372088832), (446468275/70368744177664)), (3/140737488355328), by norm_num⟩
  | 1 => ⟨((-2899070585/562949953421312), (184707999/70368744177664)), (7/562949953421312), by norm_num⟩
  | 2 => ⟨((678261035/4503599627370496), (-6816034029/4503599627370496)), (15/4503599627370496), by norm_num⟩
  | 3 => ⟨((269904399/1125899906842624), (1679788703/9007199254740992)), (15/18014398509481984), by norm_num⟩
  | 4 => ⟨((-3442292837/72057594037927936), (1280880103/72057594037927936)), (13/72057594037927936), by norm_num⟩
  | 5 => ⟨((102340317/72057594037927936), (-4288185745/576460752303423488)), (19/576460752303423488), by norm_num⟩
  | 6 => ⟨((3545947517/4611686018427387904), (785391873/1152921504606846976)), (25/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-568434593/4611686018427387904), (748426809/18446744073709551616)), (1/1152921504606846976), by norm_num⟩
  | 8 => ⟨((912897341/295147905179352825856), (-4475215681/295147905179352825856)), (39/295147905179352825856), by norm_num⟩
  | 9 => ⟨((786342861/590295810358705651712), (2713471847/2361183241434822606848)), (45/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-3399358355/18889465931478580854784), (317076983/4722366482869645213696)), (25/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((829651351/302231454903657293676544), (-6064144591/302231454903657293676544)), (109/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((254690371/151115727451828646838272), (1454984123/1208925819614629174706176)), (29/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((59/8), (6627/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12083200/133030729), (-8482560/133030729)), 0, by norm_num⟩
  | 1 => ⟨((-37024949043200/17697174858271441), (102496468992000/17697174858271441)), 0, by norm_num⟩
  | 2 => ⟨((-394221651/4398046511104), (-1450173539/4398046511104)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((513103799/35184372088832), (3410635291/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-1180635567/1125899906842624), (-384387475/4503599627370496)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((3627673877/72057594037927936), (-2129710491/72057594037927936)), (3/36028797018963968), by norm_num⟩
  | 6 => ⟨((-6053233/4503599627370496), (3398052739/1152921504606846976)), (9/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-1214723909/36893488147419103232), (-6519294995/36893488147419103232)), (23/36893488147419103232), by norm_num⟩
  | 8 => ⟨((2104117249/295147905179352825856), (4117543509/590295810358705651712)), (15/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-5158281825/9444732965739290427392), (-845308461/9444732965739290427392)), (19/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((4179421173/151115727451828646838272), (-2017062021/151115727451828646838272)), (3/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-2008013189/2417851639229258349412352), (3597650265/2417851639229258349412352)), (15/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-752194241/77371252455336267181195264), (-3638510921/38685626227668133590597632)), (149/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (6627/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (6627/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (6627/1280)))⁻¹=value ((12083200/133030729), (-8482560/133030729)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/133030729), (-8482560/133030729))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1588180487/1125899906842624), (-585255007/4503599627370496)), (1/281474976710656), by norm_num⟩
  | 1 => ⟨((-1622661065/4503599627370496), (1390848377/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 2 => ⟨((-1552012531/18014398509481984), (-840414483/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 3 => ⟨((6273024617/144115188075855872), (66488527/9007199254740992)), (25/144115188075855872), by norm_num⟩
  | 4 => ⟨((-195196611/36028797018963968), (823356177/144115188075855872)), (11/288230376151711744), by norm_num⟩
  | 5 => ⟨((-1297838099/4611686018427387904), (-2763378361/2305843009213693952)), (33/4611686018427387904), by norm_num⟩
  | 6 => ⟨((6060342295/36893488147419103232), (134432979/2305843009213693952)), (23/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-1322818743/73786976294838206464), (2085821539/147573952589676412928)), (15/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-761081531/2361183241434822606848), (-3291384207/1180591620717411303424)), (37/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((5625217865/18889465931478580854784), (80148991/590295810358705651712)), (11/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-4521051253/151115727451828646838272), (789641663/37778931862957161709568)), (25/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-25517773/75557863725914323419136), (-2357763827/604462909807314587353088)), (55/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((3573811979/9671406556917033397649408), (203375093/1208925819614629174706176)), (119/9671406556917033397649408), by norm_num⟩
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
  | 0 => ⟨((67/8), (6627/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13721600/158835529), (-8482560/158835529)), 0, by norm_num⟩
  | 1 => ⟨((-58164241203200/25228725272709841), (116394295296000/25228725272709841)), 0, by norm_num⟩
  | 2 => ⟨((-415339025/17592186044416), (-2294386273/8796093022208)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((70235631/8796093022208), (2993897577/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-5664804461/9007199254740992), (-1108878881/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((1215627823/36028797018963968), (-221875533/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((-745338845/576460752303423488), (2690808203/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1821660337/73786976294838206464), (-6266781255/73786976294838206464)), (3/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1418435973/1180591620717411303424), (5109315751/1180591620717411303424)), (7/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-395398239/2361183241434822606848), (-2925089575/18889465931478580854784)), (33/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1717908331/151115727451828646838272), (670126887/302231454903657293676544)), (75/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-2660830043/4835703278458516698824704), (1004778113/4835703278458516698824704)), (85/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((2819294153/154742504910672534362390528), (-3662436391/154742504910672534362390528)), (3/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (6627/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (6627/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (6627/1280)))⁻¹=value ((13721600/158835529), (-8482560/158835529)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/158835529), (-8482560/158835529))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2070192967/18014398509481984), (-389824497/4503599627370496)), (19/36028797018963968), by norm_num⟩
  | 1 => ⟨((-28559685/36028797018963968), (5721966645/72057594037927936)), (25/72057594037927936), by norm_num⟩
  | 2 => ⟨((-2809482495/144115188075855872), (-2157561011/144115188075855872)), (17/144115188075855872), by norm_num⟩
  | 3 => ⟨((6221577247/1152921504606846976), (-1799458935/1152921504606846976)), (35/1152921504606846976), by norm_num⟩
  | 4 => ⟨((-817055947/2305843009213693952), (2292935793/2305843009213693952)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((-1836569231/18446744073709551616), (-1299714617/9223372036854775808)), (13/9223372036854775808), by norm_num⟩
  | 6 => ⟨((7487163585/295147905179352825856), (-45418771/147573952589676412928)), (9/36893488147419103232), by norm_num⟩
  | 7 => ⟨((-69412375/36893488147419103232), (1693620455/590295810358705651712)), (3/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-203153841/1180591620717411303424), (-3757093629/9444732965739290427392)), (61/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((963974021/18889465931478580854784), (635718911/75557863725914323419136)), (37/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-1177883989/302231454903657293676544), (1330627557/302231454903657293676544)), (85/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-1805712441/9671406556917033397649408), (-2965102575/4835703278458516698824704)), (191/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((2527893927/38685626227668133590597632), (1261047749/77371252455336267181195264)), (13/4835703278458516698824704), by norm_num⟩
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
  | 0 => ⟨((75/8), (6627/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5120000/62639043), (-2827520/62639043)), 0, by norm_num⟩
  | 1 => ⟨((-1012196147200/435961078661761), (14476902400000/3923649707955849)), 0, by norm_num⟩
  | 2 => ⟨((408590981/35184372088832), (-7149275969/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((578640225/140737488355328), (4822499237/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-813750135/2251799813685248), (-2317625301/9007199254740992)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((185337559/9007199254740992), (85016063/36028797018963968)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-1030947507/1152921504606846976), (53030835/144115188075855872)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((2083753553/73786976294838206464), (-1299424117/36893488147419103232)), (9/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-424083469/1180591620717411303424), (1225941961/590295810358705651712)), (5/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-1216223809/37778931862957161709568), (-1756444481/18889465931478580854784)), (21/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1031933371/302231454903657293676544), (3715789679/1208925819614629174706176)), (11/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-1010247397/4835703278458516698824704), (-939170693/19342813113834066795298816)), (23/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((5963153839/618970019642690137449562112), (-211287549/77371252455336267181195264)), (47/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (6627/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (6627/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (6627/1280)))⁻¹=value ((5120000/62639043), (-2827520/62639043)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/62639043), (-2827520/62639043))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1581235331/288230376151711744), (-3534439111/288230376151711744)), (5/72057594037927936), by norm_num⟩
  | 1 => ⟨((2059258217/576460752303423488), (4122526359/576460752303423488)), (7/144115188075855872), by norm_num⟩
  | 2 => ⟨((-5941364911/2305843009213693952), (-10004617/18014398509481984)), (41/2305843009213693952), by norm_num⟩
  | 3 => ⟨((2252693459/4611686018427387904), (-3750445475/9223372036854775808)), (11/2305843009213693952), by norm_num⟩
  | 4 => ⟨((94778611/18446744073709551616), (2304344573/18446744073709551616)), (41/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-161669105/9223372036854775808), (-1772858419/147573952589676412928)), (35/147573952589676412928), by norm_num⟩
  | 6 => ⟨((3597383077/1180591620717411303424), (-1268992563/1180591620717411303424)), (25/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-588149589/4722366482869645213696), (4081493625/9444732965739290427392)), (17/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-2771864217/75557863725914323419136), (-213545531/4722366482869645213696)), (87/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((2137076223/302231454903657293676544), (-360116393/604462909807314587353088)), (27/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-1911841737/4835703278458516698824704), (1740200979/2417851639229258349412352)), (63/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-208059515/4835703278458516698824704), (-3095985429/38685626227668133590597632)), (143/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((5967824253/618970019642690137449562112), (422270701/618970019642690137449562112)), (79/154742504910672534362390528), by norm_num⟩
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
  | 0 => ⟨((83/8), (6627/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((16998400/220275529), (-8482560/220275529)), 0, by norm_num⟩
  | 1 => ⟨((-108495889203200/48521308676229841), (144189947904000/48521308676229841)), 0, by norm_num⟩
  | 2 => ⟨((255600789/8796093022208), (-5549082671/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((539164909/281474976710656), (3740701419/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-909054329/4503599627370496), (-1977121721/9007199254740992)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((1731503887/144115188075855872), (660470645/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((-2544833025/4611686018427387904), (62842049/1152921504606846976)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((2987229245/147573952589676412928), (-1878342535/147573952589676412928)), (3/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-2531009377/4722366482869645213696), (2079874031/2361183241434822606848)), (23/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((562044985/151115727451828646838272), (-3347752727/75557863725914323419136)), (43/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((1715711645/2417851639229258349412352), (4306623101/2417851639229258349412352)), (41/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-2385940625/38685626227668133590597632), (-1065067471/19342813113834066795298816)), (39/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((4258388271/1237940039285380274899124224), (145000231/154742504910672534362390528)), (73/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (6627/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (6627/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (6627/1280)))⁻¹=value ((16998400/220275529), (-8482560/220275529)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/220275529), (-8482560/220275529))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-225362931/4611686018427387904), (-2669120213/2305843009213693952)), (19/2305843009213693952), by norm_num⟩
  | 1 => ⟨((2652794689/4611686018427387904), (1056139811/2305843009213693952)), (29/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-4634526173/18446744073709551616), (918096199/18446744073709551616)), (11/4611686018427387904), by norm_num⟩
  | 3 => ⟨((2270571639/73786976294838206464), (-4201955285/73786976294838206464)), (49/73786976294838206464), by norm_num⟩
  | 4 => ⟨((1510016663/295147905179352825856), (902543335/73786976294838206464)), (47/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-5308339487/2361183241434822606848), (-738473725/1180591620717411303424)), (41/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((1381467013/4722366482869645213696), (-1036274931/4722366482869645213696)), (61/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-1201295/37778931862957161709568), (7894860237/151115727451828646838272)), (169/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((-1685554413/302231454903657293676544), (-2474232215/604462909807314587353088)), (55/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((3949405883/4835703278458516698824704), (-1294596063/4835703278458516698824704)), (139/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-563867959/19342813113834066795298816), (936392203/9671406556917033397649408)), (165/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-2210194343/309485009821345068724781056), (-1364203509/154742504910672534362390528)), (95/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((6019335687/4951760157141521099596496896), (-574337181/4951760157141521099596496896)), (53/618970019642690137449562112), by norm_num⟩
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
  | 0 => ⟨((91/8), (6627/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((18636800/255910729), (-8482560/255910729)), 0, by norm_num⟩
  | 1 => ⟨((-137688245043200/65490301217311441), (158087774208000/65490301217311441)), 0, by norm_num⟩
  | 2 => ⟨((321483377/8796093022208), (-539820829/4398046511104)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((791952101/1125899906842624), (5714009481/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-494147951/4503599627370496), (-3118996099/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((989320267/144115188075855872), (2585998521/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((-5982520157/18446744073709551616), (-914497845/18446744073709551616)), (11/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1863967407/147573952589676412928), (-263402577/73786976294838206464)), (5/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-3785036329/9444732965739290427392), (3204764757/9444732965739290427392)), (9/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((677679375/75557863725914323419136), (-2870793513/151115727451828646838272)), (31/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-56761777/4835703278458516698824704), (1015968603/1208925819614629174706176)), (27/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-1044558023/77371252455336267181195264), (-4765355489/154742504910672534362390528)), (23/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((1240383349/1237940039285380274899124224), (2222335117/2475880078570760549798248448)), (5/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (6627/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (6627/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (6627/1280)))⁻¹=value ((18636800/255910729), (-8482560/255910729)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18636800/255910729), (-8482560/255910729))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1546851553/36893488147419103232), (-3050315709/36893488147419103232)), (33/36893488147419103232), by norm_num⟩
  | 1 => ⟨((2212523751/36893488147419103232), (1225212979/73786976294838206464)), (53/73786976294838206464), by norm_num⟩
  | 2 => ⟨((-704875799/36893488147419103232), (1821282977/147573952589676412928)), (43/147573952589676412928), by norm_num⟩
  | 3 => ⟨((997047401/1180591620717411303424), (-437793811/73786976294838206464)), (49/590295810358705651712), by norm_num⟩
  | 4 => ⟨((249578803/295147905179352825856), (4492104729/4722366482869645213696)), (97/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-4363718401/18889465931478580854784), (157598341/18889465931478580854784)), (43/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((3370484571/151115727451828646838272), (-1126183481/37778931862957161709568)), (133/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((853069149/604462909807314587353088), (6359960715/1208925819614629174706176)), (47/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-102819967/151115727451828646838272), (-340199585/1208925819614629174706176)), (125/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((3096520057/38685626227668133590597632), (-1841347157/38685626227668133590597632)), (5/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-643369365/618970019642690137449562112), (6856336053/618970019642690137449562112)), (385/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-2371985275/2475880078570760549798248448), (-255597199/309485009821345068724781056)), (225/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((1319682611/9903520314283042199192993792), (-1368464069/39614081257132168796771975168)), (507/39614081257132168796771975168), by norm_num⟩
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
  | 0 => ⟨((99/8), (6627/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2252800/32758081), (-2827520/98274243)), 0, by norm_num⟩
  | 1 => ⟨((-18840550604800/9657826837223049), (6369837056000/3219275612407683)), 0, by norm_num⟩
  | 2 => ⟨((679315339/17592186044416), (-3381250251/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((61604445/1125899906842624), (2172971985/562949953421312)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-2068430643/36028797018963968), (-4753626429/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((558035445/144115188075855872), (2139187567/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((-3440869467/18446744073709551616), (-1326257539/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 7 => ⟨((2198321033/295147905179352825856), (-7791953/36893488147419103232)), (3/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-1195094641/4722366482869645213696), (2161163883/18889465931478580854784)), (5/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1066280465/151115727451828646838272), (-2289318147/302231454903657293676544)), (1/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-1292645023/9671406556917033397649408), (1750365979/4835703278458516698824704)), (13/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-94606885/154742504910672534362390528), (-4447037301/309485009821345068724781056)), (21/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((563845371/2475880078570760549798248448), (1201529527/2475880078570760549798248448)), (33/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (6627/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (6627/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (6627/1280)))⁻¹=value ((2252800/32758081), (-2827520/98274243)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/32758081), (-2827520/98274243))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3106257693/590295810358705651712), (-2644273737/590295810358705651712)), (13/147573952589676412928), by norm_num⟩
  | 1 => ⟨((5722750291/1180591620717411303424), (-596441539/1180591620717411303424)), (11/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-41255731/36893488147419103232), (3507640859/2361183241434822606848)), (19/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-902438243/9444732965739290427392), (-2358814405/4722366482869645213696)), (89/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((906628753/9444732965739290427392), (2149202475/37778931862957161709568)), (91/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((-2986966177/151115727451828646838272), (2008393123/302231454903657293676544)), (163/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((1523550445/1208925819614629174706176), (-1937074829/604462909807314587353088)), (65/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((2429317505/9671406556917033397649408), (543422955/1208925819614629174706176)), (47/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((-5415390693/77371252455336267181195264), (-898987381/77371252455336267181195264)), (255/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((4152688603/618970019642690137449562112), (-1913757631/309485009821345068724781056)), (329/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((130587675/1237940039285380274899124224), (2725509509/2475880078570760549798248448)), (101/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-67536147/618970019642690137449562112), (-324670861/4951760157141521099596496896)), (477/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((4077115277/316912650057057350374175801344), (-13678581/2475880078570760549798248448)), (17/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-116251495/549755813888), (-6830499729/2199023255552)), (399/549755813888), by norm_num⟩
  | 1 => ⟨((2202954307/1099511627776), (-1496257583/549755813888)), (1663/1099511627776), by norm_num⟩
  | 2 => ⟨((470188123/274877906944), (-950371329/2199023255552)), (3653/2199023255552), by norm_num⟩
  | 3 => ⟨((4720827805/8796093022208), (2107596437/8796093022208)), (11001/8796093022208), by norm_num⟩
  | 4 => ⟨((2434007491/35184372088832), (1070538177/8796093022208)), (25317/35184372088832), by norm_num⟩
  | 5 => ⟨((-232975409/140737488355328), (1785248325/70368744177664)), (94619/281474976710656), by norm_num⟩
  | 6 => ⟨((-35215829/17592186044416), (3519459277/1125899906842624)), (18673/140737488355328), by norm_num⟩
  | 7 => ⟨((-3472900081/9007199254740992), (586264269/2251799813685248)), (409789/9007199254740992), by norm_num⟩
  | 8 => ⟨((-468378163/9007199254740992), (501930587/36028797018963968)), (249265/18014398509481984), by norm_num⟩
  | 9 => ⟨((-6753746727/1152921504606846976), (-383784173/1152921504606846976)), (273177/72057594037927936), by norm_num⟩
  | 10 => ⟨((-4962514993/9223372036854775808), (-992190767/4611686018427387904)), (2183787/2305843009213693952), by norm_num⟩
  | 11 => ⟨((-2978754881/73786976294838206464), (-146156615/4611686018427387904)), (16073813/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-1608772557/590295810358705651712), (-3968452261/1180591620717411303424)), (6863995/147573952589676412928), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-116251495/549755813888), (-6830499729/2199023255552)), (1597/2199023255552), by norm_num⟩
  | 1 => ⟨((2202954307/1099511627776), (-1496257583/549755813888)), (13/8589934592), by norm_num⟩
  | 2 => ⟨((470188123/274877906944), (-950371329/2199023255552)), (1827/1099511627776), by norm_num⟩
  | 3 => ⟨((4720827805/8796093022208), (2107596437/8796093022208)), (5501/4398046511104), by norm_num⟩
  | 4 => ⟨((2434007491/35184372088832), (1070538177/8796093022208)), (25319/35184372088832), by norm_num⟩
  | 5 => ⟨((-232975409/140737488355328), (1785248325/70368744177664)), (94631/281474976710656), by norm_num⟩
  | 6 => ⟨((-35215829/17592186044416), (3519459277/1125899906842624)), (74715/562949953421312), by norm_num⟩
  | 7 => ⟨((-3472900081/9007199254740992), (586264269/2251799813685248)), (205075/4503599627370496), by norm_num⟩
  | 8 => ⟨((-468378163/9007199254740992), (501930587/36028797018963968)), (999943/72057594037927936), by norm_num⟩
  | 9 => ⟨((-6753746727/1152921504606846976), (-383784173/1152921504606846976)), (4416949/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-4962514993/9223372036854775808), (-992190767/4611686018427387904)), (9104083/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-2978754881/73786976294838206464), (-146156615/4611686018427387904)), (19025293/73786976294838206464), by norm_num⟩
  | 12 => ⟨((-1608772557/590295810358705651712), (-3968452261/1180591620717411303424)), (102135625/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile023Gamma

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
namespace Reinmann.XiRectangle.Tile031Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨31,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (8037/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (8037/640))
  have he : value ((5/8), (8037/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/16), (8037/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21/16), (8037/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((213/16), (8037/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7270400/118318323), (-1143040/39439441)), 0, by norm_num⟩
  | 1 => ⟨((-20549926092800/13999225557532329), (8310358016000/4666408519177443)), 0, by norm_num⟩
  | 2 => ⟨((339416891/17592186044416), (-1336791489/17592186044416)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((572373729/1125899906842624), (367919687/140737488355328)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((-1927615153/36028797018963968), (-1314193619/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((3113984427/1152921504606846976), (845137259/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((-1922682189/18446744073709551616), (-217818581/36893488147419103232)), (3/18446744073709551616), by norm_num⟩
  | 7 => ⟨((3881632193/1180591620717411303424), (-1568999613/1180591620717411303424)), (5/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-1544357977/18889465931478580854784), (3342554119/37778931862957161709568)), (1/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1486725777/1208925819614629174706176), (-4718563581/1208925819614629174706176)), (3/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((726369951/38685626227668133590597632), (5328541481/38685626227668133590597632)), (9/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-3185063163/1237940039285380274899124224), (-2451002843/618970019642690137449562112)), (53/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((2702286371/19807040628566084398385987584), (835629773/9903520314283042199192993792)), (39/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((213/16), (8037/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((213/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((213/16), (8037/1280)))⁻¹=value ((7270400/118318323), (-1143040/39439441)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((7270400/118318323), (-1143040/39439441))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5774874275/2147483648), (946429379/2147483648)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((3635200/118318323), (-571520/39439441)), 0, by norm_num⟩
  | 2 => ⟨((-5137481523200/13999225557532329), (2077589504000/4666408519177443)), 0, by norm_num⟩
  | 3 => ⟨((905111709/281474976710656), (-445597163/35184372088832)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((572373729/9007199254740992), (367919687/1125899906842624)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-3084184245/576460752303423488), (-4205419581/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((1037994809/4611686018427387904), (2253699357/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-2197351073/295147905179352825856), (-248935521/590295810358705651712)), (1/73786976294838206464), by norm_num⟩
  | 8 => ⟨((3881632193/18889465931478580854784), (-1568999613/18889465931478580854784)), (5/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-686381323/151115727451828646838272), (2971159217/604462909807314587353088)), (15/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((594690311/9671406556917033397649408), (-3774850865/19342813113834066795298816)), (5/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((528269055/618970019642690137449562112), (3875302895/618970019642690137449562112)), (27/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-1061687721/9903520314283042199192993792), (-3268003791/19807040628566084398385987584)), (9/4951760157141521099596496896), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-7005/276736), (171/20480)), 0, by norm_num⟩
  | 45 => ⟨((94660009097/4080638361600), (-683487/60293120)), 0, by norm_num⟩
  | 44 => ⟨((-11078933028629/499612070707200), (2174731417643/197568495616000)), 0, by norm_num⟩
  | 43 => ⟨((1557241695/68719476736), (-725066909/68719476736)), (1/137438953472), by norm_num⟩
  | 42 => ⟨((-806603381/34359738368), (1465798991/137438953472)), (1/68719476736), by norm_num⟩
  | 41 => ⟨((3318880341/137438953472), (-1512355177/137438953472)), (1/68719476736), by norm_num⟩
  | 40 => ⟨((-849986499/34359738368), (778231033/68719476736)), (1/68719476736), by norm_num⟩
  | 39 => ⟨((3484355447/137438953472), (-1595683373/137438953472)), (1/68719476736), by norm_num⟩
  | 38 => ⟨((-1787940375/68719476736), (817698133/68719476736)), (1/68719476736), by norm_num⟩
  | 37 => ⟨((1836710645/68719476736), (-209748027/17179869184)), (1/68719476736), by norm_num⟩
  | 36 => ⟨((-3776274591/137438953472), (1723415655/137438953472)), (1/68719476736), by norm_num⟩
  | 35 => ⟨((971200133/34359738368), (-885704803/68719476736)), (1/68719476736), by norm_num⟩
  | 34 => ⟨((-499961259/17179869184), (227757513/17179869184)), (1/68719476736), by norm_num⟩
  | 33 => ⟨((2060802839/68719476736), (-1875654095/137438953472)), (1/68719476736), by norm_num⟩
  | 32 => ⟨((-1062800559/34359738368), (241562469/17179869184)), (1/68719476736), by norm_num⟩
  | 31 => ⟨((2194604853/68719476736), (-498226459/34359738368)), (1/68719476736), by norm_num⟩
  | 30 => ⟨((-2268234605/68719476736), (514302667/34359738368)), (1/68719476736), by norm_num⟩
  | 29 => ⟨((4693944763/137438953472), (-2125801159/137438953472)), (1/68719476736), by norm_num⟩
  | 28 => ⟨((-4862738451/137438953472), (68722519/4294967296)), (1/68719476736), by norm_num⟩
  | 27 => ⟨((5044115201/137438953472), (-35588687/2147483648)), (1/68719476736), by norm_num⟩
  | 26 => ⟨((-5239535203/137438953472), (2362048789/137438953472)), (1/68719476736), by norm_num⟩
  | 25 => ⟨((1362673409/34359738368), (-1226454889/68719476736)), (1/68719476736), by norm_num⟩
  | 24 => ⟨((-2839784925/68719476736), (2551036835/137438953472)), (1/68719476736), by norm_num⟩
  | 23 => ⟨((2964244675/68719476736), (-2657337383/137438953472)), (1/68719476736), by norm_num⟩
  | 22 => ⟨((-3100101417/68719476736), (346609555/17179869184)), (1/34359738368), by norm_num⟩
  | 21 => ⟨((1624496985/34359738368), (-362364045/17179869184)), (1/34359738368), by norm_num⟩
  | 20 => ⟨((-1706445413/34359738368), (1518471377/68719476736)), (1/34359738368), by norm_num⟩
  | 19 => ⟨((3594177357/68719476736), (-1594382085/68719476736)), (1/34359738368), by norm_num⟩
  | 18 => ⟨((-237235763/4294967296), (1678275283/68719476736)), (1/34359738368), by norm_num⟩
  | 17 => ⟨((4021284951/68719476736), (-442869729/17179869184)), (1/34359738368), by norm_num⟩
  | 16 => ⟨((-4275233125/68719476736), (937816275/34359738368)), (1/34359738368), by norm_num⟩
  | 15 => ⟨((2281673227/34359738368), (-498196101/17179869184)), (1/34359738368), by norm_num⟩
  | 14 => ⟨((-4893001999/68719476736), (2125527041/68719476736)), (1/34359738368), by norm_num⟩
  | 13 => ⟨((5273860961/68719476736), (-1138595461/34359738368)), (1/34359738368), by norm_num⟩
  | 12 => ⟨((-5718825125/68719476736), (1226063411/34359738368)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((3122758457/34359738368), (-664032151/17179869184)), (1/34359738368), by norm_num⟩
  | 10 => ⟨((-1719662609/17179869184), (1448542525/34359738368)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((1913496973/17179869184), (-1593009915/34359738368)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((-4312635191/34359738368), (1769409397/34359738368)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((2469274881/17179869184), (-497404997/8589934592)), (1/17179869184), by norm_num⟩
  | 6 => ⟨((-721919407/4294967296), (142014823/2147483648)), (1/17179869184), by norm_num⟩
  | 5 => ⟨((3475164559/17179869184), (-165506061/2147483648)), (1/8589934592), by norm_num⟩
  | 4 => ⟨((-4359087823/17179869184), (1586163299/17179869184)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((182386029/536870912), (-1977069853/17179869184)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((-2198598683/4294967296), (1311227753/8589934592)), (1/8589934592), by norm_num⟩
  | 1 => ⟨((4406979539/4294967296), (-243230583/1073741824)), (1/2147483648), by norm_num⟩
  | 0 => ⟨((-716858675/8589934592), (3785717517/8589934592)), (3/8589934592), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-43/256), (8037/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-43/256), (8037/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-43/256), (8037/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((5774874275/2147483648), (946429379/2147483648)), (1/1073741824), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((213/16), (8037/1280))) (z:=((-43/256), (8037/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((5774874275/2147483648), (946429379/2147483648))) (r:=(1/1073741824)) (by norm_num) ?_ hs
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
  | 0 => ⟨((205/16), (8037/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((4253002207/134217728), (3024126287/134217728)), (1/33554432), by norm_num⟩
  | 1 => ⟨((982047357/536870912), (244387183/1073741824)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((110096432704000/13999225557532329), (-17944116742240/4666408519177443)), 0, by norm_num⟩
  | 3 => ⟨((-552145529/8796093022208), (177100639/2199023255552)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((13024453/35184372088832), (-3932696991/2251799813685248)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((1301320995/144115188075855872), (163595295/4503599627370496)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((-1287560117/2305843009213693952), (-3085325477/4611686018427387904)), (23/2305843009213693952), by norm_num⟩
  | 7 => ⟨((5843794665/295147905179352825856), (2637890289/295147905179352825856)), (125/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-5365110193/9444732965739290427392), (35828595/2361183241434822606848)), (161/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((4136721053/302231454903657293676544), (-4174719/590295810358705651712)), (7/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-1246882691/4835703278458516698824704), (3320640093/9671406556917033397649408)), (39/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((366468413/154742504910672534362390528), (-3714171813/309485009821345068724781056)), (419/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((883023229/9903520314283042199192993792), (3400536207/9903520314283042199192993792)), (35/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-213/16), (-8037/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2466228703/134217728), (545346439/33554432)), (5/134217728), by norm_num⟩
  | 1 => ⟨((713611901/536870912), (244387183/1073741824)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((110096432704000/13999225557532329), (-17944116742240/4666408519177443)), 0, by norm_num⟩
  | 3 => ⟨((-552145529/8796093022208), (177100639/2199023255552)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((13024453/35184372088832), (-3932696991/2251799813685248)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((1301320995/144115188075855872), (163595295/4503599627370496)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((-1287560117/2305843009213693952), (-3085325477/4611686018427387904)), (23/2305843009213693952), by norm_num⟩
  | 7 => ⟨((5843794665/295147905179352825856), (2637890289/295147905179352825856)), (125/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-5365110193/9444732965739290427392), (35828595/2361183241434822606848)), (161/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((4136721053/302231454903657293676544), (-4174719/590295810358705651712)), (7/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-1246882691/4835703278458516698824704), (3320640093/9671406556917033397649408)), (39/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((366468413/154742504910672534362390528), (-3714171813/309485009821345068724781056)), (419/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((883023229/9903520314283042199192993792), (3400536207/9903520314283042199192993792)), (35/618970019642690137449562112), by norm_num⟩
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
  | 0 => ⟨((2589566545/134217728), (545346439/33554432)), (3/67108864), by norm_num⟩
  | 1 => ⟨((713611901/536870912), (244387183/1073741824)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((110096432704000/13999225557532329), (-17944116742240/4666408519177443)), 0, by norm_num⟩
  | 3 => ⟨((-552145529/8796093022208), (177100639/2199023255552)), (3/35184372088832), by norm_num⟩
  | 4 => ⟨((13024453/35184372088832), (-3932696991/2251799813685248)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((1301320995/144115188075855872), (163595295/4503599627370496)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((-1287560117/2305843009213693952), (-3085325477/4611686018427387904)), (23/2305843009213693952), by norm_num⟩
  | 7 => ⟨((5843794665/295147905179352825856), (2637890289/295147905179352825856)), (125/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-5365110193/9444732965739290427392), (35828595/2361183241434822606848)), (161/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((4136721053/302231454903657293676544), (-4174719/590295810358705651712)), (7/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-1246882691/4835703278458516698824704), (3320640093/9671406556917033397649408)), (39/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((366468413/154742504910672534362390528), (-3714171813/309485009821345068724781056)), (419/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((883023229/9903520314283042199192993792), (3400536207/9903520314283042199192993792)), (35/618970019642690137449562112), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((41099852185600/13999225557532329), (-16620716032000/4666408519177443)), 0, by norm_num⟩
  | 1 => ⟨((-339416891/4398046511104), (1336791489/4398046511104)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-858560593/281474976710656), (-1103759061/70368744177664)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((1927615153/4503599627370496), (1314193619/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-1946240267/72057594037927936), (-528210787/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((5768046567/4611686018427387904), (5105123/72057594037927936)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-3396428169/73786976294838206464), (1372874661/73786976294838206464)), (3/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1544357977/1180591620717411303424), (-3342554119/2361183241434822606848)), (11/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-1672566499/75557863725914323419136), (2654192015/37778931862957161709568)), (17/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-113495305/302231454903657293676544), (-1665169213/604462909807314587353088)), (27/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((2189730925/38685626227668133590597632), (3370128909/38685626227668133590597632)), (21/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-4053429557/1237940039285380274899124224), (-1253444659/618970019642690137449562112)), (1/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((174270071/1237940039285380274899124224), (79225673/4951760157141521099596496896)), (49/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((339416891/4398046511104), (-1336791489/4398046511104)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((858560593/140737488355328), (1103759061/35184372088832)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((-2891422729/2251799813685248), (-3942580857/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((1946240267/18014398509481984), (528210787/9007199254740992)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-7210058209/1152921504606846976), (-25525615/72057594037927936)), (7/1152921504606846976), by norm_num⟩
  | 5 => ⟨((2547321127/9223372036854775808), (-2059311991/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-675656615/73786976294838206464), (1462367427/147573952589676412928)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1672566499/9444732965739290427392), (-2654192015/4722366482869645213696)), (13/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((1021457745/302231454903657293676544), (7493261459/302231454903657293676544)), (11/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-2737163657/4835703278458516698824704), (-4212661137/4835703278458516698824704)), (19/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((2786732821/77371252455336267181195264), (861743203/38685626227668133590597632)), (1/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-522810213/309485009821345068724781056), (-237677019/1237940039285380274899124224)), (25/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((2527289901/39614081257132168796771975168), (-429370091/19807040628566084398385987584)), (39/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-572373729/140737488355328), (-367919687/17592186044416)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((120475947/70368744177664), (1314193619/562949953421312)), (1/562949953421312), by norm_num⟩
  | 2 => ⟨((-3892480533/18014398509481984), (-528210787/4503599627370496)), (3/18014398509481984), by norm_num⟩
  | 3 => ⟨((4806705473/288230376151711744), (272273227/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 4 => ⟨((-1061383803/1152921504606846976), (858046663/2305843009213693952)), (3/2305843009213693952), by norm_num⟩
  | 5 => ⟨((675656615/18446744073709551616), (-1462367427/36893488147419103232)), (7/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-1951327583/2361183241434822606848), (6193114701/2361183241434822606848)), (7/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((-340485915/18889465931478580854784), (-4995507639/37778931862957161709568)), (7/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((2052872743/604462909807314587353088), (3159495853/604462909807314587353088)), (13/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-2322277351/9671406556917033397649408), (-89764917/604462909807314587353088)), (11/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((7667883125/618970019642690137449562112), (435741201/309485009821345068724781056)), (37/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-2527289901/4951760157141521099596496896), (429370091/2475880078570760549798248448)), (31/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((1304082493/79228162514264337593543950336), (-78758749/4951760157141521099596496896)), (25/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1927615153/2251799813685248), (-1314193619/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((3892480533/18014398509481984), (2112843149/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((-225314319/9007199254740992), (-408409841/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 3 => ⟨((1061383803/576460752303423488), (-858046663/1152921504606846976)), (3/1152921504606846976), by norm_num⟩
  | 4 => ⟨((-844570769/9223372036854775808), (456989821/4611686018427387904)), (9/36893488147419103232), by norm_num⟩
  | 5 => ⟨((1463495687/590295810358705651712), (-2322418013/295147905179352825856)), (5/295147905179352825856), by norm_num⟩
  | 6 => ⟨((595850351/9444732965739290427392), (17074489/36893488147419103232)), (3/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((-1026436371/75557863725914323419136), (-3159495853/151115727451828646838272)), (3/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((5225124039/4835703278458516698824704), (3231537013/4835703278458516698824704)), (23/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((-4792426953/77371252455336267181195264), (-272338251/38685626227668133590597632)), (11/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((1737511807/618970019642690137449562112), (-590383875/618970019642690137449562112)), (5/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-489030935/4951760157141521099596496896), (236276247/2475880078570760549798248448)), (17/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((87222841/39614081257132168796771975168), (-3687294209/633825300114114700748351602688)), (29/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3113984427/36028797018963968), (-845137259/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((5768046567/288230376151711744), (163363937/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 2 => ⟨((-2547321127/1152921504606846976), (1029655995/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 3 => ⟨((2702626461/18446744073709551616), (-1462367427/9223372036854775808)), (7/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-1463495687/295147905179352825856), (2322418013/147573952589676412928)), (11/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-715020421/4722366482869645213696), (-2622641511/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((2874021839/75557863725914323419136), (2211647097/37778931862957161709568)), (17/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-4180099231/1208925819614629174706176), (-1292614805/604462909807314587353088)), (19/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((2156592129/9671406556917033397649408), (122552213/4835703278458516698824704)), (19/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-3475023615/309485009821345068724781056), (590383875/154742504910672534362390528)), (19/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((1075868057/2475880078570760549798248448), (-4158461947/9903520314283042199192993792)), (9/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((-1674678547/158456325028528675187087900672), (2212376525/79228162514264337593543950336)), (33/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((-574227731/5070602400912917605986812821504), (-7263014489/5070602400912917605986812821504)), (29/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1922682189/288230376151711744), (-217818581/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 1 => ⟨((1698214085/1152921504606846976), (-343218665/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((-2702626461/18446744073709551616), (2924734853/18446744073709551616)), (9/18446744073709551616), by norm_num⟩
  | 3 => ⟨((60978987/9223372036854775808), (-6193114701/295147905179352825856)), (15/295147905179352825856), by norm_num⟩
  | 4 => ⟨((595850351/2361183241434822606848), (4371069185/2361183241434822606848)), (13/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((-2874021839/37778931862957161709568), (-2211647097/18889465931478580854784)), (9/18889465931478580854784), by norm_num⟩
  | 6 => ⟨((1219195609/151115727451828646838272), (754025303/151115727451828646838272)), (23/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((-5750912343/9671406556917033397649408), (-653611803/9671406556917033397649408)), (27/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((2606267711/77371252455336267181195264), (-1771151625/154742504910672534362390528)), (29/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-3586226857/2475880078570760549798248448), (866346239/618970019642690137449562112)), (15/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((767561001/19807040628566084398385987584), (-2028011815/19807040628566084398385987584)), (15/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((574227731/1267650600228229401496703205376), (7263014489/1267650600228229401496703205376)), (29/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((-2949394089/20282409603651670423947251286016), (-5155846377/20282409603651670423947251286016)), (27/10141204801825835211973625643008), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3881632193/9223372036854775808), (1568999613/9223372036854775808)), (5/4611686018427387904), by norm_num⟩
  | 1 => ⟨((772178989/9223372036854775808), (-3342554119/36893488147419103232)), (7/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-1672566501/295147905179352825856), (1327096007/73786976294838206464)), (9/147573952589676412928), by norm_num⟩
  | 3 => ⟨((-170242957/590295810358705651712), (-624438455/295147905179352825856)), (17/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((1026436371/9444732965739290427392), (3159495853/18889465931478580854784)), (15/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-4180099231/302231454903657293676544), (-2585229611/302231454903657293676544)), (11/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((5750912343/4835703278458516698824704), (653611803/4835703278458516698824704)), (29/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-5957183339/77371252455336267181195264), (2024173285/77371252455336267181195264)), (9/19342813113834066795298816), by norm_num⟩
  | 8 => ⟨((2305431551/618970019642690137449562112), (-139234217/38685626227668133590597632)), (21/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-2193031431/19807040628566084398385987584), (5794319471/19807040628566084398385987584)), (45/19807040628566084398385987584), by norm_num⟩
  | 10 => ⟨((-451178931/316912650057057350374175801344), (-2853327121/158456325028528675187087900672)), (47/316912650057057350374175801344), by norm_num⟩
  | 11 => ⟨((632013019/1267650600228229401496703205376), (4419296895/5070602400912917605986812821504)), (3/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-3590036991/81129638414606681695789005144064), (-2511643565/81129638414606681695789005144064)), (23/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1544357977/73786976294838206464), (3342554119/147573952589676412928)), (1/9223372036854775808), by norm_num⟩
  | 1 => ⟨((1672566501/590295810358705651712), (-2654192015/295147905179352825856)), (23/590295810358705651712), by norm_num⟩
  | 2 => ⟨((510728871/2361183241434822606848), (7493261459/4722366482869645213696)), (33/4722366482869645213696), by norm_num⟩
  | 3 => ⟨((-2052872741/18889465931478580854784), (-1579747927/9444732965739290427392)), (9/9444732965739290427392), by norm_num⟩
  | 4 => ⟨((2612562019/151115727451828646838272), (1615768507/151115727451828646838272)), (1/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-2156592129/1208925819614629174706176), (-490208853/2417851639229258349412352)), (13/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((2606267711/19342813113834066795298816), (-221393953/4835703278458516698824704)), (35/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((-2305431551/309485009821345068724781056), (2227747471/309485009821345068724781056)), (23/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((308395045/1237940039285380274899124224), (-1629652351/2475880078570760549798248448)), (29/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((17624177/4951760157141521099596496896), (3566658901/79228162514264337593543950336)), (1/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((-869017901/633825300114114700748351602688), (-3038266615/1267650600228229401496703205376)), (35/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((21035373/158456325028528675187087900672), (941866337/10141204801825835211973625643008)), (37/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-1466963495/162259276829213363391578010288128), (-1005758969/649037107316853453566312041152512)), (37/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1486725777/2361183241434822606848), (4718563581/2361183241434822606848)), (3/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-453981219/4722366482869645213696), (-3330338427/4722366482869645213696)), (37/9444732965739290427392), by norm_num⟩
  | 2 => ⟨((2737163655/37778931862957161709568), (2106330569/18889465931478580854784)), (15/18889465931478580854784), by norm_num⟩
  | 3 => ⟨((-1161138675/75557863725914323419136), (-2872477347/302231454903657293676544)), (35/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((4792426953/2417851639229258349412352), (68084563/302231454903657293676544)), (17/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((-3475023615/19342813113834066795298816), (1180767749/19342813113834066795298816)), (29/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((1793113429/154742504910672534362390528), (-3465384955/309485009821345068724781056)), (21/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((-274128929/618970019642690137449562112), (2897159735/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((-563973663/79228162514264337593543950336), (-3566658901/39614081257132168796771975168)), (37/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((1931150891/633825300114114700748351602688), (1687925897/316912650057057350374175801344)), (11/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-1645433621/5070602400912917605986812821504), (-2302339935/10141204801825835211973625643008)), (25/5070602400912917605986812821504), by norm_num⟩
  | 11 => ⟨((3911902653/162259276829213363391578010288128), (670505979/162259276829213363391578010288128)), (55/162259276829213363391578010288128), by norm_num⟩
  | 12 => ⟨((-3637346983/2596148429267413814265248164610048), (505219793/1298074214633706907132624082305024)), (57/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((726369951/37778931862957161709568), (5328541481/37778931862957161709568)), (9/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((-2189730925/75557863725914323419136), (-3370128911/75557863725914323419136)), (15/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((696683205/75557863725914323419136), (215435801/37778931862957161709568)), (27/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((-1916970781/1208925819614629174706176), (-871482407/4835703278458516698824704)), (33/2417851639229258349412352), by norm_num⟩
  | 4 => ⟨((3475023615/19342813113834066795298816), (-295191937/4835703278458516698824704)), (35/19342813113834066795298816), by norm_num⟩
  | 5 => ⟨((-2151736115/154742504910672534362390528), (2079230973/154742504910672534362390528)), (31/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((1535122003/2475880078570760549798248448), (-4056023629/2475880078570760549798248448)), (3/154742504910672534362390528), by norm_num⟩
  | 7 => ⟨((225589465/19807040628566084398385987584), (2853327121/19807040628566084398385987584)), (67/39614081257132168796771975168), by norm_num⟩
  | 8 => ⟨((-869017901/158456325028528675187087900672), (-3038266615/316912650057057350374175801344)), (23/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((3290867241/5070602400912917605986812821504), (2302339935/5070602400912917605986812821504)), (57/5070602400912917605986812821504), by norm_num⟩
  | 10 => ⟨((-2151546459/40564819207303340847894502572032), (-368778289/40564819207303340847894502572032)), (17/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((4364816379/1298074214633706907132624082305024), (-75782969/81129638414606681695789005144064)), (39/649037107316853453566312041152512), by norm_num⟩
  | 12 => ⟨((-3418311303/20769187434139310514121985316880384), (737032731/5192296858534827628530496329220096)), (21/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1817600/354954969), (-285760/118318323)), 0, by norm_num⟩
  | 1 => ⟨((-5137481523200/41997676672596987), (2077589504000/13999225557532329)), 0, by norm_num⟩
  | 2 => ⟨((905111709/562949953421312), (-445597163/70368744177664)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((190791243/4503599627370496), (3924476661/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-2570153537/576460752303423488), (-3504516317/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((1037994809/4611686018427387904), (2253699357/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-640894063/73786976294838206464), (-290424775/590295810358705651712)), (9/590295810358705651712), by norm_num⟩
  | 7 => ⟨((5175509591/18889465931478580854784), (-522999871/4722366482869645213696)), (7/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((-4118287939/604462909807314587353088), (4456738825/604462909807314587353088)), (11/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((495575259/4835703278458516698824704), (-1572854527/4835703278458516698824704)), (1/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((242123317/154742504910672534362390528), (7104721975/618970019642690137449562112)), (49/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-1061687721/4951760157141521099596496896), (-3268003791/9903520314283042199192993792)), (9/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((3603048495/316912650057057350374175801344), (2228346061/316912650057057350374175801344)), (53/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2590253827/134217728), (545265399/33554432)), (7/134217728), by norm_num⟩
  | 1 => ⟨((2854184907/2147483648), (978186137/4294967296)), (5/4294967296), by norm_num⟩
  | 2 => ⟨((4324419777/549755813888), (-529375391/137438953472)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-2207091559/35184372088832), (2841275217/35184372088832)), (1/8796093022208), by norm_num⟩
  | 4 => ⟨((411762665/1125899906842624), (-986596627/562949953421312)), (11/2251799813685248), by norm_num⟩
  | 5 => ⟨((1333758333/144115188075855872), (2626328233/72057594037927936)), (29/144115188075855872), by norm_num⟩
  | 6 => ⟨((-2615176113/4611686018427387904), (-3087594421/4611686018427387904)), (47/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2962331001/147573952589676412928), (2605202797/295147905179352825856)), (63/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2714729221/4722366482869645213696), (53237731/2361183241434822606848)), (81/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((4167694507/302231454903657293676544), (-139734971/18889465931478580854784)), (225/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-2478632675/9671406556917033397649408), (1715825687/4835703278458516698824704)), (157/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((666581343/309485009821345068724781056), (-3816296931/309485009821345068724781056)), (211/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((497809247/4951760157141521099596496896), (3470172021/9903520314283042199192993792)), (563/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-482726245/2251799813685248), (950607281/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((-610531977/36028797018963968), (-3139581329/36028797018963968)), (3/72057594037927936), by norm_num⟩
  | 2 => ⟨((1028061415/288230376151711744), (1401806527/288230376151711744)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((-5535972315/18446744073709551616), (-3004932477/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 4 => ⟨((640894063/36893488147419103232), (290424775/295147905179352825856)), (3/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-1811428357/2361183241434822606848), (732199819/2361183241434822606848)), (3/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((1921867705/75557863725914323419136), (-4159622903/151115727451828646838272)), (13/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((-594690311/1208925819614629174706176), (1887425433/1208925819614629174706176)), (5/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((-22699061/2417851639229258349412352), (-2664270741/38685626227668133590597632)), (1/4835703278458516698824704), by norm_num⟩
  | 9 => ⟨((1946427489/1237940039285380274899124224), (1497835071/618970019642690137449562112)), (15/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-3963353345/39614081257132168796771975168), (-1225590333/19807040628566084398385987584)), (3/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((5948418423/1267650600228229401496703205376), (169014769/316912650057057350374175801344)), (37/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((-3594367859/20282409603651670423947251286016), (610659685/10141204801825835211973625643008)), (7/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1295126899/67108864), (2181061709/134217728)), (1/16777216), by norm_num⟩
  | 1 => ⟨((5708369741/4294967296), (978185763/4294967296)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((2162210869/274877906944), (-1058749445/274877906944)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((-1103551059/17592186044416), (1420634743/17592186044416)), (5/35184372088832), by norm_num⟩
  | 4 => ⟨((823564447/2251799813685248), (-986596073/562949953421312)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((333411943/36028797018963968), (1313175289/36028797018963968)), (15/72057594037927936), by norm_num⟩
  | 6 => ⟨((-653764703/1152921504606846976), (-3087721363/4611686018427387904)), (3/288230376151711744), by norm_num⟩
  | 7 => ⟨((2962258407/147573952589676412928), (1302831797/147573952589676412928)), (127/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-2714773555/4722366482869645213696), (212300467/9444732965739290427392)), (163/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((4168169709/302231454903657293676544), (-2235028171/302231454903657293676544)), (113/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-2479600291/9671406556917033397649408), (3431052941/9671406556917033397649408)), (315/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((334016797/154742504910672534362390528), (-1908065939/154742504910672534362390528)), (423/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((124232929/1237940039285380274899124224), (216923023/618970019642690137449562112)), (141/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1566569775/2305843009213693952), (-4272172273/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 1 => ⟨((3163412751/18446744073709551616), (1717104273/18446744073709551616)), (5/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-5859602861/295147905179352825856), (-165957015/147573952589676412928)), (7/295147905179352825856), by norm_num⟩
  | 3 => ⟨((215646233/147573952589676412928), (-697333161/1180591620717411303424)), (3/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((-1372762647/18889465931478580854784), (2971159217/37778931862957161709568)), (1/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((594690311/302231454903657293676544), (-1887425433/302231454903657293676544)), (9/604462909807314587353088), by norm_num⟩
  | 6 => ⟨((968493269/19342813113834066795298816), (7104721975/19342813113834066795298816)), (5/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-1668366419/154742504910672534362390528), (-5135434529/309485009821345068724781056)), (21/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((4246450013/4951760157141521099596496896), (2626265001/4951760157141521099596496896)), (5/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((-1947398889/39614081257132168796771975168), (-442657729/79228162514264337593543950336)), (19/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((2824146175/1267650600228229401496703205376), (-239902019/316912650057057350374175801344)), (17/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((-3179477317/40564819207303340847894502572032), (1536170647/20282409603651670423947251286016)), (29/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((1134173831/649037107316853453566312041152512), (-2996658151/649037107316853453566312041152512)), (3/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1295126899/67108864), (2181061709/134217728)), (9/134217728), by norm_num⟩
  | 1 => ⟨((2854184871/2147483648), (978185763/4294967296)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((4324421727/549755813888), (-2117498891/549755813888)), (3/549755813888), by norm_num⟩
  | 3 => ⟨((-2207102067/35184372088832), (2841269465/35184372088832)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((823564283/2251799813685248), (-3946384115/2251799813685248)), (13/2251799813685248), by norm_num⟩
  | 5 => ⟨((166706007/18014398509481984), (164146883/4503599627370496)), (31/144115188075855872), by norm_num⟩
  | 6 => ⟨((-2615058581/4611686018427387904), (-3087719669/4611686018427387904)), (49/4611686018427387904), by norm_num⟩
  | 7 => ⟨((185141051/9223372036854775808), (325707337/36893488147419103232)), (1/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-5429539011/9444732965739290427392), (53076369/2361183241434822606848)), (41/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1042038713/75557863725914323419136), (-558757465/75557863725914323419136)), (227/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-309947343/1208925819614629174706176), (857761405/2417851639229258349412352)), (79/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((668009337/309485009821345068724781056), (-1908054219/154742504910672534362390528)), (53/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((496940369/4951760157141521099596496896), (3470722643/9903520314283042199192993792)), (565/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4687682289/1180591620717411303424), (265531223/1180591620717411303424)), (9/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-2070203837/2361183241434822606848), (836799793/2361183241434822606848)), (11/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((205914397/2361183241434822606848), (-3565391059/37778931862957161709568)), (3/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((-1189380623/302231454903657293676544), (3774850865/302231454903657293676544)), (5/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((-22699061/151115727451828646838272), (-5328541483/4835703278458516698824704)), (17/4835703278458516698824704), by norm_num⟩
  | 5 => ⟨((437946185/9671406556917033397649408), (337012891/4835703278458516698824704)), (3/9671406556917033397649408), by norm_num⟩
  | 6 => ⟨((-2972515009/618970019642690137449562112), (-1838385501/618970019642690137449562112)), (15/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((7010635999/19807040628566084398385987584), (99597989/2475880078570760549798248448)), (17/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((-6354328895/316912650057057350374175801344), (2159118171/316912650057057350374175801344)), (37/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((68309083/79228162514264337593543950336), (-132014665/158456325028528675187087900672)), (19/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-1871386821/81129638414606681695789005144064), (4944485949/81129638414606681695789005144064)), (19/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((-175002737/649037107316853453566312041152512), (-1106745065/324518553658426726783156020576256)), (9/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((1797725921/20769187434139310514121985316880384), (3142611125/20769187434139310514121985316880384)), (17/10384593717069655257060992658440192), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1295126899/67108864), (2181061709/134217728)), (5/67108864), by norm_num⟩
  | 1 => ⟨((2854184871/2147483648), (978185763/4294967296)), (1/536870912), by norm_num⟩
  | 2 => ⟨((4324421727/549755813888), (-2117498891/549755813888)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-2207102067/35184372088832), (2841269465/35184372088832)), (7/35184372088832), by norm_num⟩
  | 4 => ⟨((823564283/2251799813685248), (-3946384117/2251799813685248)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((1333648063/144115188075855872), (2626350133/72057594037927936)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((-2615058603/4611686018427387904), (-3087719683/4611686018427387904)), (25/2305843009213693952), by norm_num⟩
  | 7 => ⟨((740564217/36893488147419103232), (651414677/73786976294838206464)), (129/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-42418275/73786976294838206464), (53076385/2361183241434822606848)), (165/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((4168155113/302231454903657293676544), (-69844691/9444732965739290427392)), (57/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-2479578967/9671406556917033397649408), (3431046209/9671406556917033397649408)), (317/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((334004627/154742504910672534362390528), (-3816109493/309485009821345068724781056)), (425/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((993881595/9903520314283042199192993792), (1735362071/4951760157141521099596496896)), (283/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-665581889/37778931862957161709568), (2881124089/151115727451828646838272)), (15/151115727451828646838272), by norm_num⟩
  | 1 => ⟨((720836741/302231454903657293676544), (-4575576807/604462909807314587353088)), (21/604462909807314587353088), by norm_num⟩
  | 2 => ⟨((110056053/604462909807314587353088), (403677385/302231454903657293676544)), (29/4835703278458516698824704), by norm_num⟩
  | 3 => ⟨((-884739767/9671406556917033397649408), (-1361668247/9671406556917033397649408)), (17/19342813113834066795298816), by norm_num⟩
  | 4 => ⟨((4503810619/309485009821345068724781056), (1392716289/154742504910672534362390528)), (29/309485009821345068724781056), by norm_num⟩
  | 5 => ⟨((-7435523031/4951760157141521099596496896), (-105634231/618970019642690137449562112)), (23/2475880078570760549798248448), by norm_num⟩
  | 6 => ⟨((4492959825/39614081257132168796771975168), (-1526649211/39614081257132168796771975168)), (31/39614081257132168796771975168), by norm_num⟩
  | 7 => ⟨((-3974346647/633825300114114700748351602688), (3840426617/633825300114114700748351602688)), (41/633825300114114700748351602688), by norm_num⟩
  | 8 => ⟨((2126575933/10141204801825835211973625643008), (-351170877/633825300114114700748351602688)), (51/10141204801825835211973625643008), by norm_num⟩
  | 9 => ⟨((243059357/81129638414606681695789005144064), (6148583695/162259276829213363391578010288128)), (7/20282409603651670423947251286016), by norm_num⟩
  | 10 => ⟨((-2996209867/2596148429267413814265248164610048), (-654710651/324518553658426726783156020576256)), (31/1298074214633706907132624082305024), by norm_num⟩
  | 11 => ⟨((2320831995/20769187434139310514121985316880384), (3247377539/41538374868278621028243970633760768)), (65/41538374868278621028243970633760768), by norm_num⟩
  | 12 => ⟨((-1264453383/166153499473114484112975882535043072), (-433458411/332306998946228968225951765070086144)), (65/664613997892457936451903530140172288), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1295126899/67108864), (2181061709/134217728)), (11/134217728), by norm_num⟩
  | 1 => ⟨((2854184871/2147483648), (978185763/4294967296)), (9/4294967296), by norm_num⟩
  | 2 => ⟨((4324421727/549755813888), (-2117498891/549755813888)), (5/549755813888), by norm_num⟩
  | 3 => ⟨((-2207102067/35184372088832), (2841269465/35184372088832)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((823564283/2251799813685248), (-3946384117/2251799813685248)), (15/2251799813685248), by norm_num⟩
  | 5 => ⟨((1333648063/144115188075855872), (2626350133/72057594037927936)), (33/144115188075855872), by norm_num⟩
  | 6 => ⟨((-1307529301/2305843009213693952), (-3087719683/4611686018427387904)), (51/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2962256867/147573952589676412928), (1302829355/147573952589676412928)), (65/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2714769599/4722366482869645213696), (212305535/9444732965739290427392)), (83/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((2084077557/151115727451828646838272), (-2235030101/302231454903657293676544)), (229/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-1239789489/4835703278458516698824704), (3431046189/9671406556917033397649408)), (159/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((668009289/309485009821345068724781056), (-3816109469/309485009821345068724781056)), (213/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((62117595/618970019642690137449562112), (3470724129/9903520314283042199192993792)), (567/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-356565487/9671406556917033397649408), (-5231422321/19342813113834066795298816)), (9/4835703278458516698824704), by norm_num⟩
  | 1 => ⟨((2149820411/38685626227668133590597632), (1654352103/19342813113834066795298816)), (15/19342813113834066795298816), by norm_num⟩
  | 2 => ⟨((-2735941219/154742504910672534362390528), (-1692073769/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 3 => ⟨((7528126613/2475880078570760549798248448), (427799289/1237940039285380274899124224)), (33/1237940039285380274899124224), by norm_num⟩
  | 4 => ⟨((-852921769/2475880078570760549798248448), (1159246817/9903520314283042199192993792)), (35/9903520314283042199192993792), by norm_num⟩
  | 5 => ⟨((2112518103/79228162514264337593543950336), (-4082668911/158456325028528675187087900672)), (61/158456325028528675187087900672), by norm_num⟩
  | 6 => ⟨((-753571267/633825300114114700748351602688), (3982097657/1267650600228229401496703205376)), (3/79228162514264337593543950336), by norm_num⟩
  | 7 => ⟨((-110738911/5070602400912917605986812821504), (-1400660879/5070602400912917605986812821504)), (67/20282409603651670423947251286016), by norm_num⟩
  | 8 => ⟨((853178991/81129638414606681695789005144064), (2982890505/162259276829213363391578010288128)), (23/81129638414606681695789005144064), by norm_num⟩
  | 9 => ⟨((-3230887177/2596148429267413814265248164610048), (-2260376985/2596148429267413814265248164610048)), (57/2596148429267413814265248164610048), by norm_num⟩
  | 10 => ⟨((4224663807/41538374868278621028243970633760768), (724113711/41538374868278621028243970633760768)), (17/10384593717069655257060992658440192), by norm_num⟩
  | 11 => ⟨((-4285262283/664613997892457936451903530140172288), (1190427713/664613997892457936451903530140172288)), (77/664613997892457936451903530140172288), by norm_num⟩
  | 12 => ⟨((3356008415/10633823966279326983230456482242756608), (-1447198823/5316911983139663491615228241121378304)), (21/2658455991569831745807614120560689152), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1295126899/67108864), (2181061709/134217728)), (3/33554432), by norm_num⟩
  | 1 => ⟨((2854184871/2147483648), (978185763/4294967296)), (5/2147483648), by norm_num⟩
  | 2 => ⟨((4324421727/549755813888), (-2117498891/549755813888)), (3/274877906944), by norm_num⟩
  | 3 => ⟨((-2207102067/35184372088832), (2841269465/35184372088832)), (9/35184372088832), by norm_num⟩
  | 4 => ⟨((823564283/2251799813685248), (-3946384117/2251799813685248)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((1333648063/144115188075855872), (2626350133/72057594037927936)), (17/72057594037927936), by norm_num⟩
  | 6 => ⟨((-1307529301/2305843009213693952), (-3087719683/4611686018427387904)), (13/1152921504606846976), by norm_num⟩
  | 7 => ⟨((2962256867/147573952589676412928), (1302829355/147573952589676412928)), (131/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-2714769599/4722366482869645213696), (212305535/9444732965739290427392)), (167/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((2084077557/151115727451828646838272), (-2235030101/302231454903657293676544)), (115/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-2479578977/9671406556917033397649408), (3431046189/9671406556917033397649408)), (319/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((668009287/309485009821345068724781056), (-954027367/77371252455336267181195264)), (427/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((993881523/9903520314283042199192993792), (1735362063/4951760157141521099596496896)), (71/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-864620807268865/4194304), (-130220862393187/1048576)), (264308659/4194304), by norm_num⟩
  | 1 => ⟨((-1965563037/8), (-1696045565/8)), (1583/16), by norm_num⟩
  | 2 => ⟨((-2259717893/16), (-2704772211/16)), (1253/16), by norm_num⟩
  | 3 => ⟨((-206184249/4), (-1377676391/16)), (667/16), by norm_num⟩
  | 4 => ⟨((-418609813/32), (-4088640299/128)), (537/32), by norm_num⟩
  | 5 => ⟨((-1179653633/512), (-2375278667/256)), (2791/512), by norm_num⟩
  | 6 => ⟨((-234106233/1024), (-2261998683/1024)), (381/256), by norm_num⟩
  | 7 => ⟨((236556961/16384), (-1821647197/4096)), (5755/16384), by norm_num⟩
  | 8 => ⟨((838185305/65536), (-2537783119/32768)), (1199/16384), by norm_num⟩
  | 9 => ⟨((232676009/65536), (-6219747943/524288)), (7171/524288), by norm_num⟩
  | 10 => ⟨((1492311157/2097152), (-3395434097/2097152)), (4869/2097152), by norm_num⟩
  | 11 => ⟨((1971470063/16777216), (-3335589623/16777216)), (6065/16777216), by norm_num⟩
  | 12 => ⟨((564659077/33554432), (-2970186101/134217728)), (6987/134217728), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1609114732169923/10141204801825835211973625643008), (-3385982505251/10141204801825835211973625643008)), (7279/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((226536305909237/79228162514264337593543950336), (-2074241291971/316912650057057350374175801344)), (71641/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1927490974552491/39614081257132168796771975168), (-4678605897411/39614081257132168796771975168)), (161661/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((482415191111789/618970019642690137449562112), (-4981028481223/2475880078570760549798248448)), (172159/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1811366762740061/154742504910672534362390528), (-4992236029831/154742504910672534362390528)), (21575/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1587260808923577/9671406556917033397649408), (-4692163028183/9671406556917033397649408)), (162281/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1291825049576257/604462909807314587353088), (-128675761661/18889465931478580854784)), (142467/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1941555846742257/75557863725914323419136), (-6713690685275/75557863725914323419136)), (232395/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((668966122829701/2361183241434822606848), (-5055085935005/4722366482869645213696)), (175077/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1677102229788399/590295810358705651712), (-872888603579/73786976294838206464)), (242005/590295810358705651712), by norm_num⟩
  | 8 => ⟨((946606976876789/36893488147419103232), (-4388859434467/36893488147419103232)), (304431/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1901350775098373/9223372036854775808), (-9942543977339/9223372036854775808)), (345153/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1672897297052103/1152921504606846976), (-5013879924921/576460752303423488)), (348519/1152921504606846976), by norm_num⟩
  | 5 => ⟨((631982882741213/72057594037927936), (-8871133286717/144115188075855872)), (308785/144115188075855872), by norm_num⟩
  | 4 => ⟨((798197755771241/18014398509481984), (-13502852486207/36028797018963968)), (117737/9007199254740992), by norm_num⟩
  | 3 => ⟨((405352283220459/2251799813685248), (-17227455032081/9007199254740992)), (75317/1125899906842624), by norm_num⟩
  | 2 => ⟨((1247957029508973/2251799813685248), (-17762223063795/2251799813685248)), (623829/2251799813685248), by norm_num⟩
  | 1 => ⟨((656848471089831/562949953421312), (-28021137935007/1125899906842624)), (247705/281474976710656), by norm_num⟩
  | 0 => ⟨((1520900865557943/1125899906842624), (-61805849674479/1125899906842624)), (2213379/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1520900865557943/1125899906842624), (-61805849674479/1125899906842624)), (8443370823386764171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2051087726152293/1125899906842624), (-166978555900349/1125899906842624)), (3111405/562949953421312), by norm_num⟩
  | 2 => ⟨((927941950444215/281474976710656), (-304190154432363/562949953421312)), (12259177/562949953421312), by norm_num⟩
  | 3 => ⟨((1488486402367105/140737488355328), (-501413675397611/140737488355328)), (11759807/70368744177664), by norm_num⟩
  | 4 => ⟨((436134705274155/4398046511104), (-165722421960947/2199023255552)), (41568245/8796093022208), by norm_num⟩
  | 5 => ⟨((285488243115727/68719476736), (-1027122204664817/68719476736)), (56678103/34359738368), by norm_num⟩
  | 6 => ⟨((-864620807268865/4194304), (-130220862393187/1048576)), (264308659/4194304), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((1295126899/67108864), (2181061709/134217728)), (3/33554432), by norm_num⟩, 3, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((716800/22471923), (-1143040/7490641)), 0, by norm_num⟩
  | 1 => ⟨((5622530867200/504987323317929), (819331072000/168329107772643)), 0, by norm_num⟩
  | 2 => ⟨((-2414302755/4398046511104), (1697362603/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-3528081823/70368744177664), (-1906783481/35184372088832)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((1388942797/281474976710656), (-1666906947/562949953421312)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((663020349/4503599627370496), (3816510745/9007199254740992)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1249361641/36028797018963968), (644885719/144115188075855872)), (5/72057594037927936), by norm_num⟩
  | 7 => ⟨((121999277/576460752303423488), (-6265275311/2305843009213693952)), (1/144115188075855872), by norm_num⟩
  | 8 => ⟨((940488473/4611686018427387904), (274313417/4611686018427387904)), (13/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-1149733923/147573952589676412928), (1078116893/73786976294838206464)), (5/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-2338867083/2361183241434822606848), (-488446313/590295810358705651712)), (15/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((2981948277/37778931862957161709568), (-1178320631/18889465931478580854784)), (23/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((2115972063/604462909807314587353088), (4241630387/604462909807314587353088)), (35/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((21/16), (8037/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((21/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((21/16), (8037/1280)))⁻¹=value ((716800/22471923), (-1143040/7490641)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((716800/22471923), (-1143040/7490641))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((37/16), (8037/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3788800/73354969), (-10287360/73354969)), 0, by norm_num⟩
  | 1 => ⟨((45737385164800/5380951476990961), (38976749568000/5380951476990961)), 0, by norm_num⟩
  | 2 => ⟨((-3199248721/4398046511104), (1798585217/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-347972613/35184372088832), (-4332500283/70368744177664)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((5148312435/1125899906842624), (1009397249/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-1629880535/9007199254740992), (669867901/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((-2332700611/144115188075855872), (-1467884191/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 7 => ⟨((4257592125/2305843009213693952), (-702026973/1152921504606846976)), (1/144115188075855872), by norm_num⟩
  | 8 => ⟨((-91999583/18446744073709551616), (2678431369/18446744073709551616)), (13/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-741747153/73786976294838206464), (-2419898475/590295810358705651712)), (41/590295810358705651712), by norm_num⟩
  | 10 => ⟨((2583438877/4722366482869645213696), (-1414394943/2361183241434822606848)), (1/147573952589676412928), by norm_num⟩
  | 11 => ⟨((1053106393/37778931862957161709568), (4067289281/75557863725914323419136)), (25/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-5433490191/1208925819614629174706176), (682404873/1208925819614629174706176)), (39/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((37/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((37/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((37/16), (8037/1280)))⁻¹=value ((3788800/73354969), (-10287360/73354969)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3788800/73354969), (-10287360/73354969))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-32560780083200/1648427215035387), (-6788743168000/549475738345129)), 0, by norm_num⟩
  | 1 => ⟨((2896261525/1099511627776), (-1306237663/549755813888)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((1569891933/8796093022208), (1596139989/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-5664273193/140737488355328), (518933321/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((407458753/1125899906842624), (-542901393/140737488355328)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((5911842467/18014398509481984), (2274078281/18014398509481984)), (11/18014398509481984), by norm_num⟩
  | 6 => ⟨((-83273311/4503599627370496), (1790327051/72057594037927936)), (11/144115188075855872), by norm_num⟩
  | 7 => ⟨((-1884797509/1152921504606846976), (-1215305341/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 8 => ⟨((3853953475/18446744073709551616), (-790588851/9223372036854775808)), (9/9223372036854775808), by norm_num⟩
  | 9 => ⟨((667520767/295147905179352825856), (5522416809/295147905179352825856)), (29/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-3630586521/2361183241434822606848), (-1078780617/4722366482869645213696)), (3/295147905179352825856), by norm_num⟩
  | 11 => ⟨((1928841883/37778931862957161709568), (-2195142951/18889465931478580854784)), (39/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((2416358579/302231454903657293676544), (1950213975/302231454903657293676544)), (1/9444732965739290427392), by norm_num⟩
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
  | 0 => ⟨((53/16), (8037/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5427200/82570969), (-10287360/82570969)), 0, by norm_num⟩
  | 1 => ⟨((38187637964800/6817964921598961), (55831560192000/6817964921598961)), 0, by norm_num⟩
  | 2 => ⟨((-6106164613/8796093022208), (350931171/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((1255601881/70368744177664), (-3227548941/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((319586359/140737488355328), (1474289695/562949953421312)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-4283226505/18014398509481984), (498919631/9007199254740992)), (7/18014398509481984), by norm_num⟩
  | 6 => ⟨((157207737/36028797018963968), (-4793797807/288230376151711744)), (3/72057594037927936), by norm_num⟩
  | 7 => ⟨((4116695413/4611686018427387904), (471775015/576460752303423488)), (19/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-5926410741/73786976294838206464), (2118574031/73786976294838206464)), (15/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1004641971/1180591620717411303424), (-3510436981/590295810358705651712)), (23/590295810358705651712), by norm_num⟩
  | 10 => ⟨((1617369055/4722366482869645213696), (1173264681/4722366482869645213696)), (9/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-1009923063/37778931862957161709568), (1990223105/151115727451828646838272)), (7/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((35123149/604462909807314587353088), (-5072882923/2417851639229258349412352)), (43/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((53/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((53/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((53/16), (8037/1280)))⁻¹=value ((5427200/82570969), (-10287360/82570969)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((5427200/82570969), (-10287360/82570969))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3119946161/1099511627776), (906481883/549755813888)), (1/1099511627776), by norm_num⟩
  | 1 => ⟨((-582088515/4398046511104), (-6291894111/8796093022208)), (3/8796093022208), by norm_num⟩
  | 2 => ⟨((931112381/8796093022208), (593943771/35184372088832)), (3/35184372088832), by norm_num⟩
  | 3 => ⟨((-880589489/140737488355328), (1623884663/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-1092081405/1125899906842624), (-1202014501/1125899906842624)), (5/2251799813685248), by norm_num⟩
  | 5 => ⟨((611047129/4503599627370496), (-1043512833/18014398509481984)), (11/36028797018963968), by norm_num⟩
  | 6 => ⟨((37098201/36028797018963968), (1029880895/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 7 => ⟨((-2984419719/2305843009213693952), (-392516839/1152921504606846976)), (11/2305843009213693952), by norm_num⟩
  | 8 => ⟨((616087593/9223372036854775808), (-932491391/9223372036854775808)), (21/36893488147419103232), by norm_num⟩
  | 9 => ⟨((1942834937/295147905179352825856), (1244286889/147573952589676412928)), (19/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-514202679/590295810358705651712), (1461636975/4722366482869645213696)), (33/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-67093787/37778931862957161709568), (-2963187383/37778931862957161709568)), (55/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((3792292701/604462909807314587353088), (1145502391/604462909807314587353088)), (23/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((69/16), (8037/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2355200/31687923), (-1143040/10562641)), 0, by norm_num⟩
  | 1 => ⟨((3105948467200/1004124464053929), (2692087808000/334708154684643)), 0, by norm_num⟩
  | 2 => ⟨((-2419556269/4398046511104), (-144624635/1099511627776)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((3878969203/140737488355328), (-1750690705/70368744177664)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((362397845/1125899906842624), (2720014735/1125899906842624)), (5/2251799813685248), by norm_num⟩
  | 5 => ⟨((-1285130153/9007199254740992), (-651790653/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((5313627555/576460752303423488), (-725012659/144115188075855872)), (13/576460752303423488), by norm_num⟩
  | 7 => ⟨((-648836209/9223372036854775808), (3162247747/4611686018427387904)), (5/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-2544731625/73786976294838206464), (-2161124793/73786976294838206464)), (15/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1692014737/590295810358705651712), (-918030253/1180591620717411303424)), (23/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-1217379963/18889465931478580854784), (3475491405/18889465931478580854784)), (35/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-1142479903/151115727451828646838272), (-3120436599/302231454903657293676544)), (13/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((8120135301/9671406556917033397649408), (-122734227/4835703278458516698824704)), (19/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((69/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((69/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((69/16), (8037/1280)))⁻¹=value ((2355200/31687923), (-1143040/10562641)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((2355200/31687923), (-1143040/10562641))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-285591931/8796093022208), (3778994803/8796093022208)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((-1922532439/17592186044416), (-1990206181/35184372088832)), (3/35184372088832), by norm_num⟩
  | 2 => ⟨((2366681375/140737488355328), (-985969047/70368744177664)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((258049933/281474976710656), (1669303691/562949953421312)), (3/562949953421312), by norm_num⟩
  | 4 => ⟨((-6883976923/18014398509481984), (-630085877/18014398509481984)), (13/18014398509481984), by norm_num⟩
  | 5 => ⟨((179328783/9007199254740992), (-5528945395/144115188075855872)), (1/9007199254740992), by norm_num⟩
  | 6 => ⟨((1705827485/576460752303423488), (1991004543/576460752303423488)), (9/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1982509033/4611686018427387904), (1351375225/9223372036854775808)), (9/4611686018427387904), by norm_num⟩
  | 8 => ⟨((76442497/36893488147419103232), (-1602942907/36893488147419103232)), (35/147573952589676412928), by norm_num⟩
  | 9 => ⟨((271207171/73786976294838206464), (968722459/590295810358705651712)), (33/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-1211933107/4722366482869645213696), (2409906783/9444732965739290427392)), (31/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-973840039/75557863725914323419136), (-68488055/2361183241434822606848)), (53/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((822005695/302231454903657293676544), (-380864891/2417851639229258349412352)), (45/1208925819614629174706176), by norm_num⟩
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
  | 0 => ⟨((85/16), (8037/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8704000/110833369), (-10287360/110833369)), 0, by norm_num⟩
  | 1 => ⟨((15035079884800/12284035683890161), (89541181440000/12284035683890161)), 0, by norm_num⟩
  | 2 => ⟨((-3398342399/8796093022208), (-2017977677/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((3548319/137438953472), (-627807099/70368744177664)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-1350412289/2251799813685248), (3486875435/2251799813685248)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((-870378823/18014398509481984), (-3193402243/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((1732446951/288230376151711744), (1427378435/1152921504606846976)), (5/288230376151711744), by norm_num⟩
  | 7 => ⟨((-338349495/1152921504606846976), (265557749/1152921504606846976)), (15/9223372036854775808), by norm_num⟩
  | 8 => ⟨((246113131/295147905179352825856), (-1672315913/73786976294838206464)), (21/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1203115907/1180591620717411303424), (1096334177/1180591620717411303424)), (15/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-6279785349/75557863725914323419136), (51146939/4722366482869645213696)), (83/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((3337664857/1208925819614629174706176), (-5177165727/1208925819614629174706176)), (115/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1747367813/19342813113834066795298816), (5730967931/19342813113834066795298816)), (79/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((85/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((85/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((85/16), (8037/1280)))⁻¹=value ((8704000/110833369), (-10287360/110833369)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8704000/110833369), (-10287360/110833369))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2626652109/70368744177664), (646562639/17592186044416)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((-4786170835/281474976710656), (1686167983/281474976710656)), (3/140737488355328), by norm_num⟩
  | 2 => ⟨((461356441/1125899906842624), (-4149582035/1125899906842624)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((4523260239/9007199254740992), (701461657/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-4859015587/72057594037927936), (197242039/4503599627370496)), (15/72057594037927936), by norm_num⟩
  | 5 => ⟨((-398380639/288230376151711744), (-349840973/36028797018963968)), (19/576460752303423488), by norm_num⟩
  | 6 => ⟨((152455729/144115188075855872), (1446718357/4611686018427387904)), (11/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-351678995/4611686018427387904), (3253440563/36893488147419103232)), (23/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1466366795/295147905179352825856), (-3130376635/295147905179352825856)), (3/36893488147419103232), by norm_num⟩
  | 9 => ⟨((666016589/590295810358705651712), (-31155437/1180591620717411303424)), (23/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-1494127323/37778931862957161709568), (3674277555/37778931862957161709568)), (43/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-4028822497/604462909807314587353088), (-1017908883/151115727451828646838272)), (39/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((467427615/604462909807314587353088), (-1497347961/4835703278458516698824704)), (69/4835703278458516698824704), by norm_num⟩
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
  | 0 => ⟨((101/16), (8037/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((10342400/129879769), (-10287360/129879769)), 0, by norm_num⟩
  | 1 => ⟨((-567730995200/16868754395493361), (106395992064000/16868754395493361)), 0, by norm_num⟩
  | 2 => ⟨((-2185387365/8796093022208), (-2220653861/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((21869657/1099511627776), (59750513/281474976710656)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-3604439341/4503599627370496), (3509533877/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((72357075/72057594037927936), (-4519698107/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 6 => ⟨((176114479/72057594037927936), (2925098457/1152921504606846976)), (11/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-1824292837/9223372036854775808), (-155773549/36893488147419103232)), (29/36893488147419103232), by norm_num⟩
  | 8 => ⟨((593416235/73786976294838206464), (-2262324821/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-157196757/9444732965739290427392), (5890569637/9444732965739290427392)), (49/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-3632443709/151115727451828646838272), (-3852163737/151115727451828646838272)), (1/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((4754968787/2417851639229258349412352), (38071551/604462909807314587353088)), (41/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-3125623803/38685626227668133590597632), (45562399/604462909807314587353088)), (105/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((101/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((101/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((101/16), (8037/1280)))⁻¹=value ((10342400/129879769), (-10287360/129879769)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((10342400/129879769), (-10287360/129879769))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1656041667/281474976710656), (-16832681/562949953421312)), (11/1125899906842624), by norm_num⟩
  | 1 => ⟨((-1252688027/1125899906842624), (4634301875/2251799813685248)), (5/1125899906842624), by norm_num⟩
  | 2 => ⟨((-2670623413/9007199254740992), (-4070758969/9007199254740992)), (13/9007199254740992), by norm_num⟩
  | 3 => ⟨((6799835337/72057594037927936), (-628232823/72057594037927936)), (5/18014398509481984), by norm_num⟩
  | 4 => ⟨((-765633713/144115188075855872), (465240411/36028797018963968)), (7/144115188075855872), by norm_num⟩
  | 5 => ⟨((-1359337941/1152921504606846976), (-3201141297/2305843009213693952)), (9/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1946232275/9223372036854775808), (-926571307/18446744073709551616)), (11/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-1623272191/295147905179352825856), (1728018569/73786976294838206464)), (3/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-143456323/73786976294838206464), (-236310381/147573952589676412928)), (25/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((4317767333/18889465931478580854784), (-123618603/1180591620717411303424)), (25/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-120910483/302231454903657293676544), (1820854939/75557863725914323419136)), (3/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-4842347103/2417851639229258349412352), (-594676343/604462909807314587353088)), (45/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((753180571/4835703278458516698824704), (-152387833/1208925819614629174706176)), (81/19342813113834066795298816), by norm_num⟩
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
  | 0 => ⟨((117/16), (8037/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1331200/16911441), (-1143040/16911441)), 0, by norm_num⟩
  | 1 => ⟨((-77592166400/95332278898827), (1521614848000/285996836696481)), 0, by norm_num⟩
  | 2 => ⟨((-2599561487/17592186044416), (-4167691861/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((1945280655/140737488355328), (609440353/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-3109064269/4503599627370496), (41754177/140737488355328)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((2470783779/144115188075855872), (-1261263533/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((293007711/576460752303423488), (4513006669/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-3178323883/36893488147419103232), (-2208226415/36893488147419103232)), (13/36893488147419103232), by norm_num⟩
  | 8 => ⟨((6391011505/1180591620717411303424), (-327995859/590295810358705651712)), (1/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-229368087/1180591620717411303424), (3868830795/18889465931478580854784)), (39/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((109542033/151115727451828646838272), (-4420684399/302231454903657293676544)), (47/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1126190107/2417851639229258349412352), (1451144683/2417851639229258349412352)), (7/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-2987705839/77371252455336267181195264), (-1219498137/154742504910672534362390528)), (33/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((117/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((117/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((117/16), (8037/1280)))⁻¹=value ((1331200/16911441), (-1143040/16911441)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((1331200/16911441), (-1143040/16911441))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1038304165/2251799813685248), (-900751485/2251799813685248)), (7/4503599627370496), by norm_num⟩
  | 1 => ⟨((844747907/18014398509481984), (302336137/1125899906842624)), (7/9007199254740992), by norm_num⟩
  | 2 => ⟨((-583725273/9007199254740992), (-441694975/18014398509481984)), (19/72057594037927936), by norm_num⟩
  | 3 => ⟨((1472590767/144115188075855872), (-2389318323/288230376151711744)), (1/18014398509481984), by norm_num⟩
  | 4 => ⟨((383436131/1152921504606846976), (4720347427/2305843009213693952)), (23/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-4960588289/18446744073709551616), (-1824745473/18446744073709551616)), (31/18446744073709551616), by norm_num⟩
  | 6 => ⟨((4005424181/147573952589676412928), (-3454806357/147573952589676412928)), (19/73786976294838206464), by norm_num⟩
  | 7 => ⟨((515253387/590295810358705651712), (4785923707/1180591620717411303424)), (43/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-4086019203/9444732965739290427392), (-73605365/590295810358705651712)), (47/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((2429703425/75557863725914323419136), (-1261998445/37778931862957161709568)), (3/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1765786959/1208925819614629174706176), (5229188837/1208925819614629174706176)), (93/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-2068762261/4835703278458516698824704), (-608881813/9671406556917033397649408)), (89/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((878389795/38685626227668133590597632), (-1254560575/38685626227668133590597632)), (41/38685626227668133590597632), by norm_num⟩
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
  | 0 => ⟨((133/16), (8037/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((716800/9358051), (-541440/9358051)), 0, by norm_num⟩
  | 1 => ⟨((-110322483200/87573118518601), (388104192000/87573118518601)), 0, by norm_num⟩
  | 2 => ⟨((-703332085/8796093022208), (-1813532397/8796093022208)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((5081630505/562949953421312), (1571486025/281474976710656)), (3/562949953421312), by norm_num⟩
  | 4 => ⟨((-1142170209/2251799813685248), (426170497/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((2602323641/144115188075855872), (-74244775/4503599627370496)), (7/144115188075855872), by norm_num⟩
  | 6 => ⟨((-989906423/4611686018427387904), (2660382221/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 7 => ⟨((-116012927/4611686018427387904), (-1859318307/36893488147419103232)), (9/36893488147419103232), by norm_num⟩
  | 8 => ⟨((5717340357/2361183241434822606848), (2839042613/2361183241434822606848)), (5/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-2408775417/18889465931478580854784), (453329873/18889465931478580854784)), (11/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((316552943/75557863725914323419136), (-1392729503/302231454903657293676544)), (3/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((-525036287/19342813113834066795298816), (2879037457/9671406556917033397649408)), (13/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-2343484617/309485009821345068724781056), (-3771438087/309485009821345068724781056)), (113/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((133/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((133/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((133/16), (8037/1280)))⁻¹=value ((716800/9358051), (-541440/9358051)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((716800/9358051), (-541440/9358051))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((877288799/72057594037927936), (-2065110475/36028797018963968)), (1/4503599627370496), by norm_num⟩
  | 1 => ⟨((22878653/1125899906842624), (2940351647/144115188075855872)), (17/144115188075855872), by norm_num⟩
  | 2 => ⟨((-4468201257/576460752303423488), (30227347/18014398509481984)), (3/72057594037927936), by norm_num⟩
  | 3 => ⟨((1271380049/2305843009213693952), (-873142043/576460752303423488)), (11/1152921504606846976), by norm_num⟩
  | 4 => ⟨((3073566831/18446744073709551616), (1950942203/9223372036854775808)), (17/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-5729077025/147573952589676412928), (693754723/147573952589676412928)), (23/73786976294838206464), by norm_num⟩
  | 6 => ⟨((2450087631/1180591620717411303424), (-5509454471/1180591620717411303424)), (29/590295810358705651712), by norm_num⟩
  | 7 => ⟨((3371100153/9444732965739290427392), (1177695811/2361183241434822606848)), (17/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-5172025945/75557863725914323419136), (506471739/75557863725914323419136)), (19/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((1788030955/604462909807314587353088), (-4023427467/604462909807314587353088)), (5/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1067271823/2417851639229258349412352), (2840044003/4835703278458516698824704)), (79/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-2719884667/38685626227668133590597632), (789701671/77371252455336267181195264)), (77/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((1399048881/618970019642690137449562112), (-481447709/77371252455336267181195264)), (9/38685626227668133590597632), by norm_num⟩
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
  | 0 => ⟨((149/16), (8037/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((15257600/206679769), (-10287360/206679769)), 0, by norm_num⟩
  | 1 => ⟨((-63482290995200/42716526913893361), (156960423936000/42716526913893361)), 0, by norm_num⟩
  | 2 => ⟨((-1287477809/35184372088832), (-6073335437/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((3178730453/562949953421312), (3074118979/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-6202783505/18014398509481984), (-1099512219/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((2050528083/144115188075855872), (-1820569067/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((-848528627/2305843009213693952), (2708211107/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-152299133/147573952589676412928), (-1137586731/36893488147419103232)), (15/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1901870761/2361183241434822606848), (1313348037/1180591620717411303424)), (1/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-2169143181/37778931862957161709568), (-198489179/9444732965739290427392)), (33/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((6388803357/2417851639229258349412352), (-197423925/302231454903657293676544)), (33/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-1572094619/19342813113834066795298816), (869186595/9671406556917033397649408)), (67/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((236234831/309485009821345068724781056), (-6610590873/1237940039285380274899124224)), (67/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((149/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((149/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((149/16), (8037/1280)))⁻¹=value ((15257600/206679769), (-10287360/206679769)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((15257600/206679769), (-10287360/206679769))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1126525285/576460752303423488), (-5577110539/1152921504606846976)), (33/1152921504606846976), by norm_num⟩
  | 1 => ⟨((3122287637/1152921504606846976), (1440390247/2305843009213693952)), (37/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-2786347255/4611686018427387904), (1277477787/2305843009213693952)), (7/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-60353231/2305843009213693952), (-6446998827/36893488147419103232)), (27/18446744073709551616), by norm_num⟩
  | 4 => ⟨((2076630425/73786976294838206464), (1936229519/147573952589676412928)), (43/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-4719138329/1180591620717411303424), (2946163421/1180591620717411303424)), (61/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((7508989/1180591620717411303424), (-754865441/1180591620717411303424)), (39/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((5051309473/75557863725914323419136), (3234927403/75557863725914323419136)), (47/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-155890085/18889465931478580854784), (1204525081/302231454903657293676544)), (27/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((447276217/4835703278458516698824704), (-4792700759/4835703278458516698824704)), (29/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((1606824061/19342813113834066795298816), (2331592997/38685626227668133590597632)), (59/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-1431125785/154742504910672534362390528), (633784911/154742504910672534362390528)), (233/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((478214719/4951760157141521099596496896), (-4720094211/4951760157141521099596496896)), (111/2475880078570760549798248448), by norm_num⟩
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
  | 0 => ⟨((165/16), (8037/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5632000/79611123), (-1143040/26537041)), 0, by norm_num⟩
  | 1 => ⟨((-9980280012800/6337930905321129), (6437601280000/2112643635107043)), 0, by norm_num⟩
  | 2 => ⟨((-174624663/17592186044416), (-2492781533/17592186044416)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((478904593/140737488355328), (1350618975/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-4029915619/18014398509481984), (-1737342529/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((2879400737/288230376151711744), (-810811549/576460752303423488)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((-2979804699/9223372036854775808), (1221643963/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((211124583/36893488147419103232), (-4819166887/295147905179352825856)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1409465829/9444732965739290427392), (6618837953/9444732965739290427392)), (9/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-1539227183/75557863725914323419136), (-3260254765/151115727451828646838272)), (17/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1432848011/1208925819614629174706176), (1568698465/4835703278458516698824704)), (63/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-3784240579/77371252455336267181195264), (1087156761/77371252455336267181195264)), (29/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((3534149759/2475880078570760549798248448), (-3838555461/2475880078570760549798248448)), (107/2475880078570760549798248448), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((165/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((165/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((165/16), (8037/1280)))⁻¹=value ((5632000/79611123), (-1143040/26537041)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((5632000/79611123), (-1143040/26537041))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-799229075/2305843009213693952), (-594999917/2305843009213693952)), (31/9223372036854775808), by norm_num⟩
  | 1 => ⟨((544892591/2305843009213693952), (-652970391/9223372036854775808)), (37/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-1897325849/73786976294838206464), (1343134591/18446744073709551616)), (29/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-1481221053/147573952589676412928), (-2119765871/147573952589676412928)), (59/295147905179352825856), by norm_num⟩
  | 4 => ⟨((3802113203/1180591620717411303424), (18576927/2361183241434822606848)), (49/1180591620717411303424), by norm_num⟩
  | 5 => ⟨((-2733097039/9444732965739290427392), (3945989197/9444732965739290427392)), (9/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((-1953405673/75557863725914323419136), (-5025948501/75557863725914323419136)), (95/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((5392212327/604462909807314587353088), (1175856247/604462909807314587353088)), (117/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((-3721566253/4835703278458516698824704), (3678675579/4835703278458516698824704)), (17/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-979065783/38685626227668133590597632), (-2274368297/19342813113834066795298816)), (75/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((3682973743/309485009821345068724781056), (665340291/154742504910672534362390528)), (39/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-2454565307/2475880078570760549798248448), (30651245/38685626227668133590597632)), (39/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-642642599/39614081257132168796771975168), (-4792155005/39614081257132168796771975168)), (151/19807040628566084398385987584), by norm_num⟩
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
  | 0 => ⟨((181/16), (8037/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((18534400/274263769), (-10287360/274263769)), 0, by norm_num⟩
  | 1 => ⟨((-118847103795200/75220614986085361), (190670045184000/75220614986085361)), 0, by norm_num⟩
  | 2 => ⟨((411476337/70368744177664), (-4056104137/35184372088832)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((1105895105/562949953421312), (281823441/70368744177664)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-39825581/281474976710656), (-443524657/4503599627370496)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((955167493/144115188075855872), (777184439/1152921504606846976)), (11/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-545543539/2305843009213693952), (1872783061/18446744073709551616)), (5/9223372036854775808), by norm_num⟩
  | 7 => ⟨((3595055025/590295810358705651712), (-4644202647/590295810358705651712)), (9/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-1099998203/18889465931478580854784), (448696287/1180591620717411303424)), (31/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-779783597/151115727451828646838272), (-4211336887/302231454903657293676544)), (27/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((131678313/302231454903657293676544), (113049517/302231454903657293676544)), (23/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-1681795707/77371252455336267181195264), (-345679611/77371252455336267181195264)), (79/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((4051831427/4951760157141521099596496896), (-635550149/2475880078570760549798248448)), (67/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((181/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((181/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((181/16), (8037/1280)))⁻¹=value ((18534400/274263769), (-10287360/274263769)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18534400/274263769), (-10287360/274263769))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1221259945/36893488147419103232), (-654787879/147573952589676412928)), (53/147573952589676412928), by norm_num⟩
  | 1 => ⟨((4284296549/295147905179352825856), (-4167156775/295147905179352825856)), (67/295147905179352825856), by norm_num⟩
  | 2 => ⟨((14161743/18446744073709551616), (3916200263/590295810358705651712)), (27/295147905179352825856), by norm_num⟩
  | 3 => ⟨((-201799079/147573952589676412928), (-1898379181/2361183241434822606848)), (59/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((5274260933/18889465931478580854784), (-2243045993/18889465931478580854784)), (101/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-838100125/75557863725914323419136), (456534339/9444732965739290427392)), (77/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((-2885637719/604462909807314587353088), (-25343949/4722366482869645213696)), (13/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((4534784541/4835703278458516698824704), (-269194923/2417851639229258349412352)), (65/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((-513291187/9671406556917033397649408), (1965727867/19342813113834066795298816)), (77/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-241139943/38685626227668133590597632), (-3536172811/309485009821345068724781056)), (173/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((6884897829/4951760157141521099596496896), (561382877/4951760157141521099596496896)), (367/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-3422051109/39614081257132168796771975168), (1118852629/9903520314283042199192993792)), (187/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-765932247/158456325028528675187087900672), (-257571539/19807040628566084398385987584)), (367/316912650057057350374175801344), by norm_num⟩
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
  | 0 => ⟨((197/16), (8037/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((20172800/312970969), (-10287360/312970969)), 0, by norm_num⟩
  | 1 => ⟨((-150556042035200/97950827436798961), (207524855808000/97950827436798961)), 0, by norm_num⟩
  | 2 => ⟨((517769511/35184372088832), (-1645602071/17592186044416)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((1196938675/1125899906842624), (3666501567/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-1581340947/18014398509481984), (-1575871755/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((2459608819/576460752303423488), (793526489/576460752303423488)), (7/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-5907818441/36893488147419103232), (950399227/36893488147419103232)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((2796429105/590295810358705651712), (-510897665/147573952589676412928)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-1809172389/18889465931478580854784), (447279943/2361183241434822606848)), (17/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-8040761/302231454903657293676544), (-2320847039/302231454903657293676544)), (7/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((153609095/1208925819614629174706176), (4778489465/19342813113834066795298816)), (45/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-315485013/38685626227668133590597632), (-454430643/77371252455336267181195264)), (9/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((7117674359/19807040628566084398385987584), (547245169/9903520314283042199192993792)), (113/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((197/16), (8037/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((197/16), (8037/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((197/16), (8037/1280)))⁻¹=value ((20172800/312970969), (-10287360/312970969)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((20172800/312970969), (-10287360/312970969))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5382273989/2361183241434822606848), (946931481/1180591620717411303424)), (83/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((627860259/1180591620717411303424), (-214054503/147573952589676412928)), (7/295147905179352825856), by norm_num⟩
  | 2 => ⟨((323780017/1180591620717411303424), (33784945/73786976294838206464)), (93/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((-4946423013/37778931862957161709568), (-323447165/18889465931478580854784)), (107/37778931862957161709568), by norm_num⟩
  | 4 => ⟨((2810001169/151115727451828646838272), (-2785324929/151115727451828646838272)), (95/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((698209207/1208925819614629174706176), (5294920199/1208925819614629174706176)), (37/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-2779113911/4835703278458516698824704), (-775319735/2417851639229258349412352)), (13/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((3117169355/38685626227668133590597632), (-358923351/9671406556917033397649408)), (33/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((-1279610105/618970019642690137449562112), (418392847/38685626227668133590597632)), (79/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-1099871051/1237940039285380274899124224), (-1131613367/1237940039285380274899124224)), (181/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((1356805719/9903520314283042199192993792), (-466198853/19807040628566084398385987584)), (391/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((-233048385/39614081257132168796771975168), (2080779153/158456325028528675187087900672)), (405/316912650057057350374175801344), by norm_num⟩
  | 12 => ⟨((-242509601/316912650057057350374175801344), (-3040311051/2535301200456458802993406410752)), (403/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2504711085/4398046511104), (517836493/4398046511104)), (453/2199023255552), by norm_num⟩
  | 1 => ⟨((3873274693/8796093022208), (4566544293/8796093022208)), (499/1099511627776), by norm_num⟩
  | 2 => ⟨((86541401/4398046511104), (6812526037/17592186044416)), (2237/4398046511104), by norm_num⟩
  | 3 => ⟨((-1393278811/17592186044416), (4188106013/35184372088832)), (13481/35184372088832), by norm_num⟩
  | 4 => ⟨((-5035846735/140737488355328), (965604383/70368744177664)), (7673/35184372088832), by norm_num⟩
  | 5 => ⟨((-4369302219/562949953421312), (-992557767/562949953421312)), (14101/140737488355328), by norm_num⟩
  | 6 => ⟨((-4300702969/4503599627370496), (-4213092023/4503599627370496)), (43627/1125899906842624), by norm_num⟩
  | 7 => ⟨((-1957724363/36028797018963968), (-1622301677/9007199254740992)), (7311/562949953421312), by norm_num⟩
  | 8 => ⟨((125675401/36028797018963968), (-6549669343/288230376151711744)), (555349/144115188075855872), by norm_num⟩
  | 9 => ⟨((3012791261/2305843009213693952), (-1248611223/576460752303423488)), (2372401/2305843009213693952), by norm_num⟩
  | 10 => ⟨((3702360139/18446744073709551616), (-2967575037/18446744073709551616)), (4617761/18446744073709551616), by norm_num⟩
  | 11 => ⟨((1689617631/73786976294838206464), (-1208606919/147573952589676412928)), (8273183/147573952589676412928), by norm_num⟩
  | 12 => ⟨((2513425103/1180591620717411303424), (-71828869/1180591620717411303424)), (3438457/295147905179352825856), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2504711085/4398046511104), (517836493/4398046511104)), (1813/8796093022208), by norm_num⟩
  | 1 => ⟨((3873274693/8796093022208), (4566544293/8796093022208)), (3993/8796093022208), by norm_num⟩
  | 2 => ⟨((86541401/4398046511104), (6812526037/17592186044416)), (8949/17592186044416), by norm_num⟩
  | 3 => ⟨((-1393278811/17592186044416), (4188106013/35184372088832)), (13483/35184372088832), by norm_num⟩
  | 4 => ⟨((-5035846735/140737488355328), (965604383/70368744177664)), (15349/70368744177664), by norm_num⟩
  | 5 => ⟨((-4369302219/562949953421312), (-992557767/562949953421312)), (56427/562949953421312), by norm_num⟩
  | 6 => ⟨((-4300702969/4503599627370496), (-4213092023/4503599627370496)), (174689/4503599627370496), by norm_num⟩
  | 7 => ⟨((-1957724363/36028797018963968), (-1622301677/9007199254740992)), (234673/18014398509481984), by norm_num⟩
  | 8 => ⟨((125675401/36028797018963968), (-6549669343/288230376151711744)), (280557/72057594037927936), by norm_num⟩
  | 9 => ⟨((3012791261/2305843009213693952), (-1248611223/576460752303423488)), (2464635/2305843009213693952), by norm_num⟩
  | 10 => ⟨((3702360139/18446744073709551616), (-2967575037/18446744073709551616)), (5355631/18446744073709551616), by norm_num⟩
  | 11 => ⟨((1689617631/73786976294838206464), (-1208606919/147573952589676412928)), (7088071/73786976294838206464), by norm_num⟩
  | 12 => ⟨((2513425103/1180591620717411303424), (-71828869/1180591620717411303424)), (60977493/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨31,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile031Gamma

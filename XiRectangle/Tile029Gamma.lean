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
namespace Reinmann.XiRectangle.Tile029Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨29,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (1551/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (1551/128))
  have he : value ((5/8), (1551/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((21/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((213/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((290816/4673355), (-132352/4673355)), 0, by norm_num⟩
  | 1 => ⟨((-11176148992/7280082318675), (38490079232/21840246956025)), 0, by norm_num⟩
  | 2 => ⟨((802566379/35184372088832), (-673538935/8796093022208)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((210859661/562949953421312), (380764937/140737488355328)), (1/1125899906842624), by norm_num⟩
  | 4 => ⟨((-900086099/18014398509481984), (-1420897649/18014398509481984)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((3080052491/1152921504606846976), (2013741821/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((-1989579311/18446744073709551616), (-609334353/36893488147419103232)), (7/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1059495471/295147905179352825856), (-598191959/590295810358705651712)), (11/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-3677457879/37778931862957161709568), (3111539231/37778931862957161709568)), (17/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((2251556409/1208925819614629174706176), (-2382193175/604462909807314587353088)), (13/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((-41447853/19342813113834066795298816), (5763937127/38685626227668133590597632)), (39/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-2529270587/1237940039285380274899124224), (-2888231777/618970019642690137449562112)), (57/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((320985429/2475880078570760549798248448), (2302643825/19807040628566084398385987584)), (21/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((213/16), (1551/256)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((213/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((213/16), (1551/256)))⁻¹=value ((290816/4673355), (-132352/4673355)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((290816/4673355), (-132352/4673355))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2880658825/1073741824), (458586171/1073741824)), (1/1073741824), by norm_num⟩
  | 1 => ⟨((145408/4673355), (-66176/4673355)), 0, by norm_num⟩
  | 2 => ⟨((-2794037248/7280082318675), (9622519808/21840246956025)), 0, by norm_num⟩
  | 3 => ⟨((1070088505/281474976710656), (-3592207653/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((210859661/4503599627370496), (380764937/1125899906842624)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((-2880275517/576460752303423488), (-4546872477/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 6 => ⟨((4106736655/18446744073709551616), (2684989095/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((-2273804927/295147905179352825856), (-348191059/295147905179352825856)), (9/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1059495471/4722366482869645213696), (-598191959/9444732965739290427392)), (11/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-408606431/75557863725914323419136), (1382906325/302231454903657293676544)), (1/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1801245127/19342813113834066795298816), (-476438635/2417851639229258349412352)), (21/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-30143893/309485009821345068724781056), (2095977137/309485009821345068724781056)), (29/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((-1686180391/19807040628566084398385987584), (-3850975703/19807040628566084398385987584)), (39/19807040628566084398385987584), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-7005/276736), (33/4096)), 0, by norm_num⟩
  | 45 => ⟨((19116370261/816127672320), (-131901/12058624)), 0, by norm_num⟩
  | 44 => ⟨((-51755178836903/2298215525253120), (253839059111/23708219473920)), 0, by norm_num⟩
  | 43 => ⟨((789729931/34359738368), (-354790865/34359738368)), (1/137438953472), by norm_num⟩
  | 42 => ⟨((-3265572403/137438953472), (717269159/68719476736)), (1/68719476736), by norm_num⟩
  | 41 => ⟨((1678739203/68719476736), (-1477506143/137438953472)), (1/68719476736), by norm_num⟩
  | 40 => ⟨((-3440449695/137438953472), (1519524715/137438953472)), (1/68719476736), by norm_num⟩
  | 39 => ⟨((3526577331/137438953472), (-779000303/68719476736)), (1/68719476736), by norm_num⟩
  | 38 => ⟨((-3619213555/137438953472), (1597076625/137438953472)), (1/68719476736), by norm_num⟩
  | 37 => ⟨((3717728683/137438953472), (-1638718003/137438953472)), (1/68719476736), by norm_num⟩
  | 36 => ⟨((-955422633/34359738368), (105188525/8589934592)), (1/68719476736), by norm_num⟩
  | 35 => ⟨((3931457283/137438953472), (-1729823559/137438953472)), (1/68719476736), by norm_num⟩
  | 34 => ⟨((-4047665489/137438953472), (1779250209/137438953472)), (1/68719476736), by norm_num⟩
  | 33 => ⟨((4170963447/137438953472), (-915777993/68719476736)), (1/68719476736), by norm_num⟩
  | 32 => ⟨((-4302017959/137438953472), (943514993/68719476736)), (1/68719476736), by norm_num⟩
  | 31 => ⟨((1110393113/34359738368), (-1945973263/137438953472)), (1/68719476736), by norm_num⟩
  | 30 => ⟨((-4590477481/137438953472), (1004358945/68719476736)), (1/68719476736), by norm_num⟩
  | 29 => ⟨((4749705669/137438953472), (-2075641719/137438953472)), (1/68719476736), by norm_num⟩
  | 28 => ⟨((-4920369305/137438953472), (2147176513/137438953472)), (1/68719476736), by norm_num⟩
  | 27 => ⟨((159492047/4294967296), (-2223815975/137438953472)), (1/68719476736), by norm_num⟩
  | 26 => ⟨((-1325327125/34359738368), (576531657/34359738368)), (1/68719476736), by norm_num⟩
  | 25 => ⟨((689346191/17179869184), (-1197380933/68719476736)), (1/68719476736), by norm_num⟩
  | 24 => ⟨((-2873063213/68719476736), (2490479419/137438953472)), (1/68719476736), by norm_num⟩
  | 23 => ⟨((1499431539/34359738368), (-648540767/34359738368)), (1/68719476736), by norm_num⟩
  | 22 => ⟨((-392021529/8589934592), (1353424983/68719476736)), (1/68719476736), by norm_num⟩
  | 21 => ⟨((1643322103/34359738368), (-1414882695/68719476736)), (1/34359738368), by norm_num⟩
  | 20 => ⟨((-1726132445/34359738368), (1482183705/68719476736)), (1/34359738368), by norm_num⟩
  | 19 => ⟨((3635440375/68719476736), (-778101225/34359738368)), (1/34359738368), by norm_num⟩
  | 18 => ⟨((-3839114181/68719476736), (1637996901/68719476736)), (1/34359738368), by norm_num⟩
  | 17 => ⟨((4066926009/68719476736), (-864429683/34359738368)), (1/34359738368), by norm_num⟩
  | 16 => ⟨((-135107195/2147483648), (228798141/8589934592)), (1/34359738368), by norm_num⟩
  | 15 => ⟨((4614402129/68719476736), (-486141679/17179869184)), (1/34359738368), by norm_num⟩
  | 14 => ⟨((-1236818919/17179869184), (518481421/17179869184)), (1/34359738368), by norm_num⟩
  | 13 => ⟨((666473029/8589934592), (-555425137/17179869184)), (1/34359738368), by norm_num⟩
  | 12 => ⟨((-2890461189/34359738368), (74753779/2147483648)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((1578108477/17179869184), (-80963057/2147483648)), (1/17179869184), by norm_num⟩
  | 10 => ⟨((-1737798691/17179869184), (1412727985/34359738368)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((3866593897/34359738368), (-776685595/17179869184)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((-1089057857/8589934592), (862525209/17179869184)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((2493516785/17179869184), (-242411793/4294967296)), (1/17179869184), by norm_num⟩
  | 6 => ⟨((-5829951569/34359738368), (1107070749/17179869184)), (1/17179869184), by norm_num⟩
  | 5 => ⟨((3506392931/17179869184), (-1289744169/17179869184)), (1/8589934592), by norm_num⟩
  | 4 => ⟨((-2197777243/8589934592), (1544374859/17179869184)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((1470035653/4294967296), (-240479581/2147483648)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((-4424565377/8589934592), (1274865821/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((4425189963/4294967296), (-944776439/4294967296)), (1/2147483648), by norm_num⟩
  | 0 => ⟨((-771085175/8589934592), (3668689367/8589934592)), (1/2147483648), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-43/256), (1551/4096)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-43/256), (1551/4096)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-43/256), (1551/4096))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((2880658825/1073741824), (458586171/1073741824)), (1/1073741824), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((213/16), (1551/256))) (z:=((-43/256), (1551/4096))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((2880658825/1073741824), (458586171/1073741824))) (r:=(1/1073741824)) (by norm_num) ?_ hs
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
  | 0 => ⟨((205/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((133320523/4194304), (2916047109/134217728)), (1/33554432), by norm_num⟩
  | 1 => ⟨((3920991963/2147483648), (118447663/536870912)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((58025618944/7280082318675), (-82127245024/21840246956025)), 0, by norm_num⟩
  | 3 => ⟨((-289682567/4398046511104), (2808140033/35184372088832)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((254343397/562949953421312), (-3972972589/2251799813685248)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((1034785353/144115188075855872), (2721075127/72057594037927936)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((-2433525757/4611686018427387904), (-3366871955/4611686018427387904)), (23/2305843009213693952), by norm_num⟩
  | 7 => ⟨((2915157893/147573952589676412928), (1621327249/147573952589676412928)), (17/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1401776331/2361183241434822606848), (-397286141/9444732965739290427392)), (177/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((2292153933/151115727451828646838272), (-1754905531/302231454903657293676544)), (15/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-766348111/2417851639229258349412352), (3165527391/9671406556917033397649408)), (327/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1325068405/309485009821345068724781056), (-1909997587/154742504910672534362390528)), (443/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((381353245/9903520314283042199192993792), (7514760211/19807040628566084398385987584)), (1201/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-213/16), (-1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((77483851/4194304), (2102876421/134217728)), (1/33554432), by norm_num⟩
  | 1 => ⟨((2847250139/2147483648), (118447663/536870912)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((58025618944/7280082318675), (-82127245024/21840246956025)), 0, by norm_num⟩
  | 3 => ⟨((-289682567/4398046511104), (2808140033/35184372088832)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((254343397/562949953421312), (-3972972589/2251799813685248)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((1034785353/144115188075855872), (2721075127/72057594037927936)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((-2433525757/4611686018427387904), (-3366871955/4611686018427387904)), (23/2305843009213693952), by norm_num⟩
  | 7 => ⟨((2915157893/147573952589676412928), (1621327249/147573952589676412928)), (17/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1401776331/2361183241434822606848), (-397286141/9444732965739290427392)), (177/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((2292153933/151115727451828646838272), (-1754905531/302231454903657293676544)), (15/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-766348111/2417851639229258349412352), (3165527391/9671406556917033397649408)), (327/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1325068405/309485009821345068724781056), (-1909997587/154742504910672534362390528)), (443/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((381353245/9903520314283042199192993792), (7514760211/19807040628566084398385987584)), (1201/19807040628566084398385987584), by norm_num⟩
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
  | 0 => ⟨((1301410537/67108864), (2102876421/134217728)), (5/134217728), by norm_num⟩
  | 1 => ⟨((2847250139/2147483648), (118447663/536870912)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((58025618944/7280082318675), (-82127245024/21840246956025)), 0, by norm_num⟩
  | 3 => ⟨((-289682567/4398046511104), (2808140033/35184372088832)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((254343397/562949953421312), (-3972972589/2251799813685248)), (7/1125899906842624), by norm_num⟩
  | 5 => ⟨((1034785353/144115188075855872), (2721075127/72057594037927936)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((-2433525757/4611686018427387904), (-3366871955/4611686018427387904)), (23/2305843009213693952), by norm_num⟩
  | 7 => ⟨((2915157893/147573952589676412928), (1621327249/147573952589676412928)), (17/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1401776331/2361183241434822606848), (-397286141/9444732965739290427392)), (177/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((2292153933/151115727451828646838272), (-1754905531/302231454903657293676544)), (15/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-766348111/2417851639229258349412352), (3165527391/9671406556917033397649408)), (327/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((1325068405/309485009821345068724781056), (-1909997587/154742504910672534362390528)), (443/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((381353245/9903520314283042199192993792), (7514760211/19807040628566084398385987584)), (1201/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((22352297984/7280082318675), (-76980158464/21840246956025)), 0, by norm_num⟩
  | 1 => ⟨((-802566379/8796093022208), (673538935/2199023255552)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-632578983/281474976710656), (-1142294811/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((900086099/2251799813685248), (1420897649/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 4 => ⟨((-3850065613/144115188075855872), (-2517177277/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((5968737933/4611686018427387904), (914001531/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-927058537/18446744073709551616), (130854491/9223372036854775808)), (7/73786976294838206464), by norm_num⟩
  | 7 => ⟨((3677457879/2361183241434822606848), (-1555769615/1180591620717411303424)), (11/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-2533000961/75557863725914323419136), (5359934643/75557863725914323419136)), (9/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((51809817/1208925819614629174706176), (-112576897/37778931862957161709568)), (15/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((217359191/4835703278458516698824704), (3971318693/38685626227668133590597632)), (23/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-3851825147/1237940039285380274899124224), (-1726982869/618970019642690137449562112)), (35/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((1462550389/9903520314283042199192993792), (1834722619/39614081257132168796771975168)), (27/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((802566379/8796093022208), (-673538935/2199023255552)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((632578983/140737488355328), (1142294811/35184372088832)), (1/70368744177664), by norm_num⟩
  | 2 => ⟨((-2700258297/2251799813685248), (-4262692947/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 3 => ⟨((3850065613/36028797018963968), (2517177277/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-466307651/72057594037927936), (-571250957/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((5562351223/18446744073709551616), (-1570253891/18446744073709551616)), (1/2305843009213693952), by norm_num⟩
  | 6 => ⟨((-804443911/73786976294838206464), (1361298413/147573952589676412928)), (1/36893488147419103232), by norm_num⟩
  | 7 => ⟨((2533000961/9444732965739290427392), (-2679967321/4722366482869645213696)), (7/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-116572089/302231454903657293676544), (1013192073/37778931862957161709568)), (3/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-2173591909/4835703278458516698824704), (-4964148367/4835703278458516698824704)), (21/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((662032447/19342813113834066795298816), (2374601445/77371252455336267181195264)), (17/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-2193825583/1237940039285380274899124224), (-1376041965/2475880078570760549798248448)), (7/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((5824137035/79228162514264337593543950336), (-721124023/79228162514264337593543950336)), (43/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-210859661/70368744177664), (-380764937/17592186044416)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((900086099/562949953421312), (1420897649/562949953421312)), (1/562949953421312), by norm_num⟩
  | 2 => ⟨((-3850065613/18014398509481984), (-2517177277/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((2486974139/144115188075855872), (761667943/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 4 => ⟨((-2317646343/2305843009213693952), (1308544909/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 5 => ⟨((804443911/18446744073709551616), (-1361298413/36893488147419103232)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-738791947/590295810358705651712), (3126628541/1180591620717411303424)), (1/147573952589676412928), by norm_num⟩
  | 7 => ⟨((38857363/18889465931478580854784), (-337730691/2361183241434822606848)), (7/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((407548483/151115727451828646838272), (3723111275/604462909807314587353088)), (13/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-2206774823/9671406556917033397649408), (-3957669075/19342813113834066795298816)), (3/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((4022013569/309485009821345068724781056), (630685901/154742504910672534362390528)), (5/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-2912068517/4951760157141521099596496896), (360562011/4951760157141521099596496896)), (35/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((213753025/9903520314283042199192993792), (-1049086351/79228162514264337593543950336)), (29/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-900086099/1125899906842624), (-1420897649/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((3850065613/18014398509481984), (2517177277/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((-466307651/18014398509481984), (-571250957/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 3 => ⟨((2317646343/1152921504606846976), (-1308544909/2305843009213693952)), (7/2305843009213693952), by norm_num⟩
  | 4 => ⟨((-1005554889/9223372036854775808), (212702877/2305843009213693952)), (5/18446744073709551616), by norm_num⟩
  | 5 => ⟨((2216375841/590295810358705651712), (-1172485703/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 6 => ⟨((-34000193/4722366482869645213696), (2364114837/4722366482869645213696)), (13/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-407548483/37778931862957161709568), (-3723111275/151115727451828646838272)), (13/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((620655419/604462909807314587353088), (2226188855/2417851639229258349412352)), (3/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-5027516961/77371252455336267181195264), (-3079521/151115727451828646838272)), (23/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((4004094211/1237940039285380274899124224), (-495772765/1237940039285380274899124224)), (21/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-641259075/4951760157141521099596496896), (786814763/9903520314283042199192993792)), (37/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((2454450619/633825300114114700748351602688), (-3638781777/633825300114114700748351602688)), (1/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3080052491/36028797018963968), (-2013741821/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((5968737933/288230376151711744), (914001531/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 2 => ⟨((-5562351223/2305843009213693952), (1570253891/2305843009213693952)), (5/1152921504606846976), by norm_num⟩
  | 3 => ⟨((804443911/4611686018427387904), (-1361298413/9223372036854775808)), (9/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-1108187921/147573952589676412928), (1172485703/73786976294838206464)), (3/73786976294838206464), by norm_num⟩
  | 5 => ⟨((81600463/4722366482869645213696), (-5673875609/4722366482869645213696)), (1/295147905179352825856), by norm_num⟩
  | 6 => ⟨((142641969/4722366482869645213696), (2606177893/37778931862957161709568)), (19/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((-1986097341/604462909807314587353088), (-445237771/151115727451828646838272)), (21/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((4524765265/19342813113834066795298816), (1419043277/19342813113834066795298816)), (21/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-4004094211/309485009821345068724781056), (495772765/309485009821345068724781056)), (21/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((1410769965/2475880078570760549798248448), (-865496239/2475880078570760549798248448)), (5/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-368167593/19807040628566084398385987584), (1091634533/39614081257132168796771975168)), (9/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((675709663/2535301200456458802993406410752), (-4024885071/2535301200456458802993406410752)), (1/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1989579311/288230376151711744), (-609334353/576460752303423488)), (7/576460752303423488), by norm_num⟩
  | 1 => ⟨((3708234149/2305843009213693952), (-1046835927/2305843009213693952)), (7/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-804443911/4611686018427387904), (1361298413/9223372036854775808)), (5/9223372036854775808), by norm_num⟩
  | 3 => ⟨((738791947/73786976294838206464), (-3126628541/147573952589676412928)), (5/73786976294838206464), by norm_num⟩
  | 4 => ⟨((-34000193/1180591620717411303424), (2364114837/1180591620717411303424)), (15/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((-142641969/2361183241434822606848), (-2606177893/18889465931478580854784)), (5/9444732965739290427392), by norm_num⟩
  | 6 => ⟨((579278391/75557863725914323419136), (2077776265/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | 7 => ⟨((-3016510177/4835703278458516698824704), (-1892057703/9671406556917033397649408)), (15/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((6006141317/154742504910672534362390528), (-185914787/38685626227668133590597632)), (33/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-4702566551/2475880078570760549798248448), (360623433/309485009821345068724781056)), (17/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((1349947841/19807040628566084398385987584), (-2001329977/19807040628566084398385987584)), (17/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((-21115927/19807040628566084398385987584), (4024885071/633825300114114700748351602688)), (33/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((-1726525329/20282409603651670423947251286016), (-1617594857/5070602400912917605986812821504)), (15/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1059495471/2305843009213693952), (598191959/4611686018427387904)), (11/9223372036854775808), by norm_num⟩
  | 1 => ⟨((459682235/4611686018427387904), (-1555769615/18446744073709551616)), (13/36893488147419103232), by norm_num⟩
  | 2 => ⟨((-2533000961/295147905179352825856), (2679967321/147573952589676412928)), (19/295147905179352825856), by norm_num⟩
  | 3 => ⟨((38857363/1180591620717411303424), (-337730691/147573952589676412928)), (21/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((1630193931/18889465931478580854784), (3723111275/18889465931478580854784)), (17/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-1986097341/151115727451828646838272), (-3561902169/302231454903657293676544)), (25/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((6033020353/4835703278458516698824704), (236507213/604462909807314587353088)), (33/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-3432080753/38685626227668133590597632), (106237021/9671406556917033397649408)), (41/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((3023078497/618970019642690137449562112), (-927317399/309485009821345068724781056)), (3/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-482124229/2475880078570760549798248448), (2859042825/9903520314283042199192993792)), (13/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((1061829471/316912650057057350374175801344), (-6324819397/316912650057057350374175801344)), (27/158456325028528675187087900672), by norm_num⟩
  | 11 => ⟨((1479878853/5070602400912917605986812821504), (2773019755/2535301200456458802993406410752)), (27/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((-1577998071/40564819207303340847894502572032), (-960167799/20282409603651670423947251286016)), (53/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3677457879/147573952589676412928), (3111539231/147573952589676412928)), (17/147573952589676412928), by norm_num⟩
  | 1 => ⟨((1266500481/295147905179352825856), (-5359934643/590295810358705651712)), (11/295147905179352825856), by norm_num⟩
  | 2 => ⟨((-116572089/4722366482869645213696), (1013192073/590295810358705651712)), (17/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-407548483/4722366482869645213696), (-3723111275/18889465931478580854784)), (21/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((620655419/37778931862957161709568), (2226188855/151115727451828646838272)), (19/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((-4524765265/2417851639229258349412352), (-709521639/1208925819614629174706176)), (29/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((6006141317/38685626227668133590597632), (-743659147/38685626227668133590597632)), (41/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((-3023078497/309485009821345068724781056), (927317399/154742504910672534362390528)), (27/309485009821345068724781056), by norm_num⟩
  | 8 => ⟨((2169559031/4951760157141521099596496896), (-1608211589/2475880078570760549798248448)), (33/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((-165910855/19807040628566084398385987584), (988253031/19807040628566084398385987584)), (19/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-127177089/158456325028528675187087900672), (-3812902163/1267650600228229401496703205376)), (41/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((1183498553/10141204801825835211973625643008), (2880503397/20282409603651670423947251286016)), (43/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((-190726829/20282409603651670423947251286016), (-374049389/81129638414606681695789005144064)), (11/81129638414606681695789005144064), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2251556409/2361183241434822606848), (2382193175/1180591620717411303424)), (13/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((103619635/9444732965739290427392), (-7204921409/9444732965739290427392)), (9/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((2173591909/37778931862957161709568), (4964148367/37778931862957161709568)), (15/18889465931478580854784), by norm_num⟩
  | 3 => ⟨((-4413549647/302231454903657293676544), (-3957669075/302231454903657293676544)), (5/37778931862957161709568), by norm_num⟩
  | 4 => ⟨((5027516961/2417851639229258349412352), (3079521/4722366482869645213696)), (5/302231454903657293676544), by norm_num⟩
  | 5 => ⟨((-1001023553/4835703278458516698824704), (495772765/19342813113834066795298816)), (33/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((4702566551/309485009821345068724781056), (-360623433/38685626227668133590597632)), (49/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((-482124229/618970019642690137449562112), (357380353/309485009821345068724781056)), (17/1237940039285380274899124224), by norm_num⟩
  | 8 => ⟨((165910855/9903520314283042199192993792), (-988253031/9903520314283042199192993792)), (43/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((1130463013/633825300114114700748351602688), (529569745/79228162514264337593543950336)), (13/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((-180812279/633825300114114700748351602688), (-3520615263/10141204801825835211973625643008)), (59/10141204801825835211973625643008), by norm_num⟩
  | 11 => ⟨((4068839019/162259276829213363391578010288128), (1994930075/162259276829213363391578010288128)), (1/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((-2167867691/1298074214633706907132624082305024), (-62368517/1298074214633706907132624082305024)), (17/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-41447853/18889465931478580854784), (5763937127/37778931862957161709568)), (39/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((-1738873527/75557863725914323419136), (-1985659347/37778931862957161709568)), (15/37778931862957161709568), by norm_num⟩
  | 2 => ⟨((662032447/75557863725914323419136), (2374601445/302231454903657293676544)), (27/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((-4022013569/2417851639229258349412352), (-630685901/1208925819614629174706176)), (19/1208925819614629174706176), by norm_num⟩
  | 4 => ⟨((4004094211/19342813113834066795298816), (-495772765/19342813113834066795298816)), (5/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((-2821539931/154742504910672534362390528), (1730992479/154742504910672534362390528)), (9/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((1349947841/1237940039285380274899124224), (-4002659955/2475880078570760549798248448)), (7/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((-33182171/1237940039285380274899124224), (6324819397/39614081257132168796771975168)), (5/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((-1017416711/316912650057057350374175801344), (-3812902163/316912650057057350374175801344)), (55/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((180812279/316912650057057350374175801344), (3520615263/5070602400912917605986812821504)), (17/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((-2237861461/40564819207303340847894502572032), (-2194423083/81129638414606681695789005144064)), (81/81129638414606681695789005144064), by norm_num⟩
  | 11 => ⟨((5202882459/1298074214633706907132624082305024), (18710555/162259276829213363391578010288128)), (23/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((-4810767283/20769187434139310514121985316880384), (63265523/649037107316853453566312041152512)), (25/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((72704/14020065), (-33088/14020065)), 0, by norm_num⟩
  | 1 => ⟨((-2794037248/21840246956025), (9622519808/65520740868075)), 0, by norm_num⟩
  | 2 => ⟨((1070088505/562949953421312), (-3592207653/562949953421312)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((562292429/18014398509481984), (4061492661/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-2400229597/576460752303423488), (-3789060397/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((4106736655/18446744073709551616), (2684989095/18446744073709551616)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-5305544829/590295810358705651712), (-203111451/147573952589676412928)), (5/295147905179352825856), by norm_num⟩
  | 7 => ⟨((353165157/1180591620717411303424), (-1595178557/18889465931478580854784)), (15/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((-1225819293/151115727451828646838272), (2074359487/302231454903657293676544)), (3/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((750518803/4835703278458516698824704), (-3176257567/9671406556917033397649408)), (9/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((-13815951/77371252455336267181195264), (7685249503/618970019642690137449562112)), (53/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-1686180391/9903520314283042199192993792), (-3850975703/9903520314283042199192993792)), (39/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((106995143/9903520314283042199192993792), (3070191767/316912650057057350374175801344)), (57/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((81359909/4194304), (2102559661/134217728)), (3/67108864), by norm_num⟩
  | 1 => ⟨((1423487705/1073741824), (118526509/536870912)), (5/4294967296), by norm_num⟩
  | 2 => ⟨((547856599/68719476736), (-1035394573/274877906944)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-2316362309/35184372088832), (704018159/8796093022208)), (7/35184372088832), by norm_num⟩
  | 4 => ⟨((1007997691/2251799813685248), (-1993886803/1125899906842624)), (15/2251799813685248), by norm_num⟩
  | 5 => ⟨((1066869233/144115188075855872), (5463126731/144115188075855872)), (29/144115188075855872), by norm_num⟩
  | 6 => ⟨((-1237487663/2305843009213693952), (-843304797/1152921504606846976)), (47/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1479651769/73786976294838206464), (1608864917/147573952589676412928)), (69/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2841859515/4722366482869645213696), (-332462407/9444732965739290427392)), (89/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((4631215291/302231454903657293676544), (-463540895/75557863725914323419136)), (241/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-1533559719/4835703278458516698824704), (1642804707/4835703278458516698824704)), (329/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((318093817/77371252455336267181195264), (-3940338165/309485009821345068724781056)), (445/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((122087097/2475880078570760549798248448), (1926661799/4951760157141521099596496896)), (603/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1141427739/4503599627370496), (957922041/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((-899667887/72057594037927936), (-3249194129/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 2 => ⟨((960091839/288230376151711744), (1515624159/288230376151711744)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((-684456109/2305843009213693952), (-894996365/4611686018427387904)), (1/2305843009213693952), by norm_num⟩
  | 4 => ⟨((5305544829/295147905179352825856), (406222903/147573952589676412928)), (7/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-3955449759/4722366482869645213696), (1116624989/4722366482869645213696)), (7/4722366482869645213696), by norm_num⟩
  | 6 => ⟨((4576392027/151115727451828646838272), (-968034427/37778931862957161709568)), (3/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-225155641/302231454903657293676544), (3811509079/2417851639229258349412352)), (11/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((20723927/19342813113834066795298816), (-2881968563/38685626227668133590597632)), (9/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((772832679/618970019642690137449562112), (3530061061/1237940039285380274899124224)), (1/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((-470778629/4951760157141521099596496896), (-52768921/618970019642690137449562112)), (25/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((390013437/79228162514264337593543950336), (1957037461/1267650600228229401496703205376)), (41/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((-2070804279/10141204801825835211973625643008), (512799305/20282409603651670423947251286016)), (1/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1301758527/67108864), (2102559775/134217728)), (7/134217728), by norm_num⟩
  | 1 => ⟨((2846975383/2147483648), (948211685/4294967296)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((4382854623/549755813888), (-2070786255/549755813888)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((-2316372753/35184372088832), (176004113/2199023255552)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((1008038169/2251799813685248), (-249235463/140737488355328)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((533374261/72057594037927936), (682895101/18014398509481984)), (15/72057594037927936), by norm_num⟩
  | 6 => ⟨((-1237417833/2305843009213693952), (-843334339/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 7 => ⟨((2959193599/147573952589676412928), (1609097553/147573952589676412928)), (35/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-5683708911/9444732965739290427392), (-333166013/9444732965739290427392)), (179/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((4631592651/302231454903657293676544), (-1853301749/302231454903657293676544)), (121/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-191752433/604462909807314587353088), (821196225/2417851639229258349412352)), (165/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((636949379/154742504910672534362390528), (-3939860373/309485009821345068724781056)), (223/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((243163059/4951760157141521099596496896), (963393497/2475880078570760549798248448)), (151/2475880078570760549798248448), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-45718659/72057594037927936), (-72172579/72057594037927936)), (1/1152921504606846976), by norm_num⟩
  | 1 => ⟨((782235553/4611686018427387904), (2045705977/18446744073709551616)), (5/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-6063479805/295147905179352825856), (-232127373/73786976294838206464)), (9/295147905179352825856), by norm_num⟩
  | 3 => ⟨((117721719/73786976294838206464), (-531726185/1180591620717411303424)), (7/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((-3268851449/37778931862957161709568), (345726581/4722366482869645213696)), (9/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((225155641/75557863725914323419136), (-3811509079/604462909807314587353088)), (5/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-27631903/4835703278458516698824704), (3842624751/9671406556917033397649408)), (11/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-1324856021/154742504910672534362390528), (-3025766623/154742504910672534362390528)), (3/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((4035245391/4951760157141521099596496896), (1809220149/2475880078570760549798248448)), (21/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((-2042927527/39614081257132168796771975168), (-160174197/9903520314283042199192993792)), (19/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((6508242019/2535301200456458802993406410752), (-402913739/1267650600228229401496703205376)), (35/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((-4169201859/40564819207303340847894502572032), (639443109/10141204801825835211973625643008)), (31/40564819207303340847894502572032), by norm_num⟩
  | 12 => ⟨((997364061/324518553658426726783156020576256), (-1478616087/324518553658426726783156020576256)), (27/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1301758527/67108864), (2102559775/134217728)), (1/16777216), by norm_num⟩
  | 1 => ⟨((5693950767/4294967296), (948211685/4294967296)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((1095713653/137438953472), (-2070786257/549755813888)), (3/549755813888), by norm_num⟩
  | 3 => ⟨((-2316372697/35184372088832), (11000257/137438953472)), (9/35184372088832), by norm_num⟩
  | 4 => ⟨((504018987/1125899906842624), (-3987767243/2251799813685248)), (17/2251799813685248), by norm_num⟩
  | 5 => ⟨((1066748951/144115188075855872), (5463159899/144115188075855872)), (31/144115188075855872), by norm_num⟩
  | 6 => ⟨((-618708923/1152921504606846976), (-843333881/1152921504606846976)), (49/4611686018427387904), by norm_num⟩
  | 7 => ⟨((184949521/9223372036854775808), (1609094667/147573952589676412928)), (71/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2841850607/4722366482869645213696), (-333159111/9444732965739290427392)), (45/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((4631577065/302231454903657293676544), (-1853306637/302231454903657293676544)), (243/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-3068014101/9671406556917033397649408), (1642390913/4835703278458516698824704)), (331/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((636933475/154742504910672534362390528), (-3939840859/309485009821345068724781056)), (447/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((486356555/9903520314283042199192993792), (120422777/309485009821345068724781056)), (605/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1212695961/295147905179352825856), (92850949/147573952589676412928)), (9/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-2260257005/2361183241434822606848), (319035711/1180591620717411303424)), (5/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((3922621737/37778931862957161709568), (-1659487589/18889465931478580854784)), (13/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-225155641/37778931862957161709568), (3811509079/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((82895709/4835703278458516698824704), (-2881968563/2417851639229258349412352)), (5/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((1391098821/38685626227668133590597632), (3177054955/38685626227668133590597632)), (13/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((-2824671773/618970019642690137449562112), (-2532908209/618970019642690137449562112)), (17/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((3677269549/9903520314283042199192993792), (1153254219/9903520314283042199192993792)), (19/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((-457610767/19807040628566084398385987584), (453277957/158456325028528675187087900672)), (41/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((2866326279/2535301200456458802993406410752), (-1758468549/2535301200456458802993406410752)), (11/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((-3291301403/81129638414606681695789005144064), (4879433087/81129638414606681695789005144064)), (21/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((823722257/1298074214633706907132624082305024), (-4906526563/1298074214633706907132624082305024)), (41/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((131544787/2596148429267413814265248164610048), (1971925159/10384593717069655257060992658440192)), (37/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1301758527/67108864), (2102559775/134217728)), (9/134217728), by norm_num⟩
  | 1 => ⟨((5693950767/4294967296), (948211685/4294967296)), (1/536870912), by norm_num⟩
  | 2 => ⟨((1095713653/137438953472), (-2070786257/549755813888)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-2316372697/35184372088832), (11000257/137438953472)), (5/17592186044416), by norm_num⟩
  | 4 => ⟨((504018987/1125899906842624), (-1993883623/1125899906842624)), (9/1125899906842624), by norm_num⟩
  | 5 => ⟨((266687239/36028797018963968), (5463159911/144115188075855872)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((-2474835713/4611686018427387904), (-3373335543/4611686018427387904)), (25/2305843009213693952), by norm_num⟩
  | 7 => ⟨((2959192391/147573952589676412928), (402273671/36893488147419103232)), (9/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-710462679/1180591620717411303424), (-83289771/2361183241434822606848)), (181/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((4631577407/302231454903657293676544), (-1853306847/302231454903657293676544)), (61/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-3068014493/9671406556917033397649408), (410597801/1208925819614629174706176)), (83/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((636933573/154742504910672534362390528), (-3939842029/309485009821345068724781056)), (7/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((486357057/9903520314283042199192993792), (3853530745/9903520314283042199192993792)), (303/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-198112209/9444732965739290427392), (2682000145/151115727451828646838272)), (1/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((2183327429/604462909807314587353088), (-4620011005/604462909807314587353088)), (5/151115727451828646838272), by norm_num⟩
  | 2 => ⟨((-50239823/2417851639229258349412352), (873323807/604462909807314587353088)), (15/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((-1405150325/19342813113834066795298816), (-3209146419/19342813113834066795298816)), (19/19342813113834066795298816), by norm_num⟩
  | 4 => ⟨((2139902859/154742504910672534362390528), (1918869855/154742504910672534362390528)), (17/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((-1950067185/1237940039285380274899124224), (-1223148415/2475880078570760549798248448)), (13/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((5177010697/39614081257132168796771975168), (-320499565/19807040628566084398385987584)), (9/9903520314283042199192993792), by norm_num⟩
  | 7 => ⟨((-5211502325/633825300114114700748351602688), (399651943/79228162514264337593543950336)), (47/633825300114114700748351602688), by norm_num⟩
  | 8 => ⟨((116878601/316912650057057350374175801344), (-693101291/1267650600228229401496703205376)), (29/5070602400912917605986812821504), by norm_num⟩
  | 9 => ⟨((-572029345/81129638414606681695789005144064), (6814620227/162259276829213363391578010288128)), (67/162259276829213363391578010288128), by norm_num⟩
  | 10 => ⟨((-1753930493/2596148429267413814265248164610048), (-6573083863/2596148429267413814265248164610048)), (9/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((1020119965/10384593717069655257060992658440192), (2482858147/20769187434139310514121985316880384)), (19/10384593717069655257060992658440192), by norm_num⟩
  | 12 => ⟨((-5260721155/664613997892457936451903530140172288), (-2579303531/664613997892457936451903530140172288)), (77/664613997892457936451903530140172288), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1301758527/67108864), (2102559775/134217728)), (5/67108864), by norm_num⟩
  | 1 => ⟨((5693950767/4294967296), (948211685/4294967296)), (9/4294967296), by norm_num⟩
  | 2 => ⟨((1095713653/137438953472), (-2070786257/549755813888)), (5/549755813888), by norm_num⟩
  | 3 => ⟨((-2316372697/35184372088832), (11000257/137438953472)), (11/35184372088832), by norm_num⟩
  | 4 => ⟨((504018987/1125899906842624), (-1993883623/1125899906842624)), (19/2251799813685248), by norm_num⟩
  | 5 => ⟨((266687239/36028797018963968), (5463159911/144115188075855872)), (33/144115188075855872), by norm_num⟩
  | 6 => ⟨((-9667327/18014398509481984), (-3373335543/4611686018427387904)), (51/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1479596195/73786976294838206464), (1609094685/147573952589676412928)), (73/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5683701429/9444732965739290427392), (-333159089/9444732965739290427392)), (91/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((4631577405/302231454903657293676544), (-926653417/151115727451828646838272)), (245/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-767003625/2417851639229258349412352), (205298899/604462909807314587353088)), (333/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((159233397/38685626227668133590597632), (-492480249/38685626227668133590597632)), (449/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((486356979/9903520314283042199192993792), (3853530707/9903520314283042199192993792)), (607/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((81384831/19342813113834066795298816), (-5658882351/19342813113834066795298816)), (39/19342813113834066795298816), by norm_num⟩
  | 1 => ⟨((1707180439/38685626227668133590597632), (3898936573/38685626227668133590597632)), (15/19342813113834066795298816), by norm_num⟩
  | 2 => ⟨((-2599864397/154742504910672534362390528), (-2331321441/154742504910672534362390528)), (7/38685626227668133590597632), by norm_num⟩
  | 3 => ⟨((246794217/77371252455336267181195264), (309595441/309485009821345068724781056)), (19/618970019642690137449562112), by norm_num⟩
  | 4 => ⟨((-982778679/2475880078570760549798248448), (243368351/4951760157141521099596496896)), (5/1237940039285380274899124224), by norm_num⟩
  | 5 => ⟨((346264241/9903520314283042199192993792), (-212430379/9903520314283042199192993792)), (37/79228162514264337593543950336), by norm_num⟩
  | 6 => ⟨((-1325343397/633825300114114700748351602688), (3929706601/1267650600228229401496703205376)), (7/158456325028528675187087900672), by norm_num⟩
  | 7 => ⟨((65154771/1267650600228229401496703205376), (-3104770929/10141204801825835211973625643008)), (5/1267650600228229401496703205376), by norm_num⟩
  | 8 => ⟨((249718263/40564819207303340847894502572032), (233962961/10141204801825835211973625643008)), (55/162259276829213363391578010288128), by norm_num⟩
  | 9 => ⟨((-2840268079/2596148429267413814265248164610048), (-3456447761/2596148429267413814265248164610048)), (67/2596148429267413814265248164610048), by norm_num⟩
  | 10 => ⟨((4394147419/41538374868278621028243970633760768), (2154427049/41538374868278621028243970633760768)), (5/2596148429267413814265248164610048), by norm_num⟩
  | 11 => ⟨((-1277013397/166153499473114484112975882535043072), (-146956259/664613997892457936451903530140172288)), (91/664613997892457936451903530140172288), by norm_num⟩
  | 12 => ⟨((4723085189/10633823966279326983230456482242756608), (-1987597817/10633823966279326983230456482242756608)), (99/10633823966279326983230456482242756608), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1301758527/67108864), (2102559775/134217728)), (11/134217728), by norm_num⟩
  | 1 => ⟨((5693950767/4294967296), (948211685/4294967296)), (5/2147483648), by norm_num⟩
  | 2 => ⟨((1095713653/137438953472), (-2070786257/549755813888)), (3/274877906944), by norm_num⟩
  | 3 => ⟨((-2316372697/35184372088832), (11000257/137438953472)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((504018987/1125899906842624), (-1993883623/1125899906842624)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((266687239/36028797018963968), (5463159911/144115188075855872)), (17/72057594037927936), by norm_num⟩
  | 6 => ⟨((-9667327/18014398509481984), (-3373335543/4611686018427387904)), (13/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1479596195/73786976294838206464), (1609094685/147573952589676412928)), (37/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-5683701429/9444732965739290427392), (-333159089/9444732965739290427392)), (183/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((4631577405/302231454903657293676544), (-926653417/151115727451828646838272)), (123/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-3068014499/9671406556917033397649408), (3284782385/9671406556917033397649408)), (167/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((636933587/154742504910672534362390528), (-492480249/38685626227668133590597632)), (225/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((486356983/9903520314283042199192993792), (3853530705/9903520314283042199192993792)), (19/309485009821345068724781056), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1113228651986693/4194304), (47532775232903/4194304)), (242012209/4194304), by norm_num⟩
  | 1 => ⟨((-5669900345/16), (-697155341/16)), (1439/16), by norm_num⟩
  | 2 => ⟨((-1857292015/8), (-267639187/4)), (283/4), by norm_num⟩
  | 3 => ⟨((-3188689039/32), (-1472534273/32)), (1199/32), by norm_num⟩
  | 4 => ⟨((-2017128773/64), (-1318355775/64)), (1921/128), by norm_num⟩
  | 5 => ⟨((-4004918389/512), (-1755671837/256)), (621/128), by norm_num⟩
  | 6 => ⟨((-404641269/256), (-466058899/256)), (675/512), by norm_num⟩
  | 7 => ⟨((-16999053/64), (-3295342543/8192)), (1269/4096), by norm_num⟩
  | 8 => ⟨((-1225689597/32768), (-4992269207/65536)), (1053/16384), by norm_num⟩
  | 9 => ⟨((-1146072503/262144), (-3310079007/262144)), (1567/131072), by norm_num⟩
  | 10 => ⟨((-848137091/2097152), (-3904022389/2097152)), (4235/2097152), by norm_num⟩
  | 11 => ⟨((-101947929/4194304), (-1036650127/4194304)), (5249/16777216), by norm_num⟩
  | 12 => ⟨((7299785/16777216), (-4005785391/134217728)), (47/1048576), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1609243454895659/10141204801825835211973625643008), (4036689881255/10141204801825835211973625643008)), (53379/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((906222274438387/316912650057057350374175801344), (4946503910545/633825300114114700748351602688)), (65733/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((240958043270723/4951760157141521099596496896), (5578683927571/39614081257132168796771975168)), (148345/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((482461262703217/618970019642690137449562112), (2969673913447/1237940039285380274899124224)), (39497/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1811551141469115/154742504910672534362390528), (2976389677737/77371252455336267181195264)), (158403/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((198429220186451/1208925819614629174706176), (5595042174099/9671406556917033397649408)), (74473/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((80748529982477/37778931862957161709568), (4910021456109/604462909807314587353088)), (32693/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1941802100077499/75557863725914323419136), (8005811568357/75557863725914323419136)), (213341/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1338117090714313/4722366482869645213696), (6028110035547/4722366482869645213696)), (80371/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1677356640133605/590295810358705651712), (8327441343829/590295810358705651712)), (111111/295147905179352825856), by norm_num⟩
  | 8 => ⟨((946766166474219/36893488147419103232), (10467828349971/73786976294838206464)), (139797/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1901709444857517/9223372036854775808), (11857339852521/9223372036854775808)), (158531/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1673256567308055/1152921504606846976), (5979737861363/576460752303423488)), (320239/1152921504606846976), by norm_num⟩
  | 5 => ⟨((632140390048041/72057594037927936), (5290308084471/72057594037927936)), (141913/72057594037927936), by norm_num⟩
  | 4 => ⟨((99804330140451/2251799813685248), (16106036427837/36028797018963968)), (54135/4503599627370496), by norm_num⟩
  | 3 => ⟨((1622003398219665/9007199254740992), (20550746702909/9007199254740992)), (554441/9007199254740992), by norm_num⟩
  | 2 => ⟨((1248554095603469/2251799813685248), (21191785152575/2251799813685248)), (574575/2251799813685248), by norm_num⟩
  | 1 => ⟨((1314598525296211/1125899906842624), (16719695307625/562949953421312)), (14281/17592186044416), by norm_num⟩
  | 0 => ⟨((1522721465313727/1125899906842624), (73788812126493/1125899906842624)), (1023765/562949953421312), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1522721465313727/1125899906842624), (73788812126493/1125899906842624)), (3905353548290061773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1027283090651985/562949953421312), (99795556818283/562949953421312)), (1451685/281474976710656), by norm_num⟩
  | 2 => ⟨((1856917100402497/562949953421312), (364218124252679/562949953421312)), (1453205/70368744177664), by norm_num⟩
  | 3 => ⟨((1472371680459029/140737488355328), (600695371845213/140737488355328)), (22934649/140737488355328), by norm_num⟩
  | 4 => ⟨((200622122876913/2199023255552), (392773304586179/4398046511104)), (21114251/4398046511104), by norm_num⟩
  | 5 => ⟨((23895822050013/68719476736), (1119801342148599/68719476736)), (59561551/34359738368), by norm_num⟩
  | 6 => ⟨((-1113228651986693/4194304), (47532775232903/4194304)), (242012209/4194304), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((1301758527/67108864), (2102559775/134217728)), (11/134217728), by norm_num⟩, 2, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((28672/839499), (-132352/839499)), 0, by norm_num⟩
  | 1 => ⟨((927498240/78306507889), (3794796544/704758571001)), 0, by norm_num⟩
  | 2 => ⟨((-370793989013504/591644115596768499), (498000908517376/591644115596768499)), 0, by norm_num⟩
  | 3 => ⟨((-122373453/2199023255552), (-4487899965/70368744177664)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((3365153115/562949953421312), (-1856377731/562949953421312)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((1421892203/9007199254740992), (4751508291/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((-6381330947/144115188075855872), (495105115/144115188075855872)), (7/144115188075855872), by norm_num⟩
  | 7 => ⟨((559559303/1152921504606846976), (-255741093/72057594037927936)), (3/576460752303423488), by norm_num⟩
  | 8 => ⟨((5007956773/18446744073709551616), (227969933/2305843009213693952)), (5/9223372036854775808), by norm_num⟩
  | 9 => ⟨((-1834267101/147573952589676412928), (2908983875/147573952589676412928)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-3167772469/2361183241434822606848), (-3108285347/2361183241434822606848)), (15/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((4785846363/37778931862957161709568), (-3146069399/37778931862957161709568)), (3/4722366482869645213696), by norm_num⟩
  | 12 => ⟨((665084271/151115727451828646838272), (430983503/37778931862957161709568)), (19/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((21/16), (1551/256)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((21/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((21/16), (1551/256)))⁻¹=value ((28672/839499), (-132352/839499)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((28672/839499), (-132352/839499))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((37/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((151552/2756065), (-397056/2756065)), 0, by norm_num⟩
  | 1 => ⟨((67342729216/7595894284225), (60174630912/7595894284225)), 0, by norm_num⟩
  | 2 => ⟨((-447721877/549755813888), (925377323/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-139349449/17592186044416), (-617783263/8796093022208)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((5941314623/1125899906842624), (1531726351/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((-547374337/2251799813685248), (385857813/1125899906842624)), (3/4503599627370496), by norm_num⟩
  | 6 => ⟨((-81078873/4503599627370496), (-970349571/36028797018963968)), (11/144115188075855872), by norm_num⟩
  | 7 => ⟨((5614781273/2305843009213693952), (-320701887/576460752303423488)), (9/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-247878695/9223372036854775808), (7035522435/36893488147419103232)), (15/18446744073709551616), by norm_num⟩
  | 9 => ⟨((-3836238039/295147905179352825856), (-1059433931/147573952589676412928)), (25/295147905179352825856), by norm_num⟩
  | 10 => ⟨((4129652225/4722366482869645213696), (-872318083/1180591620717411303424)), (41/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((551205767/18889465931478580854784), (786813589/9444732965739290427392)), (33/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-8224531125/1208925819614629174706176), (-227881871/1208925819614629174706176)), (53/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((37/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((37/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((37/16), (1551/256)))⁻¹=value ((151552/2756065), (-397056/2756065)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((151552/2756065), (-397056/2756065))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-48205856768/2313713811435), (-31442599936/2313713811435)), 0, by norm_num⟩
  | 1 => ⟨((1637604009/549755813888), (-2789966971/1099511627776)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((1650880619/8796093022208), (231398199/549755813888)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-839638175/17592186044416), (908732279/140737488355328)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((788991607/1125899906842624), (-2622240907/562949953421312)), (5/1125899906842624), by norm_num⟩
  | 5 => ⟨((3611389551/9007199254740992), (1664645787/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 6 => ⟨((-3786807011/144115188075855872), (4376503399/144115188075855872)), (5/72057594037927936), by norm_num⟩
  | 7 => ⟨((-1123915667/576460752303423488), (-1725226857/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 8 => ⟨((1375928541/4611686018427387904), (-847000877/9223372036854775808)), (9/9223372036854775808), by norm_num⟩
  | 9 => ⟨((83851919/147573952589676412928), (1984208903/73786976294838206464)), (31/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-2616299291/1180591620717411303424), (-340912295/590295810358705651712)), (27/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((920858707/9444732965739290427392), (-1573330939/9444732965739290427392)), (23/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((846575331/75557863725914323419136), (876209623/75557863725914323419136)), (19/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((53/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((217088/3124705), (-397056/3124705)), 0, by norm_num⟩
  | 1 => ⟨((55263133696/9763781337025), (86196092928/9763781337025)), 0, by norm_num⟩
  | 2 => ⟨((-6663127023/8796093022208), (29105291/549755813888)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((1614977455/70368744177664), (-1758072595/35184372088832)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((2676769343/1125899906842624), (898996491/281474976710656)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-5143275429/18014398509481984), (361226967/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((2124203615/288230376151711744), (-2814991429/144115188075855872)), (13/288230376151711744), by norm_num⟩
  | 7 => ⟨((1135645995/1152921504606846976), (1322127695/1152921504606846976)), (11/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-3950421441/36893488147419103232), (839231859/36893488147419103232)), (9/18446744073709551616), by norm_num⟩
  | 9 => ⟨((1342506367/590295810358705651712), (-4482280923/590295810358705651712)), (29/590295810358705651712), by norm_num⟩
  | 10 => ⟨((3810342447/9444732965739290427392), (963994751/2361183241434822606848)), (47/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-6037611155/151115727451828646838272), (1730294695/151115727451828646838272)), (37/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((798371737/1208925819614629174706176), (-1774820951/604462909807314587353088)), (15/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((53/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((53/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((53/16), (1551/256)))⁻¹=value ((217088/3124705), (-397056/3124705)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((217088/3124705), (-397056/3124705))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-917975439769600/289186924606400067), (2462922705993728/1445934623032000335)), 0, by norm_num⟩
  | 1 => ⟨((-997816035/8796093022208), (-7174567783/8796093022208)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((537825907/4398046511104), (466546547/17592186044416)), (3/35184372088832), by norm_num⟩
  | 3 => ⟨((-2372354897/281474976710656), (940243527/70368744177664)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-2475553675/2251799813685248), (-3180222201/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 5 => ⟨((3229249185/18014398509481984), (-2121979503/36028797018963968)), (11/36028797018963968), by norm_num⟩
  | 6 => ⟨((-130181267/288230376151711744), (5442910255/288230376151711744)), (11/288230376151711744), by norm_num⟩
  | 7 => ⟨((-489946997/288230376151711744), (-1486922245/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 8 => ⟨((2012130417/18446744073709551616), (-1198036761/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 9 => ⟨((584399383/73786976294838206464), (3907281507/295147905179352825856)), (21/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-1586209771/1180591620717411303424), (672490869/2361183241434822606848)), (19/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((535810253/37778931862957161709568), (-4504002221/37778931862957161709568)), (17/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((5642027041/604462909807314587353088), (2674398485/604462909807314587353088)), (29/302231454903657293676544), by norm_num⟩
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
  | 0 => ⟨((69/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((94208/1208139), (-132352/1208139)), 0, by norm_num⟩
  | 1 => ⟨((1440317440/486533281107), (12468617216/1459599843321)), 0, by norm_num⟩
  | 2 => ⟨((-1028657350967296/1763399495109989619), (-301378404614144/1763399495109989619)), 0, by norm_num⟩
  | 3 => ⟨((1129600597/35184372088832), (-222443625/8796093022208)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((300522283/2251799813685248), (6180183553/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 5 => ⟨((-2801900301/18014398509481984), (-1795978797/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 6 => ⟨((3321888023/288230376151711744), (-667610393/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 7 => ⟨((-902076899/4611686018427387904), (3744251305/4611686018427387904)), (7/4611686018427387904), by norm_num⟩
  | 8 => ⟨((-339841929/9223372036854775808), (-1563164863/36893488147419103232)), (3/18446744073709551616), by norm_num⟩
  | 9 => ⟨((4435930763/1180591620717411303424), (-27027023/73786976294838206464)), (19/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-2388247555/18889465931478580854784), (129919425/590295810358705651712)), (15/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-1076866281/151115727451828646838272), (-2343279091/151115727451828646838272)), (23/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((681357183/604462909807314587353088), (1036042781/4835703278458516698824704)), (35/2417851639229258349412352), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((69/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((69/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((69/16), (1551/256)))⁻¹=value ((94208/1208139), (-132352/1208139)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((94208/1208139), (-132352/1208139))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-33494229/549755813888), (4227156135/8796093022208)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((-537216139/4398046511104), (-2577249545/35184372088832)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((2985845369/140737488355328), (-2134064377/140737488355328)), (3/140737488355328), by norm_num⟩
  | 3 => ⟨((911930839/1125899906842624), (2093349039/562949953421312)), (5/1125899906842624), by norm_num⟩
  | 4 => ⟨((-4284787673/9007199254740992), (-203356133/2251799813685248)), (7/9007199254740992), by norm_num⟩
  | 5 => ⟨((2235228339/72057594037927936), (-3369878567/72057594037927936)), (1/9007199254740992), by norm_num⟩
  | 6 => ⟨((975867425/288230376151711744), (2907957383/576460752303423488)), (9/576460752303423488), by norm_num⟩
  | 7 => ⟨((-2820103599/4611686018427387904), (287558031/2305843009213693952)), (19/9223372036854775808), by norm_num⟩
  | 8 => ⟨((3253335/288230376151711744), (-4459395981/73786976294838206464)), (19/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1457492797/295147905179352825856), (1853086015/590295810358705651712)), (19/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-4137308687/9444732965739290427392), (749654951/2361183241434822606848)), (35/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-463396673/37778931862957161709568), (-1784048613/37778931862957161709568)), (1/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((5171111401/1208925819614629174706176), (594530219/1208925819614629174706176)), (7/151115727451828646838272), by norm_num⟩
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
  | 0 => ⟨((85/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((348160/4255201), (-397056/4255201)), 0, by norm_num⟩
  | 1 => ⟨((18219040768/18106735550401), (138239016960/18106735550401)), 0, by norm_num⟩
  | 2 => ⟨((-3495235237/8796093022208), (-1167194305/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((1007606505/35184372088832), (-270287295/35184372088832)), (3/140737488355328), by norm_num⟩
  | 4 => ⟨((-915544393/1125899906842624), (3716332521/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 5 => ⟨((-24619291/562949953421312), (-949860239/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((483446911/72057594037927936), (81923061/36028797018963968)), (13/576460752303423488), by norm_num⟩
  | 7 => ⟨((-1755013405/4611686018427387904), (1014557617/4611686018427387904)), (5/2305843009213693952), by norm_num⟩
  | 8 => ⟨((195703355/36893488147419103232), (-493545185/18446744073709551616)), (29/147573952589676412928), by norm_num⟩
  | 9 => ⟨((2434999043/2361183241434822606848), (1584397351/1180591620717411303424)), (21/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-7918622753/75557863725914323419136), (-512940595/75557863725914323419136)), (119/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((347881785/75557863725914323419136), (-1393847801/302231454903657293676544)), (21/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((259302603/9671406556917033397649408), (3902222247/9671406556917033397649408)), (59/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((85/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((85/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((85/16), (1551/256)))⁻¹=value ((348160/4255201), (-397056/4255201)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((348160/4255201), (-397056/4255201))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1402364865/35184372088832), (1583485277/35184372088832)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((-5786987931/281474976710656), (190801681/35184372088832)), (1/70368744177664), by norm_num⟩
  | 2 => ⟨((511741169/562949953421312), (-4955521055/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 3 => ⟨((1309218207/2251799813685248), (2031772599/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-3321233559/36028797018963968), (205675679/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((-26701831/144115188075855872), (-3715310099/288230376151711744)), (5/144115188075855872), by norm_num⟩
  | 6 => ⟨((3128328949/2305843009213693952), (1419255663/2305843009213693952)), (3/576460752303423488), by norm_num⟩
  | 7 => ⟨((-70683411/576460752303423488), (3887882505/36893488147419103232)), (25/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-1362460587/295147905179352825856), (-591400441/36893488147419103232)), (13/147573952589676412928), by norm_num⟩
  | 9 => ⟨((1928730197/1180591620717411303424), (558376045/2361183241434822606848)), (27/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-397074703/4722366482869645213696), (2519829211/18889465931478580854784)), (13/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((-1238234889/151115727451828646838272), (-3656865557/302231454903657293676544)), (3/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((1566274353/1208925819614629174706176), (-1190519471/4835703278458516698824704)), (87/4835703278458516698824704), by norm_num⟩
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
  | 0 => ⟨((101/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((413696/5017057), (-397056/5017057)), 0, by norm_num⟩
  | 1 => ⟨((-6745456640/25170860941249), (164260478976/25170860941249)), 0, by norm_num⟩
  | 2 => ⟨((-2174234225/8796093022208), (-614972395/2199023255552)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((5983383227/281474976710656), (246126341/140737488355328)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((-532334711/562949953421312), (1731768441/2251799813685248)), (5/4503599627370496), by norm_num⟩
  | 5 => ⟨((38526553/4503599627370496), (-1245265853/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 6 => ⟨((1373513293/576460752303423488), (1838050629/576460752303423488)), (11/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-4139561455/18446744073709551616), (-685764579/18446744073709551616)), (15/18446744073709551616), by norm_num⟩
  | 8 => ⟨((3164894409/295147905179352825856), (-2168505799/295147905179352825856)), (5/73786976294838206464), by norm_num⟩
  | 9 => ⟨((-714818937/4722366482869645213696), (6868544613/9444732965739290427392)), (53/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((-1702800171/75557863725914323419136), (-2718036273/75557863725914323419136)), (9/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((1422072127/604462909807314587353088), (1429790283/2417851639229258349412352)), (47/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((-4657597493/38685626227668133590597632), (1329122281/19342813113834066795298816)), (61/19342813113834066795298816), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((101/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((101/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((101/16), (1551/256)))⁻¹=value ((413696/5017057), (-397056/5017057)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((413696/5017057), (-397056/5017057))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1927640153/281474976710656), (626752401/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 1 => ⟨((-1768221989/1125899906842624), (163417983/70368744177664)), (1/281474976710656), by norm_num⟩
  | 2 => ⟨((-676709219/2251799813685248), (-2669567871/4503599627370496)), (5/4503599627370496), by norm_num⟩
  | 3 => ⟨((2152576731/18014398509481984), (134538839/36028797018963968)), (11/36028797018963968), by norm_num⟩
  | 4 => ⟨((-2611706503/288230376151711744), (281666899/18014398509481984)), (15/288230376151711744), by norm_num⟩
  | 5 => ⟨((-2952731913/2305843009213693952), (-4730258885/2305843009213693952)), (5/576460752303423488), by norm_num⟩
  | 6 => ⟨((2716777327/9223372036854775808), (-418949611/18446744073709551616)), (3/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-60026195/4611686018427387904), (2286329269/73786976294838206464)), (27/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2761105289/1180591620717411303424), (-3245470577/1180591620717411303424)), (29/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((3387176405/9444732965739290427392), (-1681153049/18889465931478580854784)), (59/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((-1154565213/151115727451828646838272), (5366857421/151115727451828646838272)), (59/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-3292599611/1208925819614629174706176), (-2557840553/1208925819614629174706176)), (57/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((685125293/2417851639229258349412352), (-693327525/4835703278458516698824704)), (13/2417851639229258349412352), by norm_num⟩
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
  | 0 => ⟨((117/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((53248/656665), (-132352/1969995)), 0, by norm_num⟩
  | 1 => ⟨((-4000546816/3880880300025), (7047479296/1293626766675)), 0, by norm_num⟩
  | 2 => ⟨((-119954477154304/849479420738638875), (-1953428985085952/7645314786647749875)), 0, by norm_num⟩
  | 3 => ⟨((4027400901/281474976710656), (790357759/140737488355328)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-1731098789/2251799813685248), (569594835/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 5 => ⟨((3267348465/144115188075855872), (-2599833963/72057594037927936)), (5/144115188075855872), by norm_num⟩
  | 6 => ⟨((675116987/2305843009213693952), (1282293465/576460752303423488)), (7/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-199671143/2305843009213693952), (-2964481293/36893488147419103232)), (9/36893488147419103232), by norm_num⟩
  | 8 => ⟨((7331554049/1180591620717411303424), (412005901/1180591620717411303424)), (11/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-2488740479/9444732965739290427392), (1836614551/9444732965739290427392)), (7/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((78417331/18889465931478580854784), (-5058107739/302231454903657293676544)), (17/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((119041801/302231454903657293676544), (1977794689/2417851639229258349412352)), (41/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((-1680795293/38685626227668133590597632), (-771159201/38685626227668133590597632)), (25/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((117/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((117/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((117/16), (1551/256)))⁻¹=value ((53248/656665), (-132352/1969995)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((53248/656665), (-132352/1969995))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2669382873/4503599627370496), (-467203309/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((334715211/18014398509481984), (1488708603/4503599627370496)), (11/18014398509481984), by norm_num⟩
  | 2 => ⟨((-5480001691/72057594037927936), (-2929456515/72057594037927936)), (15/72057594037927936), by norm_num⟩
  | 3 => ⟨((1036863671/72057594037927936), (-2487865885/288230376151711744)), (1/18014398509481984), by norm_num⟩
  | 4 => ⟨((25652669/1152921504606846976), (781093819/288230376151711744)), (25/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-1538435993/4611686018427387904), (-1747284685/9223372036854775808)), (17/9223372036854775808), by norm_num⟩
  | 6 => ⟨((3117363033/73786976294838206464), (-928102283/36893488147419103232)), (11/36893488147419103232), by norm_num⟩
  | 7 => ⟨((187007441/1180591620717411303424), (6878345671/1180591620717411303424)), (49/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-5444613155/9444732965739290427392), (-700528139/2361183241434822606848)), (27/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((533064229/9444732965739290427392), (-2920084625/75557863725914323419136)), (57/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((117324151/151115727451828646838272), (4144203859/604462909807314587353088)), (29/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-3021265193/4835703278458516698824704), (-1162879895/4835703278458516698824704)), (113/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((452179075/9671406556917033397649408), (-3241949509/77371252455336267181195264)), (107/77371252455336267181195264), by norm_num⟩
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
  | 0 => ⟨((133/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((544768/6933985), (-397056/6933985)), 0, by norm_num⟩
  | 1 => ⟨((-69559353344/48080147980225), (216303403008/48080147980225)), 0, by norm_num⟩
  | 2 => ⟨((-1266192101/17592186044416), (-3837666045/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((2553855271/281474976710656), (916003415/140737488355328)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-305548387/562949953421312), (36930825/9007199254740992)), (5/9007199254740992), by norm_num⟩
  | 5 => ⟨((1527885701/72057594037927936), (-1131375887/72057594037927936)), (3/72057594037927936), by norm_num⟩
  | 6 => ⟨((-1768096831/4611686018427387904), (2822027597/2305843009213693952)), (7/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-1474249979/73786976294838206464), (-4357360583/73786976294838206464)), (1/4611686018427387904), by norm_num⟩
  | 8 => ⟨((182668435/73786976294838206464), (2063333925/1180591620717411303424)), (19/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-1391090291/9444732965739290427392), (21018375/9444732965739290427392)), (21/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((864698731/151115727451828646838272), (-2601867225/604462909807314587353088)), (23/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-1964016479/19342813113834066795298816), (6439585391/19342813113834066795298816)), (101/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((-1715541857/309485009821345068724781056), (-1236779307/77371252455336267181195264)), (111/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((133/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((133/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((133/16), (1551/256)))⁻¹=value ((544768/6933985), (-397056/6933985)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((544768/6933985), (-397056/6933985))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1643316761/72057594037927936), (-1198712795/18014398509481984)), (9/72057594037927936), by norm_num⟩
  | 1 => ⟨((1541866401/72057594037927936), (1015050893/36028797018963968)), (7/72057594037927936), by norm_num⟩
  | 2 => ⟨((-5735806619/576460752303423488), (384344405/576460752303423488)), (19/576460752303423488), by norm_num⟩
  | 3 => ⟨((290539701/288230376151711744), (-4180897687/2305843009213693952)), (11/1152921504606846976), by norm_num⟩
  | 4 => ⟨((1560990821/9223372036854775808), (718778597/2305843009213693952)), (9/4611686018427387904), by norm_num⟩
  | 5 => ⟨((-7766802839/147573952589676412928), (-469361435/147573952589676412928)), (51/147573952589676412928), by norm_num⟩
  | 6 => ⟨((595787147/147573952589676412928), (-852614821/147573952589676412928)), (17/295147905179352825856), by norm_num⟩
  | 7 => ⟨((52077635/147573952589676412928), (3736381153/4722366482869645213696)), (5/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-933092083/9444732965739290427392), (-212996775/18889465931478580854784)), (11/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((970914035/151115727451828646838272), (-2615472085/302231454903657293676544)), (3/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((271385339/604462909807314587353088), (4923151807/4835703278458516698824704)), (99/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-265097827/2417851639229258349412352), (-396718891/38685626227668133590597632)), (99/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((113629271/19342813113834066795298816), (-673559697/77371252455336267181195264)), (95/309485009821345068724781056), by norm_num⟩
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
  | 0 => ⟨((149/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((610304/8089057), (-397056/8089057)), 0, by norm_num⟩
  | 1 => ⟨((-107408752640/65432843149249), (242324865024/65432843149249)), 0, by norm_num⟩
  | 2 => ⟨((-1019207759/35184372088832), (-6333011645/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((3102054387/562949953421312), (1711141253/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-3216230523/9007199254740992), (-1695017643/18014398509481984)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((2274071567/144115188075855872), (-1502841387/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 6 => ⟨((-2155047499/4611686018427387904), (1346538975/2305843009213693952)), (7/4611686018427387904), by norm_num⟩
  | 7 => ⟨((243223753/73786976294838206464), (-4943509801/147573952589676412928)), (15/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1647627771/2361183241434822606848), (3174847903/2361183241434822606848)), (1/147573952589676412928), by norm_num⟩
  | 9 => ⟨((-4482393887/75557863725914323419136), (-2538583931/75557863725914323419136)), (33/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((7404735361/2417851639229258349412352), (-455832535/2417851639229258349412352)), (67/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-4290387437/38685626227668133590597632), (1591429519/19342813113834066795298816)), (17/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((669876519/309485009821345068724781056), (-3605894409/618970019642690137449562112)), (69/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((149/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((149/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((149/16), (1551/256)))⁻¹=value ((610304/8089057), (-397056/8089057)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((610304/8089057), (-397056/8089057))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-445491551/288230376151711744), (-3539404541/576460752303423488)), (5/288230376151711744), by norm_num⟩
  | 1 => ⟨((3696630347/1152921504606846976), (365762459/288230376151711744)), (1/72057594037927936), by norm_num⟩
  | 2 => ⟨((-2006278221/2305843009213693952), (656620267/1152921504606846976)), (11/2305843009213693952), by norm_num⟩
  | 3 => ⟨((108783623/18446744073709551616), (-264155835/1152921504606846976)), (27/18446744073709551616), by norm_num⟩
  | 4 => ⟨((4939416255/147573952589676412928), (1770839581/73786976294838206464)), (23/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-3529147511/590295810358705651712), (666892187/295147905179352825856)), (17/295147905179352825856), by norm_num⟩
  | 6 => ⟨((451194581/2361183241434822606848), (-4089774079/4722366482869645213696)), (23/2361183241434822606848), by norm_num⟩
  | 7 => ⟨((46933521/590295810358705651712), (753065041/9444732965739290427392)), (57/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-1959011787/151115727451828646838272), (889205271/302231454903657293676544)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((576421771/1208925819614629174706176), (-3378814329/2417851639229258349412352)), (35/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((3874647841/38685626227668133590597632), (4611093895/38685626227668133590597632)), (147/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-4790621829/309485009821345068724781056), (397653947/154742504910672534362390528)), (75/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((1328993131/2475880078570760549798248448), (-1760374301/1237940039285380274899124224)), (147/2475880078570760549798248448), by norm_num⟩
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
  | 0 => ⟨((165/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((20480/284097), (-12032/284097)), 0, by norm_num⟩
  | 1 => ⟨((-4161536/2445791073), (246415360/80711105409)), 0, by norm_num⟩
  | 2 => ⟨((-76168560640/22929782913380673), (-3349474705408/22929782913380673)), 0, by norm_num⟩
  | 3 => ⟨((226094949/70368744177664), (2924412073/562949953421312)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-1016975505/4503599627370496), (-536844301/4503599627370496)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((6147076577/576460752303423488), (-279719221/576460752303423488)), (7/576460752303423488), by norm_num⟩
  | 6 => ⟨((-3450273579/9223372036854775808), (2244030033/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((2458959217/295147905179352825856), (-4926285137/295147905179352825856)), (1/18446744073709551616), by norm_num⟩
  | 8 => ⟨((251000975/4722366482869645213696), (7348279885/9444732965739290427392)), (15/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-2779205793/151115727451828646838272), (-2033850193/75557863725914323419136)), (29/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((372621695/302231454903657293676544), (43882107/75557863725914323419136)), (27/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-1097456191/19342813113834066795298816), (100085481/19342813113834066795298816)), (25/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((4791980043/2475880078570760549798248448), (-859106209/618970019642690137449562112)), (23/618970019642690137449562112), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((165/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((165/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((165/16), (1551/256)))⁻¹=value ((20480/284097), (-12032/284097)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((20480/284097), (-12032/284097))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3426066413/9223372036854775808), (-3478625755/9223372036854775808)), (19/9223372036854775808), by norm_num⟩
  | 1 => ⟨((5649433635/18446744073709551616), (-711776987/18446744073709551616)), (1/576460752303423488), by norm_num⟩
  | 2 => ⟨((-1801282611/36893488147419103232), (3164786919/36893488147419103232)), (3/4611686018427387904), by norm_num⟩
  | 3 => ⟨((-1377625011/147573952589676412928), (-1541578203/73786976294838206464)), (29/147573952589676412928), by norm_num⟩
  | 4 => ⟨((2484051259/590295810358705651712), (1024615181/1180591620717411303424)), (13/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-2386440541/4722366482869645213696), (2238013903/4722366482869645213696)), (5/590295810358705651712), by norm_num⟩
  | 6 => ⟨((-1112519861/75557863725914323419136), (-928487159/9444732965739290427392)), (111/75557863725914323419136), by norm_num⟩
  | 7 => ⟨((3542436157/302231454903657293676544), (1696164295/302231454903657293676544)), (71/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-3267077811/2417851639229258349412352), (1951309789/2417851639229258349412352)), (41/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((131564609/19342813113834066795298816), (-431913337/2417851639229258349412352)), (181/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((4891660989/309485009821345068724781056), (3383720537/309485009821345068724781056)), (97/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-4477058519/2475880078570760549798248448), (1934764583/2475880078570760549798248448)), (25/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((536765053/19807040628566084398385987584), (-1898525505/9903520314283042199192993792)), (199/19807040628566084398385987584), by norm_num⟩
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
  | 0 => ⟨((181/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((741376/10792417), (-397056/10792417)), 0, by norm_num⟩
  | 1 => ⟨((-195992453120/116476264701889), (294367789056/116476264701889)), 0, by norm_num⟩
  | 2 => ⟨((397779871/35184372088832), (-517904027/4398046511104)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((1000844027/562949953421312), (1197001121/281474976710656)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((-2509250257/18014398509481984), (-1021061125/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((1980008601/288230376151711744), (767453749/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 6 => ⟨((-2402119065/9223372036854775808), (1487528585/18446744073709551616)), (15/18446744073709551616), by norm_num⟩
  | 7 => ⟨((2202372053/295147905179352825856), (-557867541/73786976294838206464)), (7/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-553549527/4722366482869645213696), (3749037439/9444732965739290427392)), (25/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((-990030153/302231454903657293676544), (-4772279207/302231454903657293676544)), (11/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((243582757/604462909807314587353088), (4662467519/9671406556917033397649408)), (75/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-3514054925/154742504910672534362390528), (-1415205211/154742504910672534362390528)), (1/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((293460835/309485009821345068724781056), (-1002085/9671406556917033397649408)), (109/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((181/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((181/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((181/16), (1551/256)))⁻¹=value ((741376/10792417), (-397056/10792417)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((741376/10792417), (-397056/10792417))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-726660699/18446744073709551616), (-1806645421/147573952589676412928)), (33/147573952589676412928), by norm_num⟩
  | 1 => ⟨((3128075797/147573952589676412928), (-1049398173/73786976294838206464)), (29/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-392197807/590295810358705651712), (5057268559/590295810358705651712)), (23/295147905179352825856), by norm_num⟩
  | 3 => ⟨((-3647272663/2361183241434822606848), (-3301453813/2361183241434822606848)), (57/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((1887909703/4722366482869645213696), (-713929439/9444732965739290427392)), (53/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-2238002293/75557863725914323419136), (4616405473/75557863725914323419136)), (85/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((-2861988639/604462909807314587353088), (-2676206567/302231454903657293676544)), (121/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((6466026979/4835703278458516698824704), (51785915/302231454903657293676544)), (79/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((-542610753/4835703278458516698824704), (598964895/4835703278458516698824704)), (47/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-350431027/77371252455336267181195264), (-5830656959/309485009821345068724781056)), (211/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((307958707/154742504910672534362390528), (226957403/309485009821345068724781056)), (229/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((-1756025031/9903520314283042199192993792), (2607165907/19807040628566084398385987584)), (15/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((-241219573/158456325028528675187087900672), (-6955778177/316912650057057350374175801344)), (483/316912650057057350374175801344), by norm_num⟩
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
  | 0 => ⟨((197/16), (1551/256)), 0, by norm_num⟩
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
  | 0 => ⟨((806912/12340705), (-397056/12340705)), 0, by norm_num⟩
  | 1 => ⟨((-246726754304/152292999897025), (320389251072/152292999897025)), 0, by norm_num⟩
  | 2 => ⟨((672780741/35184372088832), (-3336933693/35184372088832)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((506988663/562949953421312), (959343399/281474976710656)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-3036251407/36028797018963968), (-3492594009/36028797018963968)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((4974423231/1152921504606846976), (2090842205/1152921504606846976)), (7/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-6280488177/36893488147419103232), (373397047/36893488147419103232)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1594573969/295147905179352825856), (-1811892641/590295810358705651712)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-1201836619/9444732965739290427392), (3537312643/18889465931478580854784)), (17/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((346846681/302231454903657293676544), (-4938055517/604462909807314587353088)), (27/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((1816343651/19342813113834066795298816), (5523199999/19342813113834066795298816)), (43/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-2371760243/309485009821345068724781056), (-18918825/2417851639229258349412352)), (35/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((3727912041/9903520314283042199192993792), (656237523/4951760157141521099596496896)), (7/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((197/16), (1551/256)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((197/16), (1551/256)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((197/16), (1551/256)))⁻¹=value ((806912/12340705), (-397056/12340705)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((806912/12340705), (-397056/12340705))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-7011786517/2361183241434822606848), (1102557501/2361183241434822606848)), (13/590295810358705651712), by norm_num⟩
  | 1 => ⟨((2403585067/2361183241434822606848), (-3954872345/2361183241434822606848)), (3/147573952589676412928), by norm_num⟩
  | 2 => ⟨((266662679/1180591620717411303424), (3082283651/4722366482869645213696)), (5/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-6190924417/37778931862957161709568), (-1122603031/18889465931478580854784)), (51/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((4536738527/151115727451828646838272), (-698857149/37778931862957161709568)), (99/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((-791658085/1208925819614629174706176), (3648346667/604462909807314587353088)), (163/1208925819614629174706176), by norm_num⟩
  | 6 => ⟨((-3240774391/4835703278458516698824704), (-3068276651/4835703278458516698824704)), (15/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((4838073023/38685626227668133590597632), (-211374929/9671406556917033397649408)), (159/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((-2193862605/309485009821345068724781056), (4467612135/309485009821345068724781056)), (97/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-1117597221/1237940039285380274899124224), (-2069992655/1237940039285380274899124224)), (223/2475880078570760549798248448), by norm_num⟩
  | 10 => ⟨((4162195415/19807040628566084398385987584), (476602145/19807040628566084398385987584)), (245/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((-1157990911/79228162514264337593543950336), (1339391337/79228162514264337593543950336)), (65/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((-1520790007/2535301200456458802993406410752), (-5511686333/2535301200456458802993406410752)), (265/1267650600228229401496703205376), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6886326207/8796093022208), (-346542411/2199023255552)), (1799/8796093022208), by norm_num⟩
  | 1 => ⟨((3612921269/4398046511104), (1847234041/4398046511104)), (2107/4398046511104), by norm_num⟩
  | 2 => ⟨((965862081/4398046511104), (4123681565/8796093022208)), (2433/4398046511104), by norm_num⟩
  | 3 => ⟨((-1352406489/35184372088832), (3230777503/17592186044416)), (3735/8796093022208), by norm_num⟩
  | 4 => ⟨((-1278654433/35184372088832), (2344740479/70368744177664)), (17271/70368744177664), by norm_num⟩
  | 5 => ⟨((-1393131167/140737488355328), (845250729/562949953421312)), (64333/562949953421312), by norm_num⟩
  | 6 => ⟨((-3405545963/2251799813685248), (-716549675/1125899906842624)), (50353/1125899906842624), by norm_num⟩
  | 7 => ⟨((-2551521163/18014398509481984), (-3158616469/18014398509481984)), (136383/9007199254740992), by norm_num⟩
  | 8 => ⟨((-241350857/36028797018963968), (-943280921/36028797018963968)), (652839/144115188075855872), by norm_num⟩
  | 9 => ⟨((414007975/1152921504606846976), (-3368876361/1152921504606846976)), (1403341/1152921504606846976), by norm_num⟩
  | 10 => ⟨((2455343383/18446744073709551616), (-2460386155/9223372036854775808)), (2744407/9223372036854775808), by norm_num⟩
  | 11 => ⟨((366439515/18446744073709551616), (-1455855411/73786976294838206464)), (9868031/147573952589676412928), by norm_num⟩
  | 12 => ⟨((2545388313/1180591620717411303424), (-2621707553/2361183241434822606848)), (32901119/2361183241434822606848), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((6886326207/8796093022208), (-346542411/2199023255552)), (225/1099511627776), by norm_num⟩
  | 1 => ⟨((3612921269/4398046511104), (1847234041/4398046511104)), (527/1099511627776), by norm_num⟩
  | 2 => ⟨((965862081/4398046511104), (4123681565/8796093022208)), (4867/8796093022208), by norm_num⟩
  | 3 => ⟨((-1352406489/35184372088832), (3230777503/17592186044416)), (7471/17592186044416), by norm_num⟩
  | 4 => ⟨((-1278654433/35184372088832), (2344740479/70368744177664)), (8637/35184372088832), by norm_num⟩
  | 5 => ⟨((-1393131167/140737488355328), (845250729/562949953421312)), (16089/140737488355328), by norm_num⟩
  | 6 => ⟨((-3405545963/2251799813685248), (-716549675/1125899906842624)), (100797/2251799813685248), by norm_num⟩
  | 7 => ⟨((-2551521163/18014398509481984), (-3158616469/18014398509481984)), (273487/18014398509481984), by norm_num⟩
  | 8 => ⟨((-241350857/36028797018963968), (-943280921/36028797018963968)), (164651/36028797018963968), by norm_num⟩
  | 9 => ⟨((414007975/1152921504606846976), (-3368876361/1152921504606846976)), (724729/576460752303423488), by norm_num⟩
  | 10 => ⟨((2455343383/18446744073709551616), (-2460386155/9223372036854775808)), (1556671/4611686018427387904), by norm_num⟩
  | 11 => ⟨((366439515/18446744073709551616), (-1455855411/73786976294838206464)), (7885495/73786976294838206464), by norm_num⟩
  | 12 => ⟨((2545388313/1180591620717411303424), (-2621707553/2361183241434822606848)), (127348449/2361183241434822606848), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨29,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile029Gamma

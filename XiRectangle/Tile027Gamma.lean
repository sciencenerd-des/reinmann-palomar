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
namespace Reinmann.XiRectangle.Tile027Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨27,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (7473/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (7473/640))
  have he : value ((5/8), (7473/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((213/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((7270400/115402443), (-3188480/115402443)), 0, by norm_num⟩
  | 1 => ⟨((-7115385241600/4439241283456083), (23181524992000/13317723850368249)), 0, by norm_num⟩
  | 2 => ⟨((1860780875/70368744177664), (-5416527017/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((259396019/1125899906842624), (3141242383/1125899906842624)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((-1650114299/36028797018963968), (-1525860911/18014398509481984)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((3012393073/1152921504606846976), (2346693045/1152921504606846976)), (5/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-4073908409/36893488147419103232), (-258450059/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2281767645/590295810358705651712), (-758865633/1180591620717411303424)), (3/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-266537677/2361183241434822606848), (2782332461/37778931862957161709568)), (9/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((1534383949/604462909807314587353088), (-2344925801/604462909807314587353088)), (27/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((-1020106251/38685626227668133590597632), (6084003217/38685626227668133590597632)), (5/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-1661267027/1237940039285380274899124224), (-6583670035/1237940039285380274899124224)), (59/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((2292497467/19807040628566084398385987584), (2950994577/19807040628566084398385987584)), (11/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((213/16), (7473/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((213/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((213/16), (7473/1280)))⁻¹=value ((7270400/115402443), (-3188480/115402443)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((7270400/115402443), (-3188480/115402443))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5748081065/2147483648), (887547967/2147483648)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((3635200/115402443), (-1594240/115402443)), 0, by norm_num⟩
  | 2 => ⟨((-1778846310400/4439241283456083), (5795381248000/13317723850368249)), 0, by norm_num⟩
  | 3 => ⟨((1240520583/281474976710656), (-3611018011/281474976710656)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((259396019/9007199254740992), (3141242383/9007199254740992)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((-1320091439/288230376151711744), (-4882754915/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((4016524097/18446744073709551616), (782231015/4611686018427387904)), (7/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-4655895325/590295810358705651712), (-36921437/18446744073709551616)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((2281767645/9444732965739290427392), (-758865633/18889465931478580854784)), (3/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-3790758073/604462909807314587353088), (1236592205/302231454903657293676544)), (17/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((1227507159/9671406556917033397649408), (-1875940641/9671406556917033397649408)), (23/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-741895455/618970019642690137449562112), (1106182403/154742504910672534362390528)), (15/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-1107511351/19807040628566084398385987584), (-4389113357/19807040628566084398385987584)), (5/2475880078570760549798248448), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-7005/276736), (159/20480)), 0, by norm_num⟩
  | 45 => ⟨((96470770577/4080638361600), (-635523/60293120)), 0, by norm_num⟩
  | 44 => ⟨((-262594884620347/11491077626265600), (6162326418181/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((3202393463/137438953472), (-1386059723/137438953472)), (1/137438953472), by norm_num⟩
  | 42 => ⟨((-826123789/34359738368), (700672163/68719476736)), (1/137438953472), by norm_num⟩
  | 41 => ⟨((1697940687/68719476736), (-360291953/34359738368)), (1/68719476736), by norm_num⟩
  | 40 => ⟨((-870126087/34359738368), (1481203065/137438953472)), (1/68719476736), by norm_num⟩
  | 39 => ⟨((1784105845/68719476736), (-94925377/8589934592)), (1/68719476736), by norm_num⟩
  | 38 => ⟨((-1830980787/68719476736), (778562957/68719476736)), (1/68719476736), by norm_num⟩
  | 37 => ⟨((3761477729/137438953472), (-1597771093/137438953472)), (1/68719476736), by norm_num⟩
  | 36 => ⟨((-1933272303/68719476736), (1640910919/137438953472)), (1/68719476736), by norm_num⟩
  | 35 => ⟨((3977529691/137438953472), (-843247593/68719476736)), (1/68719476736), by norm_num⟩
  | 34 => ⟨((-4095033275/137438953472), (108415597/8589934592)), (1/68719476736), by norm_num⟩
  | 33 => ⟨((4219693645/137438953472), (-892807083/68719476736)), (1/68719476736), by norm_num⟩
  | 32 => ⟨((-2176093303/68719476736), (28744723/2147483648)), (1/68719476736), by norm_num⟩
  | 31 => ⟨((4493266863/137438953472), (-1897086363/137438953472)), (1/68719476736), by norm_num⟩
  | 30 => ⟨((-2321897067/68719476736), (1958210955/137438953472)), (1/68719476736), by norm_num⟩
  | 29 => ⟨((2402374955/68719476736), (-505851065/34359738368)), (1/68719476736), by norm_num⟩
  | 28 => ⟨((-1244314173/34359738368), (1046543133/68719476736)), (1/68719476736), by norm_num⟩
  | 27 => ⟨((5162603551/137438953472), (-1083868555/68719476736)), (1/68719476736), by norm_num⟩
  | 26 => ⟨((-2681139239/68719476736), (561976953/34359738368)), (1/68719476736), by norm_num⟩
  | 25 => ⟨((5578008475/137438953472), (-583558471/34359738368)), (1/68719476736), by norm_num⟩
  | 24 => ⟨((-363238097/8589934592), (2427452241/137438953472)), (1/68719476736), by norm_num⟩
  | 23 => ⟨((758256219/17179869184), (-1264211145/68719476736)), (1/68719476736), by norm_num⟩
  | 22 => ⟨((-396470589/8589934592), (164884529/8589934592)), (1/68719476736), by norm_num⟩
  | 21 => ⟨((1661896131/34359738368), (-1378916989/68719476736)), (1/68719476736), by norm_num⟩
  | 20 => ⟨((-3491110493/68719476736), (1444442091/68719476736)), (1/34359738368), by norm_num⟩
  | 19 => ⟨((459518229/8589934592), (-1516501441/68719476736)), (1/34359738368), by norm_num⟩
  | 18 => ⟨((-3881866207/68719476736), (798061591/34359738368)), (1/34359738368), by norm_num⟩
  | 17 => ⟨((4111940873/68719476736), (-210570373/8589934592)), (1/34359738368), by norm_num⟩
  | 16 => ⟨((-2185480167/34359738368), (1783370645/68719476736)), (1/34359738368), by norm_num⟩
  | 15 => ⟨((145773265/2147483648), (-1894481523/68719476736)), (1/34359738368), by norm_num⟩
  | 14 => ⟨((-5000783105/68719476736), (2020344333/68719476736)), (1/34359738368), by norm_num⟩
  | 13 => ⟨((2694440115/34359738368), (-270512919/8589934592)), (1/34359738368), by norm_num⟩
  | 12 => ⟨((-2921060643/34359738368), (2329864135/68719476736)), (1/34359738368), by norm_num⟩
  | 11 => ⟨((1594592209/17179869184), (-315386383/8589934592)), (1/34359738368), by norm_num⟩
  | 10 => ⟨((-3511328555/34359738368), (687804975/17179869184)), (1/17179869184), by norm_num⟩
  | 9 => ⟨((3905592315/34359738368), (-1512317213/34359738368)), (1/17179869184), by norm_num⟩
  | 8 => ⟨((-1099787857/8589934592), (1679143681/34359738368)), (1/17179869184), by norm_num⟩
  | 7 => ⟨((629343369/4294967296), (-1887261371/34359738368)), (1/17179869184), by norm_num⟩
  | 6 => ⟨((-2941827773/17179869184), (2154142729/34359738368)), (1/17179869184), by norm_num⟩
  | 5 => ⟨((442136703/2147483648), (-1254365451/17179869184)), (1/8589934592), by norm_num⟩
  | 4 => ⟨((-4431379847/17179869184), (23458647/268435456)), (1/8589934592), by norm_num⟩
  | 3 => ⟨((5923123679/17179869184), (-233644759/2147483648)), (1/8589934592), by norm_num⟩
  | 2 => ⟨((-2225698091/4294967296), (1237632007/8589934592)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((4443013655/4294967296), (-916082465/4294967296)), (1/4294967296), by norm_num⟩
  | 0 => ⟨((-824031515/8589934592), (887547967/2147483648)), (1/4294967296), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-43/256), (7473/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-43/256), (7473/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-43/256), (7473/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((5748081065/2147483648), (887547967/2147483648)), (1/2147483648), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((213/16), (7473/1280))) (z:=((-43/256), (7473/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((5748081065/2147483648), (887547967/2147483648))) (r:=(1/2147483648)) (by norm_num) ?_ hs
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
  | 0 => ⟨((205/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2139547937/67108864), (1404081945/67108864)), (3/134217728), by norm_num⟩
  | 1 => ⟨((3913959275/2147483648), (229303655/1073741824)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((35848669888000/4439241283456083), (-48892488306080/13317723850368249)), 0, by norm_num⟩
  | 3 => ⟨((-606829525/8796093022208), (2777511701/35184372088832)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((1208096079/2251799813685248), (-4003673307/2251799813685248)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((93132061/18014398509481984), (5636332179/144115188075855872)), (41/144115188075855872), by norm_num⟩
  | 6 => ⟨((-282773429/576460752303423488), (-3646285449/4611686018427387904)), (57/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1438571771/73786976294838206464), (1935642353/147573952589676412928)), (75/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2898389575/4722366482869645213696), (-991769575/9444732965739290427392)), (193/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((2502082665/151115727451828646838272), (-20200677/4722366482869645213696)), (1/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-3646360039/9671406556917033397649408), (364564731/1208925819614629174706176)), (351/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((492734705/77371252455336267181195264), (-3834823341/309485009821345068724781056)), (465/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-54429781/2475880078570760549798248448), (8094196151/19807040628566084398385987584)), (1227/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-213/16), (-7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1246161185/67108864), (2024563045/134217728)), (1/33554432), by norm_num⟩
  | 1 => ⟨((2840217451/2147483648), (229303655/1073741824)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((35848669888000/4439241283456083), (-48892488306080/13317723850368249)), 0, by norm_num⟩
  | 3 => ⟨((-606829525/8796093022208), (2777511701/35184372088832)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((1208096079/2251799813685248), (-4003673307/2251799813685248)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((93132061/18014398509481984), (5636332179/144115188075855872)), (41/144115188075855872), by norm_num⟩
  | 6 => ⟨((-282773429/576460752303423488), (-3646285449/4611686018427387904)), (57/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1438571771/73786976294838206464), (1935642353/147573952589676412928)), (75/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2898389575/4722366482869645213696), (-991769575/9444732965739290427392)), (193/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((2502082665/151115727451828646838272), (-20200677/4722366482869645213696)), (1/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-3646360039/9671406556917033397649408), (364564731/1208925819614629174706176)), (351/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((492734705/77371252455336267181195264), (-3834823341/309485009821345068724781056)), (465/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-54429781/2475880078570760549798248448), (8094196151/19807040628566084398385987584)), (1227/19807040628566084398385987584), by norm_num⟩
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
  | 0 => ⟨((653915053/33554432), (2024563045/134217728)), (5/134217728), by norm_num⟩
  | 1 => ⟨((2840217451/2147483648), (229303655/1073741824)), (1/1073741824), by norm_num⟩
  | 2 => ⟨((35848669888000/4439241283456083), (-48892488306080/13317723850368249)), 0, by norm_num⟩
  | 3 => ⟨((-606829525/8796093022208), (2777511701/35184372088832)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((1208096079/2251799813685248), (-4003673307/2251799813685248)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((93132061/18014398509481984), (5636332179/144115188075855872)), (41/144115188075855872), by norm_num⟩
  | 6 => ⟨((-282773429/576460752303423488), (-3646285449/4611686018427387904)), (57/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1438571771/73786976294838206464), (1935642353/147573952589676412928)), (75/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2898389575/4722366482869645213696), (-991769575/9444732965739290427392)), (193/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((2502082665/151115727451828646838272), (-20200677/4722366482869645213696)), (1/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-3646360039/9671406556917033397649408), (364564731/1208925819614629174706176)), (351/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((492734705/77371252455336267181195264), (-3834823341/309485009821345068724781056)), (465/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-54429781/2475880078570760549798248448), (8094196151/19807040628566084398385987584)), (1227/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((14230770483200/4439241283456083), (-46363049984000/13317723850368249)), 0, by norm_num⟩
  | 1 => ⟨((-1860780875/17592186044416), (5416527017/17592186044416)), (1/17592186044416), by norm_num⟩
  | 2 => ⟨((-389094029/281474976710656), (-2355931787/140737488355328)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((1650114299/4503599627370496), (1525860911/2251799813685248)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((-3765491341/144115188075855872), (-1466683153/72057594037927936)), (5/144115188075855872), by norm_num⟩
  | 5 => ⟨((3055431307/2305843009213693952), (775350177/2305843009213693952)), (9/4611686018427387904), by norm_num⟩
  | 6 => ⟨((-3993093379/73786976294838206464), (664007429/73786976294838206464)), (1/9223372036854775808), by norm_num⟩
  | 7 => ⟨((266537677/147573952589676412928), (-2782332461/2361183241434822606848)), (13/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((-1726181943/37778931862957161709568), (1319020763/18889465931478580854784)), (11/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((637566407/1208925819614629174706176), (-3802502011/1208925819614629174706176)), (17/1208925819614629174706176), by norm_num⟩
  | 10 => ⟨((571060541/19342813113834066795298816), (4526273149/38685626227668133590597632)), (25/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-429843275/154742504910672534362390528), (-4426491865/1237940039285380274899124224)), (39/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((1468752659/9903520314283042199192993792), (1593460829/19807040628566084398385987584)), (15/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1860780875/17592186044416), (-5416527017/17592186044416)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((389094029/140737488355328), (2355931787/70368744177664)), (1/140737488355328), by norm_num⟩
  | 2 => ⟨((-309396431/281474976710656), (-4577582733/2251799813685248)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((3765491341/36028797018963968), (1466683153/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((-1909644567/288230376151711744), (-969187721/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 5 => ⟨((1497410017/4611686018427387904), (-124501393/2305843009213693952)), (5/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-1865763739/147573952589676412928), (304317613/36893488147419103232)), (5/147573952589676412928), by norm_num⟩
  | 7 => ⟨((1726181943/4722366482869645213696), (-1319020763/2361183241434822606848)), (9/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-5603611/1180591620717411303424), (2138907381/75557863725914323419136)), (15/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-178456419/604462909807314587353088), (-5657841437/4835703278458516698824704)), (25/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((2364138013/77371252455336267181195264), (3043213157/77371252455336267181195264)), (5/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-4406257977/2475880078570760549798248448), (-2390191243/2475880078570760549798248448)), (1/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((801815333/9903520314283042199192993792), (33648431/4951760157141521099596496896)), (49/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-259396019/140737488355328), (-3141242383/140737488355328)), (3/281474976710656), by norm_num⟩
  | 1 => ⟨((1650114299/1125899906842624), (1525860911/562949953421312)), (1/562949953421312), by norm_num⟩
  | 2 => ⟨((-3765491341/18014398509481984), (-1466683153/9007199254740992)), (3/18014398509481984), by norm_num⟩
  | 3 => ⟨((5092385511/288230376151711744), (1292250295/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 4 => ⟨((-1247841681/1152921504606846976), (830009287/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((1865763739/36893488147419103232), (-304317613/9223372036854775808)), (9/73786976294838206464), by norm_num⟩
  | 6 => ⟨((-2013878933/1180591620717411303424), (1538857557/590295810358705651712)), (9/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((478174805/18889465931478580854784), (-5703753017/37778931862957161709568)), (9/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((535369257/302231454903657293676544), (4243381077/604462909807314587353088)), (17/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-1970115011/9671406556917033397649408), (-2536010965/9671406556917033397649408)), (15/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((4039069813/309485009821345068724781056), (2191008639/309485009821345068724781056)), (25/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-801815333/1237940039285380274899124224), (-33648431/618970019642690137449562112)), (41/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((2094961853/79228162514264337593543950336), (-716552265/79228162514264337593543950336)), (33/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1650114299/2251799813685248), (-1525860911/1125899906842624)), (3/2251799813685248), by norm_num⟩
  | 1 => ⟨((3765491341/18014398509481984), (1466683153/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((-1909644567/72057594037927936), (-969187721/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((4991366723/2305843009213693952), (-415004643/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 4 => ⟨((-1166102337/9223372036854775808), (1521588065/18446744073709551616)), (11/36893488147419103232), by norm_num⟩
  | 5 => ⟨((3020818399/590295810358705651712), (-4616572671/590295810358705651712)), (7/295147905179352825856), by norm_num⟩
  | 6 => ⟨((-209201477/2361183241434822606848), (2495391945/4722366482869645213696)), (15/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-535369257/75557863725914323419136), (-4243381077/151115727451828646838272)), (1/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((2216379387/2417851639229258349412352), (2853012335/2417851639229258349412352)), (1/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-2524418633/38685626227668133590597632), (-2738760799/77371252455336267181195264)), (29/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((1102496083/309485009821345068724781056), (370132741/1237940039285380274899124224)), (27/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-785610695/4951760157141521099596496896), (2149656795/39614081257132168796771975168)), (23/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((3589940803/633825300114114700748351602688), (-3296808005/633825300114114700748351602688)), (39/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3012393073/36028797018963968), (-2346693045/36028797018963968)), (5/36028797018963968), by norm_num⟩
  | 1 => ⟨((3055431307/144115188075855872), (1550700353/288230376151711744)), (1/36028797018963968), by norm_num⟩
  | 2 => ⟨((-1497410017/576460752303423488), (124501393/288230376151711744)), (9/2305843009213693952), by norm_num⟩
  | 3 => ⟨((1865763739/9223372036854775808), (-2434540903/18446744073709551616)), (9/18446744073709551616), by norm_num⟩
  | 4 => ⟨((-3020818399/295147905179352825856), (4616572671/295147905179352825856)), (7/147573952589676412928), by norm_num⟩
  | 5 => ⟨((502083545/2361183241434822606848), (-5988940667/4722366482869645213696)), (9/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((1499033921/75557863725914323419136), (1485183377/18889465931478580854784)), (11/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-886551755/302231454903657293676544), (-570602467/151115727451828646838272)), (25/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((4543953539/19342813113834066795298816), (2464884719/19342813113834066795298816)), (13/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-1102496083/77371252455336267181195264), (-370132741/309485009821345068724781056)), (13/154742504910672534362390528), by norm_num⟩
  | 10 => ⟨((1728343529/2475880078570760549798248448), (-1182311237/4951760157141521099596496896)), (25/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-1076982241/39614081257132168796771975168), (1978084803/79228162514264337593543950336)), (23/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((1837080603/2535301200456458802993406410752), (-4173670017/2535301200456458802993406410752)), (41/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4073908409/576460752303423488), (-258450059/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 1 => ⟨((3993093379/2305843009213693952), (-332003715/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 2 => ⟨((-1865763739/9223372036854775808), (304317613/2305843009213693952)), (5/9223372036854775808), by norm_num⟩
  | 3 => ⟨((2013878933/147573952589676412928), (-1538857557/73786976294838206464)), (5/73786976294838206464), by norm_num⟩
  | 4 => ⟨((-209201477/590295810358705651712), (4990783889/2361183241434822606848)), (1/147573952589676412928), by norm_num⟩
  | 5 => ⟨((-23422405/590295810358705651712), (-1485183377/9444732965739290427392)), (23/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((1034310381/151115727451828646838272), (332851439/37778931862957161709568)), (1/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-378662795/604462909807314587353088), (-1643256479/4835703278458516698824704)), (9/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((3307488249/77371252455336267181195264), (555199111/154742504910672534362390528)), (5/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-720143137/309485009821345068724781056), (1970518729/2475880078570760549798248448)), (21/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((987233721/9903520314283042199192993792), (-3626488805/39614081257132168796771975168)), (21/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((-1837080603/633825300114114700748351602688), (4173670017/633825300114114700748351602688)), (41/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((632319/1267650600228229401496703205376), (-941099971/2535301200456458802993406410752)), (19/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2281767645/4611686018427387904), (758865633/9223372036854775808)), (3/2305843009213693952), by norm_num⟩
  | 1 => ⟨((266537677/2305843009213693952), (-1391166231/18446744073709551616)), (7/18446744073709551616), by norm_num⟩
  | 2 => ⟨((-863090971/73786976294838206464), (2638041527/147573952589676412928)), (5/73786976294838206464), by norm_num⟩
  | 3 => ⟨((956349609/2361183241434822606848), (-712969127/295147905179352825856)), (21/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((1070738515/18889465931478580854784), (4243381077/18889465931478580854784)), (9/9444732965739290427392), by norm_num⟩
  | 5 => ⟨((-886551755/75557863725914323419136), (-4564819735/302231454903657293676544)), (7/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((378662795/302231454903657293676544), (1643256479/2417851639229258349412352)), (5/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((-7559973141/77371252455336267181195264), (-158628317/19342813113834066795298816)), (49/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((925898319/154742504910672534362390528), (-158345255/77371252455336267181195264)), (29/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-1410333887/4951760157141521099596496896), (2590349147/9903520314283042199192993792)), (1/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((1443420473/158456325028528675187087900672), (-819828039/39614081257132168796771975168)), (17/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-8671803/5070602400912917605986812821504), (403328559/316912650057057350374175801344)), (17/1267650600228229401496703205376), by norm_num⟩
  | 12 => ⟨((-70360229/2535301200456458802993406410752), (-5152766561/81129638414606681695789005144064)), (33/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-266537677/9223372036854775808), (2782332461/147573952589676412928)), (9/73786976294838206464), by norm_num⟩
  | 1 => ⟨((863090971/147573952589676412928), (-2638041527/295147905179352825856)), (3/73786976294838206464), by norm_num⟩
  | 2 => ⟨((-358631103/1180591620717411303424), (4277814763/2361183241434822606848)), (19/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-1070738515/18889465931478580854784), (-4243381077/18889465931478580854784)), (21/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((554094847/37778931862957161709568), (1426506167/75557863725914323419136)), (5/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((-4543953539/2417851639229258349412352), (-1232442359/1208925819614629174706176)), (1/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((3307488249/19342813113834066795298816), (277599555/19342813113834066795298816)), (47/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((-925898319/77371252455336267181195264), (1266762041/309485009821345068724781056)), (1/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((3173251245/4951760157141521099596496896), (-1457071395/2475880078570760549798248448)), (5/618970019642690137449562112), by norm_num⟩
  | 9 => ⟨((-1804275591/79228162514264337593543950336), (1024785049/19807040628566084398385987584)), (23/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((745233/158456325028528675187087900672), (-4436614149/1267650600228229401496703205376)), (51/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((211080687/2535301200456458802993406410752), (483071865/2535301200456458802993406410752)), (27/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-355267581/40564819207303340847894502572032), (-1312091987/162259276829213363391578010288128)), (27/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1534383949/1180591620717411303424), (2344925801/1180591620717411303424)), (27/2361183241434822606848), by norm_num⟩
  | 1 => ⟨((318783203/2361183241434822606848), (-3802502011/4722366482869645213696)), (21/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((713825677/18889465931478580854784), (1414460359/9444732965739290427392)), (17/18889465931478580854784), by norm_num⟩
  | 3 => ⟨((-1970115011/151115727451828646838272), (-634002741/37778931862957161709568)), (21/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((2524418633/1208925819614629174706176), (2738760797/2417851639229258349412352)), (41/2417851639229258349412352), by norm_num⟩
  | 5 => ⟨((-4409984331/19342813113834066795298816), (-92533185/4835703278458516698824704)), (9/4835703278458516698824704), by norm_num⟩
  | 6 => ⟨((5761145095/309485009821345068724781056), (-985259365/154742504910672534362390528)), (55/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((-2820667773/2475880078570760549798248448), (2590349147/2475880078570760549798248448)), (39/2475880078570760549798248448), by norm_num⟩
  | 8 => ⟨((1804275591/39614081257132168796771975168), (-4099140195/39614081257132168796771975168)), (51/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((-6624293/633825300114114700748351602688), (1232392819/158456325028528675187087900672)), (63/633825300114114700748351602688), by norm_num⟩
  | 10 => ⟨((-515975013/2535301200456458802993406410752), (-4723369347/10141204801825835211973625643008)), (9/1267650600228229401496703205376), by norm_num⟩
  | 11 => ⟨((118422527/5070602400912917605986812821504), (3498911965/162259276829213363391578010288128)), (5/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-146743429/81129638414606681695789005144064), (-810119301/1298074214633706907132624082305024)), (85/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1020106251/37778931862957161709568), (6084003217/37778931862957161709568)), (5/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((-571060541/37778931862957161709568), (-4526273149/75557863725914323419136)), (35/75557863725914323419136), by norm_num⟩
  | 2 => ⟨((1182069007/151115727451828646838272), (3043213157/302231454903657293676544)), (31/302231454903657293676544), by norm_num⟩
  | 3 => ⟨((-4039069813/2417851639229258349412352), (-1095504319/1208925819614629174706176)), (5/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((4409984331/19342813113834066795298816), (370132739/19342813113834066795298816)), (21/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-3456687057/154742504910672534362390528), (591155619/77371252455336267181195264)), (39/154742504910672534362390528), by norm_num⟩
  | 6 => ⟨((1974467441/1237940039285380274899124224), (-3626488805/2475880078570760549798248448)), (31/1237940039285380274899124224), by norm_num⟩
  | 7 => ⟨((-180427559/2475880078570760549798248448), (819828039/4951760157141521099596496896)), (47/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((745233/39614081257132168796771975168), (-1109153537/79228162514264337593543950336)), (63/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((2063900051/5070602400912917605986812821504), (2361684673/2535301200456458802993406410752)), (41/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-4168472951/81129638414606681695789005144064), (-3848803161/81129638414606681695789005144064)), (49/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((5634947673/1298074214633706907132624082305024), (972143161/649037107316853453566312041152512)), (113/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((-1498651283/5192296858534827628530496329220096), (121727537/5192296858534827628530496329220096)), (125/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1817600/346207329), (-797120/346207329)), 0, by norm_num⟩
  | 1 => ⟨((-1778846310400/13317723850368249), (5795381248000/39953171551104747)), 0, by norm_num⟩
  | 2 => ⟨((1240520583/562949953421312), (-3611018011/562949953421312)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((345861359/18014398509481984), (4188323177/18014398509481984)), (3/18014398509481984), by norm_num⟩
  | 4 => ⟨((-2200152399/576460752303423488), (-4068962429/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 5 => ⟨((4016524097/18446744073709551616), (782231015/4611686018427387904)), (7/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-5431877879/590295810358705651712), (-1378400315/590295810358705651712)), (3/147573952589676412928), by norm_num⟩
  | 7 => ⟨((760589215/2361183241434822606848), (-252955211/4722366482869645213696)), (1/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((-2843068555/302231454903657293676544), (1854888307/302231454903657293676544)), (13/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((2045845265/9671406556917033397649408), (-3126567735/9671406556917033397649408)), (19/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((-340035417/154742504910672534362390528), (4056002145/309485009821345068724781056)), (27/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-1107511351/9903520314283042199192993792), (-4389113357/9903520314283042199192993792)), (5/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((3056663289/316912650057057350374175801344), (983664859/79228162514264337593543950336)), (59/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((654091215/33554432), (2024254017/134217728)), (3/67108864), by norm_num⟩
  | 1 => ⟨((709982653/536870912), (114729703/536870912)), (5/4294967296), by norm_num⟩
  | 2 => ⟨((4440712125/549755813888), (-1010904469/274877906944)), (1/549755813888), by norm_num⟩
  | 3 => ⟨((-1213321295/17592186044416), (696423005/8796093022208)), (7/35184372088832), by norm_num⟩
  | 4 => ⟨((599750867/1125899906842624), (-4019567691/2251799813685248)), (17/2251799813685248), by norm_num⟩
  | 5 => ⟨((776435583/144115188075855872), (2830388449/72057594037927936)), (21/72057594037927936), by norm_num⟩
  | 6 => ⟨((-1152311989/2305843009213693952), (-3657054201/4611686018427387904)), (29/2305843009213693952), by norm_num⟩
  | 7 => ⟨((182792523/9223372036854775808), (1927737503/147573952589676412928)), (19/36893488147419103232), by norm_num⟩
  | 8 => ⟨((-2942812521/4722366482869645213696), (-933804315/9444732965739290427392)), (195/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((5068097995/302231454903657293676544), (-695274285/151115727451828646838272)), (129/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-3667612253/9671406556917033397649408), (3043267915/9671406556917033397649408)), (353/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((968164545/154742504910672534362390528), (-3971983133/309485009821345068724781056)), (467/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-30549599/2475880078570760549798248448), (4170056183/9903520314283042199192993792)), (77/1237940039285380274899124224), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-330805489/1125899906842624), (3851752545/4503599627370496)), (1/2251799813685248), by norm_num⟩
  | 1 => ⟨((-553378175/72057594037927936), (-6701317083/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 2 => ⟨((1760121919/576460752303423488), (3255169943/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((-2677682731/9223372036854775808), (-2085949373/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 4 => ⟨((5431877879/295147905179352825856), (689200157/147573952589676412928)), (1/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-1064824901/1180591620717411303424), (708274591/4722366482869645213696)), (1/590295810358705651712), by norm_num⟩
  | 6 => ⟨((2653530651/75557863725914323419136), (-1731229087/75557863725914323419136)), (1/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-2455014319/2417851639229258349412352), (3751881281/2417851639229258349412352)), (7/1208925819614629174706176), by norm_num⟩
  | 8 => ⟨((1020106251/77371252455336267181195264), (-6084003217/77371252455336267181195264)), (11/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((1015218739/1237940039285380274899124224), (4023353911/1237940039285380274899124224)), (19/1237940039285380274899124224), by norm_num⟩
  | 10 => ⟨((-1681164809/19807040628566084398385987584), (-4328125379/39614081257132168796771975168)), (15/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((1566669503/316912650057057350374175801344), (1699691551/633825300114114700748351602688)), (3/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((-4561438339/20282409603651670423947251286016), (-191422185/10141204801825835211973625643008)), (9/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2616364821/134217728), (506063533/33554432)), (7/134217728), by norm_num⟩
  | 1 => ⟨((5679861191/4294967296), (917837225/4294967296)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((1110178451/137438953472), (-1010902917/274877906944)), (1/274877906944), by norm_num⟩
  | 3 => ⟨((-2426652805/35184372088832), (2785684063/35184372088832)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((149942897/281474976710656), (-4019557175/2251799813685248)), (9/1125899906842624), by norm_num⟩
  | 5 => ⟨((776305599/144115188075855872), (5660798513/144115188075855872)), (43/144115188075855872), by norm_num⟩
  | 6 => ⟨((-2304462019/4611686018427387904), (-3657159867/4611686018427387904)), (59/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1462265263/73786976294838206464), (481991625/36893488147419103232)), (77/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5885500517/9444732965739290427392), (-934546991/9444732965739290427392)), (49/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((5068345851/302231454903657293676544), (-694783153/151115727451828646838272)), (259/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-1834216567/4835703278458516698824704), (760552811/2417851639229258349412352)), (177/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((1937859041/309485009821345068724781056), (-3971153205/309485009821345068724781056)), (117/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((-124425661/9903520314283042199192993792), (8339738495/19807040628566084398385987584)), (1233/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2682090543/4611686018427387904), (-4960258961/4611686018427387904)), (3/2305843009213693952), by norm_num⟩
  | 1 => ⟨((765052209/4611686018427387904), (2383942141/18446744073709551616)), (1/4611686018427387904), by norm_num⟩
  | 2 => ⟨((-3103930217/147573952589676412928), (-1575314645/295147905179352825856)), (7/295147905179352825856), by norm_num⟩
  | 3 => ⟨((4056475813/2361183241434822606848), (-674547229/2361183241434822606848)), (7/2361183241434822606848), by norm_num⟩
  | 4 => ⟨((-3790758073/37778931862957161709568), (1236592205/18889465931478580854784)), (5/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((1227507159/302231454903657293676544), (-1875940641/302231454903657293676544)), (3/151115727451828646838272), by norm_num⟩
  | 6 => ⟨((-680070833/9671406556917033397649408), (2028001073/4835703278458516698824704)), (13/9671406556917033397649408), by norm_num⟩
  | 7 => ⟨((-870187491/154742504910672534362390528), (-1724294533/77371252455336267181195264)), (7/77371252455336267181195264), by norm_num⟩
  | 8 => ⟨((900624005/1237940039285380274899124224), (579659649/618970019642690137449562112)), (27/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((-256448877/4951760157141521099596496896), (-1112893277/39614081257132168796771975168)), (3/9903520314283042199192993792), by norm_num⟩
  | 10 => ⟨((7167974533/2535301200456458802993406410752), (300806291/1267650600228229401496703205376)), (45/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((-5107716519/40564819207303340847894502572032), (1747022665/40564819207303340847894502572032)), (19/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((364692399/81129638414606681695789005144064), (-2679310633/649037107316853453566312041152512)), (33/649037107316853453566312041152512), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2616364821/134217728), (506063533/33554432)), (1/16777216), by norm_num⟩
  | 1 => ⟨((709982649/536870912), (458918613/2147483648)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((69386153/8589934592), (-2021805837/549755813888)), (3/549755813888), by norm_num⟩
  | 3 => ⟨((-2426652745/35184372088832), (2785684053/35184372088832)), (9/35184372088832), by norm_num⟩
  | 4 => ⟨((599771475/1125899906842624), (-1004889257/562949953421312)), (19/2251799813685248), by norm_num⟩
  | 5 => ⟨((97038273/18014398509481984), (2830398809/72057594037927936)), (11/36028797018963968), by norm_num⟩
  | 6 => ⟨((-2304462343/4611686018427387904), (-3657157933/4611686018427387904)), (15/1152921504606846976), by norm_num⟩
  | 7 => ⟨((91391553/4611686018427387904), (1927963211/147573952589676412928)), (39/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-2942746823/4722366482869645213696), (-467269073/4722366482869645213696)), (197/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((5068330199/302231454903657293676544), (-1389574797/302231454903657293676544)), (65/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((-1834202895/4835703278458516698824704), (3042213539/9671406556917033397649408)), (355/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((242227509/38685626227668133590597632), (-992784969/77371252455336267181195264)), (469/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-124381143/9903520314283042199192993792), (8339656729/19807040628566084398385987584)), (617/9903520314283042199192993792), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2483144173/590295810358705651712), (315062929/295147905179352825856)), (11/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((-152117843/147573952589676412928), (809456677/4722366482869645213696)), (11/4722366482869645213696), by norm_num⟩
  | 2 => ⟨((4548909687/37778931862957161709568), (-741955323/9444732965739290427392)), (7/18889465931478580854784), by norm_num⟩
  | 3 => ⟨((-1227507159/151115727451828646838272), (1875940641/151115727451828646838272)), (13/302231454903657293676544), by norm_num⟩
  | 4 => ⟨((510053125/2417851639229258349412352), (-6084003217/4835703278458516698824704)), (5/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((456848433/19342813113834066795298816), (3621018519/38685626227668133590597632)), (15/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((-2521747215/618970019642690137449562112), (-1623047017/309485009821345068724781056)), (21/618970019642690137449562112), by norm_num⟩
  | 7 => ⟨((3692863829/9903520314283042199192993792), (1001603949/4951760157141521099596496896)), (23/9903520314283042199192993792), by norm_num⟩
  | 8 => ⟨((-4031985675/158456325028528675187087900672), (-338407077/158456325028528675187087900672)), (25/158456325028528675187087900672), by norm_num⟩
  | 9 => ⟨((1755777553/1267650600228229401496703205376), (-600539041/1267650600228229401496703205376)), (27/2535301200456458802993406410752), by norm_num⟩
  | 10 => ⟨((-1203484917/20282409603651670423947251286016), (276303909/5070602400912917605986812821504)), (27/40564819207303340847894502572032), by norm_num⟩
  | 11 => ⟨((2239488735/1298074214633706907132624082305024), (-5087902497/1298074214633706907132624082305024)), (51/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((-770827/2596148429267413814265248164610048), (1147245679/5192296858534827628530496329220096)), (47/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2616364821/134217728), (506063533/33554432)), (9/134217728), by norm_num⟩
  | 1 => ⟨((709982649/536870912), (458918613/2147483648)), (1/536870912), by norm_num⟩
  | 2 => ⟨((69386153/8589934592), (-2021805837/549755813888)), (1/137438953472), by norm_num⟩
  | 3 => ⟨((-2426652745/35184372088832), (2785684053/35184372088832)), (5/17592186044416), by norm_num⟩
  | 4 => ⟨((599771475/1125899906842624), (-4019557031/2251799813685248)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((776306187/144115188075855872), (5660797631/144115188075855872)), (45/144115188075855872), by norm_num⟩
  | 6 => ⟨((-1152231181/2305843009213693952), (-3657157957/4611686018427387904)), (61/4611686018427387904), by norm_num⟩
  | 7 => ⟨((2924529751/147573952589676412928), (1927963241/147573952589676412928)), (79/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-2942746943/4722366482869645213696), (-467269083/4722366482869645213696)), (99/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((2534165309/151115727451828646838272), (-347393735/75557863725914323419136)), (261/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-917101591/2417851639229258349412352), (1521107033/4835703278458516698824704)), (89/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((968910303/154742504910672534362390528), (-3971141089/309485009821345068724781056)), (235/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((-62190573/4951760157141521099596496896), (8339661105/19807040628566084398385987584)), (1235/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-459485827/18889465931478580854784), (599559857/37778931862957161709568)), (1/9444732965739290427392), by norm_num⟩
  | 1 => ⟨((1487887465/302231454903657293676544), (-568466861/75557863725914323419136)), (11/302231454903657293676544), by norm_num⟩
  | 2 => ⟨((-618246211/2417851639229258349412352), (1843637339/1208925819614629174706176)), (17/2417851639229258349412352), by norm_num⟩
  | 3 => ⟨((-922926127/19342813113834066795298816), (-114299827/604462909807314587353088)), (19/19342813113834066795298816), by norm_num⟩
  | 4 => ⟨((1910414557/154742504910672534362390528), (1229581073/77371252455336267181195264)), (19/154742504910672534362390528), by norm_num⟩
  | 5 => ⟨((-1958336879/1237940039285380274899124224), (-2124614437/2475880078570760549798248448)), (29/2475880078570760549798248448), by norm_num⟩
  | 6 => ⟨((1425449481/9903520314283042199192993792), (239277731/19807040628566084398385987584)), (41/39614081257132168796771975168), by norm_num⟩
  | 7 => ⟨((-399040353/39614081257132168796771975168), (2183778333/633825300114114700748351602688)), (7/79228162514264337593543950336), by norm_num⟩
  | 8 => ⟨((85474781/158456325028528675187087900672), (-1255926859/2535301200456458802993406410752)), (35/5070602400912917605986812821504), by norm_num⟩
  | 9 => ⟨((-1555200509/81129638414606681695789005144064), (3533265623/81129638414606681695789005144064)), (41/81129638414606681695789005144064), by norm_num⟩
  | 10 => ⟨((10277691/2596148429267413814265248164610048), (-3824152263/1298074214633706907132624082305024)), (89/2596148429267413814265248164610048), by norm_num⟩
  | 11 => ⟨((727766409/10384593717069655257060992658440192), (3331081413/20769187434139310514121985316880384)), (3/1298074214633706907132624082305024), by norm_num⟩
  | 12 => ⟨((-1224895633/166153499473114484112975882535043072), (-2261922887/332306998946228968225951765070086144)), (3/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2616364821/134217728), (506063533/33554432)), (5/67108864), by norm_num⟩
  | 1 => ⟨((709982649/536870912), (458918613/2147483648)), (9/4294967296), by norm_num⟩
  | 2 => ⟨((69386153/8589934592), (-2021805837/549755813888)), (5/549755813888), by norm_num⟩
  | 3 => ⟨((-2426652745/35184372088832), (2785684053/35184372088832)), (11/35184372088832), by norm_num⟩
  | 4 => ⟨((599771475/1125899906842624), (-4019557031/2251799813685248)), (21/2251799813685248), by norm_num⟩
  | 5 => ⟨((776306187/144115188075855872), (5660797631/144115188075855872)), (23/72057594037927936), by norm_num⟩
  | 6 => ⟨((-2304462361/4611686018427387904), (-3657157957/4611686018427387904)), (31/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1462264875/73786976294838206464), (963981621/73786976294838206464)), (5/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-5885493881/9444732965739290427392), (-934538171/9444732965739290427392)), (199/9444732965739290427392), by norm_num⟩
  | 9 => ⟨((1267082653/75557863725914323419136), (-1389574927/302231454903657293676544)), (131/151115727451828646838272), by norm_num⟩
  | 10 => ⟨((-917101591/2417851639229258349412352), (1521107019/4835703278458516698824704)), (357/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((484455157/77371252455336267181195264), (-3971141039/309485009821345068724781056)), (471/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((-124381219/9903520314283042199192993792), (4169830485/9903520314283042199192993792)), (309/4951760157141521099596496896), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((250378393/4835703278458516698824704), (-5973114847/19342813113834066795298816)), (5/2417851639229258349412352), by norm_num⟩
  | 1 => ⟨((560652267/19342813113834066795298816), (4443776307/38685626227668133590597632)), (35/38685626227668133590597632), by norm_num⟩
  | 2 => ⟨((-2321048719/154742504910672534362390528), (-1493873445/77371252455336267181195264)), (31/154742504910672534362390528), by norm_num⟩
  | 3 => ⟨((3965452845/1237940039285380274899124224), (537768709/309485009821345068724781056)), (5/154742504910672534362390528), by norm_num⟩
  | 4 => ⟨((-2164803497/4951760157141521099596496896), (-363386619/9903520314283042199192993792)), (21/4951760157141521099596496896), by norm_num⟩
  | 5 => ⟨((848421181/19807040628566084398385987584), (-1160762175/79228162514264337593543950336)), (5/9903520314283042199192993792), by norm_num⟩
  | 6 => ⟨((-3876960733/1267650600228229401496703205376), (3560391629/1267650600228229401496703205376)), (31/633825300114114700748351602688), by norm_num⟩
  | 7 => ⟨((1417112375/10141204801825835211973625643008), (-3219542697/10141204801825835211973625643008)), (47/10141204801825835211973625643008), by norm_num⟩
  | 8 => ⟨((-2926601/81129638414606681695789005144064), (2177875725/81129638414606681695789005144064)), (63/162259276829213363391578010288128), by norm_num⟩
  | 9 => ⟨((-1013141479/1298074214633706907132624082305024), (-2318640093/1298074214633706907132624082305024)), (41/1298074214633706907132624082305024), by norm_num⟩
  | 10 => ⟨((4092497453/41538374868278621028243970633760768), (3778654035/41538374868278621028243970633760768)), (97/41538374868278621028243970633760768), by norm_num⟩
  | 11 => ⟨((-5532243887/664613997892457936451903530140172288), (-1908849335/664613997892457936451903530140172288)), (7/41538374868278621028243970633760768), by norm_num⟩
  | 12 => ⟨((5885346151/10633823966279326983230456482242756608), (-478035617/10633823966279326983230456482242756608)), (31/2658455991569831745807614120560689152), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2616364821/134217728), (506063533/33554432)), (11/134217728), by norm_num⟩
  | 1 => ⟨((709982649/536870912), (458918613/2147483648)), (5/2147483648), by norm_num⟩
  | 2 => ⟨((69386153/8589934592), (-2021805837/549755813888)), (3/274877906944), by norm_num⟩
  | 3 => ⟨((-2426652745/35184372088832), (2785684053/35184372088832)), (3/8796093022208), by norm_num⟩
  | 4 => ⟨((599771475/1125899906842624), (-4019557031/2251799813685248)), (11/1125899906842624), by norm_num⟩
  | 5 => ⟨((776306187/144115188075855872), (5660797631/144115188075855872)), (47/144115188075855872), by norm_num⟩
  | 6 => ⟨((-2304462361/4611686018427387904), (-3657157957/4611686018427387904)), (63/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1462264875/73786976294838206464), (963981621/73786976294838206464)), (81/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-5885493881/9444732965739290427392), (-934538171/9444732965739290427392)), (25/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1267082653/75557863725914323419136), (-86848433/18889465931478580854784)), (263/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((-3668406363/9671406556917033397649408), (3042214039/9671406556917033397649408)), (179/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((1937820625/309485009821345068724781056), (-248196315/19342813113834066795298816)), (59/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((-248762427/19807040628566084398385987584), (8339660969/19807040628566084398385987584)), (1237/19807040628566084398385987584), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-496797857221869/2097152), (359259522331577/2097152)), (36999365/524288), by norm_num⟩
  | 1 => ⟨((-2799080641/8), 175922016), (1751/16), by norm_num⟩
  | 2 => ⟨((-502865695/2), (1299092697/16)), (1369/16), by norm_num⟩
  | 3 => ⟨((-236138363/2), (628973001/32)), (1439/32), by norm_num⟩
  | 4 => ⟨((-5240764313/128), (60885717/64)), (143/8), by norm_num⟩
  | 5 => ⟨((-2871217893/256), (-653237255/512)), (2935/512), by norm_num⟩
  | 6 => ⟨((-1296570719/512), (-324073359/512)), (99/64), by norm_num⟩
  | 7 => ⟨((-3974424485/8192), (-1551117285/8192)), (1479/4096), by norm_num⟩
  | 8 => ⟨((-659622679/8192), (-712303449/16384)), (4879/65536), by norm_num⟩
  | 9 => ⟨((-3081157931/262144), (-2172661945/262144)), (1805/131072), by norm_num⟩
  | 10 => ⟨((-3199739669/2097152), (-2861301601/2097152)), (1213/524288), by norm_num⟩
  | 11 => ⟨((-2977688909/16777216), (-1666541945/8388608)), (5983/16777216), by norm_num⟩
  | 12 => ⟨((-1247084271/67108864), (-3491414461/134217728)), (6825/134217728), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((804684072606057/5070602400912917605986812821504), (1638358464929/5070602400912917605986812821504)), (106759/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1812601521123653/633825300114114700748351602688), (2007928094037/316912650057057350374175801344)), (131365/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1927841865783611/39614081257132168796771975168), (35384202885/309485009821345068724781056)), (74109/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1930034384470255/2475880078570760549798248448), (4822042477027/2475880078570760549798248448)), (157845/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1811741275916733/154742504910672534362390528), (4833003621629/154742504910672534362390528)), (158251/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((793806433406381/4835703278458516698824704), (4542620417465/9671406556917033397649408)), (148793/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((323033513839111/151115727451828646838272), (996627975667/151115727451828646838272)), (32657/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((971029889566773/37778931862957161709568), (6500139412327/75557863725914323419136)), (213087/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((83644485960595/295147905179352825856), (611811211053/590295810358705651712)), (160535/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((838813332413433/295147905179352825856), (3380791940073/295147905179352825856)), (110955/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1893873393865591/73786976294838206464), (4249875914683/36893488147419103232)), (139581/36893488147419103232), by norm_num⟩
  | 7 => ⟨((951049020784887/4611686018427387904), (9628367200107/9223372036854775808)), (79129/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1673651367794371/1152921504606846976), (2427936368869/288230376151711744)), (319619/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1264633313858233/144115188075855872), (268516960097/4503599627370496)), (141599/72057594037927936), by norm_num⟩
  | 4 => ⟨((1597412513563859/36028797018963968), (6540391976313/18014398509481984)), (215981/18014398509481984), by norm_num⟩
  | 3 => ⟨((1622708295566747/9007199254740992), (16692489579315/9007199254740992)), (552725/9007199254740992), by norm_num⟩
  | 2 => ⟨((1249299016048871/2251799813685248), (17216067874733/2251799813685248)), (572361/2251799813685248), by norm_num⟩
  | 1 => ⟨((328955102965435/281474976710656), (27173511259761/1125899906842624)), (909345/1125899906842624), by norm_num⟩
  | 0 => ⟨((1525610959194173/1125899906842624), (29997255239891/562949953421312)), (2032511/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((1525610959194173/1125899906842624), (29997255239891/562949953421312)), (7753414158347701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1032014232971459/562949953421312), (1270210085439/8796093022208)), (2862387/562949953421312), by norm_num⟩
  | 2 => ⟨((470043893931835/140737488355328), (298058441111821/562949953421312)), (11321495/562949953421312), by norm_num⟩
  | 3 => ⟨((1530429721283089/140737488355328), (248868570692645/70368744177664)), (10951625/70368744177664), by norm_num⟩
  | 4 => ⟨((930132801833953/8796093022208), (338285717022005/4398046511104)), (39455947/8796093022208), by norm_num⟩
  | 5 => ⟨((180921110840831/34359738368), (1117863639145203/68719476736)), (56305217/34359738368), by norm_num⟩
  | 6 => ⟨((-496797857221869/2097152), (359259522331577/2097152)), (36999365/524288), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((2616364821/134217728), (506063533/33554432)), (11/134217728), by norm_num⟩, 2, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((716800/19556043), (-3188480/19556043)), 0, by norm_num⟩
  | 1 => ⟨((536255692800/42493201979761), (2285502464000/382438817817849)), 0, by norm_num⟩
  | 2 => ⟨((-1579919269/2199023255552), (4042961221/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-2173431247/35184372088832), (-2653517705/35184372088832)), (1/17592186044416), by norm_num⟩
  | 4 => ⟨((4098417517/562949953421312), (-2056817147/562949953421312)), (1/140737488355328), by norm_num⟩
  | 5 => ⟨((1481025445/9007199254740992), (743608961/1125899906842624)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-2048416179/36028797018963968), (187387105/144115188075855872)), (3/36028797018963968), by norm_num⟩
  | 7 => ⟨((269775375/288230376151711744), (-5371159217/1152921504606846976)), (11/1152921504606846976), by norm_num⟩
  | 8 => ⟨((209044511/576460752303423488), (745625327/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-1462936561/73786976294838206464), (3925382823/147573952589676412928)), (17/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-2131052539/1180591620717411303424), (-2483693115/1180591620717411303424)), (15/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((241530055/1180591620717411303424), (-2051338167/18889465931478580854784)), (25/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((385618995/75557863725914323419136), (1410532713/75557863725914323419136)), (41/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((21/16), (7473/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((21/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((21/16), (7473/1280)))⁻¹=value ((716800/19556043), (-3188480/19556043)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((716800/19556043), (-3188480/19556043))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((37/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3788800/64607329), (-9565440/64607329)), 0, by norm_num⟩
  | 1 => ⟨((38571318476800/4174106960514241), (36241539072000/4174106960514241)), 0, by norm_num⟩
  | 2 => ⟨((-4018461513/4398046511104), (1888849849/4398046511104)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-21998533/4398046511104), (-5645777655/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((3426107653/562949953421312), (557952551/281474976710656)), (1/281474976710656), by norm_num⟩
  | 5 => ⟨((-2929074499/9007199254740992), (441811887/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((-2812228725/144115188075855872), (-160234845/4503599627370496)), (1/18014398509481984), by norm_num⟩
  | 7 => ⟨((7392586641/2305843009213693952), (-231338341/576460752303423488)), (7/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-1186095787/18446744073709551616), (2297551189/9223372036854775808)), (3/4611686018427387904), by norm_num⟩
  | 9 => ⟨((-4886169663/295147905179352825856), (-1780321361/147573952589676412928)), (21/295147905179352825856), by norm_num⟩
  | 10 => ⟨((1627426323/1180591620717411303424), (-1029226873/1180591620717411303424)), (9/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((455553895/18889465931478580854784), (37663265/295147905179352825856)), (31/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-3068754939/302231454903657293676544), (-36955061/18889465931478580854784)), (53/604462909807314587353088), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((37/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((37/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((37/16), (7473/1280)))⁻¹=value ((3788800/64607329), (-9565440/64607329)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3788800/64607329), (-9565440/64607329))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-27783402291200/1263463704039147), (-18937020416000/1263463704039147)), 0, by norm_num⟩
  | 1 => ⟨((3715451933/1099511627776), (-2975651873/1099511627776)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((1717245951/8796093022208), (538527843/1099511627776)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((-1997442983/35184372088832), (169371123/35184372088832)), (3/70368744177664), by norm_num⟩
  | 4 => ⟨((84038733/70368744177664), (-6345444499/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 5 => ⟨((551262493/1125899906842624), (150898537/562949953421312)), (7/9007199254740992), by norm_num⟩
  | 6 => ⟨((-2690717995/72057594037927936), (2657451073/72057594037927936)), (7/72057594037927936), by norm_num⟩
  | 7 => ⟨((-2617191821/1152921504606846976), (-4908482535/1152921504606846976)), (3/288230376151711744), by norm_num⟩
  | 8 => ⟨((1968880035/4611686018427387904), (-100787567/1152921504606846976)), (3/2305843009213693952), by norm_num⟩
  | 9 => ⟨((-482788289/147573952589676412928), (5705704185/147573952589676412928)), (21/147573952589676412928), by norm_num⟩
  | 10 => ⟨((-1879239431/590295810358705651712), (-727233121/590295810358705651712)), (19/1180591620717411303424), by norm_num⟩
  | 11 => ⟨((3408926985/18889465931478580854784), (-4461787127/18889465931478580854784)), (33/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((576403865/37778931862957161709568), (1558352957/75557863725914323419136)), (7/37778931862957161709568), by norm_num⟩
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
  | 0 => ⟨((53/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((102400/1392893), (-180480/1392893)), 0, by norm_num⟩
  | 1 => ⟨((11043635200/1940150909449), (18481152000/1940150909449)), 0, by norm_num⟩
  | 2 => ⟨((-2233173278720000/2702422620715145957), (50342658048000/2702422620715145957)), 0, by norm_num⟩
  | 3 => ⟨((2052548923/70368744177664), (-953871509/17592186044416)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((2747880333/1125899906842624), (2185809821/562949953421312)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((-6147624313/18014398509481984), (17332125/1125899906842624)), (1/4503599627370496), by norm_num⟩
  | 6 => ⟨((416016951/36028797018963968), (-408473655/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 7 => ⟨((1204313781/1152921504606846976), (1823406609/1152921504606846976)), (7/2305843009213693952), by norm_num⟩
  | 8 => ⟨((-162399465/1152921504606846976), (351931865/36893488147419103232)), (13/36893488147419103232), by norm_num⟩
  | 9 => ⟨((2691571593/590295810358705651712), (-1398460897/147573952589676412928)), (11/295147905179352825856), by norm_num⟩
  | 10 => ⟨((526932047/1180591620717411303424), (1519979531/2361183241434822606848)), (19/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-2195382353/37778931862957161709568), (396934871/75557863725914323419136)), (31/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((2170880321/1208925819614629174706176), (-2392405863/604462909807314587353088)), (51/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((53/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((53/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((53/16), (7473/1280)))⁻¹=value ((102400/1392893), (-180480/1392893)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((102400/1392893), (-180480/1392893))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3912785399/1099511627776), (480321835/274877906944)), (1/1099511627776), by norm_num⟩
  | 1 => ⟨((-372248921/4398046511104), (-2048586909/2199023255552)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((4970863509/35184372088832), (1388765895/35184372088832)), (3/35184372088832), by norm_num⟩
  | 3 => ⟨((-1590360515/140737488355328), (2169033865/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-1379857623/1125899906842624), (-2102817531/1125899906842624)), (3/1125899906842624), by norm_num⟩
  | 5 => ⟨((4265362287/18014398509481984), (-1916917/35184372088832)), (7/18014398509481984), by norm_num⟩
  | 6 => ⟨((-452569731/144115188075855872), (7174627945/288230376151711744)), (15/288230376151711744), by norm_num⟩
  | 7 => ⟨((-159661605/72057594037927936), (-655599811/576460752303423488)), (7/1152921504606846976), by norm_num⟩
  | 8 => ⟨((3231612243/18446744073709551616), (-3015868759/18446744073709551616)), (7/9223372036854775808), by norm_num⟩
  | 9 => ⟨((41143585/4611686018427387904), (760945581/36893488147419103232)), (7/73786976294838206464), by norm_num⟩
  | 10 => ⟨((-2429486569/1180591620717411303424), (334750397/2361183241434822606848)), (25/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((927840957/18889465931478580854784), (-3386501185/18889465931478580854784)), (23/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((2055676485/151115727451828646838272), (351780617/37778931862957161709568)), (5/37778931862957161709568), by norm_num⟩
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
  | 0 => ⟨((69/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2355200/28772043), (-3188480/28772043)), 0, by norm_num⟩
  | 1 => ⟨((769906278400/275943486131283), (7509508096000/827830458393849)), 0, by norm_num⟩
  | 2 => ⟨((-5425692483/8796093022208), (-476483011/2199023255552)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((655345091/17592186044416), (-445253777/17592186044416)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((-275347277/2251799813685248), (3490295255/1125899906842624)), (7/2251799813685248), by norm_num⟩
  | 5 => ⟨((-3004162801/18014398509481984), (-601925489/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 6 => ⟨((1025461679/72057594037927936), (-1086636319/288230376151711744)), (5/144115188075855872), by norm_num⟩
  | 7 => ⟨((-1722769903/4611686018427387904), (2174041249/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 8 => ⟨((-681655203/18446744073709551616), (-4374697001/73786976294838206464)), (13/36893488147419103232), by norm_num⟩
  | 9 => ⟨((5663934599/1180591620717411303424), (447520657/1180591620717411303424)), (41/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-2052910797/9444732965739290427392), (2364147939/9444732965739290427392)), (1/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-187892317/37778931862957161709568), (-6736375999/302231454903657293676544)), (25/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((3478236429/2417851639229258349412352), (769690605/1208925819614629174706176)), (39/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((69/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((69/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((69/16), (7473/1280)))⁻¹=value ((2355200/28772043), (-3188480/28772043)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((2355200/28772043), (-3188480/28772043))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107375271/1099511627776), (4727048109/8796093022208)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((-1195794233/8796093022208), (-3317322797/35184372088832)), (1/8796093022208), by norm_num⟩
  | 2 => ⟨((3761527517/140737488355328), (-2265773079/140737488355328)), (5/140737488355328), by norm_num⟩
  | 3 => ⟨((654222651/1125899906842624), (2619806075/562949953421312)), (3/562949953421312), by norm_num⟩
  | 4 => ⟨((-5304661663/9007199254740992), (-1579334985/9007199254740992)), (9/9007199254740992), by norm_num⟩
  | 5 => ⟨((3398525165/72057594037927936), (-1011597207/18014398509481984)), (11/72057594037927936), by norm_num⟩
  | 6 => ⟨((2122867675/576460752303423488), (4206588443/576460752303423488)), (13/576460752303423488), by norm_num⟩
  | 7 => ⟨((-7954859523/9223372036854775808), (133356677/2305843009213693952)), (13/4611686018427387904), by norm_num⟩
  | 8 => ⟨((2089461731/73786976294838206464), (-6120822519/73786976294838206464)), (13/36893488147419103232), by norm_num⟩
  | 9 => ⟨((3809378829/590295810358705651712), (1671674711/295147905179352825856)), (13/295147905179352825856), by norm_num⟩
  | 10 => ⟨((-3450614345/4722366482869645213696), (1725625539/4722366482869645213696)), (25/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((-467538785/75557863725914323419136), (-5709306929/75557863725914323419136)), (47/75557863725914323419136), by norm_num⟩
  | 12 => ⟨((1990353581/302231454903657293676544), (302911861/151115727451828646838272)), (43/604462909807314587353088), by norm_num⟩
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
  | 0 => ⟨((85/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8704000/102085729), (-9565440/102085729)), 0, by norm_num⟩
  | 1 => ⟨((7869013196800/10421496065461441), (83257589760000/10421496065461441)), 0, by norm_num⟩
  | 2 => ⟨((-3575396987/8796093022208), (-1342299213/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((4451131111/140737488355328), (-848972781/140737488355328)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-149981037/140737488355328), (244728069/140737488355328)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((-1298355615/36028797018963968), (-1117413063/9007199254740992)), (7/36028797018963968), by norm_num⟩
  | 6 => ⟨((2118026809/288230376151711744), (1037736057/288230376151711744)), (11/576460752303423488), by norm_num⟩
  | 7 => ⟨((-4445159199/9223372036854775808), (1759682389/9223372036854775808)), (17/9223372036854775808), by norm_num⟩
  | 8 => ⟨((856477377/73786976294838206464), (-4532361551/147573952589676412928)), (13/73786976294838206464), by norm_num⟩
  | 9 => ⟨((1114532837/1180591620717411303424), (4375525661/2361183241434822606848)), (39/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-4800327443/37778931862957161709568), (-328402051/9444732965739290427392)), (57/37778931862957161709568), by norm_num⟩
  | 11 => ⟨((66546141/9444732965739290427392), (-337790587/75557863725914323419136)), (83/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((-439669775/4835703278458516698824704), (5035751375/9671406556917033397649408)), (15/1208925819614629174706176), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((85/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((85/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((85/16), (7473/1280)))⁻¹=value ((8704000/102085729), (-9565440/102085729)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8704000/102085729), (-9565440/102085729))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1478739117/35184372088832), (1934098367/35184372088832)), (1/17592186044416), by norm_num⟩
  | 1 => ⟨((-6978460057/281474976710656), (608681097/140737488355328)), (1/35184372088832), by norm_num⟩
  | 2 => ⟨((1829144749/1125899906842624), (-2940232519/562949953421312)), (9/1125899906842624), by norm_num⟩
  | 3 => ⟨((744254169/1125899906842624), (2887288101/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 4 => ⟨((-4498530579/36028797018963968), (1580648355/36028797018963968)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((292124801/144115188075855872), (-2439450563/144115188075855872)), (13/288230376151711744), by norm_num⟩
  | 6 => ⟨((982496163/576460752303423488), (630475415/576460752303423488)), (17/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-3542042727/18446744073709551616), (2194576643/18446744073709551616)), (9/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-202633497/73786976294838206464), (-3511320267/147573952589676412928)), (37/295147905179352825856), by norm_num⟩
  | 9 => ⟨((5460781933/2361183241434822606848), (450935485/590295810358705651712)), (37/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-3068480255/18889465931478580854784), (207084531/1180591620717411303424)), (37/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-1345001615/151115727451828646838272), (-3166028449/151115727451828646838272)), (35/151115727451828646838272), by norm_num⟩
  | 12 => ⟨((2551203107/1208925819614629174706176), (72571263/2417851639229258349412352)), (33/1208925819614629174706176), by norm_num⟩
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
  | 0 => ⟨((101/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((10342400/121132129), (-9565440/121132129)), 0, by norm_num⟩
  | 1 => ⟨((-7733797683200/14672992676072641), (98929606656000/14672992676072641)), 0, by norm_num⟩
  | 2 => ⟨((-2143678737/8796093022208), (-1357427017/4398046511104)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((1589654429/70368744177664), (1000279755/281474976710656)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-4975161221/4503599627370496), (1666863559/2251799813685248)), (7/4503599627370496), by norm_num⟩
  | 5 => ⟨((323061121/18014398509481984), (-169377741/2251799813685248)), (5/36028797018963968), by norm_num⟩
  | 6 => ⟨((2541397713/1152921504606846976), (282408981/72057594037927936)), (7/576460752303423488), by norm_num⟩
  | 7 => ⟨((-4590426067/18446744073709551616), (-370223807/4611686018427387904)), (5/4611686018427387904), by norm_num⟩
  | 8 => ⟨((4071021455/295147905179352825856), (-59012903/9223372036854775808)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-793864757/2361183241434822606848), (3861689445/4722366482869645213696)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((-1355070707/75557863725914323419136), (-1820374785/37778931862957161709568)), (3/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((1612786145/604462909807314587353088), (1630764093/1208925819614629174706176)), (1/18889465931478580854784), by norm_num⟩
  | 12 => ⟨((-6466873533/38685626227668133590597632), (1847635803/38685626227668133590597632)), (169/38685626227668133590597632), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((101/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((101/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((101/16), (7473/1280)))⁻¹=value ((10342400/121132129), (-9565440/121132129)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((10342400/121132129), (-9565440/121132129))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((4463781969/562949953421312), (96727907/70368744177664)), (7/562949953421312), by norm_num⟩
  | 1 => ⟨((-1220509629/562949953421312), (2906452671/1125899906842624)), (7/1125899906842624), by norm_num⟩
  | 2 => ⟨((-637473141/2251799813685248), (-3467924043/4503599627370496)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((2694142039/18014398509481984), (873137913/36028797018963968)), (13/36028797018963968), by norm_num⟩
  | 4 => ⟨((-1047548243/72057594037927936), (1331333079/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 5 => ⟨((-1467077009/1152921504606846976), (-427743781/144115188075855872)), (13/1152921504606846976), by norm_num⟩
  | 6 => ⟨((930175423/2305843009213693952), (325212627/9223372036854775808)), (35/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-1889933547/73786976294838206464), (2932502123/73786976294838206464)), (5/18446744073709551616), by norm_num⟩
  | 8 => ⟨((-1528346987/590295810358705651712), (-2669682377/590295810358705651712)), (21/590295810358705651712), by norm_num⟩
  | 9 => ⟨((161412689/295147905179352825856), (-125425651/4722366482869645213696)), (11/2361183241434822606848), by norm_num⟩
  | 10 => ⟨((-105386779/4722366482869645213696), (954505255/18889465931478580854784)), (11/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-2089513849/604462909807314587353088), (-1246497295/302231454903657293676544)), (43/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((2383837545/4835703278458516698824704), (-37627655/302231454903657293676544)), (81/9671406556917033397649408), by norm_num⟩
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
  | 0 => ⟨((117/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1331200/15939481), (-3188480/47818443)), 0, by norm_num⟩
  | 1 => ⟨((-2891218124800/2286603490944249), (4244504576000/762201163648083)), 0, by norm_num⟩
  | 2 => ⟨((-1168643975/8796093022208), (-604059183/2199023255552)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((4139396701/281474976710656), (3870947/549755813888)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-3822863485/4503599627370496), (220976181/1125899906842624)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((2082656699/72057594037927936), (-1314897323/36028797018963968)), (5/72057594037927936), by norm_num⟩
  | 6 => ⟨((708407/72057594037927936), (2867990851/1152921504606846976)), (13/2305843009213693952), by norm_num⟩
  | 7 => ⟨((-1537448131/18446744073709551616), (-1910136371/18446744073709551616)), (17/36893488147419103232), by norm_num⟩
  | 8 => ⟨((4092273593/590295810358705651712), (228045735/147573952589676412928)), (21/590295810358705651712), by norm_num⟩
  | 9 => ⟨((-1610372875/4722366482869645213696), (1573491419/9444732965739290427392)), (13/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((2625037141/302231454903657293676544), (-2769337971/151115727451828646838272)), (1/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((18760045/75557863725914323419136), (2550407981/2417851639229258349412352)), (39/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((-1761557739/38685626227668133590597632), (-691883373/19342813113834066795298816)), (95/77371252455336267181195264), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((117/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((117/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((117/16), (7473/1280)))⁻¹=value ((1331200/15939481), (-3188480/47818443)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((1331200/15939481), (-3188480/47818443))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3395155237/4503599627370496), (-932053683/2251799813685248)), (9/4503599627370496), by norm_num⟩
  | 1 => ⟨((-59943029/2251799813685248), (3626063013/9007199254740992)), (5/4503599627370496), by norm_num⟩
  | 2 => ⟨((-3145238467/36028797018963968), (-2274561587/36028797018963968)), (3/9007199254740992), by norm_num⟩
  | 3 => ⟨((715398519/36028797018963968), (-2369946315/288230376151711744)), (21/288230376151711744), by norm_num⟩
  | 4 => ⟨((-77418225/144115188075855872), (1013919209/288230376151711744)), (17/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-3680379341/9223372036854775808), (-3023756531/9223372036854775808)), (23/9223372036854775808), by norm_num⟩
  | 6 => ⟨((2347671865/36893488147419103232), (-1738941555/73786976294838206464)), (31/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-401584503/295147905179352825856), (1200167855/147573952589676412928)), (37/590295810358705651712), by norm_num⟩
  | 8 => ⟨((-1728662719/2361183241434822606848), (-2786366689/4722366482869645213696)), (5/590295810358705651712), by norm_num⟩
  | 9 => ⟨((889183737/9444732965739290427392), (-1452739475/37778931862957161709568)), (43/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((-691352417/604462909807314587353088), (6318276077/604462909807314587353088)), (89/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-4180128047/4835703278458516698824704), (-2846126199/4835703278458516698824704)), (11/604462909807314587353088), by norm_num⟩
  | 12 => ⟨((3427092953/38685626227668133590597632), (-918985817/19342813113834066795298816)), (85/38685626227668133590597632), by norm_num⟩
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
  | 0 => ⟨((133/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13619200/169055329), (-9565440/169055329)), 0, by norm_num⟩
  | 1 => ⟨((-46992483123200/28579704263298241), (130273640448000/28579704263298241)), 0, by norm_num⟩
  | 2 => ⟨((-1103481801/17592186044416), (-1012102753/4398046511104)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((2543705533/281474976710656), (527411121/70368744177664)), (1/140737488355328), by norm_num⟩
  | 4 => ⟨((-2594318083/4503599627370496), (-208216211/4503599627370496)), (3/4503599627370496), by norm_num⟩
  | 5 => ⟨((441562141/18014398509481984), (-1040135481/72057594037927936)), (7/144115188075855872), by norm_num⟩
  | 6 => ⟨((-2669997141/4611686018427387904), (5879402061/4611686018427387904)), (17/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-470280179/36893488147419103232), (-4997769695/73786976294838206464)), (5/18446744073709551616), by norm_num⟩
  | 8 => ⟨((2868435849/1180591620717411303424), (349404847/147573952589676412928)), (23/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-6227877295/37778931862957161709568), (-503080973/18889465931478580854784)), (13/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((69831493/9444732965739290427392), (-1085307777/302231454903657293676544)), (29/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-1897804599/9671406556917033397649408), (855483953/2417851639229258349412352)), (65/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((-81461393/38685626227668133590597632), (-6128868187/309485009821345068724781056)), (143/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((133/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((133/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((133/16), (7473/1280)))⁻¹=value ((13619200/169055329), (-9565440/169055329)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13619200/169055329), (-9565440/169055329))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((2688662105/72057594037927936), (-2738218551/36028797018963968)), (21/72057594037927936), by norm_num⟩
  | 1 => ⟨((1533454305/72057594037927936), (5484267101/144115188075855872)), (25/144115188075855872), by norm_num⟩
  | 2 => ⟨((-7228057065/576460752303423488), (-621003255/576460752303423488)), (31/576460752303423488), by norm_num⟩
  | 3 => ⟨((1925305669/1152921504606846976), (-2417955849/1152921504606846976)), (15/1152921504606846976), by norm_num⟩
  | 4 => ⟨((1363491283/9223372036854775808), (4109087819/9223372036854775808)), (25/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-2555017493/36893488147419103232), (-649177869/36893488147419103232)), (35/73786976294838206464), by norm_num⟩
  | 6 => ⟨((4179462473/590295810358705651712), (-3984239023/590295810358705651712)), (3/36893488147419103232), by norm_num⟩
  | 7 => ⟨((605175767/2361183241434822606848), (2843666453/2361183241434822606848)), (59/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-2583337923/18889465931478580854784), (-894782461/18889465931478580854784)), (67/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((3704622697/302231454903657293676544), (-3138921545/302231454903657293676544)), (73/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((90481005/302231454903657293676544), (4042437539/2417851639229258349412352)), (77/2417851639229258349412352), by norm_num⟩
  | 11 => ⟨((-6278672197/38685626227668133590597632), (-2219772119/38685626227668133590597632)), (155/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((1951196739/154742504910672534362390528), (-3441558529/309485009821345068724781056)), (19/38685626227668133590597632), by norm_num⟩
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
  | 0 => ⟨((149/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((15257600/197932129), (-9565440/197932129)), 0, by norm_num⟩
  | 1 => ⟨((-70648357683200/39177127690472641), (145945657344000/39177127690472641)), 0, by norm_num⟩
  | 2 => ⟨((-360843021/17592186044416), (-6584951629/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((1495445071/281474976710656), (3781793847/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-3306520391/9007199254740992), (-587917035/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((4987320539/288230376151711744), (-1106473543/288230376151711744)), (7/288230376151711744), by norm_num⟩
  | 6 => ⟨((-2647801987/4611686018427387904), (2610512863/4611686018427387904)), (1/576460752303423488), by norm_num⟩
  | 7 => ⟨((155895857/18446744073709551616), (-2633531097/73786976294838206464)), (17/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1267222033/2361183241434822606848), (3730265655/2361183241434822606848)), (9/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-555911761/9444732965739290427392), (-1810453519/37778931862957161709568)), (37/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((4142454439/1208925819614629174706176), (513550843/1208925819614629174706176)), (19/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((-344139443/2417851639229258349412352), (2569676481/38685626227668133590597632)), (77/38685626227668133590597632), by norm_num⟩
  | 12 => ⟨((1201053827/309485009821345068724781056), (-3713459535/618970019642690137449562112)), (39/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((149/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((149/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((149/16), (7473/1280)))⁻¹=value ((15257600/197932129), (-9565440/197932129)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((15257600/197932129), (-9565440/197932129))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-229614053/288230376151711744), (-2208343301/288230376151711744)), (11/288230376151711744), by norm_num⟩
  | 1 => ⟨((33284729/9007199254740992), (1257296399/576460752303423488)), (7/288230376151711744), by norm_num⟩
  | 2 => ⟨((-2798682817/2305843009213693952), (2435627725/4611686018427387904)), (37/4611686018427387904), by norm_num⟩
  | 3 => ⟨((1132492971/18446744073709551616), (-5387421371/18446744073709551616)), (37/18446744073709551616), by norm_num⟩
  | 4 => ⟨((2775590631/73786976294838206464), (2946884999/73786976294838206464)), (33/73786976294838206464), by norm_num⟩
  | 5 => ⟨((-5078701107/590295810358705651712), (802845589/590295810358705651712)), (47/590295810358705651712), by norm_num⟩
  | 6 => ⟨((2447795695/4722366482869645213696), (-1325535953/1180591620717411303424)), (65/4722366482869645213696), by norm_num⟩
  | 7 => ⟨((3215398211/37778931862957161709568), (2573682653/18889465931478580854784)), (83/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((-5864518787/302231454903657293676544), (-35826605/151115727451828646838272)), (97/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((45205157/37778931862957161709568), (-2239767325/1208925819614629174706176)), (27/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((1983109151/19342813113834066795298816), (519190469/2417851639229258349412352)), (115/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-3779443697/154742504910672534362390528), (-368078197/154742504910672534362390528)), (237/309485009821345068724781056), by norm_num⟩
  | 12 => ⟨((3548982477/2475880078570760549798248448), (-152039599/77371252455336267181195264)), (59/618970019642690137449562112), by norm_num⟩
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
  | 0 => ⟨((165/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5632000/76695243), (-3188480/76695243)), 0, by norm_num⟩
  | 1 => ⟨((-3592169881600/1960720099609683), (17957519360000/5882160298829049)), 0, by norm_num⟩
  | 2 => ⟨((33498219/8796093022208), (-1320947651/8796093022208)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((1678603487/562949953421312), (787155529/140737488355328)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-4066633125/18014398509481984), (-1291433015/9007199254740992)), (5/18014398509481984), by norm_num⟩
  | 5 => ⟨((3248044413/288230376151711744), (164841837/288230376151711744)), (5/288230376151711744), by norm_num⟩
  | 6 => ⟨((-3925892725/9223372036854775808), (245854503/1152921504606846976)), (5/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1652192223/147573952589676412928), (-2461154043/147573952589676412928)), (19/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-304124449/4722366482869645213696), (7981387395/9444732965739290427392)), (9/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-574294713/37778931862957161709568), (-4891105255/151115727451828646838272)), (17/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((2976237009/2417851639229258349412352), (1054677979/1208925819614629174706176)), (1/75557863725914323419136), by norm_num⟩
  | 11 => ⟨((-4899976625/77371252455336267181195264), (-498642781/77371252455336267181195264)), (15/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((3044421505/1237940039285380274899124224), (-1336731805/1237940039285380274899124224)), (7/154742504910672534362390528), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((165/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((165/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((165/16), (7473/1280)))⁻¹=value ((5632000/76695243), (-3188480/76695243)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((5632000/76695243), (-3188480/76695243))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3477428625/9223372036854775808), (-2441928693/4611686018427387904)), (21/4611686018427387904), by norm_num⟩
  | 1 => ⟨((111512349/288230376151711744), (83654617/4611686018427387904)), (7/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-3016205727/36893488147419103232), (1782296275/18446744073709551616)), (39/36893488147419103232), by norm_num⟩
  | 3 => ⟨((-979886091/147573952589676412928), (-4315898713/147573952589676412928)), (41/147573952589676412928), by norm_num⟩
  | 4 => ⟨((3113432119/590295810358705651712), (1360464005/590295810358705651712)), (19/295147905179352825856), by norm_num⟩
  | 5 => ⟨((-3857315481/4722366482869645213696), (1139442489/2361183241434822606848)), (7/590295810358705651712), by norm_num⟩
  | 6 => ⟨((107159623/9444732965739290427392), (-2619888605/18889465931478580854784)), (79/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((4346325415/302231454903657293676544), (3564893199/302231454903657293676544)), (103/302231454903657293676544), by norm_num⟩
  | 8 => ⟨((-667316255/302231454903657293676544), (1584004011/2417851639229258349412352)), (31/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((1514484525/19342813113834066795298816), (-2473419629/9671406556917033397649408)), (141/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((45690511/2417851639229258349412352), (871352427/38685626227668133590597632)), (19/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-3781255961/1237940039285380274899124224), (503250557/1237940039285380274899124224)), (159/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((630195317/4951760157141521099596496896), (-5591774237/19807040628566084398385987584)), (161/9903520314283042199192993792), by norm_num⟩
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
  | 0 => ⟨((181/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((18534400/265516129), (-9565440/265516129)), 0, by norm_num⟩
  | 1 => ⟨((-126013170483200/70498814759144641), (177289691136000/70498814759144641)), 0, by norm_num⟩
  | 2 => ⟨((75153663/4398046511104), (-1055266155/8796093022208)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((880787651/562949953421312), (39538993/8796093022208)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-2442347991/18014398509481984), (-289821153/2251799813685248)), (3/18014398509481984), by norm_num⟩
  | 5 => ⟨((2032135363/288230376151711744), (1181768133/576460752303423488)), (3/288230376151711744), by norm_num⟩
  | 6 => ⟨((-5220501027/18446744073709551616), (1022803371/18446744073709551616)), (11/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1310282585/147573952589676412928), (-518939745/73786976294838206464)), (5/147573952589676412928), by norm_num⟩
  | 8 => ⟨((-432592253/2361183241434822606848), (3828908255/9444732965739290427392)), (9/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-274414411/302231454903657293676544), (-5273849597/302231454903657293676544)), (31/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((418300753/1208925819614629174706176), (358255989/604462909807314587353088)), (27/4835703278458516698824704), by norm_num⟩
  | 11 => ⟨((-3520799943/154742504910672534362390528), (-1118291549/77371252455336267181195264)), (47/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((5221517275/4951760157141521099596496896), (234282571/2475880078570760549798248448)), (81/4951760157141521099596496896), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((181/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((181/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((181/16), (7473/1280)))⁻¹=value ((18534400/265516129), (-9565440/265516129)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((18534400/265516129), (-9565440/265516129))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-3349500411/73786976294838206464), (-862565023/36893488147419103232)), (9/18446744073709551616), by norm_num⟩
  | 1 => ⟨((4377880207/147573952589676412928), (-1870251327/147573952589676412928)), (51/147573952589676412928), by norm_num⟩
  | 2 => ⟨((-447628069/147573952589676412928), (1574088347/147573952589676412928)), (75/590295810358705651712), by norm_num⟩
  | 3 => ⟨((-946462065/590295810358705651712), (-2631789581/1180591620717411303424)), (21/590295810358705651712), by norm_num⟩
  | 4 => ⟨((2584660841/4722366482869645213696), (186928491/9444732965739290427392)), (39/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-2232454143/37778931862957161709568), (2730688885/37778931862957161709568)), (61/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-1040923237/302231454903657293676544), (-516726747/37778931862957161709568)), (43/151115727451828646838272), by norm_num⟩
  | 7 => ⟨((2170468889/1208925819614629174706176), (871194955/1208925819614629174706176)), (115/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((-1993949791/9671406556917033397649408), (640551421/4835703278458516698824704)), (71/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((164320519/154742504910672534362390528), (-4489094913/154742504910672534362390528)), (41/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((3238520477/1237940039285380274899124224), (2380752613/1237940039285380274899124224)), (181/1237940039285380274899124224), by norm_num⟩
  | 11 => ⟨((-3213906077/9903520314283042199192993792), (586372667/4951760157141521099596496896)), (3/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((313226795/39614081257132168796771975168), (-5430362967/158456325028528675187087900672)), (393/158456325028528675187087900672), by norm_num⟩
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
  | 0 => ⟨((197/16), (7473/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((20172800/304223329), (-9565440/304223329)), 0, by norm_num⟩
  | 1 => ⟨((-157722108723200/92551833907842241), (192961708032000/92551833907842241)), 0, by norm_num⟩
  | 2 => ⟨((1669386557/70368744177664), (-6749432989/70368744177664)), (1/70368744177664), by norm_num⟩
  | 3 => ⟨((406084507/562949953421312), (4000308043/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((-1437060855/18014398509481984), (-239720801/2251799813685248)), (1/9007199254740992), by norm_num⟩
  | 5 => ⟨((311178113/72057594037927936), (1311699475/576460752303423488)), (7/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-6602060773/36893488147419103232), (-69638489/9223372036854775808)), (3/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1786142347/295147905179352825856), (-189112397/73786976294838206464)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((-1514451599/9444732965739290427392), (1701115759/9444732965739290427392)), (1/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1501929103/604462909807314587353088), (-5133351375/604462909807314587353088)), (13/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((988991829/19342813113834066795298816), (6201795699/19342813113834066795298816)), (21/9671406556917033397649408), by norm_num⟩
  | 11 => ⟨((-2084616963/309485009821345068724781056), (-190069977/19342813113834066795298816)), (17/154742504910672534362390528), by norm_num⟩
  | 12 => ⟨((1870789033/4951760157141521099596496896), (272218569/1237940039285380274899124224)), (55/9903520314283042199192993792), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((197/16), (7473/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((197/16), (7473/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((197/16), (7473/1280)))⁻¹=value ((20172800/304223329), (-9565440/304223329)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((20172800/304223329), (-9565440/304223329))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4421511269/1180591620717411303424), (-36305673/295147905179352825856)), (57/1180591620717411303424), by norm_num⟩
  | 1 => ⟨((4001575373/2361183241434822606848), (-4316030133/2361183241434822606848)), (85/2361183241434822606848), by norm_num⟩
  | 2 => ⟨((252156375/2361183241434822606848), (4202439599/4722366482869645213696)), (33/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-1831713655/9444732965739290427392), (-2365514195/18889465931478580854784)), (77/18889465931478580854784), by norm_num⟩
  | 4 => ⟨((855949731/18889465931478580854784), (-558889127/37778931862957161709568)), (37/37778931862957161709568), by norm_num⟩
  | 5 => ⟨((-881155377/302231454903657293676544), (2373644711/302231454903657293676544)), (59/302231454903657293676544), by norm_num⟩
  | 6 => ⟨((-1656805965/2417851639229258349412352), (-2671447021/2417851639229258349412352)), (43/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((1758229219/9671406556917033397649408), (665150701/38685626227668133590597632)), (29/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((-1222753001/77371252455336267181195264), (2716336723/154742504910672534362390528)), (147/154742504910672534362390528), by norm_num⟩
  | 9 => ⟨((-1469998473/2475880078570760549798248448), (-6901437391/2475880078570760549798248448)), (43/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((5891476641/19807040628566084398385987584), (317783693/2475880078570760549798248448)), (387/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((-4702179093/158456325028528675187087900672), (2927715021/158456325028528675187087900672)), (13/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((177670867/1267650600228229401496703205376), (-2281870307/633825300114114700748351602688)), (27/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3994617897/4398046511104), (-2693531983/4398046511104)), (161/549755813888), by norm_num⟩
  | 1 => ⟨((2734893207/2199023255552), (472878683/4398046511104)), (783/1099511627776), by norm_num⟩
  | 2 => ⟨((1105025075/2199023255552), (4152015347/8796093022208)), (455/549755813888), by norm_num⟩
  | 3 => ⟨((355241239/8796093022208), (66513437/274877906944)), (11165/17592186044416), by norm_num⟩
  | 4 => ⟨((-247418343/8796093022208), (496882345/8796093022208)), (3221/8796093022208), by norm_num⟩
  | 5 => ⟨((-765464681/70368744177664), (1736197521/281474976710656)), (12005/70368744177664), by norm_num⟩
  | 6 => ⟨((-4492056455/2251799813685248), (-64072185/1125899906842624)), (150839/2251799813685248), by norm_num⟩
  | 7 => ⟨((-4205791457/18014398509481984), (-2345627219/18014398509481984)), (410939/18014398509481984), by norm_num⟩
  | 8 => ⟨((-1378596405/72057594037927936), (-901411161/36028797018963968)), (990941/144115188075855872), by norm_num⟩
  | 9 => ⟨((-1155630265/1152921504606846976), (-1878585365/576460752303423488)), (1074077/576460752303423488), by norm_num⟩
  | 10 => ⟨((105011257/9223372036854775808), (-6348032147/18446744073709551616)), (8474747/18446744073709551616), by norm_num⟩
  | 11 => ⟨((1639960541/147573952589676412928), (-4435383835/147573952589676412928)), (3840875/36893488147419103232), by norm_num⟩
  | 12 => ⟨((488909449/295147905179352825856), (-1288383541/590295810358705651712)), (25811339/1180591620717411303424), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3994617897/4398046511104), (-2693531983/4398046511104)), (1289/4398046511104), by norm_num⟩
  | 1 => ⟨((2734893207/2199023255552), (472878683/4398046511104)), (3133/4398046511104), by norm_num⟩
  | 2 => ⟨((1105025075/2199023255552), (4152015347/8796093022208)), (7281/8796093022208), by norm_num⟩
  | 3 => ⟨((355241239/8796093022208), (66513437/274877906944)), (5583/8796093022208), by norm_num⟩
  | 4 => ⟨((-247418343/8796093022208), (496882345/8796093022208)), (25771/70368744177664), by norm_num⟩
  | 5 => ⟨((-765464681/70368744177664), (1736197521/281474976710656)), (1501/8796093022208), by norm_num⟩
  | 6 => ⟨((-4492056455/2251799813685248), (-64072185/1125899906842624)), (75465/1125899906842624), by norm_num⟩
  | 7 => ⟨((-4205791457/18014398509481984), (-2345627219/18014398509481984)), (102915/4503599627370496), by norm_num⟩
  | 8 => ⟨((-1378596405/72057594037927936), (-901411161/36028797018963968)), (498353/72057594037927936), by norm_num⟩
  | 9 => ⟨((-1155630265/1152921504606846976), (-1878585365/576460752303423488)), (2194271/1152921504606846976), by norm_num⟩
  | 10 => ⟨((105011257/9223372036854775808), (-6348032147/18446744073709551616)), (9212617/18446744073709551616), by norm_num⟩
  | 11 => ⟨((1639960541/147573952589676412928), (-4435383835/147573952589676412928)), (21266459/147573952589676412928), by norm_num⟩
  | 12 => ⟨((488909449/295147905179352825856), (-1288383541/590295810358705651712)), (18258751/295147905179352825856), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨27,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile027Gamma

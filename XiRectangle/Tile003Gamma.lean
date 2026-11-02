/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 38 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile003Gamma
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨3,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (987/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (987/640))
  have he : value ((3/4), (987/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_halfVariable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/8), (987/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((11/8), (987/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((107/8), (987/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((21913600/294068569), (-1263360/294068569)), 0, by norm_num⟩
  | 1 => ⟨((-239304893235200/86476323273707761), (27684765696000/86476323273707761)), 0, by norm_num⟩
  | 2 => ⟨((461257000887/4503599627370496), (-80491193781/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 3 => ⟨((-272211670743/72057594037927936), (7979722133/9007199254740992)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((320169549243/2305843009213693952), (-94825059543/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 5 => ⟨((-375219658219/73786976294838206464), (135067699889/73786976294838206464)), (3/73786976294838206464), by norm_num⟩
  | 6 => ⟨((219044813947/1180591620717411303424), (-93416499897/1180591620717411303424)), (3/1180591620717411303424), by norm_num⟩
  | 7 => ⟨((-15921598767/2361183241434822606848), (126437138179/37778931862957161709568)), (5/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((147520889931/604462909807314587353088), (-168261613705/1208925819614629174706176)), (7/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-170105974295/19342813113834066795298816), (110449387907/19342813113834066795298816)), (5/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((195225049821/618970019642690137449562112), (-143381459609/618970019642690137449562112)), (7/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-222910800151/19807040628566084398385987584), (184372970359/19807040628566084398385987584)), (5/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((253102801985/633825300114114700748351602688), (-117575084653/316912650057057350374175801344)), (7/316912650057057350374175801344), by norm_num⟩
  | _ => zero

theorem V_shiftInv : F_shift c=value ((107/8), (987/1280)) := by
  have h := centre_contains S_shift
  have he : J_shift ⟨0,by omega⟩=exact ((107/8), (987/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_shift,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_shiftInv : Sound J_shiftInv F_shiftInv c := by
  apply inv_coefficients_sound (A_shift hcre) (N_shiftInv hcre) S_shift
  · rw [V_shiftInv]
    have hv : (value ((107/8), (987/1280)))⁻¹=value ((21913600/294068569), (-1263360/294068569)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_shiftInv] using! contains_exact ((21913600/294068569), (-1263360/294068569))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_shiftInv,J_shift,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_shiftLog : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44582557783/17179869184), (7914851357/137438953472)), (1/137438953472), by norm_num⟩
  | 1 => ⟨((10956800/294068569), (-631680/294068569)), 0, by norm_num⟩
  | 2 => ⟨((-59826223308800/86476323273707761), (6921191424000/86476323273707761)), 0, by norm_num⟩
  | 3 => ⟨((153752333629/9007199254740992), (-26830397927/9007199254740992)), (1/18014398509481984), by norm_num⟩
  | 4 => ⟨((-272211670743/576460752303423488), (7979722133/72057594037927936)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((128067819697/9223372036854775808), (-37930023817/9223372036854775808)), (3/18446744073709551616), by norm_num⟩
  | 6 => ⟨((-250146438813/590295810358705651712), (90045133259/590295810358705651712)), (3/590295810358705651712), by norm_num⟩
  | 7 => ⟨((250336930225/18889465931478580854784), (-13345214271/2361183241434822606848)), (1/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((-15921598767/37778931862957161709568), (126437138179/604462909807314587353088)), (5/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((262259359877/19342813113834066795298816), (-149565878849/19342813113834066795298816)), (7/19342813113834066795298816), by norm_num⟩
  | 10 => ⟨((-34021194859/77371252455336267181195264), (176719020651/618970019642690137449562112)), (9/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((283963708831/19807040628566084398385987584), (-52138712585/4951760157141521099596496896)), (11/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((-297214400201/633825300114114700748351602688), (245830627145/633825300114114700748351602688)), (7/316912650057057350374175801344), by norm_num⟩
  | _ => zero

def logTable : ℕ → Disk
  | 48 => ⟨(0, 0), 0, by norm_num⟩
  | 47 => ⟨((1/47), 0), 0, by norm_num⟩
  | 46 => ⟨((-3491/138368), (21/20480)), 0, by norm_num⟩
  | 45 => ⟨((107370053897/4080638361600), (-41727/30146560)), 0, by norm_num⟩
  | 44 => ⟨((-2246371689977/83268678451200), (886184988479/592705486848000)), 0, by norm_num⟩
  | 43 => ⟨((485715607737/17592186044416), (-424804433/274877906944)), (1/17592186044416), by norm_num⟩
  | 42 => ⟨((-497239033207/17592186044416), (3483589173/2199023255552)), (1/17592186044416), by norm_num⟩
  | 41 => ⟨((254656450183/8796093022208), (-7133957553/4398046511104)), (1/17592186044416), by norm_num⟩
  | 40 => ⟨((-260994280653/8796093022208), (14613579643/8796093022208)), (1/8796093022208), by norm_num⟩
  | 39 => ⟨((267655943397/8796093022208), (-14975731573/8796093022208)), (1/4398046511104), by norm_num⟩
  | 38 => ⟨((-274666704563/8796093022208), (7678097515/4398046511104)), (1/8796093022208), by norm_num⟩
  | 37 => ⟨((282054683435/8796093022208), (-3939121737/2199023255552)), (1/8796093022208), by norm_num⟩
  | 36 => ⟨((-289851155747/8796093022208), (8089105681/4398046511104)), (1/8796093022208), by norm_num⟩
  | 35 => ⟨((298090966377/8796093022208), (-4155784679/2199023255552)), (1/8796093022208), by norm_num⟩
  | 34 => ⟨((-306813042573/8796093022208), (17093238765/8796093022208)), (1/8796093022208), by norm_num⟩
  | 33 => ⟨((316061007599/8796093022208), (-17590710707/8796093022208)), (1/8796093022208), by norm_num⟩
  | 32 => ⟨((-10183872205/274877906944), (18118017699/8796093022208)), (1/8796093022208), by norm_num⟩
  | 31 => ⟨((168168548569/4398046511104), (-18677927695/8796093022208)), (1/8796093022208), by norm_num⟩
  | 30 => ⟨((-173741626829/4398046511104), (9636781053/4398046511104)), (1/8796093022208), by norm_num⟩
  | 29 => ⟨((44924208261/1099511627776), (-19908454103/8796093022208)), (1/8796093022208), by norm_num⟩
  | 28 => ⟨((-11629679607/274877906944), (10293309429/4398046511104)), (1/8796093022208), by norm_num⟩
  | 27 => ⟨((385844902661/8796093022208), (-21312638675/8796093022208)), (1/8796093022208), by norm_num⟩
  | 26 => ⟨((-400586821773/8796093022208), (2761470855/1099511627776)), (1/8796093022208), by norm_num⟩
  | 25 => ⟨((416500319877/8796093022208), (-2866256895/1099511627776)), (1/8796093022208), by norm_num⟩
  | 24 => ⟨((-216865441633/4398046511104), (11917255885/4398046511104)), (1/8796093022208), by norm_num⟩
  | 23 => ⟨((452449134897/8796093022208), (-24813297917/8796093022208)), (1/8796093022208), by norm_num⟩
  | 22 => ⟨((-472856510111/8796093022208), (25875975447/8796093022208)), (1/4398046511104), by norm_num⟩
  | 21 => ⟨((123798135873/2199023255552), (-13516910473/4398046511104)), (1/4398046511104), by norm_num⟩
  | 20 => ⟨((-519744327129/8796093022208), (28300228457/8796093022208)), (1/8796093022208), by norm_num⟩
  | 19 => ⟨((136714733729/2199023255552), (-7422807843/2199023255552)), (1/4398046511104), by norm_num⟩
  | 18 => ⟨((-72119994799/1099511627776), (3903273353/1099511627776)), (1/2199023255552), by norm_num⟩
  | 17 => ⟨((305284917465/4398046511104), (-1029021403/274877906944)), (1/4398046511104), by norm_num⟩
  | 16 => ⟨((-324170241743/4398046511104), (8706943461/2199023255552)), (1/4398046511104), by norm_num⟩
  | 15 => ⟨((86387011829/1099511627776), (-9239909391/2199023255552)), (1/4398046511104), by norm_num⟩
  | 14 => ⟨((-184973525665/2199023255552), (19684966495/4398046511104)), (1/2199023255552), by norm_num⟩
  | 13 => ⟨((398057023529/4398046511104), (-10529278005/2199023255552)), (1/4398046511104), by norm_num⟩
  | 12 => ⟨((-215397611895/2199023255552), (5659656133/1099511627776)), (1/4398046511104), by norm_num⟩
  | 11 => ⟨((58676090017/549755813888), (-12237809187/2199023255552)), (1/2199023255552), by norm_num⟩
  | 10 => ⟨((-515637456985/4398046511104), (26637914283/4398046511104)), (1/2199023255552), by norm_num⟩
  | 9 => ⟨((285992417139/2199023255552), (-7305146021/1099511627776)), (1/2199023255552), by norm_num⟩
  | 8 => ⟨((-160547209413/1099511627776), (2022492047/274877906944)), (1/2199023255552), by norm_num⟩
  | 7 => ⟨((366045966965/2199023255552), (-18129139531/2199023255552)), (1/2199023255552), by norm_num⟩
  | 6 => ⟨((-106421147061/549755813888), (5153824197/549755813888)), (1/2199023255552), by norm_num⟩
  | 5 => ⟨((254325004231/1099511627776), (-23897367471/2199023255552)), (1/2199023255552), by norm_num⟩
  | 4 => ⟨((-316027255741/1099511627776), (3554276813/274877906944)), (1/1099511627776), by norm_num⟩
  | 3 => ⟨((417666927411/1099511627776), (-17562909267/1099511627776)), (1/1099511627776), by norm_num⟩
  | 2 => ⟨((-77179109821/137438953472), (11505093567/549755813888)), (1/549755813888), by norm_num⟩
  | 1 => ⟨((37490633475/34359738368), (-4191409179/137438953472)), (1/274877906944), by norm_num⟩
  | 0 => ⟨((-195209841033/1099511627776), (126637621719/2199023255552)), (3/2199023255552), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem logPolynomial : Contains (logTable 0) (Complex.logTaylor 48 (value ((-21/128), (987/20480)))) := by
  rw [← CertifiedHorner.log_horner_eq]
  apply CertifiedHorner.horner_contains (input:=exact ((-21/128), (987/20480)))
  · exact contains_exact _
  · simp [logTable,Contains,value]
  · intro k hk
    interval_cases k <;> norm_num [logTable,CertifiedTaylorModel.add,CertifiedTaylorModel.mul,exact,qadd,qmul,size]

theorem logNorm : ‖value ((-21/128), (987/20480))‖≤(1/2:ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1/2)).mp
  rw [Complex.sq_norm]
  norm_num [Complex.normSq_apply,value]

set_option maxHeartbeats 5000000 in
theorem logValue : Contains (J_shiftLog ⟨0,by omega⟩) (Complex.log (F_shift c)) := by
  change Contains ⟨((44582557783/17179869184), (7914851357/137438953472)), (1/137438953472), by norm_num⟩ (Complex.log (F_shift c))
  rw [V_shiftInv]
  have hs := log_scaled16_contains (w:=((107/8), (987/1280))) (z:=((-21/128), (987/20480))) (a:=logTable 0)
    (by norm_num [value]; ring)
    (by intro h; have hr:=congrArg Complex.re h; norm_num [value] at hr)
    logNorm logPolynomial
  apply contains_round (c:=((44582557783/17179869184), (7914851357/137438953472))) (r:=(1/137438953472)) (by norm_num) ?_ hs
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
  | 0 => ⟨((103/8), (987/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((71654693113/2147483648), (2944705973/1073741824)), (1/4294967296), by norm_num⟩
  | 1 => ⟨((488978531411/274877906944), (4105039955/137438953472)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((835425735859200/86476323273707761), (-49899904128480/86476323273707761)), 0, by norm_num⟩
  | 3 => ⟨((-278859818509/2251799813685248), (33391188337/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((341531126101/144115188075855872), (-15410129497/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((-249786291521/4611686018427387904), (30276363803/2305843009213693952)), (15/4611686018427387904), by norm_num⟩
  | 6 => ⟨((101012698889/73786976294838206464), (-61829006747/147573952589676412928)), (45/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-348465876913/9444732965739290427392), (129599152261/9444732965739290427392)), (13/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((157011662645/151115727451828646838272), (-138370998711/302231454903657293676544)), (67/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-292005355771/9671406556917033397649408), (74890018491/4835703278458516698824704)), (89/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((69462469403/77371252455336267181195264), (-40958114561/77371252455336267181195264)), (119/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-134466212281/4951760157141521099596496896), (180661636697/9903520314283042199192993792)), (37/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((263612739279/316912650057057350374175801344), (-200494223677/316912650057057350374175801344)), (23/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainLead : Sound J_mainLead F_mainLead c := by
  apply sound_round (sound_mul (A_shiftMinusHalf hcre) (A_shiftLog hcre) S_shiftMinusHalf S_shiftLog)
  intro k
  fin_cases k <;> norm_num [J_mainLead, J_shiftMinusHalf, J_shiftLog, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_negativeShift : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-107/8), (-987/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((42932099321/2147483648), (16934002907/8589934592)), (5/17179869184), by norm_num⟩
  | 1 => ⟨((351539577939/274877906944), (4105039955/137438953472)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((835425735859200/86476323273707761), (-49899904128480/86476323273707761)), 0, by norm_num⟩
  | 3 => ⟨((-278859818509/2251799813685248), (33391188337/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((341531126101/144115188075855872), (-15410129497/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((-249786291521/4611686018427387904), (30276363803/2305843009213693952)), (15/4611686018427387904), by norm_num⟩
  | 6 => ⟨((101012698889/73786976294838206464), (-61829006747/147573952589676412928)), (45/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-348465876913/9444732965739290427392), (129599152261/9444732965739290427392)), (13/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((157011662645/151115727451828646838272), (-138370998711/302231454903657293676544)), (67/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-292005355771/9671406556917033397649408), (74890018491/4835703278458516698824704)), (89/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((69462469403/77371252455336267181195264), (-40958114561/77371252455336267181195264)), (119/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-134466212281/4951760157141521099596496896), (180661636697/9903520314283042199192993792)), (37/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((263612739279/316912650057057350374175801344), (-200494223677/316912650057057350374175801344)), (23/39614081257132168796771975168), by norm_num⟩
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
  | 0 => ⟨((505191801235/274877906944), 0), (1/274877906944), by norm_num⟩
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
  | 0 => ⟨((505191801235/549755813888), 0), (1/549755813888), by norm_num⟩
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
  | 0 => ⟨((359244038357/17179869184), (16934002907/8589934592)), (3/8589934592), by norm_num⟩
  | 1 => ⟨((351539577939/274877906944), (4105039955/137438953472)), (1/137438953472), by norm_num⟩
  | 2 => ⟨((835425735859200/86476323273707761), (-49899904128480/86476323273707761)), 0, by norm_num⟩
  | 3 => ⟨((-278859818509/2251799813685248), (33391188337/2251799813685248)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((341531126101/144115188075855872), (-15410129497/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 5 => ⟨((-249786291521/4611686018427387904), (30276363803/2305843009213693952)), (15/4611686018427387904), by norm_num⟩
  | 6 => ⟨((101012698889/73786976294838206464), (-61829006747/147573952589676412928)), (45/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-348465876913/9444732965739290427392), (129599152261/9444732965739290427392)), (13/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((157011662645/151115727451828646838272), (-138370998711/302231454903657293676544)), (67/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-292005355771/9671406556917033397649408), (74890018491/4835703278458516698824704)), (89/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((69462469403/77371252455336267181195264), (-40958114561/77371252455336267181195264)), (119/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-134466212281/4951760157141521099596496896), (180661636697/9903520314283042199192993792)), (37/2475880078570760549798248448), by norm_num⟩
  | 12 => ⟨((263612739279/316912650057057350374175801344), (-200494223677/316912650057057350374175801344)), (23/39614081257132168796771975168), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainConstant : Sound J_mainConstant F_mainConstant c := by
  apply sound_round (sound_add (A_mainMinusShift hcre) (A_halfLogTwoPi hcre) S_mainMinusShift S_halfLogTwoPi)
  intro k
  fin_cases k <;> norm_num [J_mainConstant, J_mainMinusShift, J_halfLogTwoPi, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((478609786470400/86476323273707761), (-55369531392000/86476323273707761)), 0, by norm_num⟩
  | 1 => ⟨((-461257000887/1125899906842624), (80491193781/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 2 => ⟨((408317506115/18014398509481984), (-95756665597/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 3 => ⟨((-320169549243/288230376151711744), (94825059543/288230376151711744)), (1/144115188075855872), by norm_num⟩
  | 4 => ⟨((234512286387/4611686018427387904), (-84417312431/4611686018427387904)), (1/2305843009213693952), by norm_num⟩
  | 5 => ⟨((-41070902615/18446744073709551616), (140124749845/147573952589676412928)), (1/36893488147419103232), by norm_num⟩
  | 6 => ⟨((222902382737/2361183241434822606848), (-55316247953/1180591620717411303424)), (1/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-147520889931/37778931862957161709568), (21032701713/9444732965739290427392)), (3/37778931862957161709568), by norm_num⟩
  | 8 => ⟨((191369221081/1208925819614629174706176), (-124255561395/1208925819614629174706176)), (5/1208925819614629174706176), by norm_num⟩
  | 9 => ⟨((-244031312275/38685626227668133590597632), (179226824511/38685626227668133590597632)), (7/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((153251175103/618970019642690137449562112), (-126756417121/618970019642690137449562112)), (3/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-189827101489/19807040628566084398385987584), (176362626979/19807040628566084398385987584)), (9/19807040628566084398385987584), by norm_num⟩
  | 12 => ⟨((116029206045/316912650057057350374175801344), (-241935775115/633825300114114700748351602688)), (13/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower2 : Sound J_invPower2 F_invPower2 c := by
  apply sound_round (sound_mul (A_shiftInv hcre) (A_shiftInv hcre) S_shiftInv S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower2, J_shiftInv, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((461257000887/1125899906842624), (-80491193781/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 1 => ⟨((-408317506115/9007199254740992), (95756665597/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 2 => ⟨((240127161933/72057594037927936), (-35559397329/36028797018963968)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((-234512286387/1152921504606846976), (84417312431/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 4 => ⟨((205354513075/18446744073709551616), (-87577968653/18446744073709551616)), (1/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-167176787053/295147905179352825856), (165948743859/590295810358705651712)), (1/147573952589676412928), by norm_num⟩
  | 6 => ⟨((258161557379/9444732965739290427392), (-147228911991/9444732965739290427392)), (5/9444732965739290427392), by norm_num⟩
  | 7 => ⟨((-191369221081/151115727451828646838272), (124255561395/151115727451828646838272)), (5/151115727451828646838272), by norm_num⟩
  | 8 => ⟨((274535226309/4835703278458516698824704), (-100815088787/2417851639229258349412352)), (1/604462909807314587353088), by norm_num⟩
  | 9 => ⟨((-191563968879/77371252455336267181195264), (158445521401/77371252455336267181195264)), (7/77371252455336267181195264), by norm_num⟩
  | 10 => ⟨((130506132273/1237940039285380274899124224), (-242498612095/2475880078570760549798248448)), (11/2475880078570760549798248448), by norm_num⟩
  | 11 => ⟨((-174043809067/39614081257132168796771975168), (22681478917/4951760157141521099596496896)), (9/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((227546131721/1267650600228229401496703205376), (-66589911245/316912650057057350374175801344)), (7/633825300114114700748351602688), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower3 : Sound J_invPower3 F_invPower3 c := by
  apply sound_round (sound_mul (A_invPower2 hcre) (A_shiftInv hcre) S_invPower2 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower3, J_invPower2, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((272211670743/9007199254740992), (-7979722133/1125899906842624)), (1/9007199254740992), by norm_num⟩
  | 1 => ⟨((-80042387311/18014398509481984), (11853132443/9007199254740992)), (3/72057594037927936), by norm_num⟩
  | 2 => ⟨((234512286387/576460752303423488), (-84417312431/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 3 => ⟨((-273806017433/9223372036854775808), (116770624871/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 4 => ⟨((139313989211/73786976294838206464), (-138290619883/147573952589676412928)), (1/36893488147419103232), by norm_num⟩
  | 5 => ⟨((-258161557379/2361183241434822606848), (147228911991/2361183241434822606848)), (1/590295810358705651712), by norm_num⟩
  | 6 => ⟨((223264091261/37778931862957161709568), (-144964821627/37778931862957161709568)), (5/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-91511742103/302231454903657293676544), (134420118383/604462909807314587353088)), (5/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((143672976659/9671406556917033397649408), (-118834141051/9671406556917033397649408)), (9/19342813113834066795298816), by norm_num⟩
  | 9 => ⟨((-217510220455/309485009821345068724781056), (101041088373/154742504910672534362390528)), (9/309485009821345068724781056), by norm_num⟩
  | 10 => ⟨((19942519789/618970019642690137449562112), (-166330845391/4951760157141521099596496896)), (1/618970019642690137449562112), by norm_num⟩
  | 11 => ⟨((-28443266465/19807040628566084398385987584), (66589911245/39614081257132168796771975168)), (7/79228162514264337593543950336), by norm_num⟩
  | 12 => ⟨((158121175847/2535301200456458802993406410752), (-208263379457/2535301200456458802993406410752)), (11/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower4 : Sound J_invPower4 F_invPower4 c := by
  apply sound_round (sound_mul (A_invPower3 hcre) (A_shiftInv hcre) S_invPower3 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower4, J_invPower3, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((320169549243/144115188075855872), (-94825059543/144115188075855872)), (1/72057594037927936), by norm_num⟩
  | 1 => ⟨((-234512286387/576460752303423488), (84417312431/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 2 => ⟨((205354513075/4611686018427387904), (-87577968653/4611686018427387904)), (1/1152921504606846976), by norm_num⟩
  | 3 => ⟨((-139313989211/36893488147419103232), (138290619883/73786976294838206464)), (5/73786976294838206464), by norm_num⟩
  | 4 => ⟨((80675486681/295147905179352825856), (-184036139989/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 5 => ⟨((-83724034223/4722366482869645213696), (27180904055/2361183241434822606848)), (1/2361183241434822606848), by norm_num⟩
  | 6 => ⟨((20018193585/18889465931478580854784), (-117617603585/151115727451828646838272)), (1/37778931862957161709568), by norm_num⟩
  | 7 => ⟨((-143672976659/2417851639229258349412352), (118834141051/2417851639229258349412352)), (9/4835703278458516698824704), by norm_num⟩
  | 8 => ⟨((61174749503/19342813113834066795298816), (-227342448839/77371252455336267181195264)), (9/77371252455336267181195264), by norm_num⟩
  | 9 => ⟨((-99712598945/618970019642690137449562112), (207913556739/1237940039285380274899124224)), (5/618970019642690137449562112), by norm_num⟩
  | 10 => ⟨((78218982779/9903520314283042199192993792), (-183122255923/19807040628566084398385987584)), (9/19807040628566084398385987584), by norm_num⟩
  | 11 => ⟨((-118590881885/316912650057057350374175801344), (312395069185/633825300114114700748351602688)), (1/39614081257132168796771975168), by norm_num⟩
  | 12 => ⟨((43553006523/2535301200456458802993406410752), (-259181149593/10141204801825835211973625643008)), (7/5070602400912917605986812821504), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower5 : Sound J_invPower5 F_invPower5 c := by
  apply sound_round (sound_mul (A_invPower4 hcre) (A_shiftInv hcre) S_invPower4 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower5, J_invPower4, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((375219658219/2305843009213693952), (-135067699889/2305843009213693952)), (3/2305843009213693952), by norm_num⟩
  | 1 => ⟨((-41070902615/1152921504606846976), (140124749845/9223372036854775808)), (5/9223372036854775808), by norm_num⟩
  | 2 => ⟨((167176787053/36893488147419103232), (-165948743859/73786976294838206464)), (7/73786976294838206464), by norm_num⟩
  | 3 => ⟨((-258161557379/590295810358705651712), (147228911991/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 4 => ⟨((83724034223/2361183241434822606848), (-108723616221/4722366482869645213696)), (5/4722366482869645213696), by norm_num⟩
  | 5 => ⟨((-12010916151/4722366482869645213696), (70570562151/37778931862957161709568)), (3/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((201142167323/1208925819614629174706176), (-166367797471/1208925819614629174706176)), (7/1208925819614629174706176), by norm_num⟩
  | 7 => ⟨((-195759198409/19342813113834066795298816), (181873959071/19342813113834066795298816)), (1/2417851639229258349412352), by norm_num⟩
  | 8 => ⟨((179482678101/309485009821345068724781056), (-187122201065/309485009821345068724781056)), (1/38685626227668133590597632), by norm_num⟩
  | 9 => ⟨((-78218982779/2475880078570760549798248448), (183122255923/4951760157141521099596496896)), (9/4951760157141521099596496896), by norm_num⟩
  | 10 => ⟨((65224985037/39614081257132168796771975168), (-42954322013/19807040628566084398385987584)), (9/79228162514264337593543950336), by norm_num⟩
  | 11 => ⟨((-104527215655/1267650600228229401496703205376), (311017379511/2535301200456458802993406410752)), (17/2535301200456458802993406410752), by norm_num⟩
  | 12 => ⟨((161412559485/40564819207303340847894502572032), (-272846942075/40564819207303340847894502572032)), (15/40564819207303340847894502572032), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower6 : Sound J_invPower6 F_invPower6 c := by
  apply sound_round (sound_mul (A_invPower5 hcre) (A_shiftInv hcre) S_invPower5 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower6, J_invPower5, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((219044813947/18446744073709551616), (-93416499897/18446744073709551616)), (3/18446744073709551616), by norm_num⟩
  | 1 => ⟨((-222902382737/73786976294838206464), (55316247953/36893488147419103232)), (1/18446744073709551616), by norm_num⟩
  | 2 => ⟨((258161557379/590295810358705651712), (-147228911991/590295810358705651712)), (3/295147905179352825856), by norm_num⟩
  | 3 => ⟨((-223264091261/4722366482869645213696), (144964821627/4722366482869645213696)), (7/4722366482869645213696), by norm_num⟩
  | 4 => ⟨((20018193585/4722366482869645213696), (-117617603585/37778931862957161709568)), (3/18889465931478580854784), by norm_num⟩
  | 5 => ⟨((-201142167323/604462909807314587353088), (5198993671/18889465931478580854784)), (1/75557863725914323419136), by norm_num⟩
  | 6 => ⟨((114192865739/4835703278458516698824704), (-212186285583/9671406556917033397649408)), (5/4835703278458516698824704), by norm_num⟩
  | 7 => ⟨((-239310237467/154742504910672534362390528), (124748134043/77371252455336267181195264)), (3/38685626227668133590597632), by norm_num⟩
  | 8 => ⟨((234656948337/2475880078570760549798248448), (-274683383885/2475880078570760549798248448)), (13/2475880078570760549798248448), by norm_num⟩
  | 9 => ⟨((-108708308395/19807040628566084398385987584), (286362146753/39614081257132168796771975168)), (15/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((95816614351/316912650057057350374175801344), (-35637408069/79228162514264337593543950336)), (1/39614081257132168796771975168), by norm_num⟩
  | 11 => ⟨((-161412559485/10141204801825835211973625643008), (272846942075/10141204801825835211973625643008)), (1/633825300114114700748351602688), by norm_num⟩
  | 12 => ⟨((32568183281/40564819207303340847894502572032), (-126153861503/81129638414606681695789005144064)), (15/162259276829213363391578010288128), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower7 : Sound J_invPower7 F_invPower7 c := by
  apply sound_round (sound_mul (A_invPower6 hcre) (A_shiftInv hcre) S_invPower6 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower7, J_invPower6, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((15921598767/18446744073709551616), (-126437138179/295147905179352825856)), (5/295147905179352825856), by norm_num⟩
  | 1 => ⟨((-295041779861/1180591620717411303424), (21032701713/147573952589676412928)), (3/590295810358705651712), by norm_num⟩
  | 2 => ⟨((191369221081/4722366482869645213696), (-124255561395/4722366482869645213696)), (3/2361183241434822606848), by norm_num⟩
  | 3 => ⟨((-91511742103/18889465931478580854784), (134420118383/37778931862957161709568)), (7/37778931862957161709568), by norm_num⟩
  | 4 => ⟨((143672976659/302231454903657293676544), (-118834141051/302231454903657293676544)), (3/151115727451828646838272), by norm_num⟩
  | 5 => ⟨((-195759198409/4835703278458516698824704), (5683561221/151115727451828646838272)), (5/2417851639229258349412352), by norm_num⟩
  | 6 => ⟨((59827559367/19342813113834066795298816), (-249496268087/77371252455336267181195264)), (13/77371252455336267181195264), by norm_num⟩
  | 7 => ⟨((-33522421191/154742504910672534362390528), (156961933649/618970019642690137449562112)), (9/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((139767825079/9903520314283042199192993792), (-46022487871/2475880078570760549798248448)), (5/4951760157141521099596496896), by norm_num⟩
  | 9 => ⟨((-34220219411/39614081257132168796771975168), (203642331823/158456325028528675187087900672)), (11/158456325028528675187087900672), by norm_num⟩
  | 10 => ⟨((126824153881/2535301200456458802993406410752), (-107189870101/1267650600228229401496703205376)), (13/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((-55831171339/20282409603651670423947251286016), (13516485161/2535301200456458802993406410752)), (7/20282409603651670423947251286016), by norm_num⟩
  | 12 => ⟨((93629849037/649037107316853453566312041152512), (-210208477311/649037107316853453566312041152512)), (7/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower8 : Sound J_invPower8 F_invPower8 c := by
  apply sound_round (sound_mul (A_invPower7 hcre) (A_shiftInv hcre) S_invPower7 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower8, J_invPower7, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((147520889931/2361183241434822606848), (-168261613705/4722366482869645213696)), (7/4722366482869645213696), by norm_num⟩
  | 1 => ⟨((-191369221081/9444732965739290427392), (124255561395/9444732965739290427392)), (5/9444732965739290427392), by norm_num⟩
  | 2 => ⟨((274535226309/75557863725914323419136), (-201630177575/75557863725914323419136)), (5/37778931862957161709568), by norm_num⟩
  | 3 => ⟨((-143672976659/302231454903657293676544), (118834141051/302231454903657293676544)), (3/151115727451828646838272), by norm_num⟩
  | 4 => ⟨((61174749503/1208925819614629174706176), (-227342448839/4835703278458516698824704)), (3/1208925819614629174706176), by norm_num⟩
  | 5 => ⟨((-44870669525/9671406556917033397649408), (187122201065/38685626227668133590597632)), (11/38685626227668133590597632), by norm_num⟩
  | 6 => ⟨((234656948337/618970019642690137449562112), (-137341691943/309485009821345068724781056)), (1/38685626227668133590597632), by norm_num⟩
  | 7 => ⟨((-139767825079/4951760157141521099596496896), (46022487871/1237940039285380274899124224)), (11/4951760157141521099596496896), by norm_num⟩
  | 8 => ⟨((153990987349/79228162514264337593543950336), (-229097623301/79228162514264337593543950336)), (7/39614081257132168796771975168), by norm_num⟩
  | 9 => ⟨((-158530192351/1267650600228229401496703205376), (66993668813/316912650057057350374175801344)), (1/79228162514264337593543950336), by norm_num⟩
  | 10 => ⟨((76767860591/10141204801825835211973625643008), (-297362673543/20282409603651670423947251286016)), (19/20282409603651670423947251286016), by norm_num⟩
  | 11 => ⟨((-140444773555/324518553658426726783156020576256), (315312715967/324518553658426726783156020576256)), (21/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((7592608775/324518553658426726783156020576256), (-321334082765/5192296858534827628530496329220096)), (23/5192296858534827628530496329220096), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower9 : Sound J_invPower9 F_invPower9 c := by
  apply sound_round (sound_mul (A_invPower8 hcre) (A_shiftInv hcre) S_invPower8 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower9, J_invPower8, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((170105974295/37778931862957161709568), (-110449387907/37778931862957161709568)), (5/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((-244031312275/151115727451828646838272), (179226824511/151115727451828646838272)), (1/18889465931478580854784), by norm_num⟩
  | 2 => ⟨((191563968879/604462909807314587353088), (-79222760701/302231454903657293676544)), (1/75557863725914323419136), by norm_num⟩
  | 3 => ⟨((-217510220455/4835703278458516698824704), (101041088373/2417851639229258349412352)), (11/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((99712598945/19342813113834066795298816), (-207913556739/38685626227668133590597632)), (3/9671406556917033397649408), by norm_num⟩
  | 5 => ⟨((-156437965557/309485009821345068724781056), (45780563981/77371252455336267181195264)), (3/77371252455336267181195264), by norm_num⟩
  | 6 => ⟨((217416616789/4951760157141521099596496896), (-143181073377/2475880078570760549798248448)), (9/2475880078570760549798248448), by norm_num⟩
  | 7 => ⟨((-34220219411/9903520314283042199192993792), (203642331823/39614081257132168796771975168)), (13/39614081257132168796771975168), by norm_num⟩
  | 8 => ⟨((158530192351/633825300114114700748351602688), (-66993668813/158456325028528675187087900672)), (9/316912650057057350374175801344), by norm_num⟩
  | 9 => ⟨((-170595245757/10141204801825835211973625643008), (330402970603/10141204801825835211973625643008)), (11/5070602400912917605986812821504), by norm_num⟩
  | 10 => ⟨((85827361617/81129638414606681695789005144064), (-96345552101/40564819207303340847894502572032)), (13/81129638414606681695789005144064), by norm_num⟩
  | 11 => ⟨((-80987826933/1298074214633706907132624082305024), (53555680461/324518553658426726783156020576256)), (1/81129638414606681695789005144064), by norm_num⟩
  | 12 => ⟨((35803421701/10384593717069655257060992658440192), (-228361397773/20769187434139310514121985316880384)), (17/20769187434139310514121985316880384), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower10 : Sound J_invPower10 F_invPower10 c := by
  apply sound_round (sound_mul (A_invPower9 hcre) (A_shiftInv hcre) S_invPower9 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower10, J_invPower9, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_invPower11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((195225049821/604462909807314587353088), (-143381459609/604462909807314587353088)), (7/604462909807314587353088), by norm_num⟩
  | 1 => ⟨((-153251175103/1208925819614629174706176), (126756417121/1208925819614629174706176)), (7/1208925819614629174706176), by norm_num⟩
  | 2 => ⟨((130506132273/4835703278458516698824704), (-1894520407/75557863725914323419136)), (13/9671406556917033397649408), by norm_num⟩
  | 3 => ⟨((-19942519789/4835703278458516698824704), (166330845391/38685626227668133590597632)), (5/19342813113834066795298816), by norm_num⟩
  | 4 => ⟨((78218982779/154742504910672534362390528), (-45780563981/77371252455336267181195264)), (11/309485009821345068724781056), by norm_num⟩
  | 5 => ⟨((-130449970073/2475880078570760549798248448), (42954322013/618970019642690137449562112)), (3/618970019642690137449562112), by norm_num⟩
  | 6 => ⟨((191633228701/39614081257132168796771975168), (-285099264553/39614081257132168796771975168)), (19/39614081257132168796771975168), by norm_num⟩
  | 7 => ⟨((-126824153881/316912650057057350374175801344), (107189870101/158456325028528675187087900672)), (15/316912650057057350374175801344), by norm_num⟩
  | 8 => ⟨((76767860591/2535301200456458802993406410752), (-297362673543/5070602400912917605986812821504)), (21/5070602400912917605986812821504), by norm_num⟩
  | 9 => ⟨((-85827361617/40564819207303340847894502572032), (96345552101/20282409603651670423947251286016)), (7/20282409603651670423947251286016), by norm_num⟩
  | 10 => ⟨((89086609627/649037107316853453566312041152512), (-58911248507/162259276829213363391578010288128)), (9/324518553658426726783156020576256), by norm_num⟩
  | 11 => ⟨((-42964106041/5192296858534827628530496329220096), (17127104833/649037107316853453566312041152512)), (11/5192296858534827628530496329220096), by norm_num⟩
  | 12 => ⟨((38323774069/83076749736557242056487941267521536), (-152458431631/83076749736557242056487941267521536)), (25/166153499473114484112975882535043072), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_invPower11 : Sound J_invPower11 F_invPower11 c := by
  apply sound_round (sound_mul (A_invPower10 hcre) (A_shiftInv hcre) S_invPower10 S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_invPower11, J_invPower10, J_shiftInv, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5478400/882205707), (-105280/294068569)), 0, by norm_num⟩
  | 1 => ⟨((-59826223308800/259428969821123283), (2307063808000/86476323273707761)), 0, by norm_num⟩
  | 2 => ⟨((153752333629/18014398509481984), (-26830397927/18014398509481984)), (1/36028797018963968), by norm_num⟩
  | 3 => ⟨((-90737223581/288230376151711744), (85117036085/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 4 => ⟨((106723183081/9223372036854775808), (-31608353181/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 5 => ⟨((-250146438813/590295810358705651712), (90045133259/590295810358705651712)), (3/590295810358705651712), by norm_num⟩
  | 6 => ⟨((292059751929/18889465931478580854784), (-31138833299/4722366482869645213696)), (5/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((-5307199589/9444732965739290427392), (168582850905/604462909807314587353088)), (7/604462909807314587353088), by norm_num⟩
  | 8 => ⟨((49173629977/2417851639229258349412352), (-112174409137/9671406556917033397649408)), (5/9671406556917033397649408), by norm_num⟩
  | 9 => ⟨((-226807965727/309485009821345068724781056), (147265850543/309485009821345068724781056)), (1/38685626227668133590597632), by norm_num⟩
  | 10 => ⟨((65075016607/2475880078570760549798248448), (-191175279479/9903520314283042199192993792)), (5/4951760157141521099596496896), by norm_num⟩
  | 11 => ⟨((-297214400201/316912650057057350374175801344), (245830627145/316912650057057350374175801344)), (7/158456325028528675187087900672), by norm_num⟩
  | 12 => ⟨((168735201323/5070602400912917605986812821504), (-156766779537/5070602400912917605986812821504)), (5/2535301200456458802993406410752), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm1 : Sound J_mainTerm1 F_mainTerm1 c := by
  apply sound_round (sound_scale (A_shiftInv hcre) S_shiftInv)
  intro k
  fin_cases k <;> norm_num [J_mainTerm1, J_shiftInv, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((359350723447/17179869184), (33861855219/17179869184)), (7/17179869184), by norm_num⟩
  | 1 => ⟨((351476189077/274877906944), (8217413257/274877906944)), (3/274877906944), by norm_num⟩
  | 2 => ⟨((340207555725/35184372088832), (-5088758277/8796093022208)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-69892175767/562949953421312), (8389358137/562949953421312)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((343198675837/144115188075855872), (-31067199253/72057594037927936)), (9/144115188075855872), by norm_num⟩
  | 5 => ⟨((-125870280287/2305843009213693952), (30628102605/2305843009213693952)), (1/288230376151711744), by norm_num⟩
  | 6 => ⟨((102153557295/73786976294838206464), (-125604190575/295147905179352825856)), (23/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-176886538251/4722366482869645213696), (66116629653/4722366482869645213696)), (53/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((320170029037/302231454903657293676544), (-141876448997/302231454903657293676544)), (17/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-74773276175/2417851639229258349412352), (154382094811/9671406556917033397649408)), (45/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((8937007959/9671406556917033397649408), (-5306458929/9671406556917033397649408)), (15/38685626227668133590597632), by norm_num⟩
  | 11 => ⟨((-34777546821/1237940039285380274899124224), (188343843795/9903520314283042199192993792)), (149/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((137079344681/158456325028528675187087900672), (-105146073699/158456325028528675187087900672)), (185/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr1 : Sound J_mainCorr1 F_mainCorr1 c := by
  apply sound_round (sound_add (A_mainConstant hcre) (A_mainTerm1 hcre) S_mainConstant S_mainTerm1)
  intro k
  fin_cases k <;> norm_num [J_mainCorr1, J_mainConstant, J_mainTerm1, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-328004978409/288230376151711744), (14309545561/72057594037927936)), (1/144115188075855872), by norm_num⟩
  | 1 => ⟨((72589778865/576460752303423488), (-68093628869/2305843009213693952)), (1/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-85378546465/9223372036854775808), (25286682545/9223372036854775808)), (1/9223372036854775808), by norm_num⟩
  | 3 => ⟨((83382146271/147573952589676412928), (-7503761105/36893488147419103232)), (1/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-292059751929/9444732965739290427392), (124555333195/9444732965739290427392)), (1/2361183241434822606848), by norm_num⟩
  | 5 => ⟨((118881270793/75557863725914323419136), (-118007995633/151115727451828646838272)), (1/37778931862957161709568), by norm_num⟩
  | 6 => ⟨((-91790775957/1208925819614629174706176), (52348057597/1208925819614629174706176)), (1/604462909807314587353088), by norm_num⟩
  | 7 => ⟨((272169558871/77371252455336267181195264), (-176719020651/77371252455336267181195264)), (1/9671406556917033397649408), by norm_num⟩
  | 8 => ⟨((-48806262455/309485009821345068724781056), (17922682451/154742504910672534362390528)), (7/1237940039285380274899124224), by norm_num⟩
  | 9 => ⟨((272446533517/39614081257132168796771975168), (-56336185387/9903520314283042199192993792)), (11/39614081257132168796771975168), by norm_num⟩
  | 10 => ⟨((-185608721455/633825300114114700748351602688), (86221728745/316912650057057350374175801344)), (9/633825300114114700748351602688), by norm_num⟩
  | 11 => ⟨((247528972895/20282409603651670423947251286016), (-258064826789/20282409603651670423947251286016)), (7/10141204801825835211973625643008), by norm_num⟩
  | 12 => ⟨((-161810582557/324518553658426726783156020576256), (189411303097/324518553658426726783156020576256)), (11/324518553658426726783156020576256), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm2 : Sound J_mainTerm2 F_mainTerm2 c := by
  apply sound_round (sound_scale (A_invPower3 hcre) S_invPower3)
  intro k
  fin_cases k <;> norm_num [J_mainTerm2, J_invPower3, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((44918837987/2147483648), (33861858631/17179869184)), (1/2147483648), by norm_num⟩
  | 1 => ⟨((351476223691/274877906944), (2054351285/68719476736)), (1/68719476736), by norm_num⟩
  | 2 => ⟨((21262951877/2199023255552), (-20354936647/35184372088832)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((-279567430757/2251799813685248), (33556974555/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 4 => ⟨((343194219359/144115188075855872), (-31066248971/72057594037927936)), (5/72057594037927936), by norm_num⟩
  | 5 => ⟨((-251733304637/4611686018427387904), (15313150973/1152921504606846976)), (17/4611686018427387904), by norm_num⟩
  | 6 => ⟨((408591819323/295147905179352825856), (-7849463143/18446744073709551616)), (47/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-353739852679/9444732965739290427392), (16526460895/1180591620717411303424)), (27/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((320122366671/302231454903657293676544), (-70920721879/151115727451828646838272)), (69/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-299026589433/9671406556917033397649408), (154327079005/9671406556917033397649408)), (91/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((285893625429/309485009821345068724781056), (-169722484821/309485009821345068724781056)), (121/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-69524877703/2475880078570760549798248448), (188217835579/9903520314283042199192993792)), (75/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((274000671215/316912650057057350374175801344), (-105053587711/158456325028528675187087900672)), (93/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr2 : Sound J_mainCorr2 F_mainCorr2 c := by
  apply sound_round (sound_add (A_mainCorr1 hcre) (A_mainTerm2 hcre) S_mainCorr1 S_mainTerm2)
  intro k
  fin_cases k <;> norm_num [J_mainCorr2, J_mainCorr1, J_mainTerm2, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16262580279/9223372036854775808), (-77064175375/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 1 => ⟨((-190587762905/590295810358705651712), (68605815817/590295810358705651712)), (3/590295810358705651712), by norm_num⟩
  | 2 => ⟨((333782573633/9444732965739290427392), (-142348952223/9444732965739290427392)), (7/9444732965739290427392), by norm_num⟩
  | 3 => ⟨((-226440515797/75557863725914323419136), (56194283635/37778931862957161709568)), (5/75557863725914323419136), by norm_num⟩
  | 4 => ⟨((262259359877/1208925819614629174706176), (-2336966857/18889465931478580854784)), (3/604462909807314587353088), by norm_num⟩
  | 5 => ⟨((-272169558871/19342813113834066795298816), (88359510325/9671406556917033397649408)), (7/19342813113834066795298816), by norm_num⟩
  | 6 => ⟨((130150033213/154742504910672534362390528), (-95587639739/154742504910672534362390528)), (7/309485009821345068724781056), by norm_num⟩
  | 7 => ⟨((-233525600157/4951760157141521099596496896), (193152635613/4951760157141521099596496896)), (1/618970019642690137449562112), by norm_num⟩
  | 8 => ⟨((198866487273/79228162514264337593543950336), (-92380423655/39614081257132168796771975168)), (1/9903520314283042199192993792), by norm_num⟩
  | 9 => ⟨((-162072541777/1267650600228229401496703205376), (42242754385/316912650057057350374175801344)), (9/1267650600228229401496703205376), by norm_num⟩
  | 10 => ⟨((127136886295/20282409603651670423947251286016), (-74411583359/10141204801825835211973625643008)), (1/2535301200456458802993406410752), by norm_num⟩
  | 11 => ⟨((-192757242937/649037107316853453566312041152512), (253882976861/649037107316853453566312041152512)), (7/324518553658426726783156020576256), by norm_num⟩
  | 12 => ⟨((70790918539/5192296858534827628530496329220096), (-52659027219/2596148429267413814265248164610048)), (3/2596148429267413814265248164610048), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm3 : Sound J_mainTerm3 F_mainTerm3 c := by
  apply sound_round (sound_scale (A_invPower5 hcre) S_invPower5)
  intro k
  fin_cases k <;> norm_num [J_mainTerm3, J_invPower5, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((179675351963/8589934592), (16930929311/8589934592)), (9/17179869184), by norm_num⟩
  | 1 => ⟨((175738111801/137438953472), (2054351293/68719476736)), (5/274877906944), by norm_num⟩
  | 2 => ⟨((340207231275/35184372088832), (-20354937177/35184372088832)), (3/35184372088832), by norm_num⟩
  | 3 => ⟨((-279567437505/2251799813685248), (2097311119/140737488355328)), (3/1125899906842624), by norm_num⟩
  | 4 => ⟨((343194250623/144115188075855872), (-15533128943/36028797018963968)), (11/144115188075855872), by norm_num⟩
  | 5 => ⟨((-251733369527/4611686018427387904), (61252646025/4611686018427387904)), (9/2305843009213693952), by norm_num⟩
  | 6 => ⟨((102148016891/73786976294838206464), (-125591592607/295147905179352825856)), (3/18446744073709551616), by norm_num⟩
  | 7 => ⟨((-176870149047/4722366482869645213696), (132212055569/9444732965739290427392)), (55/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((160061562643/151115727451828646838272), (-141842148565/302231454903657293676544)), (35/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-74756956487/2417851639229258349412352), (19291046019/1208925819614629174706176)), (23/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((35736945673/38685626227668133590597632), (-84862377841/154742504910672534362390528)), (61/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-139051226027/4951760157141521099596496896), (94110854763/4951760157141521099596496896)), (151/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((137002495975/158456325028528675187087900672), (-105056801763/158456325028528675187087900672)), (187/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr3 : Sound J_mainCorr3 F_mainCorr3 c := by
  apply sound_round (sound_add (A_mainCorr2 hcre) (A_mainTerm3 hcre) S_mainCorr2 S_mainTerm3)
  intro k
  fin_cases k <;> norm_num [J_mainCorr3, J_mainCorr2, J_mainTerm3, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-267026058907/37778931862957161709568), (113879161779/37778931862957161709568)), (5/37778931862957161709568), by norm_num⟩
  | 1 => ⟨((67932154739/37778931862957161709568), (-33716570181/37778931862957161709568)), (3/75557863725914323419136), by norm_num⟩
  | 2 => ⟨((-78677807963/302231454903657293676544), (89739527309/604462909807314587353088)), (9/1208925819614629174706176), by norm_num⟩
  | 3 => ⟨((272169558871/9671406556917033397649408), (-88359510325/4835703278458516698824704)), (5/4835703278458516698824704), by norm_num⟩
  | 4 => ⟨((-195225049819/77371252455336267181195264), (17922682451/9671406556917033397649408)), (9/77371252455336267181195264), by norm_num⟩
  | 5 => ⟨((245201880165/1237940039285380274899124224), (-101405133697/618970019642690137449562112)), (11/1237940039285380274899124224), by norm_num⟩
  | 6 => ⟨((-278413082183/19807040628566084398385987584), (258665186235/19807040628566084398385987584)), (13/19807040628566084398385987584), by norm_num⟩
  | 7 => ⟨((145865287599/158456325028528675187087900672), (-76036957893/79228162514264337593543950336)), (1/19807040628566084398385987584), by norm_num⟩
  | 8 => ⟨((-71514498541/1267650600228229401496703205376), (83713031279/1267650600228229401496703205376)), (9/2535301200456458802993406410752), by norm_num⟩
  | 9 => ⟨((16565075565/5070602400912917605986812821504), (-5454517081/1267650600228229401496703205376)), (5/20282409603651670423947251286016), by norm_num⟩
  | 10 => ⟨((-58402507795/324518553658426726783156020576256), (86887394911/324518553658426726783156020576256)), (11/649037107316853453566312041152512), by norm_num⟩
  | 11 => ⟨((196769596325/20769187434139310514121985316880384), (-332613415101/20769187434139310514121985316880384)), (5/5192296858534827628530496329220096), by norm_num⟩
  | 12 => ⟨((-79404332571/166153499473114484112975882535043072), (153787564499/166153499473114484112975882535043072)), (19/332306998946228968225951765070086144), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm4 : Sound J_mainTerm4 F_mainTerm4 c := by
  apply sound_round (sound_scale (A_invPower7 hcre) S_invPower7)
  intro k
  fin_cases k <;> norm_num [J_mainTerm4, J_invPower7, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((179675351963/8589934592), (16930929311/8589934592)), (5/8589934592), by norm_num⟩
  | 1 => ⟨((175738111801/137438953472), (2054351293/68719476736)), (3/137438953472), by norm_num⟩
  | 2 => ⟨((170103615633/17592186044416), (-5088734293/8796093022208)), (1/8796093022208), by norm_num⟩
  | 3 => ⟨((-139783718721/1125899906842624), (33556977863/2251799813685248)), (7/2251799813685248), by norm_num⟩
  | 4 => ⟨((343194250259/144115188075855872), (-62132515505/144115188075855872)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((-125866684307/2305843009213693952), (61252645269/4611686018427387904)), (19/4611686018427387904), by norm_num⟩
  | 6 => ⟨((408592063415/295147905179352825856), (-125591588753/295147905179352825856)), (49/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-44217536175/1180591620717411303424), (132212046505/9444732965739290427392)), (7/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((80030777059/75557863725914323419136), (-70921064303/151115727451828646838272)), (71/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-299027794353/9671406556917033397649408), (154328326537/9671406556917033397649408)), (93/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((285895509687/309485009821345068724781056), (-42431168205/77371252455336267181195264)), (123/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-278102358227/9903520314283042199192993792), (47055387731/2475880078570760549798248448)), (19/1237940039285380274899124224), by norm_num⟩
  | 12 => ⟨((137002420249/158456325028528675187087900672), (-210113310199/316912650057057350374175801344)), (47/79228162514264337593543950336), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr4 : Sound J_mainCorr4 F_mainCorr4 c := by
  apply sound_round (sound_add (A_mainCorr3 hcre) (A_mainTerm4 hcre) S_mainCorr3 S_mainTerm4)
  intro k
  fin_cases k <;> norm_num [J_mainCorr4, J_mainCorr3, J_mainTerm4, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((63578026637/1208925819614629174706176), (-72516789745/2417851639229258349412352)), (7/4835703278458516698824704), by norm_num⟩
  | 1 => ⟨((-329902495601/19342813113834066795298816), (53551218379/4835703278458516698824704)), (9/19342813113834066795298816), by norm_num⟩
  | 2 => ⟨((29579553003/9671406556917033397649408), (-173795708617/77371252455336267181195264)), (9/77371252455336267181195264), by norm_num⟩
  | 3 => ⟨((-247678666833/618970019642690137449562112), (204858855953/618970019642690137449562112)), (11/618970019642690137449562112), by norm_num⟩
  | 4 => ⟨((210919001653/4951760157141521099596496896), (-48989618605/1237940039285380274899124224)), (11/4951760157141521099596496896), by norm_num⟩
  | 5 => ⟨((-154705608059/39614081257132168796771975168), (161290516743/39614081257132168796771975168)), (5/19807040628566084398385987584), by norm_num⟩
  | 6 => ⟨((50565807049/158456325028528675187087900672), (-236764128871/633825300114114700748351602688)), (15/633825300114114700748351602688), by norm_num⟩
  | 7 => ⟨((-30118319209/1267650600228229401496703205376), (79338430269/2535301200456458802993406410752)), (11/5070602400912917605986812821504), by norm_num⟩
  | 8 => ⟨((33183243065/20282409603651670423947251286016), (-197471352071/81129638414606681695789005144064)), (13/81129638414606681695789005144064), by norm_num⟩
  | 9 => ⟨((-136645553003/1298074214633706907132624082305024), (28872692283/162259276829213363391578010288128)), (15/1298074214633706907132624082305024), by norm_num⟩
  | 10 => ⟨((132340554285/20769187434139310514121985316880384), (-128156303749/10384593717069655257060992658440192)), (17/20769187434139310514121985316880384), by norm_num⟩
  | 11 => ⟨((-7566048407/20769187434139310514121985316880384), (135892348969/166153499473114484112975882535043072)), (19/332306998946228968225951765070086144), by norm_num⟩
  | 12 => ⟨((104711533813/5316911983139663491615228241121378304), (-138487416141/2658455991569831745807614120560689152)), (21/5316911983139663491615228241121378304), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm5 : Sound J_mainTerm5 F_mainTerm5 c := by
  apply sound_round (sound_scale (A_invPower9 hcre) S_invPower9)
  intro k
  fin_cases k <;> norm_num [J_mainTerm5, J_invPower9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((179675351963/8589934592), (16930929311/8589934592)), (11/17179869184), by norm_num⟩
  | 1 => ⟨((175738111801/137438953472), (2054351293/68719476736)), (7/274877906944), by norm_num⟩
  | 2 => ⟨((170103615633/17592186044416), (-5088734293/8796093022208)), (5/35184372088832), by norm_num⟩
  | 3 => ⟨((-279567437443/2251799813685248), (4194622233/281474976710656)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((343194250265/144115188075855872), (-62132515511/144115188075855872)), (13/144115188075855872), by norm_num⟩
  | 5 => ⟨((-31466671079/576460752303423488), (7656580661/576460752303423488)), (5/1152921504606846976), by norm_num⟩
  | 6 => ⟨((408592063509/295147905179352825856), (-125591588863/295147905179352825856)), (25/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-44217536203/1180591620717411303424), (132212046801/9444732965739290427392)), (57/9444732965739290427392), by norm_num⟩
  | 8 => ⟨((160061554365/151115727451828646838272), (-70921064671/151115727451828646838272)), (9/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-299027795371/9671406556917033397649408), (77164164129/4835703278458516698824704)), (47/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((285895511659/309485009821345068724781056), (-169724676639/309485009821345068724781056)), (31/77371252455336267181195264), by norm_num⟩
  | 11 => ⟨((-278102361835/9903520314283042199192993792), (11763847439/618970019642690137449562112)), (153/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((274004846739/316912650057057350374175801344), (-52528331677/79228162514264337593543950336)), (189/316912650057057350374175801344), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr5 : Sound J_mainCorr5 F_mainCorr5 c := by
  apply sound_round (sound_add (A_mainCorr4 hcre) (A_mainTerm5 hcre) S_mainCorr4 S_mainTerm5)
  intro k
  fin_cases k <;> norm_num [J_mainCorr5, J_mainCorr4, J_mainTerm5, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainTerm6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-47916708865/77371252455336267181195264), (140768157837/309485009821345068724781056)), (1/38685626227668133590597632), by norm_num⟩
  | 1 => ⟨((75228992871/309485009821345068724781056), (-124446127001/618970019642690137449562112)), (1/77371252455336267181195264), by norm_num⟩
  | 2 => ⟨((-256254998053/4951760157141521099596496896), (14879923717/309485009821345068724781056)), (7/2475880078570760549798248448), by norm_num⟩
  | 3 => ⟨((156632344571/19807040628566084398385987584), (-163299263105/19807040628566084398385987584)), (11/19807040628566084398385987584), by norm_num⟩
  | 4 => ⟨((-153586693059/158456325028528675187087900672), (179784629725/158456325028528675187087900672)), (3/39614081257132168796771975168), by norm_num⟩
  | 5 => ⟨((128072360451/1267650600228229401496703205376), (-168685708665/1267650600228229401496703205376)), (13/1267650600228229401496703205376), by norm_num⟩
  | 6 => ⟨((-188140479655/20282409603651670423947251286016), (279902983141/20282409603651670423947251286016)), (5/5070602400912917605986812821504), by norm_num⟩
  | 7 => ⟨((15564078647/20282409603651670423947251286016), (-105236204137/81129638414606681695789005144064)), (15/162259276829213363391578010288128), by norm_num⟩
  | 8 => ⟨((-75368672811/1298074214633706907132624082305024), (291942876563/2596148429267413814265248164610048)), (11/1298074214633706907132624082305024), by norm_num⟩
  | 9 => ⟨((168526106789/41538374868278621028243970633760768), (-378358148173/41538374868278621028243970633760768)), (7/10384593717069655257060992658440192), by norm_num⟩
  | 10 => ⟨((-87462897639/332306998946228968225951765070086144), (231350076943/332306998946228968225951765070086144)), (9/166153499473114484112975882535043072), by norm_num⟩
  | 11 => ⟨((84362065737/5316911983139663491615228241121378304), (-67259769931/1329227995784915872903807060280344576)), (23/5316911983139663491615228241121378304), by norm_num⟩
  | 12 => ⟨((-75250553199/85070591730234615865843651857942052864), (299359381971/85070591730234615865843651857942052864)), (13/42535295865117307932921825928971026432), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainTerm6 : Sound J_mainTerm6 F_mainTerm6 c := by
  apply sound_round (sound_scale (A_invPower11 hcre) S_invPower11)
  intro k
  fin_cases k <;> norm_num [J_mainTerm6, J_invPower11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_mainCorr6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((179675351963/8589934592), (16930929311/8589934592)), (3/4294967296), by norm_num⟩
  | 1 => ⟨((175738111801/137438953472), (2054351293/68719476736)), (1/34359738368), by norm_num⟩
  | 2 => ⟨((170103615633/17592186044416), (-5088734293/8796093022208)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((-279567437443/2251799813685248), (4194622233/281474976710656)), (9/2251799813685248), by norm_num⟩
  | 4 => ⟨((343194250265/144115188075855872), (-62132515511/144115188075855872)), (7/72057594037927936), by norm_num⟩
  | 5 => ⟨((-31466671079/576460752303423488), (61252645287/4611686018427387904)), (21/4611686018427387904), by norm_num⟩
  | 6 => ⟨((204296031753/147573952589676412928), (-125591588859/295147905179352825856)), (51/295147905179352825856), by norm_num⟩
  | 7 => ⟨((-353740289617/9444732965739290427392), (132212046789/9444732965739290427392)), (29/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((40015388589/37778931862957161709568), (-35460532327/75557863725914323419136)), (73/302231454903657293676544), by norm_num⟩
  | 9 => ⟨((-74756948833/2417851639229258349412352), (77164164085/4835703278458516698824704)), (95/9671406556917033397649408), by norm_num⟩
  | 10 => ⟨((142947755789/154742504910672534362390528), (-21215584553/38685626227668133590597632)), (125/309485009821345068724781056), by norm_num⟩
  | 11 => ⟨((-139051180839/4951760157141521099596496896), (188221558523/9903520314283042199192993792)), (77/4951760157141521099596496896), by norm_num⟩
  | 12 => ⟨((274004846459/316912650057057350374175801344), (-210113325593/316912650057057350374175801344)), (95/158456325028528675187087900672), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_mainCorr6 : Sound J_mainCorr6 F_mainCorr6 c := by
  apply sound_round (sound_add (A_mainCorr5 hcre) (A_mainTerm6 hcre) S_mainCorr5 S_mainTerm6)
  intro k
  fin_cases k <;> norm_num [J_mainCorr6, J_mainCorr5, J_mainTerm6, jetAdd, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaExp : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-495869717203731/1048576), (586056263357763/524288)), (2542349/1048576), by norm_num⟩
  | 1 => ⟨((-2552376909/4), (362283467357/256)), (825/256), by norm_num⟩
  | 2 => ⟨((-110856378383/256), (232014555435/256)), (555/256), by norm_num⟩
  | 3 => ⟨((-50463829345/256), (200291640675/512)), (503/512), by norm_num⟩
  | 4 => ⟨((-17337857979/256), (262039884035/2048)), (173/512), by norm_num⟩
  | 5 => ⟨((-76731214625/4096), (138469173089/4096)), (769/8192), by norm_num⟩
  | 6 => ⟨((-71194788467/16384), (246161695851/32768)), (721/32768), by norm_num⟩
  | 7 => ⟨((-28487844449/32768), (47299653721/32768)), (293/65536), by norm_num⟩
  | 8 => ⟨((-160572325487/1048576), (128307824655/524288)), (421/524288), by norm_num⟩
  | 9 => ⟨((-50586337645/2097152), (155931685007/4194304)), (1087/8388608), by norm_num⟩
  | 10 => ⟨((-115425022313/33554432), (42965468401/8388608)), (639/33554432), by norm_num⟩
  | 11 => ⟨((-120409553325/268435456), (86733822217/134217728)), (345/134217728), by norm_num⟩
  | 12 => ⟨((-115796222019/2147483648), (80816680629/1073741824)), (691/2147483648), by norm_num⟩
  | _ => zero

def gammaExpValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((402805612001607/2535301200456458802993406410752), (2567473074381/10141204801825835211973625643008)), (911/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((907439895011129/316912650057057350374175801344), (1576882198139/316912650057057350374175801344)), (561/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1930412009666337/39614081257132168796771975168), (1778872454039/19807040628566084398385987584)), (633/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1932771176674887/2475880078570760549798248448), (3788376073467/2475880078570760549798248448)), (1349/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((907242397834075/77371252455336267181195264), (1898814046569/77371252455336267181195264)), (169/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1590192086396463/9671406556917033397649408), (3570136638655/9671406556917033397649408)), (159/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1294398068338303/604462909807314587353088), (783441446481/151115727451828646838272)), (1117/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1945752348043177/75557863725914323419136), (5111001579709/75557863725914323419136)), (1821/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1341093112258535/4722366482869645213696), (962407866301/1180591620717411303424)), (1373/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((840735231229151/295147905179352825856), (665000827995/73786976294838206464)), (1897/590295810358705651712), by norm_num⟩
  | 8 => ⟨((118669219717245/4611686018427387904), (6690409373055/73786976294838206464)), (2387/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1907577121940923/9223372036854775808), (1895670288017/2305843009213693952)), (2707/9223372036854775808), by norm_num⟩
  | 6 => ⟨((419795443550811/288230376151711744), (7653278387735/1152921504606846976)), (2735/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1269530798737241/144115188075855872), (6776920919797/144115188075855872)), (303/18014398509481984), by norm_num⟩
  | 4 => ⟨((1604877112011441/36028797018963968), (5164106792801/18014398509481984)), (925/9007199254740992), by norm_num⟩
  | 3 => ⟨((816124937000095/4503599627370496), (13200308943601/9007199254740992)), (4739/9007199254740992), by norm_num⟩
  | 2 => ⟨((1259164335204195/2251799813685248), (13645729900439/2251799813685248)), (4915/2251799813685248), by norm_num⟩
  | 1 => ⟨((10401988955551/8796093022208), (10809628144183/562949953421312)), (7825/1125899906842624), by norm_num⟩
  | 0 => ⟨((390097537529441/281474976710656), (3004426044347/70368744177664)), (17567/1125899906842624), by norm_num⟩
  | _ => zero

def gammaExpValueSquares : ℕ → Disk
  | 0 => ⟨((390097537529441/281474976710656), (3004426044347/70368744177664)), (67012791160201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((540124970786019/281474976710656), (33310789194419/281474976710656)), (25097/562949953421312), by norm_num⟩
  | 2 => ⟨((1032508746554025/281474976710656), (127840771145989/281474976710656)), (25565/140737488355328), by norm_num⟩
  | 3 => ⟨((932348464160671/70368744177664), (234473266357407/70368744177664)), (52695/35184372088832), by norm_num⟩
  | 4 => ⟨((22601252702327/137438953472), (194165385791813/2199023255552)), (436883/8796093022208), by norm_num⟩
  | 5 => ⟨((41330875891183/2147483648), (498901152960295/17179869184)), (862647/34359738368), by norm_num⟩
  | 6 => ⟨((-495869717203731/1048576), (586056263357763/524288)), (2542349/1048576), by norm_num⟩
  | _ => zero

def gammaExpValue : CertifiedScalarExp.Data :=
  ⟨⟨((179675351963/8589934592), (16930929311/8589934592)), (3/4294967296), by norm_num⟩, 0, gammaExpValuePoly, gammaExpValueSquares⟩

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
  | 0 => ⟨((2252800/4071769), (-1263360/4071769)), 0, by norm_num⟩
  | 1 => ⟨((-1739514675200/16579302789361), (2846097408000/16579302789361)), 0, by norm_num⟩
  | 2 => ⟨((10525961869/4398046511104), (-140223033427/2199023255552)), (1/4398046511104), by norm_num⟩
  | 3 => ⟨((81191112787/8796093022208), (316858337787/17592186044416)), (3/17592186044416), by norm_num⟩
  | 4 => ⟨((-188154295443/35184372088832), (-31231588461/8796093022208)), (1/8796093022208), by norm_num⟩
  | 5 => ⟨((285723947093/140737488355328), (2684796169/17592186044416)), (1/17592186044416), by norm_num⟩
  | 6 => ⟨((-82373757047/140737488355328), (153538049591/562949953421312)), (15/562949953421312), by norm_num⟩
  | 7 => ⟨((67331001485/562949953421312), (-5849433601/35184372088832)), (7/562949953421312), by norm_num⟩
  | 8 => ⟨((-8213686287/1125899906842624), (290689337531/4503599627370496)), (25/4503599627370496), by norm_num⟩
  | 9 => ⟨((-72015409419/9007199254740992), (-42756128259/2251799813685248)), (11/4503599627370496), by norm_num⟩
  | 10 => ⟨((185816947439/36028797018963968), (144557628551/36028797018963968)), (39/36028797018963968), by norm_num⟩
  | 11 => ⟨((-73829918249/36028797018963968), (-44651711275/144115188075855872)), (17/36028797018963968), by norm_num⟩
  | 12 => ⟨((177246632921/288230376151711744), (-66925134239/288230376151711744)), (59/288230376151711744), by norm_num⟩
  | _ => zero

theorem V_gammaInverse0 : F_base c=value ((11/8), (987/1280)) := by
  have h := centre_contains S_base
  have he : J_base ⟨0,by omega⟩=exact ((11/8), (987/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_base,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse0 : Sound J_gammaInverse0 F_gammaInverse0 c := by
  apply inv_coefficients_sound (A_base hcre) (N_gammaInverse0 hcre) S_base
  · rw [V_gammaInverse0]
    have hv : (value ((11/8), (987/1280)))⁻¹=value ((2252800/4071769), (-1263360/4071769)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse0] using! contains_exact ((2252800/4071769), (-1263360/4071769))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse0,J_base,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFactor1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((19/8), (987/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3891200/10215769), (-1263360/10215769)), 0, by norm_num⟩
  | 1 => ⟨((-6772679475200/104361936261361), (4915986432000/104361936261361)), 0, by norm_num⟩
  | 2 => ⟨((83094995695/8796093022208), (-228416629091/17592186044416)), (1/17592186044416), by norm_num⟩
  | 3 => ⟨((-70108488547/70368744177664), (215113042325/70368744177664)), (1/35184372088832), by norm_num⟩
  | 4 => ⟨((203790333/281474976710656), (-362427979875/562949953421312)), (5/562949953421312), by norm_num⟩
  | 5 => ⟨((44665363397/1125899906842624), (69049852067/562949953421312)), (3/1125899906842624), by norm_num⟩
  | 6 => ⟨((-136366240961/9007199254740992), (-188314804387/9007199254740992)), (7/9007199254740992), by norm_num⟩
  | 7 => ⟨((300922116817/72057594037927936), (219461075383/72057594037927936)), (15/72057594037927936), by norm_num⟩
  | 8 => ⟨((-283523733779/288230376151711744), (-46378688773/144115188075855872)), (1/18014398509481984), by norm_num⟩
  | 9 => ⟨((477862611567/2305843009213693952), (537397273/1152921504606846976)), (17/1152921504606846976), by norm_num⟩
  | 10 => ⟨((-182151421647/4611686018427387904), (117373497465/9223372036854775808)), (35/9223372036854775808), by norm_num⟩
  | 11 => ⟨((248496269261/36893488147419103232), (-179520385287/36893488147419103232)), (37/36893488147419103232), by norm_num⟩
  | 12 => ⟨((-144903395719/147573952589676412928), (12388812457/9223372036854775808)), (39/147573952589676412928), by norm_num⟩
  | _ => zero

theorem V_gammaInverse1 : F_gammaFactor1 c=value ((19/8), (987/1280)) := by
  have h := centre_contains S_gammaFactor1
  have he : J_gammaFactor1 ⟨0,by omega⟩=exact ((19/8), (987/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor1,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse1 : Sound J_gammaInverse1 F_gammaInverse1 c := by
  apply inv_coefficients_sound (A_gammaFactor1 hcre) (N_gammaInverse1 hcre) S_gammaFactor1
  · rw [V_gammaInverse1]
    have hv : (value ((19/8), (987/1280)))⁻¹=value ((3891200/10215769), (-1263360/10215769)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse1] using! contains_exact ((3891200/10215769), (-1263360/10215769))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse1,J_gammaFactor1,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct1 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7170016870400/41596251525361), (-7762083840000/41596251525361)), 0, by norm_num⟩
  | 1 => ⟨((-88015440773/2199023255552), (136955740455/1099511627776)), (1/2199023255552), by norm_num⟩
  | 2 => ⟨((-62043071957/8796093022208), (-223341909581/4398046511104)), (3/8796093022208), by norm_num⟩
  | 3 => ⟨((179909347711/17592186044416), (263080077205/17592186044416)), (1/4398046511104), by norm_num⟩
  | 4 => ⟨((-94089884617/17592186044416), (-51137302551/17592186044416)), (5/35184372088832), by norm_num⟩
  | 5 => ⟨((70035194167/35184372088832), (4215906335/140737488355328)), (9/140737488355328), by norm_num⟩
  | 6 => ⟨((-20060758633/35184372088832), (165307724865/562949953421312)), (1/35184372088832), by norm_num⟩
  | 7 => ⟨((129960094895/1125899906842624), (-190610954535/1125899906842624)), (15/1125899906842624), by norm_num⟩
  | 8 => ⟨((-3553085851/562949953421312), (292138671555/4503599627370496)), (13/2251799813685248), by norm_num⟩
  | 9 => ⟨((-147764120491/18014398509481984), (-42757177863/2251799813685248)), (45/18014398509481984), by norm_num⟩
  | 10 => ⟨((46810001355/9007199254740992), (72049569163/18014398509481984)), (5/4503599627370496), by norm_num⟩
  | 11 => ⟨((-296290361547/144115188075855872), (-21975229885/72057594037927936)), (17/36028797018963968), by norm_num⟩
  | 12 => ⟨((355059294731/576460752303423488), (-134624569257/576460752303423488)), (59/288230376151711744), by norm_num⟩
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
  | 0 => ⟨((27/8), (987/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((614400/2181841), (-421120/6545523)), 0, by norm_num⟩
  | 1 => ⟨((-1610022092800/42843871343529), (86245376000/4760430149281)), 0, by norm_num⟩
  | 2 => ⟨((20707059629/4398046511104), (-132283484065/35184372088832)), (1/35184372088832), by norm_num⟩
  | 3 => ⟨((-76275279349/140737488355328), (95816995353/140737488355328)), (3/281474976710656), by norm_num⟩
  | 4 => ⟨((61257223793/1125899906842624), (-255112914857/2251799813685248)), (5/2251799813685248), by norm_num⟩
  | 5 => ⟨((-36172962523/9007199254740992), (159442540751/9007199254740992)), (1/2251799813685248), by norm_num⟩
  | 6 => ⟨((-71871757/18014398509481984), (-94451627193/36028797018963968)), (3/36028797018963968), by norm_num⟩
  | 7 => ⟨((97875551979/1152921504606846976), (425408832201/1152921504606846976)), (17/1152921504606846976), by norm_num⟩
  | 8 => ⟨((-54931039861/2305843009213693952), (-113496844647/2305843009213693952)), (13/4611686018427387904), by norm_num⟩
  | 9 => ⟨((22770477453/4611686018427387904), (56852546251/9223372036854775808)), (19/36893488147419103232), by norm_num⟩
  | 10 => ⟨((-263710832237/295147905179352825856), (-104636291181/147573952589676412928)), (7/73786976294838206464), by norm_num⟩
  | 11 => ⟨((350896743233/2361183241434822606848), (10491037849/147573952589676412928)), (5/295147905179352825856), by norm_num⟩
  | 12 => ⟨((-438443590143/18889465931478580854784), (-98768980815/18889465931478580854784)), (7/2361183241434822606848), by norm_num⟩
  | _ => zero

theorem V_gammaInverse2 : F_gammaFactor2 c=value ((27/8), (987/1280)) := by
  have h := centre_contains S_gammaFactor2
  have he : J_gammaFactor2 ⟨0,by omega⟩=exact ((27/8), (987/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor2,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse2 : Sound J_gammaInverse2 F_gammaInverse2 c := by
  apply inv_coefficients_sound (A_gammaFactor2 hcre) (N_gammaInverse2 hcre) S_gammaFactor2
  · rw [V_gammaInverse2]
    have hv : (value ((27/8), (987/1280)))⁻¹=value ((614400/2181841), (-421120/6545523)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse2] using! contains_exact ((614400/2181841), (-421120/6545523))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse2,J_gammaFactor2,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct2 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((160676981393/4398046511104), (-279880327577/4398046511104)), (1/4398046511104), by norm_num⟩
  | 1 => ⟨((-27944171835/4398046511104), (52541533471/1099511627776)), (1/4398046511104), by norm_num⟩
  | 2 => ⟨((-51861974197/8796093022208), (-365546375633/17592186044416)), (3/17592186044416), by norm_num⟩
  | 3 => ⟨((187902059929/35184372088832), (221278941043/35184372088832)), (5/35184372088832), by norm_num⟩
  | 4 => ⟨((-93145477391/35184372088832), (-41804497827/35184372088832)), (11/140737488355328), by norm_num⟩
  | 5 => ⟨((34249050463/35184372088832), (-5277633491/140737488355328)), (11/281474976710656), by norm_num⟩
  | 6 => ⟨((-78112873515/281474976710656), (175601593465/1125899906842624)), (19/1125899906842624), by norm_num⟩
  | 7 => ⟨((125353768413/2251799813685248), (-193624595525/2251799813685248)), (17/2251799813685248), by norm_num⟩
  | 8 => ⟨((-24101915655/9007199254740992), (293366332055/9007199254740992)), (15/4503599627370496), by norm_num⟩
  | 9 => ⟨((-75704237483/18014398509481984), (-341954779607/36028797018963968)), (25/18014398509481984), by norm_num⟩
  | 10 => ⟨((94315436069/36028797018963968), (35903775533/18014398509481984)), (11/18014398509481984), by norm_num⟩
  | 11 => ⟨((-297239633061/288230376151711744), (-43238963111/288230376151711744)), (19/72057594037927936), by norm_num⟩
  | 12 => ⟨((44451492923/144115188075855872), (-67700942113/576460752303423488)), (65/576460752303423488), by norm_num⟩
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
  | 0 => ⟨((35/8), (987/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((1024000/4619167), (-180480/4619167)), 0, by norm_num⟩
  | 1 => ⟨((-508001484800/21336703773889), (184811520000/21336703773889)), 0, by norm_num⟩
  | 2 => ⟨((173797666293/70368744177664), (-100290232889/70368744177664)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-276878370585/1125899906842624), (232187667241/1125899906842624)), (1/562949953421312), by norm_num⟩
  | 4 => ⟨((52307747543/2251799813685248), (-124581414605/4503599627370496)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((-146592341451/72057594037927936), (126821457729/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 6 => ⟨((90347964699/576460752303423488), (-247825922911/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 7 => ⟨((-41382953493/4611686018427387904), (58469361625/1152921504606846976)), (7/4611686018427387904), by norm_num⟩
  | 8 => ⟨((287398715/73786976294838206464), (-427712270481/73786976294838206464)), (15/73786976294838206464), by norm_num⟩
  | 9 => ⟨((66591412947/590295810358705651712), (189657241097/295147905179352825856)), (17/590295810358705651712), by norm_num⟩
  | 10 => ⟨((-118331538655/4722366482869645213696), (-81486469651/1180591620717411303424)), (19/4722366482869645213696), by norm_num⟩
  | 11 => ⟨((38967677019/9444732965739290427392), (270535448139/37778931862957161709568)), (21/37778931862957161709568), by norm_num⟩
  | 12 => ⟨((-180498209093/302231454903657293676544), (-215533886089/302231454903657293676544)), (23/302231454903657293676544), by norm_num⟩
  | _ => zero

theorem V_gammaInverse3 : F_gammaFactor3 c=value ((35/8), (987/1280)) := by
  have h := centre_contains S_gammaFactor3
  have he : J_gammaFactor3 ⟨0,by omega⟩=exact ((35/8), (987/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor3,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse3 : Sound J_gammaInverse3 F_gammaInverse3 c := by
  apply inv_coefficients_sound (A_gammaFactor3 hcre) (N_gammaInverse3 hcre) S_gammaFactor3
  · rw [V_gammaInverse3]
    have hv : (value ((35/8), (987/1280)))⁻¹=value ((1024000/4619167), (-180480/4619167)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse3] using! contains_exact ((1024000/4619167), (-180480/4619167))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse3,J_gammaFactor3,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct3 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((49368393663/8796093022208), (-273292943979/17592186044416)), (1/8796093022208), by norm_num⟩
  | 1 => ⟨((307753749/2199023255552), (445902880725/35184372088832)), (1/8796093022208), by norm_num⟩
  | 2 => ⟨((-41905137953/17592186044416), (-12705980167/2199023255552)), (3/35184372088832), by norm_num⟩
  | 3 => ⟨((254248782359/140737488355328), (250435995999/140737488355328)), (7/140737488355328), by norm_num⟩
  | 4 => ⟨((-30550860107/35184372088832), (-90608310933/281474976710656)), (1/35184372088832), by norm_num⟩
  | 5 => ⟨((356753521823/1125899906842624), (-31107395893/1125899906842624)), (1/70368744177664), by norm_num⟩
  | 6 => ⟨((-202680884279/2251799813685248), (15388472741/281474976710656)), (15/2251799813685248), by norm_num⟩
  | 7 => ⟨((40284375595/2251799813685248), (-261706529585/9007199254740992)), (13/4503599627370496), by norm_num⟩
  | 8 => ⟨((-3314408205/4503599627370496), (392531232687/36028797018963968)), (45/36028797018963968), by norm_num⟩
  | 9 => ⟨((-6456913103/4503599627370496), (-227835114627/72057594037927936)), (19/36028797018963968), by norm_num⟩
  | 10 => ⟨((31665075065/36028797018963968), (190810675651/288230376151711744)), (65/288230376151711744), by norm_num⟩
  | 11 => ⟨((-198778721425/576460752303423488), (-56691004411/1152921504606846976)), (7/72057594037927936), by norm_num⟩
  | 12 => ⟨((237434370715/2305843009213693952), (-90787868191/2305843009213693952)), (3/72057594037927936), by norm_num⟩
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
  | 0 => ⟨((43/8), (987/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((8806400/48308569), (-1263360/48308569)), 0, by norm_num⟩
  | 1 => ⟨((-37978301235200/2333717838827761), (11125653504000/2333717838827761)), 0, by norm_num⟩
  | 2 => ⟨((12498990423/8796093022208), (-5693940005/8796093022208)), (1/140737488355328), by norm_num⟩
  | 3 => ⟨((-136293982251/1125899906842624), (87350250827/1125899906842624)), (3/2251799813685248), by norm_num⟩
  | 4 => ⟨((22561308169/2251799813685248), (-155902711885/18014398509481984)), (1/4503599627370496), by norm_num⟩
  | 5 => ⟨((-230602563945/288230376151711744), (132561664267/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 6 => ⟨((70208339675/1152921504606846976), (-108722580277/1152921504606846976)), (1/288230376151711744), by norm_num⟩
  | 7 => ⟨((-159285020757/36893488147419103232), (43311278335/4611686018427387904)), (7/18446744073709551616), by norm_num⟩
  | 8 => ⟨((79901825617/295147905179352825856), (-134657926053/147573952589676412928)), (13/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-60180555081/4722366482869645213696), (409475658929/4722366482869645213696)), (23/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((1048167815/37778931862957161709568), (-304876441185/37778931862957161709568)), (5/9444732965739290427392), by norm_num⟩
  | 11 => ⟨((7782017217/75557863725914323419136), (444838364795/604462909807314587353088)), (17/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((-91929317791/4835703278458516698824704), (-19865899265/302231454903657293676544)), (29/4835703278458516698824704), by norm_num⟩
  | _ => zero

theorem V_gammaInverse4 : F_gammaFactor4 c=value ((43/8), (987/1280)) := by
  have h := centre_contains S_gammaFactor4
  have he : J_gammaFactor4 ⟨0,by omega⟩=exact ((43/8), (987/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor4,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse4 : Sound J_gammaInverse4 F_gammaInverse4 c := by
  apply inv_coefficients_sound (A_gammaFactor4 hcre) (N_gammaInverse4 hcre) S_gammaFactor4
  · rw [V_gammaInverse4]
    have hv : (value ((43/8), (987/1280)))⁻¹=value ((8806400/48308569), (-1263360/48308569)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse4] using! contains_exact ((8806400/48308569), (-1263360/48308569))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse4,J_gammaFactor4,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct4 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((86816609319/140737488355328), (-209608120621/70368744177664)), (1/35184372088832), by norm_num⟩
  | 1 => ⟨((47803859437/140737488355328), (181986826631/70368744177664)), (5/140737488355328), by norm_num⟩
  | 2 => ⟨((-45747728739/70368744177664), (-344043900243/281474976710656)), (7/281474976710656), by norm_num⟩
  | 3 => ⟨((31743259883/70368744177664), (213948213923/562949953421312)), (1/70368744177664), by norm_num⟩
  | 4 => ⟨((-239582899905/1125899906842624), (-36431681947/562949953421312)), (9/1125899906842624), by norm_num⟩
  | 5 => ⟨((174021802611/2251799813685248), (-45967833395/4503599627370496)), (9/2251799813685248), by norm_num⟩
  | 6 => ⟨((-49289264037/2251799813685248), (64225631151/4503599627370496)), (17/9007199254740992), by norm_num⟩
  | 7 => ⟨((19410568713/4503599627370496), (-66207794823/9007199254740992)), (29/36028797018963968), by norm_num⟩
  | 8 => ⟨((-10518057247/72057594037927936), (196837963325/72057594037927936)), (25/72057594037927936), by norm_num⟩
  | 9 => ⟨((-52812900263/144115188075855872), (-227640742425/288230376151711744)), (21/144115188075855872), by norm_num⟩
  | 10 => ⟨((31886607329/144115188075855872), (95053365441/576460752303423488)), (9/144115188075855872), by norm_num⟩
  | 11 => ⟨((-199384192355/2305843009213693952), (-55719008421/4611686018427387904)), (123/4611686018427387904), by norm_num⟩
  | 12 => ⟨((237785644075/9223372036854775808), (-45654650077/4611686018427387904)), (53/4611686018427387904), by norm_num⟩
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
  | 0 => ⟨((51/8), (987/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((3481600/22519923), (-421120/22519923)), 0, by norm_num⟩
  | 1 => ⟨((-1990699417600/169048977308643), (1466171392000/507146931925929)), 0, by norm_num⟩
  | 2 => ⟨((248612599657/281474976710656), (-46947322977/140737488355328)), (1/281474976710656), by norm_num⟩
  | 3 => ⟨((-293439267501/4503599627370496), (4791305651/140737488355328)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((169995480959/36028797018963968), (-58381927547/18014398509481984)), (3/36028797018963968), by norm_num⟩
  | 5 => ⟨((-192783846321/576460752303423488), (169845530941/576460752303423488)), (5/576460752303423488), by norm_num⟩
  | 6 => ⟨((213027687301/9223372036854775808), (-238906441691/9223372036854775808)), (1/1152921504606846976), by norm_num⟩
  | 7 => ⟨((-56933490881/36893488147419103232), (163674962311/73786976294838206464)), (3/36893488147419103232), by norm_num⟩
  | 8 => ⟨((116345862665/1180591620717411303424), (-54867186903/295147905179352825856)), (9/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((-111065060555/18889465931478580854784), (288845734107/18889465931478580854784)), (13/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((94154993081/302231454903657293676544), (-373861678361/302231454903657293676544)), (19/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-60522194119/4835703278458516698824704), (476480268629/4835703278458516698824704)), (27/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((446657847/9671406556917033397649408), (-299184115265/38685626227668133590597632)), (5/9671406556917033397649408), by norm_num⟩
  | _ => zero

theorem V_gammaInverse5 : F_gammaFactor5 c=value ((51/8), (987/1280)) := by
  have h := centre_contains S_gammaFactor5
  have he : J_gammaFactor5 ⟨0,by omega⟩=exact ((51/8), (987/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor5,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse5 : Sound J_gammaInverse5 F_gammaInverse5 c := by
  apply inv_coefficients_sound (A_gammaFactor5 hcre) (N_gammaInverse5 hcre) S_gammaFactor5
  · rw [V_gammaInverse5]
    have hv : (value ((51/8), (987/1280)))⁻¹=value ((3481600/22519923), (-421120/22519923)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse5] using! contains_exact ((3481600/22519923), (-421120/22519923))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse5,J_gammaFactor5,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct5 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((11165256959/281474976710656), (-132869324289/281474976710656)), (1/140737488355328), by norm_num⟩
  | 1 => ⟨((28772811051/281474976710656), (242257391027/562949953421312)), (5/562949953421312), by norm_num⟩
  | 2 => ⟨((-152323345757/1125899906842624), (-235447437193/1125899906842624)), (3/562949953421312), by norm_num⟩
  | 3 => ⟨((6281142075/70368744177664), (36715808321/562949953421312)), (1/281474976710656), by norm_num⟩
  | 4 => ⟨((-374859256597/9007199254740992), (-46084842967/4503599627370496)), (1/562949953421312), by norm_num⟩
  | 5 => ⟨((271470157943/18014398509481984), (-23610242333/9007199254740992)), (1/1125899906842624), by norm_num⟩
  | 6 => ⟨((-153401033201/36028797018963968), (213117525277/72057594037927936)), (15/36028797018963968), by norm_num⟩
  | 7 => ⟨((119665859881/144115188075855872), (-107036536399/72057594037927936)), (13/72057594037927936), by norm_num⟩
  | 8 => ⟨((-12556638433/576460752303423488), (78922831279/144115188075855872)), (11/144115188075855872), by norm_num⟩
  | 9 => ⟨((-172617833969/2305843009213693952), (-11369627729/72057594037927936)), (37/1152921504606846976), by norm_num⟩
  | 10 => ⟨((205460636227/4611686018427387904), (151502054649/4611686018427387904)), (1/72057594037927936), by norm_num⟩
  | 11 => ⟨((-319962469713/18446744073709551616), (-43789659977/18446744073709551616)), (107/18446744073709551616), by norm_num⟩
  | 12 => ⟨((381005862221/73786976294838206464), (-73465593753/36893488147419103232)), (23/9223372036854775808), by norm_num⟩
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
  | 0 => ⟨((59/8), (987/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((12083200/90087769), (-1263360/90087769)), 0, by norm_num⟩
  | 1 => ⟨((-72203821875200/8115806123397361), (15265431552000/8115806123397361)), 0, by norm_num⟩
  | 2 => ⟨((41056942549/70368744177664), (-53065124117/281474976710656)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-340531312325/9007199254740992), (75364308643/4503599627370496)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((174242674259/72057594037927936), (-199938144067/144115188075855872)), (1/36028797018963968), by norm_num⟩
  | 5 => ⟨((-175749687375/1152921504606846976), (31704137687/288230376151711744)), (3/1152921504606846976), by norm_num⟩
  | 6 => ⟨((174354737539/18446744073709551616), (-155793390425/18446744073709551616)), (1/4611686018427387904), by norm_num⟩
  | 7 => ⟨((-84803522081/147573952589676412928), (93364749499/147573952589676412928)), (5/295147905179352825856), by norm_num⟩
  | 8 => ⟨((161041995049/4722366482869645213696), (-219391792251/4722366482869645213696)), (7/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-148187203519/75557863725914323419136), (15842377665/4722366482869645213696)), (9/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((130569697879/1208925819614629174706176), (-288610958521/1208925819614629174706176)), (3/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-107724300097/19342813113834066795298816), (162166318827/9671406556917033397649408)), (15/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((39601619253/154742504910672534362390528), (-360099555719/309485009821345068724781056)), (19/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse6 : F_gammaFactor6 c=value ((59/8), (987/1280)) := by
  have h := centre_contains S_gammaFactor6
  have he : J_gammaFactor6 ⟨0,by omega⟩=exact ((59/8), (987/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor6,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse6 : Sound J_gammaInverse6 F_gammaInverse6 c := by
  apply inv_coefficients_sound (A_gammaFactor6 hcre) (N_gammaInverse6 hcre) S_gammaFactor6
  · rw [V_gammaInverse6]
    have hv : (value ((59/8), (987/1280)))⁻¹=value ((12083200/90087769), (-1263360/90087769)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse6] using! contains_exact ((12083200/90087769), (-1263360/90087769))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse6,J_gammaFactor6,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct6 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5852027553/4503599627370496), (-287647013797/4503599627370496)), (3/2251799813685248), by norm_num⟩
  | 1 => ⟨((91335428047/4503599627370496), (272739587443/4503599627370496)), (7/4503599627370496), by norm_num⟩
  | 2 => ⟨((-102967691069/4503599627370496), (-33856332185/1125899906842624)), (9/9007199254740992), by norm_num⟩
  | 3 => ⟨((263568755121/18014398509481984), (84238664677/9007199254740992)), (3/4503599627370496), by norm_num⟩
  | 4 => ⟨((-60999881559/9007199254740992), (-47323330631/36028797018963968)), (3/9007199254740992), by norm_num⟩
  | 5 => ⟨((176387634177/72057594037927936), (-75273223139/144115188075855872)), (23/144115188075855872), by norm_num⟩
  | 6 => ⟨((-49727014639/72057594037927936), (73296276951/144115188075855872)), (11/144115188075855872), by norm_num⟩
  | 7 => ⟨((153633004891/1152921504606846976), (-288031883397/1152921504606846976)), (19/576460752303423488), by norm_num⟩
  | 8 => ⟨((-11190435597/4611686018427387904), (421725185447/4611686018427387904)), (1/72057594037927936), by norm_num⟩
  | 9 => ⟨((-58716411959/4611686018427387904), (-121117682589/4611686018427387904)), (27/4611686018427387904), by norm_num⟩
  | 10 => ⟨((137877641865/18446744073709551616), (50300135313/9223372036854775808)), (23/9223372036854775808), by norm_num⟩
  | 11 => ⟨((-427853095921/147573952589676412928), (-57329290053/147573952589676412928)), (155/147573952589676412928), by norm_num⟩
  | 12 => ⟨((127180606825/147573952589676412928), (-3078524585/9223372036854775808)), (33/73786976294838206464), by norm_num⟩
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
  | 0 => ⟨((67/8), (987/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((13721600/115892569), (-1263360/115892569)), 0, by norm_num⟩
  | 1 => ⟨((-93343114035200/13431087549419761), (17335320576000/13431087549419761)), 0, by norm_num⟩
  | 2 => ⟨((227651133697/562949953421312), (-32169328963/281474976710656)), (1/562949953421312), by norm_num⟩
  | 3 => ⟨((-210018981235/9007199254740992), (80794458175/9007199254740992)), (1/4503599627370496), by norm_num⟩
  | 4 => ⟨((95941404707/72057594037927936), (-94843617967/144115188075855872)), (3/144115188075855872), by norm_num⟩
  | 5 => ⟨((-173479114055/2305843009213693952), (53284633095/1152921504606846976)), (1/576460752303423488), by norm_num⟩
  | 6 => ⟨((310049306203/73786976294838206464), (-232141533283/73786976294838206464)), (9/73786976294838206464), by norm_num⟩
  | 7 => ⟨((-4272377283/18446744073709551616), (246922278827/1180591620717411303424)), (11/1180591620717411303424), by norm_num⟩
  | 8 => ⟨((118729780023/9444732965739290427392), (-257729171731/18889465931478580854784)), (13/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-101222033407/151115727451828646838272), (264828266089/302231454903657293676544)), (15/302231454903657293676544), by norm_num⟩
  | 10 => ⟨((168658480179/4835703278458516698824704), (-268498821333/4835703278458516698824704)), (1/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((-136336853881/77371252455336267181195264), (269029142279/77371252455336267181195264)), (17/77371252455336267181195264), by norm_num⟩
  | 12 => ⟨((105675739539/1237940039285380274899124224), (-33339090157/154742504910672534362390528)), (19/1237940039285380274899124224), by norm_num⟩
  | _ => zero

theorem V_gammaInverse7 : F_gammaFactor7 c=value ((67/8), (987/1280)) := by
  have h := centre_contains S_gammaFactor7
  have he : J_gammaFactor7 ⟨0,by omega⟩=exact ((67/8), (987/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor7,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse7 : Sound J_gammaInverse7 F_gammaInverse7 c := by
  apply inv_coefficients_sound (A_gammaFactor7 hcre) (N_gammaInverse7 hcre) S_gammaFactor7
  · rw [V_gammaInverse7]
    have hv : (value ((67/8), (987/1280)))⁻¹=value ((13721600/115892569), (-1263360/115892569)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse7] using! contains_exact ((13721600/115892569), (-1263360/115892569))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse7,J_gammaFactor7,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct7 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-30628428825/36028797018963968), (-271947309891/36028797018963968)), (7/36028797018963968), by norm_num⟩
  | 1 => ⟨((113593229249/36028797018963968), (66576099265/9007199254740992)), (9/36028797018963968), by norm_num⟩
  | 2 => ⟨((-235033859565/72057594037927936), (-268880778119/72057594037927936)), (11/72057594037927936), by norm_num⟩
  | 3 => ⟨((147551281825/72057594037927936), (165868378569/144115188075855872)), (15/144115188075855872), by norm_num⟩
  | 4 => ⟨((-271990115515/288230376151711744), (-19983590775/144115188075855872)), (15/288230376151711744), by norm_num⟩
  | 5 => ⟨((196430267067/576460752303423488), (-98529399941/1152921504606846976)), (29/1152921504606846976), by norm_num⟩
  | 6 => ⟨((-110530374823/1152921504606846976), (43036668465/576460752303423488)), (27/2305843009213693952), by norm_num⟩
  | 7 => ⟨((168995040213/9223372036854775808), (-331804111545/9223372036854775808)), (47/9223372036854775808), by norm_num⟩
  | 8 => ⟨((-6604980939/36893488147419103232), (482686897455/36893488147419103232)), (79/36893488147419103232), by norm_num⟩
  | 9 => ⟨((-136836642851/73786976294838206464), (-69106147427/18446744073709551616)), (67/73786976294838206464), by norm_num⟩
  | 10 => ⟨((79292448493/73786976294838206464), (57250324287/73786976294838206464)), (113/295147905179352825856), by norm_num⟩
  | 11 => ⟨((-245178915787/590295810358705651712), (-2009421849/36893488147419103232)), (95/590295810358705651712), by norm_num⟩
  | 12 => ⟨((145548657583/1180591620717411303424), (-113225565965/2361183241434822606848)), (81/1180591620717411303424), by norm_num⟩
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
  | 0 => ⟨((75/8), (987/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((5120000/48324723), (-421120/48324723)), 0, by norm_num⟩
  | 1 => ⟨((-1446503219200/259475428114081), (2156134400000/2335278853026729)), 0, by norm_num⟩
  | 2 => ⟨((327972021189/1125899906842624), (-20604319513/281474976710656)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-272243122321/18014398509481984), (92721407415/18014398509481984)), (1/9007199254740992), by norm_num⟩
  | 4 => ⟨((56072248865/72057594037927936), (-97570037537/288230376151711744)), (3/288230376151711744), by norm_num⟩
  | 5 => ⟨((-91652545017/2305843009213693952), (24584152255/1152921504606846976)), (3/4611686018427387904), by norm_num⟩
  | 6 => ⟨((297027440197/147573952589676412928), (-48064579921/36893488147419103232)), (7/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-59589236351/590295810358705651712), (183665291557/2361183241434822606848)), (1/295147905179352825856), by norm_num⟩
  | 8 => ⟨((23653367509/4722366482869645213696), (-172291631283/37778931862957161709568)), (1/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((-18547162317/75557863725914323419136), (159226224833/604462909807314587353088)), (9/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((229328054943/19342813113834066795298816), (-290608322901/19342813113834066795298816)), (17/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-87059260691/154742504910672534362390528), (262307017259/309485009821345068724781056)), (1/19342813113834066795298816), by norm_num⟩
  | 12 => ⟨((16161998453/618970019642690137449562112), (-29308739547/618970019642690137449562112)), (1/309485009821345068724781056), by norm_num⟩
  | _ => zero

theorem V_gammaInverse8 : F_gammaFactor8 c=value ((75/8), (987/1280)) := by
  have h := centre_contains S_gammaFactor8
  have he : J_gammaFactor8 ⟨0,by omega⟩=exact ((75/8), (987/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor8,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse8 : Sound J_gammaInverse8 F_gammaInverse8 c := by
  apply inv_coefficients_sound (A_gammaFactor8 hcre) (N_gammaInverse8 hcre) S_gammaFactor8
  · rw [V_gammaInverse8]
    have hv : (value ((75/8), (987/1280)))⁻¹=value ((5120000/48324723), (-421120/48324723)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse8] using! contains_exact ((5120000/48324723), (-421120/48324723))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse8,J_gammaFactor8,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct8 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-44919451557/288230376151711744), (-114183539775/144115188075855872)), (7/288230376151711744), by norm_num⟩
  | 1 => ⟨((118221604701/288230376151711744), (114851134707/144115188075855872)), (5/144115188075855872), by norm_num⟩
  | 2 => ⟨((-58121710857/144115188075855872), (-117412231597/288230376151711744)), (3/144115188075855872), by norm_num⟩
  | 3 => ⟨((144185274027/576460752303423488), (71435240771/576460752303423488)), (1/72057594037927936), by norm_num⟩
  | 4 => ⟨((-132561399169/1152921504606846976), (-6884624031/576460752303423488)), (1/144115188075855872), by norm_num⟩
  | 5 => ⟨((191389377947/4611686018427387904), (-54843547391/4611686018427387904)), (31/9223372036854775808), by norm_num⟩
  | 6 => ⟨((-53742309335/4611686018427387904), (176279671575/18446744073709551616)), (29/18446744073709551616), by norm_num⟩
  | 7 => ⟨((635109149/288230376151711744), (-41764837087/9223372036854775808)), (51/73786976294838206464), by norm_num⟩
  | 8 => ⟨((-576921375/295147905179352825856), (15100591445/9223372036854775808)), (85/295147905179352825856), by norm_num⟩
  | 9 => ⟨((-139403418695/590295810358705651712), (-275959737495/590295810358705651712)), (9/73786976294838206464), by norm_num⟩
  | 10 => ⟨((319146915915/2361183241434822606848), (228036017065/2361183241434822606848)), (121/2361183241434822606848), by norm_num⟩
  | 11 => ⟨((-122927820165/2361183241434822606848), (-31537521715/4722366482869645213696)), (51/2361183241434822606848), by norm_num⟩
  | 12 => ⟨((291486772635/18889465931478580854784), (-14233241505/2361183241434822606848)), (43/4722366482869645213696), by norm_num⟩
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
  | 0 => ⟨((83/8), (987/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((16998400/177332569), (-1263360/177332569)), 0, by norm_num⟩
  | 1 => ⟨((-143674762035200/31446840028139761), (21475098624000/31446840028139761)), 0, by norm_num⟩
  | 2 => ⟨((243804231795/1125899906842624), (-55174493081/1125899906842624)), (1/1125899906842624), by norm_num⟩
  | 3 => ⟨((-45954069567/4503599627370496), (56205834021/18014398509481984)), (3/36028797018963968), by norm_num⟩
  | 4 => ⟨((137755830833/288230376151711744), (-107155533947/576460752303423488)), (3/576460752303423488), by norm_num⟩
  | 5 => ⟨((-205168466907/9223372036854775808), (48937272005/4611686018427387904)), (3/9223372036854775808), by norm_num⟩
  | 6 => ⟨((303509718755/295147905179352825856), (-86748296451/147573952589676412928)), (3/147573952589676412928), by norm_num⟩
  | 7 => ⟨((-27857211879/590295810358705651712), (150343799421/4722366482869645213696)), (3/2361183241434822606848), by norm_num⟩
  | 8 => ⟨((81164693459/37778931862957161709568), (-15999055073/9444732965739290427392)), (3/37778931862957161709568), by norm_num⟩
  | 9 => ⟨((-234374482747/2417851639229258349412352), (214805180545/2417851639229258349412352)), (11/2417851639229258349412352), by norm_num⟩
  | 10 => ⟨((167487109923/38685626227668133590597632), (-178080935713/38685626227668133590597632)), (5/19342813113834066795298816), by norm_num⟩
  | 11 => ⟨((-59143846461/309485009821345068724781056), (73053416213/309485009821345068724781056)), (9/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((20595381907/2475880078570760549798248448), (-118783473781/9903520314283042199192993792)), (15/19807040628566084398385987584), by norm_num⟩
  | _ => zero

theorem V_gammaInverse9 : F_gammaFactor9 c=value ((83/8), (987/1280)) := by
  have h := centre_contains S_gammaFactor9
  have he : J_gammaFactor9 ⟨0,by omega⟩=exact ((83/8), (987/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor9,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse9 : Sound J_gammaInverse9 F_gammaInverse9 c := by
  apply inv_coefficients_sound (A_gammaFactor9 hcre) (N_gammaInverse9 hcre) S_gammaFactor9
  · rw [V_gammaInverse9]
    have hv : (value ((83/8), (987/1280)))⁻¹=value ((16998400/177332569), (-1263360/177332569)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse9] using! contains_exact ((16998400/177332569), (-1263360/177332569))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse9,J_gammaFactor9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-94923895359/4611686018427387904), (-21570349701/288230376151711744)), (3/1152921504606846976), by norm_num⟩
  | 1 => ⟨((26659783135/576460752303423488), (88755218579/1152921504606846976)), (5/1152921504606846976), by norm_num⟩
  | 2 => ⟨((-101576185257/2305843009213693952), (-183080156097/4611686018427387904)), (3/1152921504606846976), by norm_num⟩
  | 3 => ⟨((125028470111/4611686018427387904), (27306666619/2305843009213693952)), (1/576460752303423488), by norm_num⟩
  | 4 => ⟨((-459252307701/36893488147419103232), (-29392066197/36893488147419103232)), (15/18446744073709551616), by norm_num⟩
  | 5 => ⟨((331513294193/73786976294838206464), (-53191928735/36893488147419103232)), (15/36893488147419103232), by norm_num⟩
  | 6 => ⟨((-46455399931/36893488147419103232), (159991046191/147573952589676412928)), (7/36893488147419103232), by norm_num⟩
  | 7 => ⟨((138982188985/590295810358705651712), (-149402407867/295147905179352825856)), (3/36893488147419103232), by norm_num⟩
  | 8 => ⟨((2355540793/1180591620717411303424), (429853335501/2361183241434822606848)), (81/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((-126143285555/4722366482869645213696), (-244844620373/4722366482869645213696)), (69/4722366482869645213696), by norm_num⟩
  | 10 => ⟨((285405835369/18889465931478580854784), (100910974525/9444732965739290427392)), (115/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((-219127161067/37778931862957161709568), (-27484774787/37778931862957161709568)), (3/1180591620717411303424), by norm_num⟩
  | 12 => ⟨((8107420283/4722366482869645213696), (-50891976011/75557863725914323419136)), (81/75557863725914323419136), by norm_num⟩
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
  | 0 => ⟨((91/8), (987/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2662400/30423967), (-180480/30423967)), 0, by norm_num⟩
  | 1 => ⟨((-503985766400/132231109716727), (480509952000/925617768017089)), 0, by norm_num⟩
  | 2 => ⟨((93015093243/562949953421312), (-38302177965/1125899906842624)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-256836456033/36028797018963968), (71286139205/36028797018963968)), (1/18014398509481984), by norm_num⟩
  | 4 => ⟨((352845851109/1152921504606846976), (-62094745397/576460752303423488)), (1/288230376151711744), by norm_num⟩
  | 5 => ⟨((-241126497329/18446744073709551616), (51843826875/9223372036854775808)), (1/4611686018427387904), by norm_num⟩
  | 6 => ⟨((40971753535/73786976294838206464), (-168065667219/590295810358705651712)), (7/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-110745989341/4722366482869645213696), (66607315085/4722366482869645213696)), (3/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((297480032155/302231454903657293676544), (-207544534177/302231454903657293676544)), (5/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-99205103671/2417851639229258349412352), (159415309383/4835703278458516698824704)), (9/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((131337523733/77371252455336267181195264), (-30254857555/19342813113834066795298816)), (15/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-86203468843/1237940039285380274899124224), (181912333681/2475880078570760549798248448)), (3/618970019642690137449562112), by norm_num⟩
  | 12 => ⟨((224131030861/79228162514264337593543950336), (-271070186899/79228162514264337593543950336)), (19/79228162514264337593543950336), by norm_num⟩
  | _ => zero

theorem V_gammaInverse10 : F_gammaFactor10 c=value ((91/8), (987/1280)) := by
  have h := centre_contains S_gammaFactor10
  have he : J_gammaFactor10 ⟨0,by omega⟩=exact ((91/8), (987/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor10,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse10 : Sound J_gammaInverse10 F_gammaInverse10 c := by
  apply inv_coefficients_sound (A_gammaFactor10 hcre) (N_gammaInverse10 hcre) S_gammaFactor10
  · rw [V_gammaInverse10]
    have hv : (value ((91/8), (987/1280)))⁻¹=value ((2662400/30423967), (-180480/30423967)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse10] using! contains_exact ((2662400/30423967), (-180480/30423967))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse10,J_gammaFactor10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-82833023433/36893488147419103232), (-59277642529/9223372036854775808)), (5/18446744073709551616), by norm_num⟩
  | 1 => ⟨((170487758595/36893488147419103232), (62137587571/9223372036854775808)), (1/2305843009213693952), by norm_num⟩
  | 2 => ⟨((-39777060553/9223372036854775808), (-128899257387/36893488147419103232)), (5/18446744073709551616), by norm_num⟩
  | 3 => ⟨((97465792895/36893488147419103232), (37468222493/36893488147419103232)), (27/147573952589676412928), by norm_num⟩
  | 4 => ⟨((-178957020303/147573952589676412928), (-9584539763/295147905179352825856)), (13/147573952589676412928), by norm_num⟩
  | 5 => ⟨((258414915003/590295810358705651712), (-91494368867/590295810358705651712)), (13/295147905179352825856), by norm_num⟩
  | 6 => ⟨((-144568290871/1180591620717411303424), (509237103/4611686018427387904)), (3/147573952589676412928), by norm_num⟩
  | 7 => ⟨((106873764627/4722366482869645213696), (-240314515565/4722366482869645213696)), (41/4722366482869645213696), by norm_num⟩
  | 8 => ⟨((3921977277/9444732965739290427392), (344035805785/18889465931478580854784)), (69/18889465931478580854784), by norm_num⟩
  | 9 => ⟨((-102657317871/37778931862957161709568), (-195484338687/37778931862957161709568)), (59/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((114835555217/75557863725914323419136), (20092816615/18889465931478580854784)), (97/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((-351525757505/604462909807314587353088), (-43092936075/604462909807314587353088)), (81/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((103907060567/604462909807314587353088), (-81883327479/1208925819614629174706176)), (137/1208925819614629174706176), by norm_num⟩
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
  | 0 => ⟨((99/8), (987/1280)), 0, by norm_num⟩
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
  | 0 => ⟨((2252800/27986641), (-421120/83959923)), 0, by norm_num⟩
  | 1 => ⟨((-22749314252800/7049268670165929), (948699136000/2349756223388643)), 0, by norm_num⟩
  | 2 => ⟨((290199785579/2251799813685248), (-54815852129/2251799813685248)), (1/2251799813685248), by norm_num⟩
  | 3 => ⟨((-369357590613/72057594037927936), (93887916259/72057594037927936)), (1/36028797018963968), by norm_num⟩
  | 4 => ⟨((117042902057/576460752303423488), (-18820311729/288230376151711744)), (1/576460752303423488), by norm_num⟩
  | 5 => ⟨((-295444398599/36893488147419103232), (7233915555/2305843009213693952)), (1/9223372036854775808), by norm_num⟩
  | 6 => ⟨((371222804327/1180591620717411303424), (-172778179099/1180591620717411303424)), (3/590295810358705651712), by norm_num⟩
  | 7 => ⟨((-116060699769/9444732965739290427392), (126158609553/18889465931478580854784)), (5/18889465931478580854784), by norm_num⟩
  | 8 => ⟨((144415697283/302231454903657293676544), (-181111421091/604462909807314587353088)), (1/75557863725914323419136), by norm_num⟩
  | 9 => ⟨((-178729888105/9671406556917033397649408), (128218898455/9671406556917033397649408)), (3/4835703278458516698824704), by norm_num⟩
  | 10 => ⟨((219901589619/309485009821345068724781056), (-89740085521/154742504910672534362390528)), (5/154742504910672534362390528), by norm_num⟩
  | 11 => ⟨((-268814008065/9903520314283042199192993792), (3887580225/154742504910672534362390528)), (15/9903520314283042199192993792), by norm_num⟩
  | 12 => ⟨((20390392377/19807040628566084398385987584), (-171008024903/158456325028528675187087900672)), (11/158456325028528675187087900672), by norm_num⟩
  | _ => zero

theorem V_gammaInverse11 : F_gammaFactor11 c=value ((99/8), (987/1280)) := by
  have h := centre_contains S_gammaFactor11
  have he : J_gammaFactor11 ⟨0,by omega⟩=exact ((99/8), (987/1280)) := by
    apply CertifiedScalarExp.disk_ext <;> norm_num [J_gammaFactor11,exact]
  rw [he] at h
  exact value_eq_of_exact h

set_option maxHeartbeats 5000000 in
theorem S_gammaInverse11 : Sound J_gammaInverse11 F_gammaInverse11 c := by
  apply inv_coefficients_sound (A_gammaFactor11 hcre) (N_gammaInverse11 hcre) S_gammaFactor11
  · rw [V_gammaInverse11]
    have hv : (value ((99/8), (987/1280)))⁻¹=value ((2252800/27986641), (-421120/83959923)) := by
      apply Complex.ext <;> norm_num [value,Complex.inv_re,Complex.inv_im,Complex.normSq_apply]
    rw [hv]
    simpa [J_gammaInverse11] using! contains_exact ((2252800/27986641), (-421120/83959923))
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_gammaInverse11,J_gammaFactor11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaProduct11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-62855770733/295147905179352825856), (-298734039429/590295810358705651712)), (15/590295810358705651712), by norm_num⟩
  | 1 => ⟨((30666431381/73786976294838206464), (39767667431/73786976294838206464)), (3/73786976294838206464), by norm_num⟩
  | 2 => ⟨((-28242044527/73786976294838206464), (-165433589959/590295810358705651712)), (15/590295810358705651712), by norm_num⟩
  | 3 => ⟨((17255525521/73786976294838206464), (46526329843/590295810358705651712)), (21/1180591620717411303424), by norm_num⟩
  | 4 => ⟨((-507118192147/4722366482869645213696), (520986999/590295810358705651712)), (5/590295810358705651712), by norm_num⟩
  | 5 => ⟨((22892330169/590295810358705651712), (-70727754397/4722366482869645213696)), (5/1180591620717411303424), by norm_num⟩
  | 6 => ⟨((-51126467587/4722366482869645213696), (96362985097/9444732965739290427392)), (37/18889465931478580854784), by norm_num⟩
  | 7 => ⟨((37337617199/18889465931478580854784), (-351163426463/75557863725914323419136)), (63/75557863725914323419136), by norm_num⟩
  | 8 => ⟨((17190469833/302231454903657293676544), (500496507607/302231454903657293676544)), (53/151115727451828646838272), by norm_num⟩
  | 9 => ⟨((-151797357765/604462909807314587353088), (-70933251167/151115727451828646838272)), (91/604462909807314587353088), by norm_num⟩
  | 10 => ⟨((167992077975/1208925819614629174706176), (116374596093/1208925819614629174706176)), (75/1208925819614629174706176), by norm_num⟩
  | 11 => ⟨((-128155920733/2417851639229258349412352), (-30695129033/4835703278458516698824704)), (31/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((302650355631/19342813113834066795298816), (-119766850849/19342813113834066795298816)), (105/9671406556917033397649408), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaProduct11 : Sound J_gammaProduct11 F_gammaProduct11 c := by
  apply sound_round (sound_mul (A_gammaProduct10 hcre) (A_gammaInverse11 hcre) S_gammaProduct10 S_gammaInverse11)
  intro k
  fin_cases k <;> norm_num [J_gammaProduct11, J_gammaProduct10, J_gammaInverse11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaFinite : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((366361568893/549755813888), (697301013/549755813888)), (491/274877906944), by norm_num⟩
  | 1 => ⟨((7295904945/137438953472), (254257869465/1099511627776)), (2611/549755813888), by norm_num⟩
  | 2 => ⟨((151725733843/8796093022208), (-219219840101/8796093022208)), (14075/2199023255552), by norm_num⟩
  | 3 => ⟨((30064608033/2199023255552), (185063770013/8796093022208)), (51199/8796093022208), by norm_num⟩
  | 4 => ⟨((-338691890891/70368744177664), (-138248353805/70368744177664)), (281559/70368744177664), by norm_num⟩
  | 5 => ⟨((288582033589/140737488355328), (3258892635/17592186044416)), (159787/70368744177664), by norm_num⟩
  | 6 => ⟨((-39661494903/70368744177664), (175401918051/562949953421312)), (639859/562949953421312), by norm_num⟩
  | 7 => ⟨((130710575307/1125899906842624), (-187879204525/1125899906842624)), (585705/1125899906842624), by norm_num⟩
  | 8 => ⟨((-14119949719/2251799813685248), (9159890561/140737488355328)), (123655/562949953421312), by norm_num⟩
  | 9 => ⟨((-73823792863/9007199254740992), (-341575791611/18014398509481984)), (1551207/18014398509481984), by norm_num⟩
  | 10 => ⟨((23404219119/4503599627370496), (72082631517/18014398509481984)), (35853/1125899906842624), by norm_num⟩
  | 11 => ⟨((-296277549999/144115188075855872), (-43918561069/144115188075855872)), (1629089/144115188075855872), by norm_num⟩
  | 12 => ⟨((177526518405/288230376151711744), (-33654326551/144115188075855872)), (2248323/576460752303423488), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaFinite : Sound J_gammaFinite F_gammaFinite c := by
  apply sound_round (sound_mul (A_gammaExp hcre) (A_gammaProduct11 hcre) S_gammaExp S_gammaProduct11)
  intro k
  fin_cases k <;> norm_num [J_gammaFinite, J_gammaExp, J_gammaProduct11, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_gammaActual : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((366361568893/549755813888), (697301013/549755813888)), (983/549755813888), by norm_num⟩
  | 1 => ⟨((7295904945/137438953472), (254257869465/1099511627776)), (5223/1099511627776), by norm_num⟩
  | 2 => ⟨((151725733843/8796093022208), (-219219840101/8796093022208)), (56301/8796093022208), by norm_num⟩
  | 3 => ⟨((30064608033/2199023255552), (185063770013/8796093022208)), (25/4294967296), by norm_num⟩
  | 4 => ⟨((-338691890891/70368744177664), (-138248353805/70368744177664)), (140781/35184372088832), by norm_num⟩
  | 5 => ⟨((288582033589/140737488355328), (3258892635/17592186044416)), (79895/35184372088832), by norm_num⟩
  | 6 => ⟨((-39661494903/70368744177664), (175401918051/562949953421312)), (319941/281474976710656), by norm_num⟩
  | 7 => ⟨((130710575307/1125899906842624), (-187879204525/1125899906842624)), (585751/1125899906842624), by norm_num⟩
  | 8 => ⟨((-14119949719/2251799813685248), (9159890561/140737488355328)), (989421/4503599627370496), by norm_num⟩
  | 9 => ⟨((-73823792863/9007199254740992), (-341575791611/18014398509481984)), (193991/2251799813685248), by norm_num⟩
  | 10 => ⟨((23404219119/4503599627370496), (72082631517/18014398509481984)), (574369/18014398509481984), by norm_num⟩
  | 11 => ⟨((-296277549999/144115188075855872), (-43918561069/144115188075855872)), (817427/72057594037927936), by norm_num⟩
  | 12 => ⟨((177526518405/288230376151711744), (-33654326551/144115188075855872)), (1135691/288230376151711744), by norm_num⟩
  | _ => zero

set_option maxHeartbeats 5000000 in
theorem S_gammaActual : Sound J_gammaActual F_gammaActual c := by
  apply sound_round (gamma_sound hc S_gammaFinite)
  intro k
  fin_cases k <;> norm_num [J_gammaActual,J_gammaFinite,inflate,zero,size]

def gammaJet : Jet 12 := J_gammaActual
theorem gammaJet_sound : Sound gammaJet F_gammaActual (Data.centre ⟨3,by norm_num [Data.count]⟩) := S_gammaActual

end Reinmann.XiRectangle.Tile003Gamma

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
namespace Reinmann.XiRectangle.Tile018Terms3
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

def J_log22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((772760613339579/250000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log22 : Sound J_log22 F_log22 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log22_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog22 : Sound J_negLog22 F_negLog22 c := by
  apply sound_round (sound_scale (A_log22 hcre) S_log22)
  intro k
  fin_cases k <;> norm_num [J_negLog22, J_log22, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2489236171/1073741824), (-13527442819/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-26551852495/8589934592), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg22 : Sound J_arg22 F_arg22 c := by
  apply sound_round (sound_mul (A_negLog22 hcre) (A_variable hcre) S_negLog22 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg22, J_negLog22, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term22 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1769743632777187/18014398509481984), (-28392170503441/4503599627370496)), (3647717/18014398509481984), by norm_num⟩
  | 1 => ⟨((-652116859/2147483648), (1339132757/68719476736)), (45/68719476736), by norm_num⟩
  | 2 => ⟨((32251534331/68719476736), (-2069658101/68719476736)), (9/8589934592), by norm_num⟩
  | 3 => ⟨((-8307571817/17179869184), (1066233509/34359738368)), (39/34359738368), by norm_num⟩
  | 4 => ⟨((12839528585/34359738368), (-1647886521/68719476736)), (31/34359738368), by norm_num⟩
  | 5 => ⟨((-31750022349/137438953472), (1018737439/68719476736)), (79/137438953472), by norm_num⟩
  | 6 => ⟨((16356777829/137438953472), (-524826779/68719476736)), (21/68719476736), by norm_num⟩
  | 7 => ⟨((-28891139811/549755813888), (463503387/137438953472)), (19/137438953472), by norm_num⟩
  | 8 => ⟨((2790741865/137438953472), (-716354323/549755813888)), (61/1099511627776), by norm_num⟩
  | 9 => ⟨((-15335647255/2199023255552), (492062583/1099511627776)), (43/2199023255552), by norm_num⟩
  | 10 => ⟨((9480627343/4398046511104), (-1216789067/8796093022208)), (55/8796093022208), by norm_num⟩
  | 11 => ⟨((-21312742983/35184372088832), (42740303/1099511627776)), (1/549755813888), by norm_num⟩
  | 12 => ⟨((21959531119/140737488355328), (-704597819/70368744177664)), (17/35184372088832), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395238986542947/2535301200456458802993406410752), (-83477241841/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((1778393532125567/633825300114114700748351602688), (-49375624283/316912650057057350374175801344)), (1441/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889319839042353/39614081257132168796771975168), (-111072814379/39614081257132168796771975168)), (1621/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889068706979383/2475880078570760549798248448), (-117986968897/2475880078570760549798248448)), (3445/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770735147964001/154742504910672534362390528), (-117955599135/154742504910672534362390528)), (3445/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387281640127893/2417851639229258349412352), (-55275027811/4835703278458516698824704)), (1615/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258415380106067/604462909807314587353088), (-96697993389/604462909807314587353088)), (2827/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117949112975465/4722366482869645213696), (-157071820075/75557863725914323419136)), (4593/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648542553963849/2361183241434822606848), (-29437319119/1180591620717411303424)), (3445/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202602991170641/73786976294838206464), (-161816601565/590295810358705651712)), (37/4611686018427387904), by norm_num⟩
  | 8 => ⟨((56959224835771/2305843009213693952), (-202137863997/73786976294838206464)), (185/2305843009213693952), by norm_num⟩
  | 7 => ⟨((1821781137962571/9223372036854775808), (-227222526127/9223372036854775808)), (1665/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1593031006788193/1152921504606846976), (-226994537443/1152921504606846976)), (6661/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193746796335657/144115188075855872), (-99182020947/72057594037927936)), (1457/36028797018963968), by norm_num⟩
  | 4 => ⟨((745194753849981/18014398509481984), (-148517238673/18014398509481984)), (8743/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487703149364597/9007199254740992), (-370399554571/9007199254740992)), (10929/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224854978288625/4503599627370496), (-369062699455/2251799813685248)), (21859/4503599627370496), by norm_num⟩
  | 1 => ⟨((276437976520885/281474976710656), (-1100527966687/2251799813685248)), (16397/1125899906842624), by norm_num⟩
  | 0 => ⟨((542922767277707/562949953421312), (-2174559771525/2251799813685248)), (65617/2251799813685248), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((542922767277707/562949953421312), (-2174559771525/2251799813685248)), (250308999068450217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1047215063764269/1125899906842624), (-4194397749185/2251799813685248)), (126693/2251799813685248), by norm_num⟩
  | 2 => ⟨((60876581083429/70368744177664), (-3901267314857/1125899906842624)), (236151/2251799813685248), by norm_num⟩
  | 3 => ⟨((1685247603620625/2251799813685248), (-3375018536943/562949953421312)), (205115/1125899906842624), by norm_num⟩
  | 4 => ⟨((630579418349667/1125899906842624), (-20206918455153/2251799813685248)), (77369/281474976710656), by norm_num⟩
  | 5 => ⟨((1412304310682945/4503599627370496), (-45268915322401/4503599627370496)), (352209/1125899906842624), by norm_num⟩
  | 6 => ⟨((1769743632777187/18014398509481984), (-28392170503441/4503599627370496)), (3647717/18014398509481984), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2489236171/1073741824), (-13527442819/536870912)), (1/536870912), by norm_num⟩, -4, term22ValuePoly, term22ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term22Value_checks : CertifiedScalarExp.Checks term22Value := by
  constructor
  · norm_num [term22Value, CertifiedScalarExp.reduced, term22ValuePoly, term22ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term22ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value, term22ValueSquares, term22ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term22Value, CertifiedScalarExp.roundingCheck, term22ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term22 : Sound J_term22 F_term22 c := by
  apply exp_sound (A_arg22 hcre) S_arg22 term22Value term22Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term22Value,J_arg22]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term22,J_arg22,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((62709884318583/20000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log23 : Sound J_log23 F_log23 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log23_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog23 : Sound J_negLog23 F_negLog23 c := by
  apply sound_round (sound_scale (A_log23 hcre) S_log23)
  intro k
  fin_cases k <;> norm_num [J_negLog23, J_log23, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2525033459/1073741824), (-13721978703/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg23 : Sound J_arg23 F_arg23 c := by
  apply sound_round (sound_mul (A_negLog23 hcre) (A_variable hcre) S_negLog23 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg23, J_negLog23, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term23 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((195203672008447/2251799813685248), (-88683804797373/2251799813685248)), (1202299/4503599627370496), by norm_num⟩
  | 1 => ⟨((-9339294197/34359738368), (4242974197/34359738368)), (15/17179869184), by norm_num⟩
  | 2 => ⟨((3660412867/8589934592), (-3325955263/17179869184)), (49/34359738368), by norm_num⟩
  | 3 => ⟨((-7651468915/17179869184), (3476171163/17179869184)), (53/34359738368), by norm_num⟩
  | 4 => ⟨((11995568263/34359738368), (-5449757287/34359738368)), (43/34359738368), by norm_num⟩
  | 5 => ⟨((-7522406981/34359738368), (6835072981/68719476736)), (7/8589934592), by norm_num⟩
  | 6 => ⟨((3931077263/34359738368), (-3571888633/68719476736)), (15/34359738368), by norm_num⟩
  | 7 => ⟨((-14086708595/274877906944), (6399792085/274877906944)), (55/274877906944), by norm_num⟩
  | 8 => ⟨((5521099165/274877906944), (-10033255533/1099511627776)), (11/137438953472), by norm_num⟩
  | 9 => ⟨((-7693944221/1099511627776), (3495468299/1099511627776)), (63/2199023255552), by norm_num⟩
  | 10 => ⟨((9649727041/4398046511104), (-8768016507/8796093022208)), (81/8796093022208), by norm_num⟩
  | 11 => ⟨((-5501211513/8796093022208), (9997114561/35184372088832)), (47/17592186044416), by norm_num⟩
  | 12 => ⟨((5749672293/35184372088832), (-10448631627/140737488355328)), (101/140737488355328), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790456259316641/5070602400912917605986812821504), (-555480293767/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889170966936045/316912650057057350374175801344), (-657081522801/633825300114114700748351602688)), (721/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((118078861883425/2475880078570760549798248448), (-369532973819/19807040628566084398385987584)), (3245/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889007028038205/2475880078570760549798248448), (-785069273655/2475880078570760549798248448)), (431/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((442668366702613/38685626227668133590597632), (-784857533361/154742504910672534362390528)), (431/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549068732087513/9671406556917033397649408), (-735579043437/9671406556917033397649408)), (3233/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314591194475365/151115727451828646838272), (-80425857365/75557863725914323419136)), (2829/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887103574668761/75557863725914323419136), (-1045114829245/75557863725914323419136)), (4597/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297023429431221/4722366482869645213696), (-391733830529/2361183241434822606848)), (431/590295810358705651712), by norm_num⟩
  | 9 => ⟨((810369557652837/295147905179352825856), (-1076669643059/590295810358705651712)), (4741/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822589168043007/73786976294838206464), (-42029377925/2305843009213693952)), (5927/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821661845475071/9223372036854775808), (-377956325409/2305843009213693952)), (6669/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1592911698893227/1152921504606846976), (-94392902851/72057594037927936)), (3335/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193642384803675/144115188075855872), (-1319771519513/144115188075855872)), (2919/72057594037927936), by norm_num⟩
  | 4 => ⟨((372558214169171/9007199254740992), (-1976204263193/36028797018963968)), (8759/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487507277738147/9007199254740992), (-2464224287753/9007199254740992)), (10953/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224463066163389/4503599627370496), (-4910402305833/4503599627370496)), (21921/4503599627370496), by norm_num⟩
  | 1 => ⟨((138182221128845/140737488355328), (-3660325676793/1125899906842624)), (32919/2251799813685248), by norm_num⟩
  | 0 => ⟨((2170512994163195/2251799813685248), (-14462472347937/2251799813685248)), (65989/2251799813685248), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((2170512994163195/2251799813685248), (-14462472347937/2251799813685248)), (251728066451262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2092067627901201/2251799813685248), (-108909354309/8796093022208)), (64031/1125899906842624), by norm_num⟩
  | 2 => ⟨((1943320891317271/2251799813685248), (-25903061046561/1125899906842624)), (30141/281474976710656), by norm_num⟩
  | 3 => ⟨((837954641751143/1125899906842624), (-89418178960529/2251799813685248)), (427287/2251799813685248), by norm_num⟩
  | 4 => ⟨((1243750132129641/2251799813685248), (-133099536933141/2251799813685248)), (669955/2251799813685248), by norm_num⟩
  | 5 => ⟨((1358201466353289/4503599627370496), (-294062670475249/4503599627370496)), (1638561/4503599627370496), by norm_num⟩
  | 6 => ⟨((195203672008447/2251799813685248), (-88683804797373/2251799813685248)), (1202299/4503599627370496), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2525033459/1073741824), (-13721978703/536870912)), (1/536870912), by norm_num⟩, -4, term23ValuePoly, term23ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term23Value_checks : CertifiedScalarExp.Checks term23Value := by
  constructor
  · norm_num [term23Value, CertifiedScalarExp.reduced, term23ValuePoly, term23ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term23ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value, term23ValueSquares, term23ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term23Value, CertifiedScalarExp.roundingCheck, term23ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term23 : Sound J_term23 F_term23 c := by
  apply exp_sound (A_arg23 hcre) S_arg23 term23Value term23Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term23Value,J_arg23]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term23,J_arg23,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1589026915173973/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log24 : Sound J_log24 F_log24 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log24_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog24 : Sound J_negLog24 F_negLog24 c := by
  apply sound_round (sound_scale (A_log24 hcre) S_log24)
  intro k
  fin_cases k <;> norm_num [J_negLog24, J_log24, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-2559306987/1073741824), (-6954116955/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-27299274533/8589934592), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg24 : Sound J_arg24 F_arg24 c := by
  apply sound_round (sound_mul (A_negLog24 hcre) (A_variable hcre) S_negLog24 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg24, J_negLog24, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term24 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((297201269307041/4503599627370496), (-290132387842835/4503599627370496)), (736453/2251799813685248), by norm_num⟩
  | 1 => ⟨((-14412256353/68719476736), (14069463295/68719476736)), (37/34359738368), by norm_num⟩
  | 2 => ⟨((11450731627/34359738368), (-11178377929/34359738368)), (15/8589934592), by norm_num⟩
  | 3 => ⟨((-12130347169/34359738368), (2960457233/8589934592)), (33/17179869184), by norm_num⟩
  | 4 => ⟨((9637724071/34359738368), (-9408492449/34359738368)), (27/17179869184), by norm_num⟩
  | 5 => ⟨((-1531460295/8589934592), (5980139093/34359738368)), (35/34359738368), by norm_num⟩
  | 6 => ⟨((12978835351/137438953472), (-12670135967/137438953472)), (19/34359738368), by norm_num⟩
  | 7 => ⟨((-11784982115/274877906944), (5752339163/137438953472)), (71/274877906944), by norm_num⟩
  | 8 => ⟨((1170415861/68719476736), (-9140621755/549755813888)), (29/274877906944), by norm_num⟩
  | 9 => ⟨((-13225403059/2199023255552), (12910839103/2199023255552)), (21/549755813888), by norm_num⟩
  | 10 => ⟨((4203104285/2199023255552), (-8206268333/4398046511104)), (109/8796093022208), by norm_num⟩
  | 11 => ⟨((-9714684853/17592186044416), (9483622731/17592186044416)), (65/17592186044416), by norm_num⟩
  | 12 => ⟨((10291263803/70368744177664), (-10046487849/70368744177664)), (71/70368744177664), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197608867455839/1267650600228229401496703205376), (-1007391911991/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778292221599047/633825300114114700748351602688), (-595794065623/316912650057057350374175801344)), (1443/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889205845803259/39614081257132168796771975168), (-1340259337165/39614081257132168796771975168)), (3247/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944473781261993/1237940039285380274899124224), (-1423679406801/2475880078570760549798248448)), (1725/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770613973589465/154742504910672534362390528), (-1423290166677/154742504910672534362390528)), (1725/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((774506463891157/4835703278458516698824704), (-1333921109047/9671406556917033397649408)), (3235/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314578979938833/151115727451828646838272), (-583383855923/302231454903657293676544)), (2831/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943512062581147/37778931862957161709568), (-1895223019515/75557863725914323419136)), (575/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1296963794226445/4722366482869645213696), (-710369956919/2361183241434822606848)), (3451/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620657038902307/590295810358705651712), (-488104334373/147573952589676412928)), (2373/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455621613940505/18446744073709551616), (-2438872744339/73786976294838206464)), (5933/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821546133945369/9223372036854775808), (-1370733205367/4611686018427387904)), (6677/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398198946906863/288230376151711744), (-342329674753/144115188075855872)), (6679/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1193540738471745/144115188075855872), (-2393128889563/144115188075855872)), (5847/144115188075855872), by norm_num⟩
  | 4 => ⟨((745039970523949/18014398509481984), (-3583345168975/36028797018963968)), (8775/36028797018963968), by norm_num⟩
  | 3 => ⟨((1487315356552597/9007199254740992), (-558511689831/1125899906842624)), (10977/9007199254740992), by norm_num⟩
  | 2 => ⟨((139004806881757/281474976710656), (-8903008433253/4503599627370496)), (5495/1125899906842624), by norm_num⟩
  | 1 => ⟨((1105165288227153/1125899906842624), (-6635931843803/1125899906842624)), (33037/2251799813685248), by norm_num⟩
  | 0 => ⟨((2169320499057181/2251799813685248), (-26214910946515/2251799813685248)), (33173/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2169320499057181/2251799813685248), (-26214910946515/2251799813685248)), (126544956687545421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((261194632926385/281474976710656), (-6313676658957/281474976710656)), (64689/1125899906842624), by norm_num⟩
  | 2 => ⟨((1937870983868923/2251799813685248), (-93740394353981/2251799813685248)), (245917/2251799813685248), by norm_num⟩
  | 3 => ⟨((415951349873319/562949953421312), (-20167955109841/281474976710656)), (221871/1125899906842624), by norm_num⟩
  | 4 => ⟨((1217788819532373/2251799813685248), (-238426541503795/2251799813685248)), (179833/562949953421312), by norm_num⟩
  | 5 => ⟨((1266686660703255/4503599627370496), (-32235678184899/281474976710656)), (1860739/4503599627370496), by norm_num⟩
  | 6 => ⟨((297201269307041/4503599627370496), (-290132387842835/4503599627370496)), (736453/2251799813685248), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2559306987/1073741824), (-6954116955/268435456)), (1/536870912), by norm_num⟩, -4, term24ValuePoly, term24ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term24Value_checks : CertifiedScalarExp.Checks term24Value := by
  constructor
  · norm_num [term24Value, CertifiedScalarExp.reduced, term24ValuePoly, term24ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term24ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value, term24ValueSquares, term24ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term24Value, CertifiedScalarExp.roundingCheck, term24ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term24 : Sound J_term24 F_term24 c := by
  apply exp_sound (A_arg24 hcre) S_arg24 term24Value term24Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term24Value,J_arg24]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term24,J_arg24,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((16094379124341/5000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log25 : Sound J_log25 F_log25 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log25_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog25 : Sound J_negLog25 F_negLog25 c := by
  apply sound_round (sound_scale (A_log25 hcre) S_log25)
  intro k
  fin_cases k <;> norm_num [J_negLog25, J_log25, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-162011325/67108864), (-7043442353/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-27649932795/8589934592), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg25 : Sound J_arg25 F_arg25 c := by
  apply sound_round (sound_mul (A_negLog25 hcre) (A_variable hcre) S_negLog25 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg25, J_negLog25, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term25 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((180512278432763/4503599627370496), (-1440414351683837/18014398509481984)), (6822751/18014398509481984), by norm_num⟩
  | 1 => ⟨((-2216516911/17179869184), (8843450421/34359738368)), (43/34359738368), by norm_num⟩
  | 2 => ⟨((1783673175/8589934592), (-222390381/536870912)), (71/34359738368), by norm_num⟩
  | 3 => ⟨((-3827614975/17179869184), (3817850779/8589934592)), (39/17179869184), by norm_num⟩
  | 4 => ⟨((6160308655/34359738368), (-12289187575/34359738368)), (1/536870912), by norm_num⟩
  | 5 => ⟨((-7931707441/68719476736), (15822947517/68719476736)), (21/17179869184), by norm_num⟩
  | 6 => ⟨((8510393777/137438953472), (-16977367747/137438953472)), (23/34359738368), by norm_num⟩
  | 7 => ⟨((-7826828797/274877906944), (15613725317/274877906944)), (43/137438953472), by norm_num⟩
  | 8 => ⟨((1574599375/137438953472), (-3141165185/137438953472)), (71/549755813888), by norm_num⟩
  | 9 => ⟨((-9010559755/2199023255552), (4493786967/549755813888)), (103/2199023255552), by norm_num⟩
  | 10 => ⟨((5800774593/4398046511104), (-1446494223/549755813888)), (17/1099511627776), by norm_num⟩
  | 11 => ⟨((-6789808401/17592186044416), (13544975375/17592186044416)), (81/17592186044416), by norm_num⟩
  | 12 => ⟨((1821295843/17592186044416), (-14533197927/70368744177664)), (89/70368744177664), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((98801941140089/633825300114114700748351602688), (-720426461461/5070602400912917605986812821504)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444561063423367/158456325028528675187087900672), (-1704219008117/633825300114114700748351602688)), (361/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((944575924451035/19807040628566084398385987584), (-958422056751/19807040628566084398385987584)), (3249/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((29513908535045/38685626227668133590597632), (-509036343451/618970019642690137449562112)), (863/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770556507224771/154742504910672534362390528), (-508895355137/38685626227668133590597632)), (3453/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1548958999897721/9671406556917033397649408), (-953879293609/4835703278458516698824704)), (3237/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258268679740553/604462909807314587353088), (-208586250103/75557863725914323419136)), (2833/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943473630328249/37778931862957161709568), (-2710499062571/75557863725914323419136)), (1151/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((324226514727681/1180591620717411303424), (-253986609171/590295810358705651712)), (1727/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202572188972247/73786976294838206464), (-2792258808875/590295810358705651712)), (2375/295147905179352825856), by norm_num⟩
  | 8 => ⟨((455596708904897/18446744073709551616), (-1743967142169/36893488147419103232)), (5939/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821433771419809/9223372036854775808), (-3920643499537/9223372036854775808)), (1671/2305843009213693952), by norm_num⟩
  | 6 => ⟨((398170765911831/288230376151711744), (-3916544208051/1152921504606846976)), (209/36028797018963968), by norm_num⟩
  | 5 => ⟨((18647526555573/2251799813685248), (-213898116617/9007199254740992)), (5855/144115188075855872), by norm_num⟩
  | 4 => ⟨((186241321851749/4503599627370496), (-2562177808823/18014398509481984)), (4395/18014398509481984), by norm_num⟩
  | 3 => ⟨((743563620872045/4503599627370496), (-3194688088539/4503599627370496)), (1375/1125899906842624), by norm_num⟩
  | 2 => ⟨((1111848243161221/2251799813685248), (-12730667992189/4503599627370496)), (22037/4503599627370496), by norm_num⟩
  | 1 => ⟨((69054673407883/70368744177664), (-18976212471655/2251799813685248)), (33151/2251799813685248), by norm_num⟩
  | 0 => ⟨((67753669890935/70368744177664), (-4684473435605/281474976710656)), (66689/2251799813685248), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((67753669890935/70368744177664), (-4684473435605/281474976710656)), (254398354537200217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1043460603222965/1125899906842624), (-36083095752569/1125899906842624)), (65321/1125899906842624), by norm_num⟩
  | 2 => ⟨((58953929015/68719476736), (-33441062239461/562949953421312)), (250527/2251799813685248), by norm_num⟩
  | 3 => ⟨((1649332861207011/2251799813685248), (-229510712606295/2251799813685248)), (14363/70368744177664), by norm_num⟩
  | 4 => ⟨((592331454964125/1125899906842624), (-42026333557721/281474976710656)), (766985/2251799813685248), by norm_num⟩
  | 5 => ⟨((286523826125631/1125899906842624), (-88439546541439/562949953421312)), (2072099/4503599627370496), by norm_num⟩
  | 6 => ⟨((180512278432763/4503599627370496), (-1440414351683837/18014398509481984)), (6822751/18014398509481984), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-162011325/67108864), (-7043442353/268435456)), (1/536870912), by norm_num⟩, -4, term25ValuePoly, term25ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term25Value_checks : CertifiedScalarExp.Checks term25Value := by
  constructor
  · norm_num [term25Value, CertifiedScalarExp.reduced, term25ValuePoly, term25ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term25ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value, term25ValueSquares, term25ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term25Value, CertifiedScalarExp.roundingCheck, term25ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term25 : Sound J_term25 F_term25 c := by
  apply exp_sound (A_arg25 hcre) S_arg25 term25Value term25Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term25Value,J_arg25]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term25,J_arg25,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1629048269010741/500000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log26 : Sound J_log26 F_log26 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log26_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog26 : Sound J_negLog26 F_negLog26 c := by
  apply sound_round (sound_scale (A_log26 hcre) S_log26)
  intro k
  fin_cases k <;> norm_num [J_negLog26, J_log26, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1311882945/536870912), (-28517055513/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg26 : Sound J_arg26 F_arg26 c := by
  apply sound_round (sound_mul (A_negLog26 hcre) (A_variable hcre) S_negLog26 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg26, J_negLog26, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term26 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((226003857430323/18014398509481984), (-387035401217773/4503599627370496)), (3774507/9007199254740992), by norm_num⟩
  | 1 => ⟨((-702230821/17179869184), (601291037/2147483648)), (3/2147483648), by norm_num⟩
  | 2 => ⟨((2287935807/34359738368), (-979532123/2147483648)), (5/2147483648), by norm_num⟩
  | 3 => ⟨((-2484771911/34359738368), (4255213625/8589934592)), (89/34359738368), by norm_num⟩
  | 4 => ⟨((1011953345/17179869184), (-3465974195/8589934592)), (147/68719476736), by norm_num⟩
  | 5 => ⟨((-329704169/8589934592), (18067965641/68719476736)), (97/68719476736), by norm_num⟩
  | 6 => ⟨((1432277349/68719476736), (-19622392101/137438953472)), (107/137438953472), by norm_num⟩
  | 7 => ⟨((-2666570213/274877906944), (9133092539/137438953472)), (101/274877906944), by norm_num⟩
  | 8 => ⟨((2171985795/549755813888), (-29756497183/1099511627776)), (167/1099511627776), by norm_num⟩
  | 9 => ⟨((-1572564311/1099511627776), (21544342323/2199023255552)), (123/2199023255552), by norm_num⟩
  | 10 => ⟨((2049426535/4398046511104), (-28077418855/8796093022208)), (81/4398046511104), by norm_num⟩
  | 11 => ⟨((-1214041727/8796093022208), (8316267379/8796093022208)), (97/17592186044416), by norm_num⟩
  | 12 => ⟨((2636976765/70368744177664), (-18063467971/70368744177664)), (107/70368744177664), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790396370611537/5070602400912917605986812821504), (-58040969313/316912650057057350374175801344)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778197904262881/633825300114114700748351602688), (-1098346313481/316912650057057350374175801344)), (2889/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889099659653677/39614081257132168796771975168), (-308844165049/4951760157141521099596496896)), (1625/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472208658264321/618970019642690137449562112), (-2624520961977/2475880078570760549798248448)), (1727/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770500924249301/154742504910672534362390528), (-163986562387/9671406556917033397649408)), (1727/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1548906816769297/9671406556917033397649408), (-307377091699/1208925819614629174706176)), (3239/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629111472742493/302231454903657293676544), (-2150858231405/604462909807314587353088)), (2835/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886872803857271/75557863725914323419136), (-3493680101049/75557863725914323419136)), (9/147573952589676412928), by norm_num⟩
  | 10 => ⟨((648425047578339/2361183241434822606848), (-1309489617925/2361183241434822606848)), (3457/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620500365021013/590295810358705651712), (-3599016245267/590295810358705651712)), (4755/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822290107772095/73786976294838206464), (-2247826015481/36893488147419103232)), (5945/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1821324548587233/9223372036854775808), (-5053324203223/9223372036854775808)), (1673/2305843009213693952), by norm_num⟩
  | 6 => ⟨((199071667125541/144115188075855872), (-2523986865579/576460752303423488)), (837/144115188075855872), by norm_num⟩
  | 5 => ⟨((1193345123597403/144115188075855872), (-4410964523695/144115188075855872)), (733/18014398509481984), by norm_num⟩
  | 4 => ⟨((1489784584673819/36028797018963968), (-3302219380423/18014398509481984)), (2201/9007199254740992), by norm_num⟩
  | 3 => ⟨((743471396200653/4503599627370496), (-4117286256901/4503599627370496)), (5511/4503599627370496), by norm_num⟩
  | 2 => ⟨((2223321739260995/4503599627370496), (-16406369398513/4503599627370496)), (5523/1125899906842624), by norm_num⟩
  | 1 => ⟨((552293233803083/562949953421312), (-24453146580307/2251799813685248)), (33261/2251799813685248), by norm_num⟩
  | 0 => ⟨((1083453498993605/1125899906842624), (-24141921880855/1125899906842624)), (67019/2251799813685248), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((1083453498993605/1125899906842624), (-24141921880855/1125899906842624)), (255657204634856467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2084179321729679/2251799813685248), (-92927087302437/2251799813685248)), (32965/562949953421312), by norm_num⟩
  | 2 => ⟨((481300333096243/562949953421312), (-43004869395415/562949953421312)), (254973/2251799813685248), by norm_num⟩
  | 3 => ⟨((1632831412101423/2251799813685248), (-294139936795171/2251799813685248)), (474941/2251799813685248), by norm_num⟩
  | 4 => ⟨((572790729941821/1125899906842624), (-426575155956395/2251799813685248)), (203215/562949953421312), by norm_num⟩
  | 5 => ⟨((1003988463521489/4503599627370496), (-108508000342815/562949953421312)), (567521/1125899906842624), by norm_num⟩
  | 6 => ⟨((226003857430323/18014398509481984), (-387035401217773/4503599627370496)), (3774507/9007199254740992), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1311882945/536870912), (-28517055513/1073741824)), (1/536870912), by norm_num⟩, -4, term26ValuePoly, term26ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term26Value_checks : CertifiedScalarExp.Checks term26Value := by
  constructor
  · norm_num [term26Value, CertifiedScalarExp.reduced, term26ValuePoly, term26ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term26ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value, term26ValueSquares, term26ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term26Value, CertifiedScalarExp.roundingCheck, term26ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term26 : Sound J_term26 F_term26 c := by
  apply exp_sound (A_arg26 hcre) S_arg26 term26Value term26Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term26Value,J_arg26]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term26,J_arg26,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3295836866004329/1000000000000000), 0), (1/125000000000000), by norm_num⟩
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

theorem S_log27 : Sound J_log27 F_log27 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log27_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
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
theorem S_negLog27 : Sound J_negLog27 F_negLog27 c := by
  apply sound_round (sound_scale (A_log27 hcre) S_log27)
  intro k
  fin_cases k <;> norm_num [J_negLog27, J_log27, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-165884901/67108864), (-28847384285/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-28311023105/8589934592), 0), (1/8589934592), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg27 : Sound J_arg27 F_arg27 c := by
  apply sound_round (sound_mul (A_negLog27 hcre) (A_variable hcre) S_negLog27 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg27, J_negLog27, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term27 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-246332001080869/18014398509481984), (-187600712923569/2251799813685248)), (2009065/4503599627370496), by norm_num⟩
  | 1 => ⟨((1548519307/34359738368), (2358632453/8589934592)), (103/68719476736), by norm_num⟩
  | 2 => ⟨((-1275916755/17179869184), (-485854237/1073741824)), (43/17179869184), by norm_num⟩
  | 3 => ⟨((2803475653/34359738368), (17080493929/34359738368)), (3/1073741824), by norm_num⟩
  | 4 => ⟨((-4619899205/68719476736), (-28147260791/68719476736)), (5/2147483648), by norm_num⟩
  | 5 => ⟨((3045286823/68719476736), (9276877979/34359738368)), (27/17179869184), by norm_num⟩
  | 6 => ⟨((-1672794763/68719476736), (-2547923037/17179869184)), (121/137438953472), by norm_num⟩
  | 7 => ⟨((1575216757/137438953472), (19194374119/274877906944)), (29/68719476736), by norm_num⟩
  | 8 => ⟨((-1297914365/274877906944), (-3953845365/137438953472)), (97/549755813888), by norm_num⟩
  | 9 => ⟨((475301557/274877906944), (2895828737/274877906944)), (9/137438953472), by norm_num⟩
  | 10 => ⟨((-1253213115/2199023255552), (-15270686575/4398046511104)), (97/4398046511104), by norm_num⟩
  | 11 => ⟨((375489635/2199023255552), (18301706103/17592186044416)), (59/8796093022208), by norm_num⟩
  | 12 => ⟨((-1650070109/35184372088832), (-5026619807/17592186044416)), (33/17592186044416), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790377935240215/5070602400912917605986812821504), (-282256238529/1267650600228229401496703205376)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((3472955196987/1237940039285380274899124224), (-1335266329205/316912650057057350374175801344)), (1445/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889049153140997/39614081257132168796771975168), (-1501850446517/19807040628566084398385987584)), (813/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1888780892289381/2475880078570760549798248448), (-797656788985/618970019642690137449562112)), (27/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((1770447096285177/154742504910672534362390528), (-797430450265/38685626227668133590597632)), (27/1208925819614629174706176), by norm_num⟩
  | 13 => ⟨((193607032560641/1208925819614629174706176), (-2989402553579/9671406556917033397649408)), (1621/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258178616256541/604462909807314587353088), (-2614765942121/604462909807314587353088)), (2837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1886800595648309/75557863725914323419136), (-4247192960875/75557863725914323419136)), (4611/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648397893812773/2361183241434822606848), (-3183818965133/4722366482869645213696)), (865/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((101276590408257/36893488147419103232), (-546898979771/73786976294838206464)), (4759/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911098045911079/36893488147419103232), (-5465153325015/73786976294838206464)), (5951/73786976294838206464), by norm_num⟩
  | 7 => ⟨((910609137928927/4611686018427387904), (-3071513107669/4611686018427387904)), (6699/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796233217389907/576460752303423488), (-6136442929671/1152921504606846976)), (419/72057594037927936), by norm_num⟩
  | 5 => ⟨((1193250878010275/144115188075855872), (-5361989348005/144115188075855872)), (367/9007199254740992), by norm_num⟩
  | 4 => ⟨((1489641809105367/36028797018963968), (-2007051881563/9007199254740992)), (4409/18014398509481984), by norm_num⟩
  | 3 => ⟨((1486761871795913/9007199254740992), (-10009445347211/9007199254740992)), (11043/9007199254740992), by norm_num⟩
  | 2 => ⟨((2222952590216751/4503599627370496), (-9970813752439/2251799813685248)), (22145/4503599627370496), by norm_num⟩
  | 1 => ⟨((2208601101064243/2251799813685248), (-14859954348245/1125899906842624)), (33367/2251799813685248), by norm_num⟩
  | 0 => ⟨((2165691836574793/2251799813685248), (-29336715575973/1125899906842624)), (67337/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2165691836574793/2251799813685248), (-29336715575973/1125899906842624)), (256870278365325217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((520336946805817/562949953421312), (-112859562468517/2251799813685248)), (66517/1125899906842624), by norm_num⟩
  | 2 => ⟨((1918141792306919/2251799813685248), (-208633111330089/2251799813685248)), (4051/35184372088832), by norm_num⟩
  | 3 => ⟨((1614592974986063/2251799813685248), (-177719123906635/1125899906842624)), (489739/2251799813685248), by norm_num⟩
  | 4 => ⟨((275399050993583/562949953421312), (-509715023931411/2251799813685248)), (856917/2251799813685248), by norm_num⟩
  | 5 => ⟨((423530007060639/2251799813685248), (-124678075746127/562949953421312)), (613181/1125899906842624), by norm_num⟩
  | 6 => ⟨((-246332001080869/18014398509481984), (-187600712923569/2251799813685248)), (2009065/4503599627370496), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-165884901/67108864), (-28847384285/1073741824)), (1/536870912), by norm_num⟩, -4, term27ValuePoly, term27ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term27Value_checks : CertifiedScalarExp.Checks term27Value := by
  constructor
  · norm_num [term27Value, CertifiedScalarExp.reduced, term27ValuePoly, term27ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term27ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value, term27ValueSquares, term27ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term27Value, CertifiedScalarExp.roundingCheck, term27ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term27 : Sound J_term27 F_term27 c := by
  apply exp_sound (A_arg27 hcre) S_arg27 term27Value term27Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term27Value,J_arg27]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term27,J_arg27,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term22Jet : Jet 12 := J_term22
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨18,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile018Terms3

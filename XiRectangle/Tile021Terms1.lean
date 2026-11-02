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
namespace Reinmann.XiRectangle.Tile021Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨21,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6063/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (6063/640))
  have he : value ((3/4), (6063/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
  rw [he] at h
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_log9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((109861228866811/50000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log9 : Sound J_log9 F_log9 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log9_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog9 : Sound J_negLog9 F_negLog9 c := by
  apply sound_round (sound_scale (A_log9 hcre) S_log9)
  intro k
  fin_cases k <;> norm_num [J_negLog9, J_log9, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-55294967/33554432), (-87305569/4194304)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg9 : Sound J_arg9 F_arg9 c := by
  apply sound_round (sound_mul (A_negLog9 hcre) (A_variable hcre) S_negLog9 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg9, J_negLog9, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term9 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-166727105688595/2251799813685248), (-800005402908353/4503599627370496)), (18933581/4503599627370496), by norm_num⟩
  | 1 => ⟨((1397464349/8589934592), (1676360639/4294967296)), (81/8589934592), by norm_num⟩
  | 2 => ⟨((-1535271507/8589934592), (-3683340797/8589934592)), (91/8589934592), by norm_num⟩
  | 3 => ⟨((2248890859/17179869184), (5395417951/17179869184)), (17/2147483648), by norm_num⟩
  | 4 => ⟨((-1235329567/17179869184), (-370467029/2147483648)), (19/4294967296), by norm_num⟩
  | 5 => ⟨((2171437189/68719476736), (651199409/8589934592)), (17/8589934592), by norm_num⟩
  | 6 => ⟨((-1590378387/137438953472), (-3815550257/137438953472)), (51/68719476736), by norm_num⟩
  | 7 => ⟨((31200165/8589934592), (2395320229/274877906944)), (131/549755813888), by norm_num⟩
  | 8 => ⟨((-2193720619/2199023255552), (-2631528239/1099511627776)), (73/1099511627776), by norm_num⟩
  | 9 => ⟨((2142265271/8796093022208), (642450947/1099511627776)), (145/8796093022208), by norm_num⟩
  | 10 => ⟨((-941407581/17592186044416), (-2258574417/17592186044416)), (65/17592186044416), by norm_num⟩
  | 11 => ⟨((1504351909/140737488355328), (3609160159/140737488355328)), (53/70368744177664), by norm_num⟩
  | 12 => ⟨((-2203599325/1125899906842624), (-5286756937/1125899906842624)), (79/562949953421312), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (-2560561680775/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444855548078135/158456325028528675187087900672), (-94763299873/19807040628566084398385987584)), (11563/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890476597095187/39614081257132168796771975168), (-852743541615/9903520314283042199192993792)), (13011/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890297151080689/2475880078570760549798248448), (-3623549710827/2475880078570760549798248448)), (13827/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885981452330459/77371252455336267181195264), (-905715785455/38685626227668133590597632)), (6915/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((193784606544693/1208925819614629174706176), (-1697852406719/4835703278458516698824704)), (12969/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259421155762395/604462909807314587353088), (-2970512439393/604462909807314587353088)), (11351/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888818825585045/75557863725914323419136), (-603214445175/9444732965739290427392)), (4613/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1298308675619889/4722366482869645213696), (-3618090645655/4722366482869645213696)), (3461/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((811252196584081/295147905179352825856), (-1243232883449/147573952589676412928)), (4761/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824792864263137/73786976294838206464), (-1553312631705/18446744073709551616)), (11909/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1824137018535723/9223372036854775808), (-6985901487895/9223372036854775808)), (13407/4611686018427387904), by norm_num⟩
  | 6 => ⟨((797690948110279/576460752303423488), (-1745224165553/288230376151711744)), (26837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597899108832479/72057594037927936), (-1525664180075/36028797018963968)), (5877/36028797018963968), by norm_num⟩
  | 4 => ⟨((373363861524267/9007199254740992), (-9142735791203/36028797018963968)), (35313/36028797018963968), by norm_num⟩
  | 3 => ⟨((1491516029070591/9007199254740992), (-11408747960807/9007199254740992)), (44231/9007199254740992), by norm_num⟩
  | 2 => ⟨((558105572385165/1125899906842624), (-11379269281075/2251799813685248)), (22183/1125899906842624), by norm_num⟩
  | 1 => ⟨((1111354646631333/1125899906842624), (-4248827205043/281474976710656)), (8361/140737488355328), by norm_num⟩
  | 0 => ⟨((1096761942458355/1125899906842624), (-33696847946195/1125899906842624)), (135135/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1096761942458355/1125899906842624), (-33696847946195/1125899906842624)), (515499119285201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((533684776754979/562949953421312), (-65649566508683/1125899906842624)), (271365/1125899906842624), by norm_num⟩
  | 2 => ⟨((252013498553365/281474976710656), (-62236747748741/562949953421312)), (546163/1125899906842624), by norm_num⟩
  | 3 => ⟨((888781674185023/1125899906842624), (-222890158436591/1125899906842624)), (2197513/2251799813685248), by norm_num⟩
  | 4 => ⟨((1314953198131341/2251799813685248), (-351897512328915/1125899906842624)), (4339487/2251799813685248), by norm_num⟩
  | 5 => ⟨((273952966210517/1125899906842624), (-821971396283363/2251799813685248)), (7780739/2251799813685248), by norm_num⟩
  | 6 => ⟨((-166727105688595/2251799813685248), (-800005402908353/4503599627370496)), (18933581/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-87305569/4194304)), (1/134217728), by norm_num⟩, -3, term9ValuePoly, term9ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term9Value_checks : CertifiedScalarExp.Checks term9Value := by
  constructor
  · norm_num [term9Value, CertifiedScalarExp.reduced, term9ValuePoly, term9ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term9ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value, term9ValueSquares, term9ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term9Value, CertifiedScalarExp.roundingCheck, term9ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term9 : Sound J_term9 F_term9 c := by
  apply exp_sound (A_arg9 hcre) S_arg9 term9Value term9Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term9Value,J_arg9]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term9,J_arg9,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1151292546497023/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log10 : Sound J_log10 F_log10 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log10_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog10 : Sound J_negLog10 F_negLog10 c := by
  apply sound_round (sound_scale (A_log10 hcre) S_log10)
  intro k
  fin_cases k <;> norm_num [J_negLog10, J_log10, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-231785805/134217728), (-5855488893/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg10 : Sound J_arg10 F_arg10 c := by
  apply sound_round (sound_mul (A_negLog10 hcre) (A_variable hcre) S_negLog10 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg10, J_negLog10, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term10 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-788247050674767/4503599627370496), (-283215062112885/9007199254740992)), (2112109/562949953421312), by norm_num⟩
  | 1 => ⟨((1730924519/4294967296), (621916561/8589934592)), (151/17179869184), by norm_num⟩
  | 2 => ⟨((-1992800497/4294967296), (-716007901/8589934592)), (89/8589934592), by norm_num⟩
  | 3 => ⟨((6118123623/17179869184), (549556373/8589934592)), (139/17179869184), by norm_num⟩
  | 4 => ⟨((-7043750125/34359738368), (-158175039/4294967296)), (163/34359738368), by norm_num⟩
  | 5 => ⟨((3243766807/34359738368), (582738379/34359738368)), (19/8589934592), by norm_num⟩
  | 6 => ⟨((-4979366063/137438953472), (-447268235/68719476736)), (119/137438953472), by norm_num⟩
  | 7 => ⟨((3275832591/274877906944), (1176997909/549755813888)), (159/549755813888), by norm_num⟩
  | 8 => ⟨((-3771441645/1099511627776), (-169383615/274877906944)), (93/1099511627776), by norm_num⟩
  | 9 => ⟨((1929792291/2199023255552), (693369221/4398046511104)), (97/4398046511104), by norm_num⟩
  | 10 => ⟨((-3554808769/17592186044416), (-638616653/17592186044416)), (91/17592186044416), by norm_num⟩
  | 11 => ⟨((2976454429/70368744177664), (1069432135/140737488355328)), (155/140737488355328), by norm_num⟩
  | 12 => ⟨((-2284513199/281474976710656), (-820819497/562949953421312)), (121/562949953421312), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581726236476819/10141204801825835211973625643008), (-482591571521/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889647019857931/316912650057057350374175801344), (-4571597958829/633825300114114700748351602688)), (5791/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((945166043701203/19807040628566084398385987584), (-1285558607303/9903520314283042199192993792)), (13033/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945071587065255/1237940039285380274899124224), (-85354028525/38685626227668133590597632)), (3463/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((885904219084009/77371252455336267181195264), (-1365392664329/38685626227668133590597632)), (13857/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550131520177261/9671406556917033397649408), (-5119067384265/9671406556917033397649408)), (3249/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259293470594047/604462909807314587353088), (-4478028864499/604462909807314587353088)), (11377/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944305181905359/37778931862957161709568), (-7274631120683/75557863725914323419136)), (289/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1298151478291821/4722366482869645213696), (-2727039151103/2361183241434822606848)), (1735/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1622286865295729/590295810358705651712), (-1874069568057/147573952589676412928)), (9549/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824518884419995/73786976294838206464), (-9365728829591/73786976294838206464)), (23893/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911912974361195/4611686018427387904), (-10530093926815/9223372036854775808)), (26907/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1595067278938551/1152921504606846976), (-10522155376313/1152921504606846976)), (26941/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597759472198721/72057594037927936), (-9197955382961/144115188075855872)), (5903/36028797018963968), by norm_num⟩
  | 4 => ⟨((746514294642623/18014398509481984), (-13779072714465/36028797018963968)), (35495/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490968594541163/9007199254740992), (-4298146781859/2251799813685248)), (44505/9007199254740992), by norm_num⟩
  | 2 => ⟨((139455375256911/281474976710656), (-17145710465441/2251799813685248)), (22355/1125899906842624), by norm_num⟩
  | 1 => ⟨((1110450966574573/1125899906842624), (-25601389153265/1125899906842624)), (67577/1125899906842624), by norm_num⟩
  | 0 => ⟨((1094750542689909/1125899906842624), (-6341771502269/140737488355328)), (17151/140737488355328), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1094750542689909/1125899906842624), (-6341771502269/140737488355328)), (65425873339605287/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((1062176830499235/1125899906842624), (-49330550621991/562949953421312)), (279191/1125899906842624), by norm_num⟩
  | 2 => ⟨((248353694576481/281474976710656), (-186154266779853/1125899906842624)), (575711/1125899906842624), by norm_num⟩
  | 3 => ⟨((845740820235597/1125899906842624), (-328498827542151/1125899906842624)), (1206309/1125899906842624), by norm_num⟩
  | 4 => ⟨((1078898846380505/2251799813685248), (-61689513020531/140737488355328)), (5032405/2251799813685248), by norm_num⟩
  | 5 => ⟨((84283753506823/2251799813685248), (-1891656450869335/4503599627370496)), (4617019/1125899906842624), by norm_num⟩
  | 6 => ⟨((-788247050674767/4503599627370496), (-283215062112885/9007199254740992)), (2112109/562949953421312), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-231785805/134217728), (-5855488893/268435456)), (1/134217728), by norm_num⟩, -3, term10ValuePoly, term10ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term10Value_checks : CertifiedScalarExp.Checks term10Value := by
  constructor
  · norm_num [term10Value, CertifiedScalarExp.reduced, term10ValuePoly, term10ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term10ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value, term10ValueSquares, term10ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term10Value, CertifiedScalarExp.roundingCheck, term10ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term10 : Sound J_term10 F_term10 c := by
  apply exp_sound (A_arg10 hcre) S_arg10 term10Value term10Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term10Value,J_arg10]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term10,J_arg10,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((239789527279837/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log11 : Sound J_log11 F_log11 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log11_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog11 : Sound J_negLog11 F_negLog11 c := by
  apply sound_round (sound_scale (A_log11 hcre) S_log11)
  intro k
  fin_cases k <;> norm_num [J_negLog11, J_log11, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-482760083/268435456), (-3048931651/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg11 : Sound J_arg11 F_arg11 c := by
  apply sound_round (sound_mul (A_negLog11 hcre) (A_variable hcre) S_negLog11 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg11, J_negLog11, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term11 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-1116025763280879/9007199254740992), (989070172197921/9007199254740992)), (16882831/4503599627370496), by norm_num⟩
  | 1 => ⟨((2552140143/8589934592), (-2261816683/8589934592)), (79/8589934592), by norm_num⟩
  | 2 => ⟨((-382485299/1073741824), (1355899883/4294967296)), (97/8589934592), by norm_num⟩
  | 3 => ⟨((1222879587/4294967296), (-16933885/67108864)), (79/8589934592), by norm_num⟩
  | 4 => ⟨((-2932337181/17179869184), (2598763699/17179869184)), (97/17179869184), by norm_num⟩
  | 5 => ⟨((1406287493/17179869184), (-623156319/8589934592)), (95/34359738368), by norm_num⟩
  | 6 => ⟨((-4496173509/137438953472), (3984702911/137438953472)), (77/68719476736), by norm_num⟩
  | 7 => ⟨((3080386629/274877906944), (-2729971507/274877906944)), (27/68719476736), by norm_num⟩
  | 8 => ⟨((-923305567/274877906944), (1636546443/549755813888)), (33/274877906944), by norm_num⟩
  | 9 => ⟨((3935982319/4398046511104), (-3488237315/4398046511104)), (143/4398046511104), by norm_num⟩
  | 10 => ⟨((-3775229359/17592186044416), (3345771107/17592186044416)), (35/4398046511104), by norm_num⟩
  | 11 => ⟨((1645928115/35184372088832), (-1458692495/35184372088832)), (125/70368744177664), by norm_num⟩
  | 12 => ⟨((-1315587749/140737488355328), (1165930613/140737488355328)), (51/140737488355328), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581633122367159/10141204801825835211973625643008), (196729385523/633825300114114700748351602688)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444796883457259/158456325028528675187087900672), (1863401000789/316912650057057350374175801344)), (2893/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890212504247079/39614081257132168796771975168), (2095986415097/19807040628566084398385987584)), (13021/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890016416608851/2475880078570760549798248448), (4453152050341/2475880078570760549798248448)), (6919/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771682017530033/154742504910672534362390528), (4452230622207/154742504910672534362390528)), (6921/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((12109479364053/75557863725914323419136), (2086493650029/4835703278458516698824704)), (12981/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259190436792365/604462909807314587353088), (3650385101859/604462909807314587353088)), (11363/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236055450492559/9444732965739290427392), (5930040827997/75557863725914323419136)), (18471/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298026994285403/4722366482869645213696), (4445925289651/4722366482869645213696)), (13861/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622116651110801/590295810358705651712), (6110539099391/590295810358705651712)), (4767/147573952589676412928), by norm_num⟩
  | 8 => ⟨((912153771174533/36893488147419103232), (7634262471045/73786976294838206464)), (5963/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1823590147021415/9223372036854775808), (8583168495851/9223372036854775808)), (3357/1152921504606846976), by norm_num⟩
  | 6 => ⟨((797416960833915/576460752303423488), (8576449611655/1152921504606846976)), (6721/288230376151711744), by norm_num⟩
  | 5 => ⟨((298829375581917/36028797018963968), (1874209388021/36028797018963968)), (23555/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492731906161145/36028797018963968), (11230151842611/36028797018963968)), (35395/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490607305622111/9007199254740992), (3502818315419/2251799813685248)), (44355/9007199254740992), by norm_num⟩
  | 2 => ⟨((278824002666029/562949953421312), (3492920290623/562949953421312)), (44521/2251799813685248), by norm_num⟩
  | 1 => ⟨((554983024259241/562949953421312), (2607332053389/140737488355328)), (67199/1125899906842624), by norm_num⟩
  | 0 => ⟨((1093921934304623/1125899906842624), (41322544639975/1125899906842624)), (17009/140737488355328), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((1093921934304623/1125899906842624), (41322544639975/1125899906842624)), (64884186327886537/536870912000000000000000000), by norm_num⟩
  | 1 => ⟨((530667796664217/562949953421312), (20074447865315/281474976710656)), (68601/281474976710656), by norm_num⟩
  | 2 => ⟨((497373478559499/562949953421312), (151386288648857/1125899906842624)), (278239/562949953421312), by norm_num⟩
  | 3 => ⟨((858516547014637/1125899906842624), (267503441589747/1125899906842624)), (566479/562949953421312), by norm_num⟩
  | 4 => ⟨((1182152278708017/2251799813685248), (101987809747755/281474976710656)), (1133079/562949953421312), by norm_num⟩
  | 5 => ⟨((324978780098439/2251799813685248), (856666714055253/2251799813685248)), (8043181/2251799813685248), by norm_num⟩
  | 6 => ⟨((-1116025763280879/9007199254740992), (989070172197921/9007199254740992)), (16882831/4503599627370496), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-482760083/268435456), (-3048931651/134217728)), (1/134217728), by norm_num⟩, -4, term11ValuePoly, term11ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term11Value_checks : CertifiedScalarExp.Checks term11Value := by
  constructor
  · norm_num [term11Value, CertifiedScalarExp.reduced, term11ValuePoly, term11ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term11ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value, term11ValueSquares, term11ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term11Value, CertifiedScalarExp.roundingCheck, term11ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term11 : Sound J_term11 F_term11 c := by
  apply exp_sound (A_arg11 hcre) S_arg11 term11Value term11Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term11Value,J_arg11]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term11,J_arg11,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((621226662447/250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log12 : Sound J_log12 F_log12 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log12_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog12 : Sound J_negLog12 F_negLog12 c := by
  apply sound_round (sound_scale (A_log12 hcre) S_log12)
  intro k
  fin_cases k <;> norm_num [J_negLog12, J_log12, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-500277787/268435456), (-789891725/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg12 : Sound J_arg12 F_arg12 c := by
  apply sound_round (sound_mul (A_negLog12 hcre) (A_variable hcre) S_negLog12 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg12, J_negLog12, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term12 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-29806123953243/9007199254740992), (1396705900518975/9007199254740992)), (28171463/9007199254740992), by norm_num⟩
  | 1 => ⟨((141268607/17179869184), (-3309901981/8589934592)), (17/2147483648), by norm_num⟩
  | 2 => ⟨((-87759825/8589934592), (4112398721/8589934592)), (43/4294967296), by norm_num⟩
  | 3 => ⟨((145383315/17179869184), (-212894311/536870912)), (9/1073741824), by norm_num⟩
  | 4 => ⟨((-11289499/2147483648), (4232179913/17179869184)), (23/4294967296), by norm_num⟩
  | 5 => ⟨((22442681/8589934592), (-4206628803/34359738368)), (93/34359738368), by norm_num⟩
  | 6 => ⟨((-148714579/137438953472), (1742179981/34359738368)), (157/137438953472), by norm_num⟩
  | 7 => ⟨((105583385/274877906944), (-154612665/8589934592)), (57/137438953472), by norm_num⟩
  | 8 => ⟨((-32795607/274877906944), (3073584315/549755813888)), (9/68719476736), by norm_num⟩
  | 9 => ⟨((144878261/4398046511104), (-3394475601/2199023255552)), (161/4398046511104), by norm_num⟩
  | 10 => ⟨((-72001791/8796093022208), (3373981997/8796093022208)), (163/17592186044416), by norm_num⟩
  | 11 => ⟨((130121985/70368744177664), (-3048738291/35184372088832)), (149/70368744177664), by norm_num⟩
  | 12 => ⟨((-107780329/281474976710656), (631319171/35184372088832)), (63/140737488355328), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581548115842083/10141204801825835211973625643008), (2073931501653/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779091095858117/633825300114114700748351602688), (1227622273801/316912650057057350374175801344)), (2889/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1890104270889403/39614081257132168796771975168), (690423473017/9903520314283042199192993792)), (13003/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889901750439431/2475880078570760549798248448), (2933741410685/2475880078570760549798248448)), (13817/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771567724391725/154742504910672534362390528), (2933113401811/154742504910672534362390528)), (3455/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((96869162807549/604462909807314587353088), (2749126699169/9671406556917033397649408)), (12959/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314774355807807/151115727451828646838272), (2404818909135/604462909807314587353088)), (5671/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888293198736497/75557863725914323419136), (3906580536185/75557863725914323419136)), (18435/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648957419496693/2361183241434822606848), (91526307183/147573952589676412928)), (13831/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202745436331681/73786976294838206464), (2012690553909/295147905179352825856)), (1189/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1824117669765443/73786976294838206464), (2514531451983/36893488147419103232)), (11895/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823378707474257/9223372036854775808), (2827017659593/4611686018427387904)), (26779/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199328148384185/144115188075855872), (5649462516219/1152921504606846976)), (26797/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1195137897224057/144115188075855872), (617267385959/18014398509481984)), (23469/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492468560336175/36028797018963968), (7396936873113/36028797018963968)), (35245/36028797018963968), by norm_num⟩
  | 3 => ⟨((745144350597287/4503599627370496), (4614108405423/4503599627370496)), (44129/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229986424790333/4503599627370496), (18402655916287/4503599627370496)), (22119/1125899906842624), by norm_num⟩
  | 1 => ⟨((554775577341509/562949953421312), (1716864835041/140737488355328)), (133263/2251799813685248), by norm_num⟩
  | 0 => ⟨((2186496185449413/2251799813685248), (27202436671851/1125899906842624)), (67183/562949953421312), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2186496185449413/2251799813685248), (27202436671851/1125899906842624)), (256282808543968023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2121771948689361/2251799813685248), (105654194758265/2251799813685248)), (33429/140737488355328), by norm_num⟩
  | 2 => ⟨((1994295126095405/2251799813685248), (49776650956501/562949953421312)), (529075/1125899906842624), by norm_num⟩
  | 3 => ⟨((1748632176959203/2251799813685248), (352675515088315/2251799813685248)), (2061417/2251799813685248), by norm_num⟩
  | 4 => ⟨((651331093804835/1125899906842624), (547739412678795/2251799813685248)), (1923649/1125899906842624), by norm_num⟩
  | 5 => ⟨((620352796166257/2251799813685248), (633732552266681/2251799813685248)), (790373/281474976710656), by norm_num⟩
  | 6 => ⟨((-29806123953243/9007199254740992), (1396705900518975/9007199254740992)), (28171463/9007199254740992), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-500277787/268435456), (-789891725/33554432)), (1/134217728), by norm_num⟩, -4, term12ValuePoly, term12ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term12Value_checks : CertifiedScalarExp.Checks term12Value := by
  constructor
  · norm_num [term12Value, CertifiedScalarExp.reduced, term12ValuePoly, term12ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term12ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value, term12ValueSquares, term12ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term12Value, CertifiedScalarExp.roundingCheck, term12ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term12 : Sound J_term12 F_term12 c := by
  apply exp_sound (A_arg12 hcre) S_arg12 term12Value term12Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term12Value,J_arg12]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term12,J_arg12,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((80154667420673/31250000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log13 : Sound J_log13 F_log13 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log13_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog13 : Sound J_negLog13 F_negLog13 c := by
  apply sound_round (sound_scale (A_log13 hcre) S_log13)
  intro k
  fin_cases k <;> norm_num [J_negLog13, J_log13, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-516392513/268435456), (-6522682927/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg13 : Sound J_arg13 F_arg13 c := by
  apply sound_round (sound_mul (A_negLog13 hcre) (A_variable hcre) S_negLog13 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg13, J_negLog13, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term13 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((884135691253451/9007199254740992), (974255777971963/9007199254740992)), (19195621/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2162707589/8589934592), (-1191576353/4294967296)), (49/8589934592), by norm_num⟩
  | 2 => ⟨((346702215/1073741824), (3056333001/8589934592)), (65/8589934592), by norm_num⟩
  | 3 => ⟨((-1185698165/4294967296), (-1306556561/4294967296)), (29/4294967296), by norm_num⟩
  | 4 => ⟨((1520627873/8589934592), (837812853/4294967296)), (77/17179869184), by norm_num⟩
  | 5 => ⟨((-3120266789/34359738368), (-1719158031/17179869184)), (81/34359738368), by norm_num⟩
  | 6 => ⟨((333471929/8589934592), (2939702191/68719476736)), (71/68719476736), by norm_num⟩
  | 7 => ⟨((-61095615/4294967296), (-2154339213/137438953472)), (53/137438953472), by norm_num⟩
  | 8 => ⟨((2507314535/549755813888), (1381442745/274877906944)), (69/549755813888), by norm_num⟩
  | 9 => ⟨((-357285267/274877906944), (-393703409/274877906944)), (81/2199023255552), by norm_num⟩
  | 10 => ⟨((2932539571/8796093022208), (3231453779/8796093022208)), (85/8796093022208), by norm_num⟩
  | 11 => ⟨((-10684397/137438953472), (-3014005561/35184372088832)), (81/35184372088832), by norm_num⟩
  | 12 => ⟨((2338554643/140737488355328), (644230969/35184372088832)), (71/140737488355328), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917417231/10141204801825835211973625643008), (1086187675831/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779000864546923/633825300114114700748351602688), (1285766786365/633825300114114700748351602688)), (5771/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1845705968333/38685626227668133590597632), (1446243347215/39614081257132168796771975168)), (12985/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944897124836313/1237940039285380274899124224), (192041498495/309485009821345068724781056)), (6899/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((442865110294399/38685626227668133590597632), (191999103705/19342813113834066795298816)), (1725/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((193725782241715/1208925819614629174706176), (1439633021499/9671406556917033397649408)), (6469/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314752462626185/151115727451828646838272), (157414843673/75557863725914323419136)), (11323/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((118009457854639/4722366482869645213696), (1022858967287/37778931862957161709568)), (9201/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((81113050777663/295147905179352825856), (383424508609/1180591620717411303424)), (3451/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621818318242855/590295810358705651712), (2107875815729/590295810358705651712)), (2373/73786976294838206464), by norm_num⟩
  | 8 => ⟨((455984281107593/18446744073709551616), (2633407075915/73786976294838206464)), (11867/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823176857647281/9223372036854775808), (2960607396141/9223372036854775808)), (26709/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594424914487391/1152921504606846976), (1479069918251/576460752303423488)), (26719/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194964429875603/144115188075855872), (2585598956863/144115188075855872)), (11695/72057594037927936), by norm_num⟩
  | 4 => ⟨((1492211893573759/36028797018963968), (242053633767/2251799813685248)), (17553/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489974034571963/9007199254740992), (2415695889329/4503599627370496)), (43921/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229375519681193/4503599627370496), (4816899630553/2251799813685248)), (21989/1125899906842624), by norm_num⟩
  | 1 => ⟨((2218231769451407/2251799813685248), (7189221074687/1125899906842624)), (1033/17592186044416), by norm_num⟩
  | 0 => ⟨((273117108284513/281474976710656), (889658696331/70368744177664)), (33201/281474976710656), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((273117108284513/281474976710656), (889658696331/70368744177664)), (126651764989757449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((2119699358790941/2251799813685248), (55247485420771/2251799813685248)), (32635/140737488355328), by norm_num⟩
  | 2 => ⟨((124624563086301/140737488355328), (13001606393861/281474976710656)), (1008679/2251799813685248), by norm_num⟩
  | 3 => ⟨((440224462245345/562949953421312), (11513062618853/140737488355328)), (1879577/2251799813685248), by norm_num⟩
  | 4 => ⟨((1361945346796411/2251799813685248), (288101307443273/2251799813685248)), (1623581/1125899906842624), by norm_num⟩
  | 5 => ⟨((786878457641415/2251799813685248), (348501880756593/2251799813685248)), (2379417/1125899906842624), by norm_num⟩
  | 6 => ⟨((884135691253451/9007199254740992), (974255777971963/9007199254740992)), (19195621/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-516392513/268435456), (-6522682927/268435456)), (1/134217728), by norm_num⟩, -4, term13ValuePoly, term13ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term13Value_checks : CertifiedScalarExp.Checks term13Value := by
  constructor
  · norm_num [term13Value, CertifiedScalarExp.reduced, term13ValuePoly, term13ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term13ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value, term13ValueSquares, term13ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term13Value, CertifiedScalarExp.roundingCheck, term13ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term13 : Sound J_term13 F_term13 c := by
  apply exp_sound (A_arg13 hcre) S_arg13 term13Value term13Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term13Value,J_arg13]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term13,J_arg13,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1319528664807629/500000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log14 : Sound J_log14 F_log14 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log14_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog14 : Sound J_negLog14 F_negLog14 c := by
  apply sound_round (sound_scale (A_log14 hcre) S_log14)
  intro k
  fin_cases k <;> norm_num [J_negLog14, J_log14, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-265656209/134217728), (-6711139983/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg14 : Sound J_arg14 F_arg14 c := by
  apply sound_round (sound_mul (A_negLog14 hcre) (A_variable hcre) S_negLog14 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg14, J_negLog14, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term14 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((616851830141781/4503599627370496), (163545944111361/9007199254740992)), (5425883/4503599627370496), by norm_num⟩
  | 1 => ⟨((-1552493423/4294967296), (-823225255/17179869184)), (7/2147483648), by norm_num⟩
  | 2 => ⟨((4097119147/8589934592), (543134661/8589934592)), (39/8589934592), by norm_num⟩
  | 3 => ⟨((-1802088719/4294967296), (-119446959/2147483648)), (71/17179869184), by norm_num⟩
  | 4 => ⟨((2377907721/8589934592), (630454745/17179869184)), (49/17179869184), by norm_num⟩
  | 5 => ⟨((-78442935/536870912), (-332761243/17179869184)), (27/17179869184), by norm_num⟩
  | 6 => ⟨((1104082147/17179869184), (585450665/68719476736)), (49/68719476736), by norm_num⟩
  | 7 => ⟨((-1664992047/68719476736), (-441439391/137438953472)), (19/68719476736), by norm_num⟩
  | 8 => ⟨((4394009465/549755813888), (291245965/274877906944)), (13/137438953472), by norm_num⟩
  | 9 => ⟨((-5153796837/2199023255552), (-341606577/1099511627776)), (63/2199023255552), by norm_num⟩
  | 10 => ⟨((5440466127/8796093022208), (721215473/8796093022208)), (69/8796093022208), by norm_num⟩
  | 11 => ⟨((-1305245637/8796093022208), (-692119629/35184372088832)), (17/8796093022208), by norm_num⟩
  | 12 => ⟨((4592824087/140737488355328), (608847793/140737488355328)), (31/70368744177664), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197674689623573/1267650600228229401496703205376), (171679732515/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778916027391577/633825300114114700748351602688), (203206001713/633825300114114700748351602688)), (11529/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889907535274651/39614081257132168796771975168), (228567193289/39614081257132168796771975168)), (6485/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((59052906129899/77371252455336267181195264), (242803620559/2475880078570760549798248448)), (3445/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((442839820468855/38685626227668133590597632), (1896472579/1208925819614629174706176)), (13781/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549711521138099/9671406556917033397649408), (227518151079/9671406556917033397649408)), (1615/1208925819614629174706176), by norm_num⟩
  | 12 => ⟨((1258927055800359/604462909807314587353088), (199019843711/604462909807314587353088)), (11305/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888016971640217/75557863725914323419136), (40412191085/9444732965739290427392)), (9185/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297708210733727/4722366482869645213696), (60594296529/1180591620717411303424)), (6889/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621680256862981/590295810358705651712), (83278193629/147573952589676412928)), (9473/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823764946254303/73786976294838206464), (416157322157/73786976294838206464)), (23683/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911491852272325/4611686018427387904), (467855949269/9223372036854775808)), (6661/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797116222289475/576460752303423488), (467454988919/1152921504606846976)), (13323/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194796785942927/144115188075855872), (204286249165/72057594037927936)), (23317/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491961958763675/36028797018963968), (611958670799/36028797018963968)), (34979/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489664287861783/9007199254740992), (763375804533/9007199254740992)), (43729/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228764011325879/4503599627370496), (1522044390397/4503599627370496)), (87477/4503599627370496), by norm_num⟩
  | 1 => ⟨((2217334363700293/2251799813685248), (567833700079/562949953421312)), (2051/35184372088832), by norm_num⟩
  | 0 => ⟨((545805212286637/562949953421312), (4495959389981/2251799813685248)), (262727/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((545805212286637/562949953421312), (4495959389981/2251799813685248)), (1002223977095793967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2116721492527657/2251799813685248), (8718068291389/2251799813685248)), (510501/2251799813685248), by norm_num⟩
  | 2 => ⟨((1989712338096873/2251799813685248), (16390198110467/2251799813685248)), (963709/2251799813685248), by norm_num⟩
  | 3 => ⟨((1758009981936237/2251799813685248), (14482539347437/1125899906842624)), (1717115/2251799813685248), by norm_num⟩
  | 4 => ⟨((686064565336963/1125899906842624), (45226842247421/2251799813685248)), (681331/562949953421312), by norm_num⟩
  | 5 => ⟨((208798854204807/562949953421312), (110235496706111/4503599627370496)), (6861631/4503599627370496), by norm_num⟩
  | 6 => ⟨((616851830141781/4503599627370496), (163545944111361/9007199254740992)), (5425883/4503599627370496), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-265656209/134217728), (-6711139983/268435456)), (1/134217728), by norm_num⟩, -4, term14ValuePoly, term14ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term14Value_checks : CertifiedScalarExp.Checks term14Value := by
  constructor
  · norm_num [term14Value, CertifiedScalarExp.reduced, term14ValuePoly, term14ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term14ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value, term14ValueSquares, term14ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term14Value, CertifiedScalarExp.roundingCheck, term14ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term14 : Sound J_term14 F_term14 c := by
  apply exp_sound (A_arg14 hcre) S_arg14 term14Value term14Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term14Value,J_arg14]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term14,J_arg14,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_log15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((270805020110221/100000000000000), 0), (3/500000000000000), by norm_num⟩
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

theorem S_log15 : Sound J_log15 F_log15 c := by
  have h := constant_sound (d:=12) (c:=c) RectangleLogInputs.log15_contains
  convert h using 1
  all_goals first | (funext k; fin_cases k <;> rfl) | rfl

def J_negLog15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
theorem S_negLog15 : Sound J_negLog15 F_negLog15 c := by
  apply sound_round (sound_scale (A_log15 hcre) S_log15)
  intro k
  fin_cases k <;> norm_num [J_negLog15, J_log15, jetScale, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_arg15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((-272601259/134217728), (-6886589305/268435456)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
theorem S_arg15 : Sound J_arg15 F_arg15 c := by
  apply sound_round (sound_mul (A_negLog15 hcre) (A_variable hcre) S_negLog15 S_variable)
  intro k
  fin_cases k <;> norm_num [J_arg15, J_negLog15, J_variable, jetMul, sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def J_term15 : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((1024474782482831/9007199254740992), (-36814405927345/562949953421312)), (883853/562949953421312), by norm_num⟩
  | 1 => ⟨((-2645806447/8589934592), (3042457867/17179869184)), (19/4294967296), by norm_num⟩
  | 2 => ⟨((3582488341/8589934592), (-128736385/536870912)), (27/4294967296), by norm_num⟩
  | 3 => ⟨((-1616926379/4294967296), (464832791/2147483648)), (51/8589934592), by norm_num⟩
  | 4 => ⟨((2189358903/8589934592), (-1258790533/8589934592)), (71/17179869184), by norm_num⟩
  | 5 => ⟨((-2371557527/17179869184), (2727094365/34359738368)), (79/34359738368), by norm_num⟩
  | 6 => ⟨((4281531225/68719476736), (-2461702815/68719476736)), (37/34359738368), by norm_num⟩
  | 7 => ⟨((-828185821/34359738368), (238086243/17179869184)), (59/137438953472), by norm_num⟩
  | 8 => ⟨((2242768779/274877906944), (-2578997993/549755813888)), (41/274877906944), by norm_num⟩
  | 9 => ⟨((-5398693727/2199023255552), (388003113/274877906944)), (101/2199023255552), by norm_num⟩
  | 10 => ⟨((2923986727/4398046511104), (-1681171053/4398046511104)), (7/549755813888), by norm_num⟩
  | 11 => ⟨((-719845713/4398046511104), (413881419/4398046511104)), (57/17592186044416), by norm_num⟩
  | 12 => ⟨((81224097/2199023255552), (-2988831093/140737488355328)), (105/140737488355328), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798419/10141204801825835211973625643008), (-339853397831/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444708981453247/158456325028528675187087900672), (-25139234721/19807040628566084398385987584)), (721/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((1889817418388015/39614081257132168796771975168), (-226212944023/9903520314283042199192993792)), (6489/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889597242629161/2475880078570760549798248448), (-120150732037/309485009821345068724781056)), (6895/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771263523484591/154742504910672534362390528), (-960981885933/154742504910672534362390528)), (13791/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774810871245057/4835703278458516698824704), (-450341310917/4835703278458516698824704)), (6465/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258848494338717/604462909807314587353088), (-787859479211/604462909807314587353088)), (11315/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((117993081227759/4722366482869645213696), (-319956480889/18889465931478580854784)), (18387/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648806224171841/2361183241434822606848), (-959479601465/4722366482869645213696)), (431/147573952589676412928), by norm_num⟩
  | 9 => ⟨((101346785624091/36893488147419103232), (-164831410461/73786976294838206464)), (9483/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823600317353427/73786976294838206464), (-823682459071/36893488147419103232)), (23711/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822798469247669/9223372036854775808), (-1851981320689/9223372036854775808)), (3335/1152921504606846976), by norm_num⟩
  | 6 => ⟨((1594047174753995/1152921504606846976), (-115647027069/72057594037927936)), (13343/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194634636278553/144115188075855872), (-808613886509/72057594037927936)), (23357/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491718657821663/36028797018963968), (-2422185173887/36028797018963968)), (35049/36028797018963968), by norm_num⟩
  | 3 => ⟨((93085001840775/562949953421312), (-3021343237261/9007199254740992)), (10959/2251799813685248), by norm_num⟩
  | 2 => ⟨((2228155103982285/4503599627370496), (-3011782095943/2251799813685248)), (87743/4503599627370496), by norm_num⟩
  | 1 => ⟨((554105011970293/562949953421312), (-1123461085891/281474976710656)), (131797/2251799813685248), by norm_num⟩
  | 0 => ⟨((2181388526630713/2251799813685248), (-4446408261185/562949953421312)), (132165/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((2181388526630713/2251799813685248), (-4446408261185/562949953421312)), (504169468406295421/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1056519222191923/1125899906842624), (-34458991982209/2251799813685248)), (258153/1125899906842624), by norm_num⟩
  | 2 => ⟨((247787570757145/281474976710656), (-16167772634717/562949953421312)), (984783/2251799813685248), by norm_num⟩
  | 3 => ⟨((871599056093475/1125899906842624), (-113862287938399/2251799813685248)), (1790411/2251799813685248), by norm_num⟩
  | 4 => ⟨((1343714045684043/2251799813685248), (-88144836045025/1125899906842624)), (1476553/1125899906842624), by norm_num⟩
  | 5 => ⟨((1576063180482167/4503599627370496), (-420788574644665/4503599627370496)), (7973591/4503599627370496), by norm_num⟩
  | 6 => ⟨((1024474782482831/9007199254740992), (-36814405927345/562949953421312)), (883853/562949953421312), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-272601259/134217728), (-6886589305/268435456)), (1/134217728), by norm_num⟩, -4, term15ValuePoly, term15ValueSquares⟩

set_option maxHeartbeats 5000000 in
-- A bounded Horner table and six outward-rounded squarings.
theorem term15Value_checks : CertifiedScalarExp.Checks term15Value := by
  constructor
  · norm_num [term15Value, CertifiedScalarExp.reduced, term15ValuePoly, term15ValueSquares,
      CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul, CertifiedTaylorModel.add,
      exact, qmul, qadd, size]
  · rfl
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, CertifiedScalarExp.reduced,
        term15ValuePoly, CertifiedScalarExp.piDisk, CertifiedTaylorModel.mul,
        CertifiedTaylorModel.add, exact, qmul, qadd, size]
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value, term15ValueSquares, term15ValuePoly, inflate]
  · intro k hk
    interval_cases k <;>
      norm_num [term15Value, CertifiedScalarExp.roundingCheck, term15ValueSquares,
        CertifiedTaylorModel.mul, exact, qmul, qadd, size]

set_option maxHeartbeats 5000000 in
theorem S_term15 : Sound J_term15 F_term15 c := by
  apply exp_sound (A_arg15 hcre) S_arg15 term15Value term15Value_checks
  · apply CertifiedScalarExp.disk_ext <;> norm_num [term15Value,J_arg15]
  · rfl
  · intro n hn
    have hlt : n < 12 := by omega
    interval_cases n <;> norm_num [J_term15,J_arg15,sum, CertifiedTaylorModel.get, CertifiedTaylorModel.mul, CertifiedTaylorModel.add, exact, zero, qmul, qadd, size]

def term9Jet : Jet 12 := J_term9
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨21,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile021Terms1

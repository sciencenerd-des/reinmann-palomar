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
namespace Reinmann.XiRectangle.Tile030Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨30,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((7/8), (1551/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((7/8), (1551/128))
  have he : value ((7/8), (1551/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-516086359/268435456), (-7146874485/268435456)), (3/268435456), by norm_num⟩
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
  | 0 => ⟨((6525713705731/562949953421312), (-1312981782704507/9007199254740992)), (38662497/9007199254740992), by norm_num⟩
  | 1 => ⟨((-437575029/17179869184), (10747149/33554432)), (41/4294967296), by norm_num⟩
  | 2 => ⟨((60090663/2147483648), (-1511289595/4294967296)), (183/17179869184), by norm_num⟩
  | 3 => ⟨((-352087151/17179869184), (2213761761/8589934592)), (17/2147483648), by norm_num⟩
  | 4 => ⟨((386807271/34359738368), (-2432065875/17179869184)), (151/34359738368), by norm_num⟩
  | 5 => ⟨((-339960977/68719476736), (1068758983/17179869184)), (135/68719476736), by norm_num⟩
  | 6 => ⟨((497980409/274877906944), (-6262142679/274877906944)), (25/34359738368), by norm_num⟩
  | 7 => ⟨((-625242739/1099511627776), (3931238229/549755813888)), (127/549755813888), by norm_num⟩
  | 8 => ⟨((171724839/1099511627776), (-1079726657/549755813888)), (141/2199023255552), by norm_num⟩
  | 9 => ⟨((-167696905/4398046511104), (4217603463/8796093022208)), (35/2199023255552), by norm_num⟩
  | 10 => ⟨((294774209/35184372088832), (-7413617589/70368744177664)), (249/70368744177664), by norm_num⟩
  | 11 => ⟨((-58880467/35184372088832), (2961705959/140737488355328)), (201/281474976710656), by norm_num⟩
  | 12 => ⟨((344996291/1125899906842624), (-542294427/140737488355328)), (149/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581471403062135/10141204801825835211973625643008), (-30355755681/158456325028528675187087900672)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779000678050255/633825300114114700748351602688), (-2299742292891/633825300114114700748351602688)), (17331/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890002590814207/39614081257132168796771975168), (-1293385278545/19807040628566084398385987584)), (4875/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889793765423251/2475880078570760549798248448), (-2747904313311/2475880078570760549798248448)), (20721/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((110716237229621/9671406556917033397649408), (-171706101985/9671406556917033397649408)), (20725/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774902740771111/4835703278458516698824704), (-80467096329/302231454903657293676544)), (19433/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259009000043851/604462909807314587353088), (-1126217210405/302231454903657293676544)), (17009/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888149623069457/75557863725914323419136), (-1829499139267/37778931862957161709568)), (27645/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648903627599921/2361183241434822606848), (-2743192373421/4722366482869645213696)), (5185/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621815722015513/590295810358705651712), (-471271706069/73786976294838206464)), (1783/36893488147419103232), by norm_num⟩
  | 8 => ⟨((1823933197407745/73786976294838206464), (-2355072226719/36893488147419103232)), (17837/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1823171503638059/9223372036854775808), (-2647688554209/4611686018427387904)), (20077/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594418392262683/1152921504606846976), (-2645480377539/576460752303423488)), (40181/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597478705662037/72057594037927936), (-4624626247193/144115188075855872)), (35187/144115188075855872), by norm_num⟩
  | 4 => ⟨((746099374560513/18014398509481984), (-6927020498335/36028797018963968)), (52839/36028797018963968), by norm_num⟩
  | 3 => ⟨((744976519850283/4503599627370496), (-2160359994701/2251799813685248)), (66151/9007199254740992), by norm_num⟩
  | 2 => ⟨((2229319896049149/4503599627370496), (-2153870310087/562949953421312)), (66305/2251799813685248), by norm_num⟩
  | 1 => ⟨((2218114455296057/2251799813685248), (-6429240695955/562949953421312)), (199687/2251799813685248), by norm_num⟩
  | 0 => ⟨((2184567954605543/2251799813685248), (-25458937817891/1125899906842624)), (402477/2251799813685248), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2184567954605543/2251799813685248), (-25458937817891/1125899906842624)), (1535327919966887717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1059096037143755/1125899906842624), (-98795247032619/2251799813685248)), (799123/2251799813685248), by norm_num⟩
  | 2 => ⟨((1988177250717177/2251799813685248), (-185866708017253/2251799813685248)), (786769/1125899906842624), by norm_num⟩
  | 3 => ⟨((870037896643115/1125899906842624), (-164106932729877/1125899906842624)), (3038407/2251799813685248), by norm_num⟩
  | 4 => ⟨((648401204928077/1125899906842624), (-253626898286639/1125899906842624)), (2790793/1125899906842624), by norm_num⟩
  | 5 => ⟨((316278131700259/1125899906842624), (-584250821771191/2251799813685248)), (8943509/2251799813685248), by norm_num⟩
  | 6 => ⟨((6525713705731/562949953421312), (-1312981782704507/9007199254740992)), (38662497/9007199254740992), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-516086359/268435456), (-7146874485/268435456)), (3/268435456), by norm_num⟩, -4, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-67604193/33554432), (-117024669/4194304)), (3/268435456), by norm_num⟩
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
  | 0 => ⟨((-1118328034821679/9007199254740992), (-438239737084953/9007199254740992)), (2484589/562949953421312), by norm_num⟩
  | 1 => ⟨((4911509441/17179869184), (1924675533/17179869184)), (177/17179869184), by norm_num⟩
  | 2 => ⟨((-5654584211/17179869184), (-2215864595/17179869184)), (103/8589934592), by norm_num⟩
  | 3 => ⟨((2170026885/8589934592), (106296183/1073741824)), (5/536870912), by norm_num⟩
  | 4 => ⟨((-1249167889/8589934592), (-1958048051/34359738368)), (187/34359738368), by norm_num⟩
  | 5 => ⟨((4602104575/68719476736), (1803428901/68719476736)), (175/68719476736), by norm_num⟩
  | 6 => ⟨((-3532245797/137438953472), (-692091417/68719476736)), (137/137438953472), by norm_num⟩
  | 7 => ⟨((4647598009/549755813888), (910628217/274877906944)), (183/549755813888), by norm_num⟩
  | 8 => ⟨((-5350744947/2199023255552), (-1048399479/1099511627776)), (107/1099511627776), by norm_num⟩
  | 9 => ⟨((2737899011/4398046511104), (1072901783/4398046511104)), (111/4398046511104), by norm_num⟩
  | 10 => ⟨((-5043396359/35184372088832), (-1976358121/35184372088832)), (207/35184372088832), by norm_num⟩
  | 11 => ⟨((4222854281/140737488355328), (413702977/35184372088832)), (175/140737488355328), by norm_num⟩
  | 12 => ⟨((-3241160439/562949953421312), (-1270115077/562949953421312)), (17/70368744177664), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581351314710245/10141204801825835211973625643008), (-3605777643047/10141204801825835211973625643008)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778851617222567/633825300114114700748351602688), (-4267671920627/633825300114114700748351602688)), (17367/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889834534153435/39614081257132168796771975168), (-4800259623375/39614081257132168796771975168)), (19543/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944807365503401/1237940039285380274899124224), (-159350774879/77371252455336267181195264)), (10385/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771280228172577/154742504910672534362390528), (-2549021195017/77371252455336267181195264)), (20777/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387409142744579/2417851639229258349412352), (-4778158580973/9671406556917033397649408)), (19485/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258860637686565/604462909807314587353088), (-2089816381705/302231454903657293676544)), (17057/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943953737299869/37778931862957161709568), (-848693575055/9444732965739290427392)), (13865/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297624717549805/4722366482869645213696), (-2545050745515/2361183241434822606848)), (20809/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621563229174227/590295810358705651712), (-3497771387413/295147905179352825856)), (28631/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823615328903141/73786976294838206464), (-8739409459519/73786976294838206464)), (4477/9223372036854775808), by norm_num⟩
  | 7 => ⟨((455702702291565/2305843009213693952), (-9824936382779/9223372036854775808)), (10083/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1594053839358491/1152921504606846976), (-4908157565655/576460752303423488)), (10095/288230376151711744), by norm_num⟩
  | 5 => ⟨((298658524128195/36028797018963968), (-8579580721345/144115188075855872)), (35387/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491705139128439/36028797018963968), (-6424995396727/18014398509481984)), (53189/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489320965625775/9007199254740992), (-2003574373755/1125899906842624)), (33339/4503599627370496), by norm_num⟩
  | 2 => ⟨((557002695220081/1125899906842624), (-7988899457849/1125899906842624)), (16741/562949953421312), by norm_num⟩
  | 1 => ⟨((1108019562718643/1125899906842624), (-23839863582183/1125899906842624)), (25291/281474976710656), by norm_num⟩
  | 0 => ⟨((544993804032527/562949953421312), (-47173326496627/1125899906842624)), (102605/562949953421312), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((544993804032527/562949953421312), (-47173326496627/1125899906842624)), (391407015086936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((526622151665377/562949953421312), (-45668661130565/562949953421312)), (207263/562949953421312), by norm_num⟩
  | 2 => ⟨((488933807245951/562949953421312), (-85443220812405/562949953421312)), (842809/1125899906842624), by norm_num⟩
  | 3 => ⟨((823361730387345/1125899906842624), (-593673792865923/2251799813685248)), (859917/562949953421312), by norm_num⟩
  | 4 => ⟨((1047717283566545/2251799813685248), (-3391788803845/8796093022208)), (3422251/1125899906842624), by norm_num⟩
  | 5 => ⟨((305329276946101/4503599627370496), (-1616006444235565/4503599627370496)), (23295447/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1118328034821679/9007199254740992), (-438239737084953/9007199254740992)), (2484589/562949953421312), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-67604193/33554432), (-117024669/4194304)), (3/268435456), by norm_num⟩, -4, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-563220097/268435456), (-7799592595/268435456)), (1/134217728), by norm_num⟩
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
  | 0 => ⟨((-784476862379983/9007199254740992), (97281089034415/1125899906842624)), (6284839/2251799813685248), by norm_num⟩
  | 1 => ⟨((224243803/1073741824), (-1779707821/8589934592)), (117/17179869184), by norm_num⟩
  | 2 => ⟨((-4301705241/17179869184), (4267552971/17179869184)), (143/17179869184), by norm_num⟩
  | 3 => ⟨((3438346221/17179869184), (-3411048365/17179869184)), (117/17179869184), by norm_num⟩
  | 4 => ⟨((-4122397075/34359738368), (4089668375/34359738368)), (143/34359738368), by norm_num⟩
  | 5 => ⟨((494253823/8589934592), (-1961319293/34359738368)), (35/17179869184), by norm_num⟩
  | 6 => ⟨((-3160450415/137438953472), (3135358841/137438953472)), (57/68719476736), by norm_num⟩
  | 7 => ⟨((541316365/68719476736), (-1074037449/137438953472)), (5/17179869184), by norm_num⟩
  | 8 => ⟨((-2596039905/1099511627776), (1287714661/549755813888)), (49/549755813888), by norm_num⟩
  | 9 => ⟨((2766680807/4398046511104), (-2744715465/4398046511104)), (53/2199023255552), by norm_num⟩
  | 10 => ⟨((-2653684331/17592186044416), (82269253/549755813888)), (13/2199023255552), by norm_num⟩
  | 11 => ⟨((2313911677/70368744177664), (-2295540979/70368744177664)), (93/70368744177664), by norm_num⟩
  | 12 => ⟨((-3699011915/562949953421312), (3669644575/562949953421312)), (151/562949953421312), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581242681576647/10141204801825835211973625643008), (768599461989/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((444681428226729/158456325028528675187087900672), (1819124333985/316912650057057350374175801344)), (5785/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944846535051321/19807040628566084398385987584), (4092264717537/39614081257132168796771975168)), (3255/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472366163363525/618970019642690137449562112), (4347099023713/2475880078570760549798248448)), (13837/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885565203492641/77371252455336267181195264), (4346050403483/154742504910672534362390528)), (865/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1549496385861885/9671406556917033397649408), (63645442233/151115727451828646838272)), (12979/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258738247797255/604462909807314587353088), (3563031049141/604462909807314587353088)), (11361/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943854550427897/37778931862957161709568), (1446959433955/18889465931478580854784)), (18469/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297476383001827/4722366482869645213696), (4339052046109/4722366482869645213696)), (13859/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405339998224313/147573952589676412928), (5963229832515/590295810358705651712)), (9533/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823362368038401/73786976294838206464), (7449588830521/73786976294838206464)), (2981/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1822527717555109/9223372036854775808), (2093668365333/2305843009213693952)), (13425/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796886303374967/576460752303423488), (8367034986025/1152921504606846976)), (13439/576460752303423488), by norm_num⟩
  | 5 => ⟨((597195052824021/72057594037927936), (7312567817953/144115188075855872)), (23549/144115188075855872), by norm_num⟩
  | 4 => ⟨((372835829724099/9007199254740992), (2737922467263/9007199254740992)), (17693/18014398509481984), by norm_num⟩
  | 3 => ⟨((186109495013111/1125899906842624), (3414902500163/2251799813685248)), (11085/2251799813685248), by norm_num⟩
  | 2 => ⟨((278392811979563/562949953421312), (1701833546995/281474976710656)), (44503/2251799813685248), by norm_num⟩
  | 1 => ⟨((17303052512473/17592186044416), (2538733161269/140737488355328)), (33581/562949953421312), by norm_num⟩
  | 0 => ⟨((272211594782083/281474976710656), (20086241945583/562949953421312)), (67981/562949953421312), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((272211594782083/281474976710656), (20086241945583/562949953421312)), (259326936961936773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((525789460361145/562949953421312), (9712600418485/140737488355328)), (136339/562949953421312), by norm_num⟩
  | 2 => ⟨((1953603166645035/2251799813685248), (290287001276889/2251799813685248)), (1093987/2251799813685248), by norm_num⟩
  | 3 => ⟨((828736810202275/1125899906842624), (503690959990185/2251799813685248)), (1090145/1125899906842624), by norm_num⟩
  | 4 => ⟨((1107342759337163/2251799813685248), (741499731855533/2251799813685248)), (4185067/2251799813685248), by norm_num⟩
  | 5 => ⟨((600751567882631/4503599627370496), (364639145154243/1125899906842624)), (13744615/4503599627370496), by norm_num⟩
  | 6 => ⟨((-784476862379983/9007199254740992), (97281089034415/1125899906842624)), (6284839/2251799813685248), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-563220097/268435456), (-7799592595/268435456)), (1/134217728), by norm_num⟩, -5, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-291828709/134217728), (-1010326625/33554432)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((134074555636833/4503599627370496), (988282403647895/9007199254740992)), (9411929/2251799813685248), by norm_num⟩
  | 1 => ⟨((-635457525/8589934592), (-4684046777/17179869184)), (45/4294967296), by norm_num⟩
  | 2 => ⟨((1579052629/17179869184), (1454927373/4294967296)), (113/8589934592), by norm_num⟩
  | 3 => ⟨((-1307932793/17179869184), (-75319973/268435456)), (189/17179869184), by norm_num⟩
  | 4 => ⟨((1625045447/34359738368), (748652407/4294967296)), (237/34359738368), by norm_num⟩
  | 5 => ⟨((-1615234495/68719476736), (-2976530151/34359738368)), (119/34359738368), by norm_num⟩
  | 6 => ⟨((167237789/17179869184), (4930933043/137438953472)), (25/17179869184), by norm_num⟩
  | 7 => ⟨((-474937479/137438953472), (-3500830945/274877906944)), (9/17179869184), by norm_num⟩
  | 8 => ⟨((295043825/274877906944), (4349619047/1099511627776)), (181/1099511627776), by norm_num⟩
  | 9 => ⟨((-1303389089/4398046511104), (-2401866065/2199023255552)), (101/2199023255552), by norm_num⟩
  | 10 => ⟨((647760043/8796093022208), (4774730365/17592186044416)), (203/17592186044416), by norm_num⟩
  | 11 => ⟨((-585317541/35184372088832), (-4314457903/70368744177664)), (93/35184372088832), by norm_num⟩
  | 12 => ⟨((969639633/281474976710656), (893418761/70368744177664)), (39/70368744177664), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581143507299009/10141204801825835211973625643008), (1701011178407/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444653318526493/158456325028528675187087900672), (2012727146941/633825300114114700748351602688)), (5775/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889566878582581/39614081257132168796771975168), (2263886804597/39614081257132168796771975168)), (25991/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((236166370851055/309485009821345068724781056), (2404846089771/2475880078570760549798248448)), (27619/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442749290209583/38685626227668133590597632), (601061485467/38685626227668133590597632)), (27623/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774685967671611/4835703278458516698824704), (2253343100117/9671406556917033397649408)), (25901/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258629821016099/604462909807314587353088), (1971037952319/604462909807314587353088)), (5667/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887533783071203/75557863725914323419136), (3201742255801/75557863725914323419136)), (9211/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297345660248945/4722366482869645213696), (2400262023377/4722366482869645213696)), (3455/590295810358705651712), by norm_num⟩
  | 9 => ⟨((405295372977465/147573952589676412928), (3298663532069/590295810358705651712)), (297/4611686018427387904), by norm_num⟩
  | 8 => ⟨((455785275941155/18446744073709551616), (4120785752625/73786976294838206464)), (23769/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822281351811569/9223372036854775808), (2316194405667/4611686018427387904)), (209/36028797018963968), by norm_num⟩
  | 6 => ⟨((24898897363595/18014398509481984), (2314011710943/576460752303423488)), (53535/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194180908675107/144115188075855872), (4044614323745/144115188075855872)), (46877/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491036667917763/36028797018963968), (6057121365611/36028797018963968)), (4399/2251799813685248), by norm_num⟩
  | 3 => ⟨((372126276824005/2251799813685248), (7554278963565/9007199254740992)), (22025/2251799813685248), by norm_num⟩
  | 2 => ⟨((1113219002789773/2251799813685248), (15057299411923/4503599627370496)), (11035/281474976710656), by norm_num⟩
  | 1 => ⟨((2213826440236909/2251799813685248), (22458186153465/2251799813685248)), (132873/1125899906842624), by norm_num⟩
  | 0 => ⟨((2176130517076225/2251799813685248), (44407614961929/2251799813685248)), (535127/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2176130517076225/2251799813685248), (44407614961929/2251799813685248)), (2041347512252043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1051064122644403/1125899906842624), (42915345103911/1125899906842624)), (1055397/2251799813685248), by norm_num⟩
  | 2 => ⟨((1959133412059197/2251799813685248), (40062868178147/562949953421312)), (256369/281474976710656), by norm_num⟩
  | 3 => ⟨((846550205877463/1125899906842624), (278847180477481/2251799813685248)), (3860697/2251799813685248), by norm_num⟩
  | 4 => ⟨((1238490756272119/2251799813685248), (52415436000777/281474976710656)), (6761785/2251799813685248), by norm_num⟩
  | 5 => ⟨((603085211005177/2251799813685248), (230628078316411/1125899906842624)), (19912577/4503599627370496), by norm_num⟩
  | 6 => ⟨((134074555636833/4503599627370496), (988282403647895/9007199254740992)), (9411929/2251799813685248), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-291828709/134217728), (-1010326625/33554432)), (1/67108864), by norm_num⟩, -5, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-150614483/67108864), (-4171483267/134217728)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((901375115433823/9007199254740992), (9836012593255/281474976710656)), (19922791/9007199254740992), by norm_num⟩
  | 1 => ⟨((-4409754797/17179869184), (-769924139/8589934592)), (25/4294967296), by norm_num⟩
  | 2 => ⟨((2827699433/8589934592), (987408213/8589934592)), (131/17179869184), by norm_num⟩
  | 3 => ⟨((-2417635281/8589934592), (-422108677/4294967296)), (57/8589934592), by norm_num⟩
  | 4 => ⟨((1550278015/8589934592), (270671845/4294967296)), (149/34359738368), by norm_num⟩
  | 5 => ⟨((-6362215357/68719476736), (-138851915/4294967296)), (39/17179869184), by norm_num⟩
  | 6 => ⟨((5439586731/137438953472), (949728347/68719476736)), (17/17179869184), by norm_num⟩
  | 7 => ⟨((-3986361283/274877906944), (-696001461/137438953472)), (101/274877906944), by norm_num⟩
  | 8 => ⟨((2556203703/549755813888), (446302125/274877906944)), (33/274877906944), by norm_num⟩
  | 9 => ⟨((-2914014687/2199023255552), (-2035097509/4398046511104)), (153/4398046511104), by norm_num⟩
  | 10 => ⟨((5979440079/17592186044416), (2087968819/17592186044416)), (159/17592186044416), by norm_num⟩
  | 11 => ⟨((-5577076723/70368744177664), (-1947467011/70368744177664)), (75/35184372088832), by norm_num⟩
  | 12 => ⟨((1192076613/70368744177664), (1665051419/281474976710656)), (131/281474976710656), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581052275801731/10141204801825835211973625643008), (54702239427/1267650600228229401496703205376)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778507355997867/633825300114114700748351602688), (517752994639/633825300114114700748351602688)), (2883/79228162514264337593543950336), by norm_num⟩
  | 16 => ⟨((1889447857768983/39614081257132168796771975168), (72794810737/4951760157141521099596496896)), (25947/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889204685037243/2475880078570760549798248448), (309307141669/1237940039285380274899124224)), (13785/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770871078978819/154742504910672534362390528), (618455040261/154742504910672534362390528)), (27571/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549253945876255/9671406556917033397649408), (579632462085/9671406556917033397649408)), (25849/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258526792362681/604462909807314587353088), (507009330995/604462909807314587353088)), (22619/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471841689735777/18889465931478580854784), (823573288077/75557863725914323419136)), (18379/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297220739597207/4722366482869645213696), (617402838249/4722366482869645213696)), (13785/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((202626286253707/73786976294838206464), (848478827817/590295810358705651712)), (4739/73786976294838206464), by norm_num⟩
  | 8 => ⟨((227865993302779/9223372036854775808), (1059923873659/73786976294838206464)), (23697/36893488147419103232), by norm_num⟩
  | 7 => ⟨((28469417344341/144115188075855872), (1191487431241/9223372036854775808)), (53325/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593292237320769/1152921504606846976), (4649726057/4503599627370496)), (53333/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298493747344735/36028797018963968), (520118944353/72057594037927936)), (11669/36028797018963968), by norm_num⟩
  | 4 => ⟨((1490731031324271/36028797018963968), (778879550691/18014398509481984)), (35015/18014398509481984), by norm_num⟩
  | 3 => ⟨((1488128716653859/9007199254740992), (485665325829/2251799813685248)), (43785/4503599627370496), by norm_num⟩
  | 2 => ⟨((69553191054191/140737488355328), (3871743649693/4503599627370496)), (175233/4503599627370496), by norm_num⟩
  | 1 => ⟨((1106382280718257/1125899906842624), (2886892981351/1125899906842624)), (131545/1125899906842624), by norm_num⟩
  | 0 => ⟨((2174173014601439/2251799813685248), (11412958838407/2251799813685248)), (527151/2251799813685248), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2174173014601439/2251799813685248), (11412958838407/2251799813685248)), (2010921486861418967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2099164416421067/2251799813685248), (22039034706741/2251799813685248)), (511651/1125899906842624), by norm_num⟩
  | 2 => ⟨((978329756788375/1125899906842624), (41090293326693/2251799813685248)), (1927909/2251799813685248), by norm_num⟩
  | 3 => ⟨((212431630056949/281474976710656), (35704645175253/1125899906842624)), (1710401/1125899906842624), by norm_num⟩
  | 4 => ⟨((1280327555071189/2251799813685248), (26946608411947/562949953421312)), (5380381/2251799813685248), by norm_num⟩
  | 5 => ⟨((90351100656475/281474976710656), (245140691856199/4503599627370496)), (3316717/1125899906842624), by norm_num⟩
  | 6 => ⟨((901375115433823/9007199254740992), (9836012593255/281474976710656)), (19922791/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-150614483/67108864), (-4171483267/134217728)), (1/67108864), by norm_num⟩, -5, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-77483061/33554432), (-67062627/2097152)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((757162450357459/9007199254740992), (-238421143259391/4503599627370496)), (22125523/9007199254740992), by norm_num⟩
  | 1 => ⟨((-3811254719/17179869184), (2400234473/17179869184)), (113/17179869184), by norm_num⟩
  | 2 => ⟨((2514529925/8589934592), (-3167178189/17179869184)), (151/17179869184), by norm_num⟩
  | 3 => ⟨((-4423992419/17179869184), (696530401/4294967296)), (135/17179869184), by norm_num⟩
  | 4 => ⟨((2918792405/17179869184), (-459545915/4294967296)), (91/17179869184), by norm_num⟩
  | 5 => ⟨((-770286049/8589934592), (242553603/4294967296)), (49/17179869184), by norm_num⟩
  | 6 => ⟨((677609681/17179869184), (-1706967637/68719476736)), (11/8589934592), by norm_num⟩
  | 7 => ⟨((-4087430389/274877906944), (643540779/68719476736)), (135/274877906944), by norm_num⟩
  | 8 => ⟨((1348370391/274877906944), (-849170505/274877906944)), (91/549755813888), by norm_num⟩
  | 9 => ⟨((-790761503/549755813888), (1992008573/2199023255552)), (109/2199023255552), by norm_num⟩
  | 10 => ⟨((104343247/274877906944), (-1051404965/4398046511104)), (117/8796093022208), by norm_num⟩
  | 11 => ⟨((-801069995/8796093022208), (252247089/4398046511104)), (57/17592186044416), by norm_num⟩
  | 12 => ⟨((1409379761/70368744177664), (-1775185411/140737488355328)), (51/70368744177664), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1580967808634167/10141204801825835211973625643008), (-732101543127/10141204801825835211973625643008)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889203584300457/316912650057057350374175801344), (-866068725627/633825300114114700748351602688)), (721/19807040628566084398385987584), by norm_num⟩
  | 16 => ⟨((1889335154804255/39614081257132168796771975168), (-974131898537/39614081257132168796771975168)), (25957/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889084946908761/2475880078570760549798248448), (-1034771419449/2475880078570760549798248448)), (13791/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1770751350726449/154742504910672534362390528), (-1034497346593/154742504910672534362390528)), (27583/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387285427784437/2417851639229258349412352), (-60596885049/604462909807314587353088)), (12931/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258428597469903/604462909807314587353088), (-424032701215/302231454903657293676544)), (22631/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887207211947549/75557863725914323419136), (-344390229205/18889465931478580854784)), (18389/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1297101096603875/4722366482869645213696), (-1032693736477/4722366482869645213696)), (13793/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405211452242905/147573952589676412928), (-709589646579/295147905179352825856)), (2371/36893488147419103232), by norm_num⟩
  | 8 => ⟨((227840298402909/9223372036854775808), (-221601626701/9223372036854775808)), (47427/73786976294838206464), by norm_num⟩
  | 7 => ⟨((227726439239843/1152921504606846976), (-249102425613/1152921504606846976)), (26683/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593061113765875/1152921504606846976), (-1990827280443/1152921504606846976)), (13345/288230376151711744), by norm_num⟩
  | 5 => ⟨((298443209506451/36028797018963968), (-1739735367323/144115188075855872)), (23361/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490427968114963/36028797018963968), (-2605132628949/36028797018963968)), (70113/36028797018963968), by norm_num⟩
  | 3 => ⟨((743875087506227/4503599627370496), (-3248607339073/9007199254740992)), (87693/9007199254740992), by norm_num⟩
  | 2 => ⟨((1112472947642427/2251799813685248), (-1618462097239/1125899906842624)), (175543/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211632405307947/2251799813685248), (-4826281516269/1125899906842624)), (131855/1125899906842624), by norm_num⟩
  | 0 => ⟨((2171917444747751/2251799813685248), (-4768380205001/562949953421312)), (529015/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2171917444747751/2251799813685248), (-4768380205001/562949953421312)), (2018032082564543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2094707335410785/2251799813685248), (-36793779224921/2251799813685248)), (257365/562949953421312), by norm_num⟩
  | 2 => ⟨((973986455673281/1125899906842624), (-17113466030933/562949953421312)), (1948927/2251799813685248), by norm_num⟩
  | 3 => ⟨((841529630829847/1125899906842624), (-118435282017185/2251799813685248)), (3490425/2251799813685248), by norm_num⟩
  | 4 => ⟨((1251737186006345/2251799813685248), (-88521900168415/1125899906842624)), (2792425/1125899906842624), by norm_num⟩
  | 5 => ⟨((1363799274039735/4503599627370496), (-393662539781113/4503599627370496)), (14174489/4503599627370496), by norm_num⟩
  | 6 => ⟨((757162450357459/9007199254740992), (-238421143259391/4503599627370496)), (22125523/9007199254740992), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-77483061/33554432), (-67062627/2097152)), (1/67108864), by norm_num⟩, -5, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-159017401/67108864), (-2202107045/67108864)), (1/67108864), by norm_num⟩
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
  | 0 => ⟨((18102042192259/1125899906842624), (-207460600108429/2251799813685248)), (8039849/2251799813685248), by norm_num⟩
  | 1 => ⟨((-748004745/17179869184), (2143149261/8589934592)), (21/2147483648), by norm_num⟩
  | 2 => ⟨((63301075/1073741824), (-5803755787/17179869184)), (115/8589934592), by norm_num⟩
  | 3 => ⟨((-457126637/8589934592), (5238954009/17179869184)), (209/17179869184), by norm_num⟩
  | 4 => ⟨((1237921881/34359738368), (-7093675229/34359738368)), (285/34359738368), by norm_num⟩
  | 5 => ⟨((-83808865/4294967296), (1921002863/17179869184)), (39/8589934592), by norm_num⟩
  | 6 => ⟨((302611485/34359738368), (-3468114793/68719476736)), (71/34359738368), by norm_num⟩
  | 7 => ⟨((-468278339/137438953472), (5366759407/274877906944)), (111/137438953472), by norm_num⟩
  | 8 => ⟨((634060625/549755813888), (-3633363473/549755813888)), (303/1099511627776), by norm_num⟩
  | 9 => ⟨((-763141335/2199023255552), (1093258965/549755813888)), (23/274877906944), by norm_num⟩
  | 10 => ⟨((413325009/4398046511104), (-18503751/34359738368)), (201/8796093022208), by norm_num⟩
  | 11 => ⟨((-203509977/8796093022208), (4664700427/35184372088832)), (25/4398046511104), by norm_num⟩
  | 12 => ⟨((91852539/17592186044416), (-4210747643/140737488355328)), (91/70368744177664), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790444585791105/5070602400912917605986812821504), (-1821084314209/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222289007745431/79228162514264337593543950336), (-1077054808365/316912650057057350374175801344)), (361/9903520314283042199192993792), by norm_num⟩
  | 16 => ⟨((1889228065325923/39614081257132168796771975168), (-2422872427751/39614081257132168796771975168)), (25995/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472242759476205/618970019642690137449562112), (-1286839805981/1237940039285380274899124224)), (3453/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((221329662455621/19342813113834066795298816), (-1286489866949/77371252455336267181195264)), (6907/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549034637413403/9671406556917033397649408), (-2411425118543/9671406556917033397649408)), (12953/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258334757262917/604462909807314587353088), (-2109253864999/604462909807314587353088)), (22673/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887054439343605/75557863725914323419136), (-1713072381119/37778931862957161709568)), (36851/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648493135229023/2361183241434822606848), (-1284195234481/2361183241434822606848)), (27647/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202585940336355/73786976294838206464), (-882389636365/147573952589676412928)), (38027/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1822523929830809/73786976294838206464), (-137780703907/2305843009213693952)), (743/1152921504606846976), by norm_num⟩
  | 7 => ⟨((1821587426530959/9223372036854775808), (-4956030594999/9223372036854775808)), (53521/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398209000042685/288230376151711744), (-4950941708413/1152921504606846976)), (26777/576460752303423488), by norm_num⟩
  | 5 => ⟨((1193574712330557/144115188075855872), (-2163177621153/72057594037927936)), (2931/9007199254740992), by norm_num⟩
  | 4 => ⟨((1490128484916983/36028797018963968), (-6478110954951/36028797018963968)), (35209/18014398509481984), by norm_num⟩
  | 3 => ⟨((1487371823199721/9007199254740992), (-4038842701733/4503599627370496)), (88151/9007199254740992), by norm_num⟩
  | 2 => ⟨((2224177269325801/4503599627370496), (-16095650921667/4503599627370496)), (176689/4503599627370496), by norm_num⟩
  | 1 => ⟨((1105224954236977/1125899906842624), (-5998666414895/562949953421312)), (66501/562949953421312), by norm_num⟩
  | 0 => ⟨((1084717849759627/1125899906842624), (-23698507354813/1125899906842624)), (535907/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1084717849759627/1125899906842624), (-23698507354813/1125899906842624)), (2044322976119231467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((522271645636031/562949953421312), (-1426980419407/35184372088832)), (1055171/2251799813685248), by norm_num⟩
  | 2 => ⟨((1934426918504933/2251799813685248), (-169455100134221/2251799813685248)), (2043441/2251799813685248), by norm_num⟩
  | 3 => ⟨((1649033119865969/2251799813685248), (-36392945010631/281474976710656)), (3818421/2251799813685248), by norm_num⟩
  | 4 => ⟨((73123331218891/140737488355328), (-426419231672465/2251799813685248)), (822499/281474976710656), by norm_num⟩
  | 5 => ⟨((1054271479368705/4503599627370496), (-886222855902209/4503599627370496)), (18659297/4503599627370496), by norm_num⟩
  | 6 => ⟨((18102042192259/1125899906842624), (-207460600108429/2251799813685248)), (8039849/2251799813685248), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-159017401/67108864), (-2202107045/67108864)), (1/67108864), by norm_num⟩, -5, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨30,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile030Terms1

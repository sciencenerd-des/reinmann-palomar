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
namespace Reinmann.XiRectangle.Tile025Terms3
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨25,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((5/8), (7191/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((5/8), (7191/640))
  have he : value ((5/8), (7191/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-259295435/134217728), (-2330741837/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-1659490781/536870912), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((-1285362542734255/9007199254740992), (224931766296899/9007199254740992)), (13794041/2251799813685248), by norm_num⟩
  | 1 => ⟨((1894526571/4294967296), (-165766153/2147483648)), (41/2147483648), by norm_num⟩
  | 2 => ⟨((-1464015515/2147483648), (1024780433/8589934592)), (1/33554432), by norm_num⟩
  | 3 => ⟨((1508444703/2147483648), (-1055879941/8589934592)), (133/4294967296), by norm_num⟩
  | 4 => ⟨((-582833327/1073741824), (815942431/8589934592)), (207/8589934592), by norm_num⟩
  | 5 => ⟨((2882500091/8589934592), (-504422539/8589934592)), (129/8589934592), by norm_num⟩
  | 6 => ⟨((-1484988359/8589934592), (259865247/8589934592)), (67/8589934592), by norm_num⟩
  | 7 => ⟨((2622949749/34359738368), (-918005155/68719476736)), (119/34359738368), by norm_num⟩
  | 8 => ⟨((-2026912257/68719476736), (709398227/137438953472)), (93/68719476736), by norm_num⟩
  | 9 => ⟨((5569130521/549755813888), (-974568905/549755813888)), (257/549755813888), by norm_num⟩
  | 10 => ⟨((-1721441887/549755813888), (150621693/274877906944)), (5/34359738368), by norm_num⟩
  | 11 => ⟨((241865907/274877906944), (-677204433/4398046511104)), (181/4398046511104), by norm_num⟩
  | 12 => ⟨((-1993647431/8796093022208), (174438971/4398046511104)), (47/4398046511104), by norm_num⟩
  | _ => zero

def term22ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790729624827833/5070602400912917605986812821504), (1933304967801/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778977912784207/633825300114114700748351602688), (2288504815595/316912650057057350374175801344)), (5791/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((944988253221375/19807040628566084398385987584), (2574116388905/19807040628566084398385987584)), (13033/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889765438137021/2475880078570760549798248448), (5468915740499/2475880078570760549798248448)), (27703/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771430779621103/154742504910672534362390528), (5467698891923/154742504910672534362390528)), (27713/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774888773807871/4835703278458516698824704), (2562337447505/4835703278458516698824704)), (25991/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258983826973099/604462909807314587353088), (4482797812683/604462909807314587353088)), (711/18889465931478580854784), by norm_num⟩
  | 11 => ⟨((1888107347464861/75557863725914323419136), (7282122798647/75557863725914323419136)), (36991/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297774351346891/4722366482869645213696), (5459471612321/4722366482869645213696)), (1735/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621768535807517/590295810358705651712), (3751664030285/295147905179352825856)), (9549/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1823871302957005/73786976294838206464), (9373992641265/73786976294838206464)), (47785/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823097874368201/9223372036854775808), (5269318800217/4611686018427387904)), (53813/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199292471726853/144115188075855872), (10529759108819/1152921504606846976)), (26941/576460752303423488), by norm_num⟩
  | 5 => ⟨((597441509406733/72057594037927936), (1150444151423/18014398509481984)), (5903/18014398509481984), by norm_num⟩
  | 4 => ⟨((186509498279295/4503599627370496), (13785363571701/36028797018963968)), (4437/2251799813685248), by norm_num⟩
  | 3 => ⟨((1489780095700809/9007199254740992), (4299194155895/2251799813685248)), (89013/9007199254740992), by norm_num⟩
  | 2 => ⟨((139307237113493/281474976710656), (17144411289827/2251799813685248)), (44711/1125899906842624), by norm_num⟩
  | 1 => ⟨((1108681832062471/1125899906842624), (25585797223931/1125899906842624)), (16895/140737488355328), by norm_num⟩
  | 0 => ⟨((1091246597649343/1125899906842624), (6331110789847/140737488355328)), (137221/562949953421312), by norm_num⟩
  | _ => zero

def term22ValueSquares : ℕ → Disk
  | 0 => ⟨((1091246597649343/1125899906842624), (6331110789847/140737488355328)), (523456575633811773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((1055381406441511/1125899906842624), (98179997234547/1125899906842624)), (556683/1125899906842624), by norm_num⟩
  | 2 => ⟨((245179565806605/281474976710656), (92030688461815/562949953421312)), (71295/70368744177664), by norm_num⟩
  | 3 => ⟨((103020894187769/140737488355328), (320654354452909/1125899906842624)), (73757/35184372088832), by norm_num⟩
  | 4 => ⟨((1023949426372589/2251799813685248), (58680346485823/140737488355328)), (4799779/1125899906842624), by norm_num⟩
  | 5 => ⟨((148295920843215/4503599627370496), (1707738508784565/4503599627370496)), (33470735/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1285362542734255/9007199254740992), (224931766296899/9007199254740992)), (13794041/2251799813685248), by norm_num⟩
  | _ => zero

def term22Value : CertifiedScalarExp.Data :=
  ⟨⟨((-259295435/134217728), (-2330741837/67108864)), (1/67108864), by norm_num⟩, -6, term22ValuePoly, term22ValueSquares⟩

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
  | 0 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-263024319/134217728), (-591064961/16777216)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6733422557/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((-992650362402473/9007199254740992), (790799667902285/9007199254740992)), (57555157/9007199254740992), by norm_num⟩
  | 1 => ⟨((185516445/536870912), (-2364681039/8589934592)), (87/4294967296), by norm_num⟩
  | 2 => ⟨((-2326742961/4294967296), (926805465/2147483648)), (275/8589934592), by norm_num⟩
  | 3 => ⟨((2431829699/4294967296), (-1937328783/4294967296)), (145/4294967296), by norm_num⟩
  | 4 => ⟨((-1906246989/4294967296), (3037241597/8589934592)), (115/4294967296), by norm_num⟩
  | 5 => ⟨((2390810563/8589934592), (-476162673/2147483648)), (73/4294967296), by norm_num⟩
  | 6 => ⟨((-2498790897/17179869184), (1990673743/17179869184)), (77/8589934592), by norm_num⟩
  | 7 => ⟨((279819443/4294967296), (-891678001/17179869184)), (139/34359738368), by norm_num⟩
  | 8 => ⟨((-877372245/34359738368), (2795851215/137438953472)), (55/34359738368), by norm_num⟩
  | 9 => ⟨((1222664711/137438953472), (-1948083403/274877906944)), (155/274877906944), by norm_num⟩
  | 10 => ⟨((-3066926503/1099511627776), (2443281697/1099511627776)), (49/274877906944), by norm_num⟩
  | 11 => ⟨((1748423693/2199023255552), (-2785780229/4398046511104)), (113/2199023255552), by norm_num⟩
  | 12 => ⟨((-228423849/1099511627776), (2911599265/17592186044416)), (119/8796093022208), by norm_num⟩
  | _ => zero

def term23ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581423060041861/10141204801825835211973625643008), (1608005567543/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778938529708869/633825300114114700748351602688), (3806703915875/633825300114114700748351602688)), (23145/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889932405675451/39614081257132168796771975168), (4281789214259/39614081257132168796771975168)), (6511/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1889718845278981/2475880078570760549798248448), (1137122397947/618970019642690137449562112)), (13839/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((27677882559781/2417851639229258349412352), (4547464292387/154742504910672534362390528)), (13843/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549734460758283/9671406556917033397649408), (532769818677/1208925819614629174706176)), (6491/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1258946441222309/604462909807314587353088), (3728299681175/604462909807314587353088)), (22727/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((472011796571401/18889465931478580854784), (6056445386319/75557863725914323419136)), (18473/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648864873434041/2361183241434822606848), (2270274008071/2361183241434822606848)), (6931/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621708043008009/590295810358705651712), (1560087983199/147573952589676412928)), (19071/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823796943095741/73786976294838206464), (7796088755915/73786976294838206464)), (47711/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823015944439617/9223372036854775808), (8764618995923/9223372036854775808)), (6715/1152921504606846976), by norm_num⟩
  | 6 => ⟨((49820624894367/36028797018963968), (1094643239571/144115188075855872)), (26889/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194815630905249/144115188075855872), (7654099576789/144115188075855872)), (2945/9007199254740992), by norm_num⟩
  | 4 => ⟨((1491979726933601/36028797018963968), (11464353463509/36028797018963968)), (70809/36028797018963968), by norm_num⟩
  | 3 => ⟨((744834092359381/4503599627370496), (7150536105425/4503599627370496)), (44369/4503599627370496), by norm_num⟩
  | 2 => ⟨((139294819125631/281474976710656), (14257064294501/2251799813685248)), (89079/2251799813685248), by norm_num⟩
  | 1 => ⟨((277141012465831/281474976710656), (21275739855923/1125899906842624)), (134471/1125899906842624), by norm_num⟩
  | 0 => ⟨((1091134865115631/1125899906842624), (42113035897693/1125899906842624)), (272367/1125899906842624), by norm_num⟩
  | _ => zero

def term23ValueSquares : ℕ → Disk
  | 0 => ⟨((1091134865115631/1125899906842624), (42113035897693/1125899906842624)), (1038997654441451671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1055868091695787/1125899906842624), (81625376224961/1125899906842624)), (274145/562949953421312), by norm_num⟩
  | 2 => ⟨((492137319793001/562949953421312), (153096433714595/1125899906842624)), (1107873/1125899906842624), by norm_num⟩
  | 3 => ⟨((1679293234452975/2251799813685248), (535354648137113/2251799813685248)), (4476643/2251799813685248), by norm_num⟩
  | 4 => ⟨((562532502356721/1125899906842624), (399243943971331/1125899906842624)), (8805569/2251799813685248), by norm_num⟩
  | 5 => ⟨((557943342762467/4503599627370496), (1595791551188763/4503599627370496)), (30087893/4503599627370496), by norm_num⟩
  | 6 => ⟨((-992650362402473/9007199254740992), (790799667902285/9007199254740992)), (57555157/9007199254740992), by norm_num⟩
  | _ => zero

def term23Value : CertifiedScalarExp.Data :=
  ⟨⟨((-263024319/134217728), (-591064961/16777216)), (1/67108864), by norm_num⟩, -6, term23ValuePoly, term23ValueSquares⟩

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
  | 0 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-133297239/67108864), (-2396351113/67108864)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6824818633/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((-503810079528527/9007199254740992), (1128469862320711/9007199254740992)), (54489143/9007199254740992), by norm_num⟩
  | 1 => ⟨((763480927/4294967296), (-1710099205/4294967296)), (167/8589934592), by norm_num⟩
  | 2 => ⟨((-606595871/2147483648), (5434787329/8589934592)), (67/2147483648), by norm_num⟩
  | 3 => ⟨((1285196221/4294967296), (-179917153/268435456)), (143/4294967296), by norm_num⟩
  | 4 => ⟨((-1021105693/4294967296), (2287145589/4294967296)), (229/8589934592), by norm_num⟩
  | 5 => ⟨((2596103087/17179869184), (-181716795/536870912)), (293/17179869184), by norm_num⟩
  | 6 => ⟨((-85943285/1073741824), (3080030701/17179869184)), (157/17179869184), by norm_num⟩
  | 7 => ⟨((2497210387/68719476736), (-5593430495/68719476736)), (287/68719476736), by norm_num⟩
  | 8 => ⟨((-1984067259/137438953472), (2222027901/68719476736)), (115/68719476736), by norm_num⟩
  | 9 => ⟨((1401216123/274877906944), (-3138544125/274877906944)), (41/68719476736), by norm_num⟩
  | 10 => ⟨((-1781256107/1099511627776), (3989784871/1099511627776)), (105/549755813888), by norm_num⟩
  | 11 => ⟨((1029259599/2199023255552), (-4610818579/4398046511104)), (245/4398046511104), by norm_num⟩
  | 12 => ⟨((-2180694941/17592186044416), (4884476549/17592186044416)), (131/8796093022208), by norm_num⟩
  | _ => zero

def term24ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395347102722001/2535301200456458802993406410752), (1296552963597/5070602400912917605986812821504)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((111181264384679/39614081257132168796771975168), (3069253437189/633825300114114700748351602688)), (23127/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((236236185125505/4951760157141521099596496896), (1726150423057/19807040628566084398385987584)), (13011/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((944836723575601/1237940039285380274899124224), (229207840843/154742504910672534362390528)), (13827/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771339321049611/154742504910672534362390528), (3666488385187/154742504910672534362390528)), (6915/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1549692370572557/9671406556917033397649408), (1718221828401/4835703278458516698824704)), (12969/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629454931032661/302231454903657293676544), (3005999198601/604462909807314587353088)), (22703/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943994106551907/37778931862957161709568), (2441541126243/37778931862957161709568)), (4613/9444732965739290427392), by norm_num⟩
  | 10 => ⟨((1297685926093347/4722366482869645213696), (3660853981601/4722366482869645213696)), (27689/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621648453605935/590295810358705651712), (2515653129625/295147905179352825856)), (19045/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823723451462903/73786976294838206464), (6285582292793/73786976294838206464)), (47639/73786976294838206464), by norm_num⟩
  | 7 => ⟨((455733658203791/2305843009213693952), (1766600100341/2305843009213693952)), (53631/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594180390334379/1152921504606846976), (882538032189/144115188075855872)), (26839/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194747890148703/144115188075855872), (6170912812269/144115188075855872)), (11755/36028797018963968), by norm_num⟩
  | 4 => ⟨((23310655248207/562949953421312), (4621337132063/18014398509481984)), (35317/18014398509481984), by norm_num⟩
  | 3 => ⟨((93097038120837/562949953421312), (5764701685707/4503599627370496)), (88475/9007199254740992), by norm_num⟩
  | 2 => ⟨((2228505864126585/4503599627370496), (11493547604691/2251799813685248)), (177499/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216860711288699/2251799813685248), (34301737918667/2251799813685248)), (33453/281474976710656), by norm_num⟩
  | 0 => ⟨((2181931086145063/2251799813685248), (67890099775891/2251799813685248)), (270385/1125899906842624), by norm_num⟩
  | _ => zero

def term24ValueSquares : ℕ → Disk
  | 0 => ⟨((2181931086145063/2251799813685248), (67890099775891/2251799813685248)), (1031436924460982921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1056091702764349/1125899906842624), (65783609289885/1125899906842624)), (1080591/2251799813685248), by norm_num⟩
  | 2 => ⟨((1973536359039403/2251799813685248), (246819538847871/2251799813685248)), (1076729/1125899906842624), by norm_num⟩
  | 3 => ⟨((425651278190101/562949953421312), (432638222169867/2251799813685248)), (530847/281474976710656), by norm_num⟩
  | 4 => ⟨((75264470731239/140737488355328), (654242925650183/2251799813685248)), (4026957/1125899906842624), by norm_num⟩
  | 5 => ⟨((28370077847417/140737488355328), (174940053656479/562949953421312)), (6647125/1125899906842624), by norm_num⟩
  | 6 => ⟨((-503810079528527/9007199254740992), (1128469862320711/9007199254740992)), (54489143/9007199254740992), by norm_num⟩
  | _ => zero

def term24Value : CertifiedScalarExp.Data :=
  ⟨⟨((-133297239/67108864), (-2396351113/67108864)), (1/67108864), by norm_num⟩, -6, term24ValuePoly, term24ValueSquares⟩

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
  | 0 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-270018875/134217728), (-4854264325/134217728)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6912483199/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((46696841098817/9007199254740992), (1203790054759397/9007199254740992)), (47829357/9007199254740992), by norm_num⟩
  | 1 => ⟨((-286696115/17179869184), (-1847672799/4294967296)), (37/2147483648), by norm_num⟩
  | 2 => ⟨((115354899/4294967296), (5947429305/8589934592)), (15/536870912), by norm_num⟩
  | 3 => ⟨((-15471379/536870912), (-3190672735/4294967296)), (259/8589934592), by norm_num⟩
  | 4 => ⟨((199201791/8589934592), (2567594833/4294967296)), (105/4294967296), by norm_num⟩
  | 5 => ⟨((-64120583/4294967296), (-6611815149/17179869184)), (17/1073741824), by norm_num⟩
  | 6 => ⟨((137597463/17179869184), (7094203981/34359738368)), (147/17179869184), by norm_num⟩
  | 7 => ⟨((-253090941/68719476736), (-6524389055/68719476736)), (17/4294967296), by norm_num⟩
  | 8 => ⟨((101833539/68719476736), (2625149775/68719476736)), (221/137438953472), by norm_num⟩
  | 9 => ⟨((-291368459/549755813888), (-3755569399/274877906944)), (159/274877906944), by norm_num⟩
  | 10 => ⟨((93787889/549755813888), (4835484619/1099511627776)), (103/549755813888), by norm_num⟩
  | 11 => ⟨((-1715293/34359738368), (-5659936197/4398046511104)), (243/4398046511104), by norm_num⟩
  | 12 => ⟨((117788057/8796093022208), (6072877265/17592186044416)), (131/8796093022208), by norm_num⟩
  | _ => zero

def term25ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581355176385417/10141204801825835211973625643008), (249454079773/1267650600228229401496703205376)), (4853/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((444715737336401/158456325028528675187087900672), (2361972334925/633825300114114700748351602688)), (23109/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944923832274349/19807040628566084398385987584), (166046714333/2475880078570760549798248448)), (26001/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((59050911808313/77371252455336267181195264), (88194202119/77371252455336267181195264)), (27631/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((885647616212237/77371252455336267181195264), (176347656371/9671406556917033397649408)), (6909/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774825614663087/4835703278458516698824704), (2644522304185/9671406556917033397649408)), (12957/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629437027594437/302231454903657293676544), (2313264668635/604462909807314587353088)), (22679/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887930386126923/75557863725914323419136), (3757757346767/75557863725914323419136)), (36863/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297642869891807/4722366482869645213696), (1408591449765/2361183241434822606848)), (3457/590295810358705651712), by norm_num⟩
  | 9 => ⟨((1621589761129915/590295810358705651712), (3871782704035/590295810358705651712)), (38041/590295810358705651712), by norm_num⟩
  | 8 => ⟨((455912712423993/18446744073709551616), (604620507009/9223372036854775808)), (47571/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1822854004672509/9223372036854775808), (339861613187/576460752303423488)), (26773/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594101071122233/1152921504606846976), (5433040659549/1152921504606846976)), (26791/576460752303423488), by norm_num⟩
  | 5 => ⟨((597339977732349/72057594037927936), (4748576801387/144115188075855872)), (11731/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491782965820809/36028797018963968), (7112208943001/36028797018963968)), (35233/18014398509481984), by norm_num⟩
  | 3 => ⟨((23272406435993/140737488355328), (4435819057249/4503599627370496)), (2757/281474976710656), by norm_num⟩
  | 2 => ⟨((1114141973156025/2251799813685248), (17687508499449/4503599627370496)), (176869/4503599627370496), by norm_num⟩
  | 1 => ⟨((1108282900900103/1125899906842624), (26392198126369/2251799813685248)), (266363/2251799813685248), by norm_num⟩
  | 0 => ⟨((1090745885090003/1125899906842624), (26115131302561/1125899906842624)), (134245/562949953421312), by norm_num⟩
  | _ => zero

def term25ValueSquares : ℕ → Disk
  | 0 => ⟨((1090745885090003/1125899906842624), (26115131302561/1125899906842624)), (512104036571311773/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((528041870565687/562949953421312), (50599474844499/1125899906842624)), (1065339/2251799813685248), by norm_num⟩
  | 2 => ⟨((1976645623051887/2251799813685248), (1483182540481/17592186044416)), (2094313/2251799813685248), by norm_num⟩
  | 3 => ⟨((1719107477288783/2251799813685248), (333298689478027/2251799813685248)), (2014973/1125899906842624), by norm_num⟩
  | 4 => ⟨((1263097405362871/2251799813685248), (254452578675059/1125899906842624)), (7346201/2251799813685248), by norm_num⟩
  | 5 => ⟨((593494407511161/2251799813685248), (570918231645761/2251799813685248)), (2890463/562949953421312), by norm_num⟩
  | 6 => ⟨((46696841098817/9007199254740992), (1203790054759397/9007199254740992)), (47829357/9007199254740992), by norm_num⟩
  | _ => zero

def term25Value : CertifiedScalarExp.Data :=
  ⟨⟨((-270018875/134217728), (-4854264325/134217728)), (1/67108864), by norm_num⟩, -6, term25ValuePoly, term25ValueSquares⟩

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
  | 0 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-273308947/134217728), (-614176449/16777216)), (1/67108864), by norm_num⟩
  | 1 => ⟨((-6996709039/2147483648), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((135565640672077/2251799813685248), (1042980116018069/9007199254740992)), (9827379/2251799813685248), by norm_num⟩
  | 1 => ⟨((-1684898165/8589934592), (-1620354607/4294967296)), (31/2147483648), by norm_num⟩
  | 2 => ⟨((2744780439/8589934592), (5279271735/8589934592)), (51/2147483648), by norm_num⟩
  | 3 => ⟨((-1490459941/4294967296), (-1433364747/2147483648)), (7/268435456), by norm_num⟩
  | 4 => ⟨((2428031187/8589934592), (291877545/536870912)), (23/1073741824), by norm_num⟩
  | 5 => ⟨((-1582152001/8589934592), (-760772175/2147483648)), (61/4294967296), by norm_num⟩
  | 6 => ⟨((859133993/8589934592), (3304892253/17179869184)), (67/8589934592), by norm_num⟩
  | 7 => ⟨((-799754711/17179869184), (-3076473717/34359738368)), (63/17179869184), by norm_num⟩
  | 8 => ⟨((2605678055/137438953472), (5011724183/137438953472)), (207/137438953472), by norm_num⟩
  | 9 => ⟨((-1886566811/274877906944), (-226787239/17179869184)), (19/34359738368), by norm_num⟩
  | 10 => ⟨((1229323359/549755813888), (4728926197/1099511627776)), (25/137438953472), by norm_num⟩
  | 11 => ⟨((-2912912131/4398046511104), (-1400663461/1099511627776)), (239/4398046511104), by norm_num⟩
  | 12 => ⟨((1581758155/8796093022208), (1521165591/4398046511104)), (131/8796093022208), by norm_num⟩
  | _ => zero

def term26ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581323245535579/10141204801825835211973625643008), (1421595808309/10141204801825835211973625643008)), (19411/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((222353328538245/79228162514264337593543950336), (1682491096117/633825300114114700748351602688)), (5773/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((236225861781089/4951760157141521099596496896), (1892464362979/39614081257132168796771975168)), (25981/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889585976850663/2475880078570760549798248448), (1005162816367/1237940039285380274899124224)), (3451/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885626081709401/77371252455336267181195264), (1004927904879/77371252455336267181195264)), (27611/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774805496155751/4835703278458516698824704), (1883740775431/9671406556917033397649408)), (12945/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((314709746971689/151115727451828646838272), (1647774290567/604462909807314587353088)), (22657/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471968416056351/18889465931478580854784), (2676698143533/75557863725914323419136)), (36825/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297600557925849/4722366482869645213696), (501676437489/1180591620717411303424)), (27625/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((101345747167619/36893488147419103232), (2757892017389/590295810358705651712)), (37993/590295810358705651712), by norm_num⟩
  | 8 => ⟨((227947393718861/9223372036854775808), (1722686770213/36893488147419103232)), (23753/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822774108598605/9223372036854775808), (3873308735761/9223372036854775808)), (6683/1152921504606846976), by norm_num⟩
  | 6 => ⟨((398505532859933/288230376151711744), (1934945398443/576460752303423488)), (26745/576460752303423488), by norm_num⟩
  | 5 => ⟨((298652989258729/36028797018963968), (845578237969/36028797018963968)), (46833/144115188075855872), by norm_num⟩
  | 4 => ⟨((93230194399927/2251799813685248), (2532897821597/18014398509481984)), (35153/18014398509481984), by norm_num⟩
  | 3 => ⟨((744656464736079/4503599627370496), (1579709030423/2251799813685248)), (43991/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114026471959205/2251799813685248), (12597529594165/4503599627370496)), (176265/4503599627370496), by norm_num⟩
  | 1 => ⟨((2216247036614797/2251799813685248), (18796226516091/2251799813685248)), (132577/1125899906842624), by norm_num⟩
  | 0 => ⟨((2180964190607005/2251799813685248), (4649238734077/281474976710656)), (533345/2251799813685248), by norm_num⟩
  | _ => zero

def term26ValueSquares : ℕ → Disk
  | 0 => ⟨((2180964190607005/2251799813685248), (4649238734077/281474976710656)), (2034549721724700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((527935630076743/562949953421312), (72047777113973/2251799813685248)), (1050755/2251799813685248), by norm_num⟩
  | 2 => ⟨((247261410784315/281474976710656), (16891638579561/281474976710656)), (2038041/2251799813685248), by norm_num⟩
  | 3 => ⟨((1729542811095463/2251799813685248), (59353771826537/562949953421312)), (1912621/1125899906842624), by norm_num⟩
  | 4 => ⟨((651690348736669/1125899906842624), (182351714837359/1125899906842624)), (417671/140737488355328), by norm_num⟩
  | 5 => ⟨((1390703242280707/4503599627370496), (422193311902277/2251799813685248)), (4950425/1125899906842624), by norm_num⟩
  | 6 => ⟨((135565640672077/2251799813685248), (1042980116018069/9007199254740992)), (9827379/2251799813685248), by norm_num⟩
  | _ => zero

def term26Value : CertifiedScalarExp.Data :=
  ⟨⟨((-273308947/134217728), (-614176449/16777216)), (1/67108864), by norm_num⟩, -6, term26ValuePoly, term26ValueSquares⟩

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
  | 0 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-276474835/134217728), (-2485163173/67108864)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-55294967/16777216), 0), (1/2147483648), by norm_num⟩
  | 2 => ⟨(0, 0), 0, by norm_num⟩
  | 3 => ⟨(0, 0), 0, by norm_num⟩
  | 4 => ⟨(0, 0), 0, by norm_num⟩
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
  | 0 => ⟨((901847027029663/9007199254740992), (710529588077481/9007199254740992)), (15168941/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2834644965/8589934592), (-1116652303/4294967296)), (49/8589934592), by norm_num⟩
  | 2 => ⟨((4671263689/8589934592), (3680303827/8589934592)), (83/8589934592), by norm_num⟩
  | 3 => ⟨((-1282976923/2147483648), (-2021613505/4294967296)), (47/4294967296), by norm_num⟩
  | 4 => ⟨((4228482641/8589934592), (3331454159/8589934592)), (79/8589934592), by norm_num⟩
  | 5 => ⟨((-2787277795/8589934592), (-2195985887/8589934592)), (53/8589934592), by norm_num⟩
  | 6 => ⟨((3062137637/17179869184), (2412537081/17179869184)), (15/4294967296), by norm_num⟩
  | 7 => ⟨((-22527469/268435456), (-1135904093/17179869184)), (29/17179869184), by norm_num⟩
  | 8 => ⟨((4751799221/137438953472), (1871877293/68719476736)), (49/68719476736), by norm_num⟩
  | 9 => ⟨((-1740128339/137438953472), (-2741956529/274877906944)), (37/137438953472), by norm_num⟩
  | 10 => ⟨((4588143305/1099511627776), (3614816565/1099511627776)), (25/274877906944), by norm_num⟩
  | 11 => ⟨((-343676633/274877906944), (-2166153763/2199023255552)), (31/1099511627776), by norm_num⟩
  | 12 => ⟨((3020538979/8796093022208), (2379763143/8796093022208)), (35/4398046511104), by norm_num⟩
  | _ => zero

def term27ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790646259958961/5070602400912917605986812821504), (869225992823/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((111174450824651/39614081257132168796771975168), (514354381559/316912650057057350374175801344)), (11539/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1889767113231667/39614081257132168796771975168), (72318060793/2475880078570760549798248448)), (6491/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889543788322923/2475880078570760549798248448), (1229148730401/2475880078570760549798248448)), (6897/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771210063477101/154742504910672534362390528), (1228858242797/154742504910672534362390528)), (13795/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549571617683819/9671406556917033397649408), (4499008021/37778931862957161709568)), (6467/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((157350578636661/75557863725914323419136), (1007469353037/604462909807314587353088)), (5659/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1887818007315333/75557863725914323419136), (818279795539/37778931862957161709568)), (9197/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648779484612527/2361183241434822606848), (613457036661/2361183241434822606848)), (6899/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((405368755048121/147573952589676412928), (843092819225/295147905179352825856)), (9487/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823508356169913/73786976294838206464), (2106500964283/73786976294838206464)), (11861/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911347490050513/4611686018427387904), (2368122037847/9223372036854775808)), (13347/4611686018427387904), by norm_num⟩
  | 6 => ⟨((796971822373175/576460752303423488), (1183004696301/576460752303423488)), (26701/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298636000442523/36028797018963968), (516970987387/36028797018963968)), (23373/144115188075855872), by norm_num⟩
  | 4 => ⟨((186447826887059/4503599627370496), (3097083522007/36028797018963968)), (8769/9007199254740992), by norm_num⟩
  | 3 => ⟨((372297454518961/2251799813685248), (3863068985361/9007199254740992)), (43875/9007199254740992), by norm_num⟩
  | 2 => ⟨((2227814212161075/4503599627370496), (962667096939/562949953421312)), (87843/4503599627370496), by norm_num⟩
  | 1 => ⟨((276988444294819/281474976710656), (11490194461545/2251799813685248)), (131997/2251799813685248), by norm_num⟩
  | 0 => ⟨((2180359017157135/2251799813685248), (1420893534771/140737488355328)), (264929/2251799813685248), by norm_num⟩
  | _ => zero

def term27ValueSquares : ℕ → Disk
  | 0 => ⟨((2180359017157135/2251799813685248), (1420893534771/140737488355328)), (1010623940474700217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1055477615410031/1125899906842624), (11006513144303/562949953421312)), (259199/1125899906842624), by norm_num⟩
  | 2 => ⟨((494514839435417/562949953421312), (82544660866745/2251799813685248)), (992219/2251799813685248), by norm_num⟩
  | 3 => ⟨((1734570354777431/2251799813685248), (145020208161275/2251799813685248)), (226993/281474976710656), by norm_num⟩
  | 4 => ⟨((1326806866551761/2251799813685248), (223419286555959/2251799813685248)), (3031559/2251799813685248), by norm_num⟩
  | 5 => ⟨((759614719358361/2251799813685248), (526572995913707/4503599627370496)), (8348171/4503599627370496), by norm_num⟩
  | 6 => ⟨((901847027029663/9007199254740992), (710529588077481/9007199254740992)), (15168941/9007199254740992), by norm_num⟩
  | _ => zero

def term27Value : CertifiedScalarExp.Data :=
  ⟨⟨((-276474835/134217728), (-2485163173/67108864)), (1/134217728), by norm_num⟩, -6, term27ValuePoly, term27ValueSquares⟩

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
theorem term22Jet_sound : Sound term22Jet F_term22 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term22

def term23Jet : Jet 12 := J_term23
theorem term23Jet_sound : Sound term23Jet F_term23 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term23

def term24Jet : Jet 12 := J_term24
theorem term24Jet_sound : Sound term24Jet F_term24 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term24

def term25Jet : Jet 12 := J_term25
theorem term25Jet_sound : Sound term25Jet F_term25 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term25

def term26Jet : Jet 12 := J_term26
theorem term26Jet_sound : Sound term26Jet F_term26 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term26

def term27Jet : Jet 12 := J_term27
theorem term27Jet_sound : Sound term27Jet F_term27 (Data.centre ⟨25,by norm_num [Data.count]⟩) := S_term27

end Reinmann.XiRectangle.Tile025Terms3
